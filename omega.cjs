"use strict";
// Exact rational DC simulation of a specified OMEGA conductance configuration.
// Rational inputs: integers, BigInts, or strings such as "3/7"; no floats.
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){[a,b]=[b,a%b];}return a;}
class Q {
  constructor(a,b=1n){
    a=BigInt(a);b=BigInt(b);if(!b)throw Error("Zero denominator");
    if(b<0n){a=-a;b=-b;}const d=gcd(a,b);this.n=a/d;this.d=b/d;
  }
  static of(x){
    if(x instanceof Q)return x;
    if(typeof x==="number"&&!Number.isSafeInteger(x))throw Error("Use exact rational strings");
    if(typeof x==="string"){const p=x.split("/");if(p.length>2)throw Error("Invalid rational");return new Q(p[0],p[1]===undefined?1n:p[1]);}
    return new Q(x);
  }
  add(x){x=Q.of(x);return new Q(this.n*x.d+x.n*this.d,this.d*x.d);}
  sub(x){x=Q.of(x);return new Q(this.n*x.d-x.n*this.d,this.d*x.d);}
  mul(x){x=Q.of(x);return new Q(this.n*x.n,this.d*x.d);}
  div(x){x=Q.of(x);return new Q(this.n*x.d,this.d*x.n);}
  cmp(x){x=Q.of(x);const v=this.n*x.d-x.n*this.d;return v<0n?-1:v>0n?1:0;}
  toString(){return this.d===1n?String(this.n):this.n+"/"+this.d;}
}
function solveLinear(A,b){
  const n=b.length;
  if(A.length!==n||A.some(r=>r.length!==n))throw Error("Matrix dimensions");
  const M=A.map((r,i)=>[...r.map(Q.of),Q.of(b[i])]);let updates=0;
  for(let k=0;k<n;k++){
    let p=k;while(p<n&&!M[p][k].n)p++;
    if(p===n)throw Error("Singular network: specify sufficient boundary conditions");
    [M[k],M[p]]=[M[p],M[k]];
    for(let i=k+1;i<n;i++){
      const f=M[i][k].div(M[k][k]);M[i][k]=new Q(0);
      if(!f.n)continue;
      for(let j=k+1;j<=n;j++){M[i][j]=M[i][j].sub(f.mul(M[k][j]));updates++;}
    }
  }
  const x=Array(n);
  for(let i=n-1;i>=0;i--){
    let v=M[i][n];for(let j=i+1;j<n;j++)v=v.sub(M[i][j].mul(x[j]));
    x[i]=v.div(M[i][i]);
  }
  return {x,updates};
}
// network: {size, edges:[[u,v,g],...], fixed:{node:voltage}, injections?:{node:current}}
function equilibrium(net){
  const {size,edges,fixed,injections={}}=net;
  if(!Number.isSafeInteger(size)||size<1)throw Error("Invalid network size");
  const check=i=>{if(!Number.isSafeInteger(i)||i<0||i>=size)throw Error("Invalid node");};
  const fixedMap=new Map(Object.entries(fixed).map(([k,v])=>{const i=Number(k);check(i);return [i,Q.of(v)];}));
  const inj=new Map(Object.entries(injections).map(([k,v])=>{const i=Number(k);check(i);return [i,Q.of(v)];}));
  const free=Array.from({length:size},(_,i)=>i).filter(i=>!fixedMap.has(i));
  const index=new Map(free.map((v,i)=>[v,i]));
  const A=free.map(()=>free.map(()=>new Q(0)));
  const b=free.map(v=>inj.get(v)||new Q(0));
  const parsed=edges.map(([u,v,g])=>{
    check(u);check(v);g=Q.of(g);
    if(u===v||g.cmp(0)<=0)throw Error("Edges require distinct nodes and positive conductance");
    for(const [p,q] of [[u,v],[v,u]])if(index.has(p)){
      const i=index.get(p);A[i][i]=A[i][i].add(g);
      if(index.has(q))A[i][index.get(q)]=A[i][index.get(q)].sub(g);
      else b[i]=b[i].add(g.mul(fixedMap.get(q)));
    }
    return [u,v,g];
  });
  const {x,updates}=solveLinear(A,b);
  const volts=Array.from({length:size},(_,i)=>fixedMap.has(i)?fixedMap.get(i):x[index.get(i)]);
  const residual=Array.from({length:size},()=>new Q(0));
  let power=new Q(0);
  for(const [u,v,g] of parsed){
    const dv=volts[u].sub(volts[v]),current=g.mul(dv);
    residual[u]=residual[u].add(current);residual[v]=residual[v].sub(current);
    power=power.add(g.mul(dv.mul(dv)));
  }
  for(const u of free)if(residual[u].sub(inj.get(u)||0).n)throw Error("KCL verification failed");
  return {volts,power,updates,freeNodes:free.length};
}
// Original paper: order m means (m+1)^2 nodes and 2m(m+1) edges.
// Boundary voltages must be supplied explicitly; a return terminal is not inferred.
function squareGrid(m,fixed,g=1){
  if(!Number.isSafeInteger(m)||m<1)throw Error("Invalid grid order");
  const id=(x,y)=>x*(m+1)+y,edges=[];
  for(let x=0;x<=m;x++)for(let y=0;y<=m;y++){
    if(x<m)edges.push([id(x,y),id(x+1,y),g]);
    if(y<m)edges.push([id(x,y),id(x,y+1),g]);
  }
  return {size:(m+1)**2,edges,fixed};
}
function evaluate(taps,gates,output,dialect="grid"){
  if(!["grid","beol"].includes(dialect))throw Error("Unknown dialect");
  if(!taps.length||taps.some(x=>x!==0&&x!==1))throw Error("Boolean taps required");
  const nodes=[...taps];
  for(const gate of gates){
    if(gate.length!==3)throw Error("Expected [opcode,a,b]");
    const [op,ai,bi]=gate;
    if(!gate.every(Number.isSafeInteger)||op<0||op>7)throw Error("Invalid gate");
    const read=i=>{if(i>=0&&i<nodes.length)return nodes[i];throw Error("Topological operand required");};
    const a=read(ai),b=read(bi);
    const table=dialect==="grid"
      ?[a&b,a|b,a^b,1^a^b,1^(a&b),1^(a|b),1^a,a]
      :[a&b,a|b,1^(a&b),1^(a|b),a^b,1^a^b,1^a,0];
    nodes.push(table[op]);
  }
  if(!Number.isSafeInteger(output)||output<0||output>=nodes.length)throw Error("Invalid output");
  return nodes[output];
}
function simulate(net,tapNodes,threshold,gates,output,dialect="grid"){
  const dc=equilibrium(net),theta=Q.of(threshold);
  const taps=tapNodes.map(i=>{
    if(!Number.isSafeInteger(i)||i<0||i>=net.size)throw Error("Invalid tap");
    return dc.volts[i].cmp(theta)>0?1:0; // strict >, matching the original paper
  });
  const accepted=evaluate(taps,gates,output,dialect);
  return {voltages:dc.volts.map(String),power:String(dc.power),taps,accepted,
    status:accepted?"SAT_WITNESS":"CANDIDATE_REJECTED",updates:dc.updates};
}
module.exports={Q,solveLinear,equilibrium,squareGrid,evaluate,simulate};
