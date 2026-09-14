"use strict";
const {Q,equilibrium,squareGrid,evaluate,simulate}=require("./omega.cjs");
function run(){
  let assertions=0;
  function check(ok,msg){assertions++;if(!ok)throw Error(msg);}
  function fails(fn,msg){let threw=false;try{fn();}catch{threw=true;}check(threw,msg);}
  for(const dialect of ["grid","beol"])for(let op=0;op<8;op++)for(let a=0;a<2;a++)for(let b=0;b<2;b++){
    const table=dialect==="grid"
      ?[a&&b,a||b,a!==b,a===b,!(a&&b),!(a||b),!a,a]
      :[a&&b,a||b,!(a&&b),!(a||b),a!==b,a===b,!a,0];
    check(evaluate([a,b],[[op,0,1]],2,dialect)===Number(table[op]),"opcode");
  }
  // Independent analytic voltage divider, not supplied witness bits.
  const divider={size:3,edges:[[0,1,2],[1,2,1]],fixed:{0:1,2:0}};
  const d=equilibrium(divider);
  check(String(d.volts[1])==="2/3","voltage divider");
  check(String(d.power)==="2/3","dissipation");
  const equal=simulate(divider,[1],"2/3",[],0);
  check(equal.taps[0]===0,"strict threshold equality");
  check(equal.status==="CANDIDATE_REJECTED","rejection is not UNSAT");
  check(simulate(divider,[1],"1/2",[],0).status==="SAT_WITNESS","witness");
  fails(()=>equilibrium({size:2,edges:[[0,1,1]],fixed:{}}),"floating network");
  fails(()=>evaluate([1],[[0,1,0]],1),"forward dependency");
  fails(()=>Q.of(0.1),"float input");
  const grids=[];
  // Entire left boundary=1, entire right boundary=0: exact solution 1-x/m.
  // These are explicit analytic test fixtures, not the paper's midpoint source.
  for(const m of [1,2,3,4,5]){
    const fixed={};
    for(let y=0;y<=m;y++){fixed[y]=1;fixed[m*(m+1)+y]=0;}
    const net=squareGrid(m,fixed);
    check(net.edges.length===2*m*(m+1),"edge count");
    const r=equilibrium(net);
    for(let x=0;x<=m;x++)for(let y=0;y<=m;y++)
      check(r.volts[x*(m+1)+y].cmp(new Q(m-x,m))===0,"linear potential");
    check(r.power.cmp(new Q(m+1,m))===0,"analytic grid power");
    grids.push({m,nodes:net.size,edges:net.edges.length,free:r.freeNodes,eliminationUpdates:r.updates});
  }
  // Original paper's three-input circuit: (a AND NOT b) OR (b XOR c).
  const gates=[[6,1,1],[0,0,3],[2,1,2],[1,4,5]];
  let satisfying=0;
  for(let mask=0;mask<8;mask++){
    const t=[mask&1,(mask>>1)&1,(mask>>2)&1];
    const expected=Number((t[0]&&!t[1])||(t[1]!==t[2]));
    check(evaluate(t,gates,6)===expected,"original benchmark");
    satisfying+=expected;
  }
  const chains=[];
  for(const n of [10,20,50,100]){
    const gates=[];let last=0;
    for(let i=1;i<n;i++){gates.push([0,last,i]);last=n+gates.length-1;}
    check(evaluate(Array(n).fill(1),gates,last)===1,"AND true");
    check(evaluate(Array.from({length:n},(_,i)=>i===n-1?0:1),gates,last)===0,"AND false");
    chains.push({n,gates:gates.length});
  }
  return {assertions,originalBenchmark:{assignments:8,satisfying},grids,chains,
    scope:"Exact DC and digital unit tests; no RTL co-simulation or global SAT-selection benchmark."};
}
if(require.main===module)console.log(JSON.stringify(run(),null,2));
module.exports={run};
