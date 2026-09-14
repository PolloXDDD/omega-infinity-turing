# OMEGA INFINITY: deterministic Turing simulation

An exact electrical and Boolean simulation layer derived from Kaoru Aguilera Katayama's original conductive-GRID manuscript.

**Status:** fixed-conductance rational DC simulation is implemented and has a polynomial bit-complexity proof. The formula-dependent global configuration selector required for an unconditional P=NP proof is still open. This repository does not claim that P=NP has been proved.

## Run

```sh
node tests.cjs
```

No packages are required. JavaScript BigInt is used for exact rational arithmetic. Inputs are integers, BigInts, or rational strings such as "2/3"; floating-point coefficients are rejected.

- [omega.cjs](omega.cjs): exact Kirchhoff solver, grid generator, strict threshold readout, both OMEGA opcode tables.
- [tests.cjs](tests.cjs): 188 assertions, analytic network fixtures, original circuit truth table, and chains with 10/20/50/100 inputs.
- [results/validation.json](results/validation.json): actual results from executing these sources in the session's V8 runtime with an in-memory CommonJS adapter.
- [paper/omega_turing.tex](paper/omega_turing.tex): English research draft, exact simulation theorem and conditional P=NP transfer theorem.

Compile the paper with `pdflatex omega_turing.tex` twice from its directory. The TeX has not been compiled in this session; no PDF compilation result is claimed.

## Example

```javascript
const {simulate}=require("./omega.cjs");
const network={
  size:3,
  edges:[[0,1,2],[1,2,1]],
  fixed:{0:1,2:0}
};
console.log(simulate(network,[1],"1/2",[],0));
// voltage at node 1 = 2/3; tap = 1; SAT_WITNESS for F(x)=x
```

The output is a witness for the supplied circuit when accepted. CANDIDATE_REJECTED is not an UNSAT verdict. Conductance selection is an input, not an implicit argmin oracle.

## Model and resources

For order m the original lattice has (m+1)^2 vertices and 2m(m+1) edges. Supply fixed potentials and any injections explicitly. The matrix must be grounded sufficiently for a unique solution. Positive conductances and rational boundary data are required. Equality to the threshold reads zero, as in the original paper.

Dense Gaussian elimination is a reference polynomial algorithm, not a large-device performance implementation. It computes one specified configuration's equilibrium without enumerating conductance states. It does not model configuration switching, noise, nonlinear transistor behavior, or physical settling time. The digital evaluator accepts valid topological circuits; programming/reset cycles and malformed RTL addressing are outside its scope.

The next construction is a uniform formula-to-network compiler and polynomial-time selector whose taps satisfy every satisfiable input circuit. The paper states exactly how such a construction would imply P=NP.

## Provenance

The uploaded source manuscripts remain unchanged. The original hardware repositories were read only:
- https://github.com/PolloXDDD/Repository-The-OMEGA-INFINITY-KAORU-Processor
- https://github.com/PolloXDDD/ttsky-CRYPTOGRAPHY-DESTROYER-OMEGA-INFINITY

New simulation code and research draft were prepared with AI assistance. No fabrication, complete SAT solver, cryptographic attack, or unconditional complexity breakthrough is claimed by these new files.
