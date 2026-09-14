# Lean 4: conditional OMEGA formalization

**This is not a definitive proof of P=NP.** A successful Lean check validates the implications below with all their hypotheses. It does not establish those hypotheses for the physical processor.

## File and verification

`Omega.lean` uses Lean core only, with toolchain `leanprover/lean4:v4.19.0`.
Run from this directory:

```sh
lean --version
lean -DwarningAsError=true Omega.lean
```

The GitHub Actions workflow **Lean conditional verification** performs this check and prints each named theorem's axioms. The workflow checks this conditional formalization, not the standard P=NP assertion. Consult the run for the precise commit before claiming verification.

## What the declarations say

- `selected_iff_satisfiable`: a witness selector complete on all satisfiable circuits yields an exact decision rule.
- `rejection_after_complete_selection`: with that completeness property, rejection implies unsatisfiability.
- `complete_of_global_minimum`: a surjective tap map, an action ranking strictly preferring satisfying configurations, and a global minimizer imply selector completeness. The natural-valued ranking is an abstract sufficient-condition model; it is not a formalization of physical dissipation.
- `AbstractTransfer.conditional_class_collapse`: an abstract pair of language classes coincides if the supplied selector belongs to the first class, the second reduces to satisfiability, reductions preserve the first class, and the first is contained in the second.

The names `P`, `NP`, and `PolyMap` in the last theorem are **parameters**, not the standard complexity classes defined through Turing machines. Consequently the theorem alone is not a formal P=NP proof.

## Outstanding constructions

1. A concrete uniform model of Turing machines, encodings, and polynomial time, with the standard P and NP definitions and reduction theorems.
2. A concrete formula-to-network compiler and deterministic global configuration selector.
3. A proof of selector completeness for every satisfiable input and of polynomial bit cost.
4. Formal correctness and bit-complexity proofs connecting that machine to the electrical simulation.

No `sorry`, `admit`, custom axiom, or hidden oracle is used in a proof body. Selection and complexity assumptions are explicit arguments, which still need constructions. An axiom-free conditional theorem does not discharge its hypotheses.

The LaTeX paper is intentionally unchanged: the user's condition requires a definitive verified proof before updating it as such.
