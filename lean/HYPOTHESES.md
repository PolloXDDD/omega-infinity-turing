# Constructive work on the outstanding hypotheses

This update addresses individual hypotheses rather than claiming an unconditional P=NP proof. The LaTeX paper is unchanged.

## A concrete objective with proved preference

For a Boolean circuit F define penalty(F,x)=0 when F(x)=true and 1 otherwise.
The Lean theorem `penalty_strict_preference` proves the required strict ranking for this objective. `penalty_minimizer_complete` proves that a global minimizer accepts whenever F is satisfiable.

This objective is computed by evaluating F. It has **not** been shown equal to the original conductive grid's electrical dissipation. Defining the objective does not compute its global minimizer. Thus the physical-action hypothesis remains open.

## A subclass with a constructed selector

For circuits containing only variables, AND and OR (the `Positive` predicate), the explicit assignment setting every input to true satisfies the circuit. Lean proves `positive_all_true` and `positive_penalty_minimum` with no selector or minimizer hypothesis.

The assignment has n output bits and needs no search. Inspecting a tree circuit for positivity and evaluating it takes a traversal. These operational cost observations are not a Lean formalization of Turing-machine bit complexity. Arbitrary circuits with NOT gates remain outside this construction.

## A necessary condition on any general selector

`no_formula_independent_selector` proves that one fixed tap assignment cannot be complete for both F(x)=x and F(x)=NOT x.

`no_formula_independent_action_preference` proves that a formula-independent action cannot provide the claimed strict preference for both circuits if both tap patterns are realizable: one circuit requires A(s1)<A(s0), the other A(s0)<A(s1).

These theorems do **not** exclude formula-dependent selection or feedback. They show exactly why the compiler and physical feedback law must enter the action or selection mechanism. The original paper already describes formula-dependent boundary conditions at an abstract level; their explicit electrical implementation is the construction still needed.

## Remaining target

Construct explicit formula-dependent boundary/loading or switching equations from the source architecture, prove their global selection property for arbitrary circuits, and bound the complete deterministic implementation's bit cost polynomially. No generic SAT oracle, random success assumption, or exponential enumeration has been inserted into the new construction.

All named results are checked by the repository's pinned Lean 4 workflow. See its log for the exact commit and theorem axioms. These results do not discharge the standard P/NP definitions and complexity bridge, which remain explicit open obligations in lean/README.md.
