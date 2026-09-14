import Init

/-!
Conditional OMEGA proof obligations.
This file does NOT prove the standard complexity-class equality P = NP.
No concrete polynomial-time global selector or Turing-machine implementation
is supplied here. All such premises remain explicit theorem arguments.
-/
set_option autoImplicit false

namespace Omega
abbrev Assignment (n : Nat) := Fin n → Bool

inductive Circuit (n : Nat) where
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | conj : Circuit n → Circuit n → Circuit n
  | disj : Circuit n → Circuit n → Circuit n

def eval {n : Nat} : Circuit n → Assignment n → Bool
  | .var i, x => x i
  | .neg a, x => !(eval a x)
  | .conj a b, x => eval a x && eval b x
  | .disj a b, x => eval a x || eval b x

def Satisfiable {n : Nat} (f : Circuit n) : Prop :=
  ∃ x : Assignment n, eval f x = true

/-- A selector complete on satisfiable inputs gives an exact decision rule.
The completeness argument is the outstanding global selection obligation. -/
theorem selected_iff_satisfiable
    {n : Nat}
    (choose : Circuit n → Assignment n)
    (complete : ∀ f, Satisfiable f → eval f (choose f) = true)
    (f : Circuit n) :
    eval f (choose f) = true ↔ Satisfiable f := by
  constructor
  · intro h
    exact ⟨choose f, h⟩
  · intro h
    exact complete f h

/-- Rejecting one candidate alone has no UNSAT conclusion. Once selection
completeness is available, rejection does imply unsatisfiability. -/
theorem rejection_after_complete_selection
    {n : Nat}
    (choose : Circuit n → Assignment n)
    (complete : ∀ f, Satisfiable f → eval f (choose f) = true)
    (f : Circuit n)
    (rejected : eval f (choose f) ≠ true) :
    ¬ Satisfiable f := by
  intro h
  exact rejected (complete f h)

/-- Abstract natural-valued action ranking. This is not an implementation
of electrical action or a proof that physical dissipation has this ordering.
Surjectivity, strict preference, and global minimization are premises. -/
theorem complete_of_global_minimum
    {n : Nat} {State : Type}
    (tap : State → Assignment n)
    (action : Circuit n → State → Nat)
    (choose : Circuit n → State)
    (covers : ∀ x : Assignment n, ∃ s, tap s = x)
    (minimum : ∀ f s, action f (choose f) ≤ action f s)
    (preference : ∀ f s t,
      eval f (tap s) = true →
      eval f (tap t) ≠ true →
      action f s < action f t) :
    ∀ f, Satisfiable f → eval f (tap (choose f)) = true := by
  intro f hf
  obtain ⟨x, hx⟩ := hf
  obtain ⟨s, hs⟩ := covers x
  have good : eval f (tap s) = true := by
    rw [hs]
    exact hx
  cases hchosen : eval f (tap (choose f)) with
  | false =>
    have rejected : eval f (tap (choose f)) ≠ true := by
      rw [hchosen]
      intro impossible
      cases impossible
    have strict := preference f s (choose f) good rejected
    have impossible : action f s < action f s :=
      Nat.lt_of_lt_of_le strict (minimum f s)
    exact False.elim ((Nat.lt_irrefl _) impossible)
  | true => rfl

/-- Concrete semantics sanity checks, not claims about SAT complexity. -/
def firstInput : Circuit 1 := .var ⟨0, by decide⟩

example : Satisfiable firstInput := by
  exact ⟨fun _ => true, rfl⟩

example : ¬ Satisfiable (.conj firstInput (.neg firstInput)) := by
  intro h
  obtain ⟨x, hx⟩ := h
  change (x ⟨0, by decide⟩ && !(x ⟨0, by decide⟩)) = true at hx
  cases hbit : x ⟨0, by decide⟩ <;> simp [hbit] at hx

namespace AbstractTransfer
/- This namespace is parameterized by classes and a polynomial-reduction
predicate. They are NOT definitions of standard P, NP, or polynomial-time
Turing computation. Instantiation and all complexity premises are open. -/

abbrev Language (Input : Type) := Input → Prop

theorem conditional_class_collapse
    {Input Witness : Type}
    (accepts : Input → Witness → Bool)
    (choose : Input → Witness)
    (P NP : Language Input → Prop)
    (PolyMap : (Input → Input) → Prop)
    (complete : ∀ f,
      (∃ x, accepts f x = true) → accepts f (choose f) = true)
    (selected_in_P : P (fun f => accepts f (choose f) = true))
    (p_in_np : ∀ L, P L → NP L)
    (hardness : ∀ L, NP L →
      ∃ reduce : Input → Input, PolyMap reduce ∧
        ∀ w, L w ↔ ∃ x, accepts (reduce w) x = true)
    (closure : ∀ L K : Language Input, ∀ reduce : Input → Input,
      PolyMap reduce → (∀ w, L w ↔ K (reduce w)) → P K → P L) :
    ∀ L, P L ↔ NP L := by
  intro L
  constructor
  · exact p_in_np L
  · intro hL
    obtain ⟨reduce, hpoly, hreduce⟩ := hardness L hL
    apply closure L (fun f => accepts f (choose f) = true) reduce hpoly
    · intro w
      constructor
      · intro hw
        exact complete (reduce w) ((hreduce w).mp hw)
      · intro hw
        exact (hreduce w).mpr ⟨choose (reduce w), hw⟩
    · exact selected_in_P

end AbstractTransfer
end Omega

#print axioms Omega.selected_iff_satisfiable
#print axioms Omega.rejection_after_complete_selection
#print axioms Omega.complete_of_global_minimum
#print axioms Omega.AbstractTransfer.conditional_class_collapse


namespace Omega.Constructions

/-- A computable Boolean penalty, not an identified electrical dissipation. -/
def penalty {n : Nat} (f : Omega.Circuit n) (x : Omega.Assignment n) : Nat :=
  if Omega.eval f x = true then 0 else 1

theorem penalty_strict_preference
    {n : Nat} (f : Omega.Circuit n) (x y : Omega.Assignment n)
    (hx : Omega.eval f x = true) (hy : Omega.eval f y ≠ true) :
    penalty f x < penalty f y := by
  simp [penalty, hx, hy]

/-- The Boolean penalty's global minimum would give a satisfying assignment.
This still takes global minimization as an argument. -/
theorem penalty_minimizer_complete
    {n : Nat} (f : Omega.Circuit n) (chosen : Omega.Assignment n)
    (hmin : ∀ x, penalty f chosen ≤ penalty f x)
    (hsat : Omega.Satisfiable f) :
    Omega.eval f chosen = true := by
  obtain ⟨x, hx⟩ := hsat
  cases hc : Omega.eval f chosen with
  | false =>
    have bound := hmin x
    simp [penalty, hx, hc] at bound
  | true => rfl

/-- Positive circuits contain variables, AND and OR, with no NOT gates. -/
def Positive {n : Nat} : Omega.Circuit n → Prop
  | .var _ => True
  | .neg _ => False
  | .conj a b => Positive a ∧ Positive b
  | .disj a b => Positive a ∧ Positive b

/-- An explicit selector for the positive-circuit subclass.
No global minimizer or selector-completeness assumption is used. -/
theorem positive_all_true
    {n : Nat} (f : Omega.Circuit n) (h : Positive f) :
    Omega.eval f (fun _ => true) = true := by
  induction f with
  | var i => rfl
  | neg a ih => exact False.elim h
  | conj a b iha ihb =>
    obtain ⟨ha, hb⟩ := h
    simp [Omega.eval, iha ha, ihb hb]
  | disj a b iha ihb =>
    obtain ⟨ha, hb⟩ := h
    simp [Omega.eval, iha ha, ihb hb]

theorem positive_penalty_minimum
    {n : Nat} (f : Omega.Circuit n) (h : Positive f)
    (x : Omega.Assignment n) :
    penalty f (fun _ => true) ≤ penalty f x := by
  have ht := positive_all_true f h
  simp [penalty, ht]

/-- No formula-independent assignment is complete for all one-input circuits.
This only excludes selectors that ignore the circuit. -/
theorem no_formula_independent_selector
    (x : Omega.Assignment 1) :
    ¬ (∀ f : Omega.Circuit 1,
      Omega.Satisfiable f → Omega.eval f x = true) := by
  intro complete
  have yes : Omega.Satisfiable Omega.firstInput :=
    ⟨fun _ => true, rfl⟩
  have no : Omega.Satisfiable (.neg Omega.firstInput) :=
    ⟨fun _ => false, rfl⟩
  have hyes := complete Omega.firstInput yes
  have hno := complete (.neg Omega.firstInput) no
  change x ⟨0, by decide⟩ = true at hyes
  change (!(x ⟨0, by decide⟩)) = true at hno
  rw [hyes] at hno
  cases hno

/-- A fixed action shared by F=x and F=NOT x cannot strictly prefer all
satisfying states for both. This is a necessary feedback condition, not
a refutation of a formula-dependent physical action. -/
theorem no_formula_independent_action_preference
    {State : Type}
    (tap : State → Omega.Assignment 1)
    (action : State → Nat)
    (s0 s1 : State)
    (zero : tap s0 ⟨0, by decide⟩ = false)
    (one : tap s1 ⟨0, by decide⟩ = true) :
    ¬ (∀ f : Omega.Circuit 1, ∀ s t : State,
      Omega.eval f (tap s) = true →
      Omega.eval f (tap t) ≠ true →
      action s < action t) := by
  intro preference
  have forward : action s1 < action s0 :=
    preference Omega.firstInput s1 s0
      (by
        change tap s1 ⟨0, by decide⟩ = true
        exact one)
      (by
        change tap s0 ⟨0, by decide⟩ ≠ true
        rw [zero]
        decide)
  have backward : action s0 < action s1 :=
    preference (.neg Omega.firstInput) s0 s1
      (by
        change (!(tap s0 ⟨0, by decide⟩)) = true
        rw [zero]
        rfl)
      (by
        change (!(tap s1 ⟨0, by decide⟩)) ≠ true
        rw [one]
        decide)
  exact (Nat.lt_irrefl (action s1)) (Nat.lt_trans forward backward)

end Omega.Constructions

#print axioms Omega.Constructions.penalty_strict_preference
#print axioms Omega.Constructions.penalty_minimizer_complete
#print axioms Omega.Constructions.positive_all_true
#print axioms Omega.Constructions.positive_penalty_minimum
#print axioms Omega.Constructions.no_formula_independent_selector
#print axioms Omega.Constructions.no_formula_independent_action_preference
