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
