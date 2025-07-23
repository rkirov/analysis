import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  set P : Object → Prop := fun x ↦ False
  have he := h P
  simp [P] at he
  exact he

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  set P : Object → Prop := fun y ↦ y = x
  apply h P

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  set P : Object → Prop := fun y ↦ y = x₁ ∨ y = x₂
  exact h P

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  set P : Object → Prop := fun x ↦ x ∈ A ∨ x ∈ B
  exact h P

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  set P' : Object → Prop := fun x ↦ ∃ h : x ∈ A , P ⟨x, h⟩
  exact h P'

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  set P' : Object → Prop := fun x ↦ ∃ a : A, P a x
  exact h P'

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  set A': Set := {(A :Object)} with ha'
  have h_non_empty : A' ≠ ∅ := by
    have ha: (A:Object) ∈ A' := by rw [mem_singleton];
    apply nonempty_of_inhabited ha
  have h := axiom_of_regularity h_non_empty
  obtain ⟨ x, hx ⟩ := h
  have hx_in_a : (x:Object) ∈ A' := by simp [subtype_property]
  change (x:Object) ∈ {set_to_object A} at hx_in_a
  rw [mem_singleton] at hx_in_a
  rw [hx_in_a] at hx
  simp at hx
  rw [disjoint_iff] at hx
  rw [ha'] at hx
  rw [eq_empty_iff_forall_notMem] at hx
  contrapose! hx
  use A
  rw [mem_inter]
  constructor
  . exact hx
  . rw [mem_singleton]

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  set U: Set := {(A:Object), (B:Object)} with hu
  have ne : U ≠ ∅ := by
    rw [hu]
    apply nonempty_of_inhabited (show (A:Object) ∈ U by rw [hu]; simp)
  have h := axiom_of_regularity ne
  rw [hu] at h
  simp at h
  cases h with
  | inl h1 =>
    rw [disjoint_iff] at h1
    rw [eq_empty_iff_forall_notMem] at h1
    right
    specialize h1 B
    contrapose! h1
    rw [mem_inter]
    constructor
    . exact h1
    . rw [mem_pair]
      tauto
  | inr h2 =>
    rw [disjoint_iff] at h2
    rw [eq_empty_iff_forall_notMem] at h2
    left
    specialize h2 A
    contrapose! h2
    rw [mem_inter]
    constructor
    . exact h2
    . rw [mem_pair]
      tauto

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  . intro h
    set P : Object → Prop := fun x ↦ True
    obtain ⟨ U, hU ⟩ := h P
    use U
    simp only [iff_true, P] at hU
    exact hU
  . dsimp [axiom_of_universal_specification]
    intro hU
    obtain ⟨ U, hU ⟩ := hU
    intro P
    set P' : U → Prop := fun x => P x with hP
    use specify U P'
    intro x
    rw [hP]
    have xU : x ∈ U := hU x;
    rw [specification_axiom' P' ⟨x, xU⟩]

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  by_contra! h
  obtain ⟨ U, hU ⟩ := h
  specialize hU U
  have n := not_mem_self U
  contradiction

end Chapter3
