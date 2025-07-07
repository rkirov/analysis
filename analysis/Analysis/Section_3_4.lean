import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.
-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ y = f x ∧ x.val ∈ S) (by
    intro x y y' ⟨ hy, hy' ⟩
    simp_all
  )

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  rw [SetTheory.Set.replacement_axiom]
  apply exists_congr; intro x
  tauto

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
  apply SetTheory.Set.ext
  intro x
  rw [SetTheory.Set.specification_axiom'']
  rw [mem_image]
  constructor
  . intro h
    obtain ⟨s, hsS, hfs⟩ := h
    rw [← hfs]
    use (f s).property
    use s
  . intro h
    obtain ⟨hx, s, hs, hfs⟩ := h
    use s
    constructor
    . exact hs
    . rw [hfs]

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext x
  simp only [Set.mem_setOf_eq, _root_.Set.mem_image, mem_image]
  constructor
  . rintro ⟨s, hs, hf⟩
    use (f s)
    constructor
    . use s
    . exact hf
  . rintro ⟨y, ⟨s, hs, hf⟩ , hy⟩
    use s
    constructor
    . exact hs
    . rw [← hy]
      rw [coe_inj]
      exact hf

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (U: Set) :
  image f U ⊆ Y := by
  rw [SetTheory.Set.subset_def]
  intro x h
  rw [mem_image] at h
  obtain ⟨ x', ⟨ hx', hf ⟩ ⟩ := h
  rw [← hf]
  exact (f x').property

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by
  intro x h
  rw [mem_image] at h
  obtain ⟨ x', hx', hf ⟩ := h
  rw [← hf]
  exact (f x').property

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  apply SetTheory.Set.ext
  intro x
  rw [mem_image]
  constructor
  . intro h
    obtain ⟨x, hx, hf⟩ := h
    unfold f_3_4_2 at hf
    rw [mem_triple] at ⊢ hx
    -- todo: simplify so that one can use ⟨;⟩
    rcases hx with h | h | h
    .
      change ((x:Object) = ↑(1: nat)) at h
      rw [coe_inj] at h
      rw [h] at hf
      have : nat_equiv.symm 1 = 1 := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [this] at hf
      simp only [mul_one, Nat.cast_ofNat] at hf
      left
      rw [← hf]
      rfl
    . have : x = 2 := by
        rw [← coe_inj]
        exact h
      rw [this] at hf
      have : nat_equiv.symm 2 = 2 := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [this] at hf
      simp only [Nat.reduceMul, Nat.cast_ofNat] at hf
      right
      left
      rw [← hf]
      rfl
    . have : x = 3 := by
        rw [← coe_inj]
        exact h
      rw [this] at hf
      have : nat_equiv.symm 3 = 3 := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [this] at hf
      simp only [Nat.reduceMul, Nat.cast_ofNat] at hf
      right
      right
      rw [← hf]
      rfl
  . intro h
    rw [mem_triple] at h
    rcases h with h | h | h
    . rw [h]
      use 1
      constructor
      . rw [mem_triple]
        tauto
      . unfold f_3_4_2
        have : nat_equiv.symm 1 = 1 := by
          rw [Equiv.symm_apply_eq]
          rfl
        rw [this]
        rfl
    . rw [h]
      use 2
      constructor
      . rw [mem_triple]
        tauto
      . unfold f_3_4_2
        have : nat_equiv.symm 2 = 2 := by
          rw [Equiv.symm_apply_eq]
          rfl
        rw [this]
        rfl
    . rw [h]
      use 3
      constructor
      . rw [mem_triple]
        tauto
      . unfold f_3_4_2
        have : nat_equiv.symm 3 = 3 := by
          rw [Equiv.symm_apply_eq]
          rfl
        rw [this]
        rfl

/-- Example 3.4.3 is written using Mathlib's notion of image -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
  intro h
  rw [mem_image]
  use x

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
  use Nat
  use {0}
  use fun x ↦ ⟨0, by simp⟩
  use {0}
  use 1
  simp only [mem_singleton, Classical.not_imp]
  constructor
  . rw [mem_image]
    use 0
    simp only [mem_singleton, and_true]
    rfl
  . by_contra h
    have : ((1:Nat.toSubtype):Object) = 1 := by rfl
    rw [this] at h
    rw [ofNat_inj'] at h
    contradiction

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set :=
  X.specify (P := fun x ↦ (f x).val ∈ U)

theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by
  rw [specification_axiom']

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by
  rw [subset_def]
  intro x h
  rw [preimage] at h
  exact specification_axiom h

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.preimage_setOf_eq, _root_.Set.mem_image]
  constructor
  . intro h
    have hxX := preimage_in_domain _ _ _ h
    use ⟨ x, hxX⟩
    constructor
    . rw [← mem_preimage]
      apply h
    . rfl
  . intro h
    obtain ⟨x', ⟨ hx', hxf'⟩⟩  := h
    rw [← hxf']
    rw [mem_preimage]
    exact hx'

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by
  intro x h
  rw [preimage] at h
  exact specification_axiom h

/-- Example 3.4.5 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  apply SetTheory.Set.ext
  intro x
  constructor
  . intro h
    have hx := preimage_in_domain _ _ _ h
    let x': Nat := ⟨x, hx⟩
    have :x = x'.val := by rfl
    rw [this] at h
    rw [mem_preimage] at h
    rw [f_3_4_2] at h
    rw [mem_triple] at ⊢ h
    rcases h with h | h | h
    . left
      rw [SetTheory.Object.ofnat_eq] at h
      rw [← SetTheory.Object.ofnat_eq'] at h
      rw [ofNat_inj'] at h
      change 2 * nat_equiv.symm x' = 2 at h
      rw [mul_eq_left₀] at h
      rw [Equiv.symm_apply_eq] at h
      rw [this, h]
      rfl -- why does this work?
      exact Ne.symm (Nat.zero_ne_add_one 1)
    . right
      left
      rw [SetTheory.Object.ofnat_eq] at h
      rw [← SetTheory.Object.ofnat_eq'] at h
      rw [ofNat_inj'] at h
      change 2 * nat_equiv.symm x' = 4 at h
      have h2 (a: ℕ) : 2 * a = 4 → a = 2 := by omega
      apply (h2 _) at h
      rw [Equiv.symm_apply_eq] at h
      rw [this, h]
      rfl
    . right
      right
      rw [SetTheory.Object.ofnat_eq] at h
      rw [← SetTheory.Object.ofnat_eq'] at h
      rw [ofNat_inj'] at h
      change 2 * nat_equiv.symm x' = 6 at h
      have h2 (a: ℕ) : 2 * a = 6 → a = 3 := by omega
      apply (h2 _) at h
      rw [Equiv.symm_apply_eq] at h
      rw [this, h]
      rfl
  . intro h
    rw [mem_triple] at h
    rcases h with h | h | h
    . rw [h]
      have : (1:Object) = (1:Nat) := by rfl
      rw [this]
      rw [mem_preimage]
      rw [mem_triple]
      left
      simp_all only [Object.ofnat_eq]
      have : nat_equiv.symm 1 = 1 := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [this]
      simp only [mul_one, Nat.cast_ofNat]
    . rw [h]
      have : (2:Object) = (2:Nat) := by rfl
      rw [this]
      rw [mem_preimage]
      rw [mem_triple]
      right
      left
      simp_all only [Object.ofnat_eq]
      have : nat_equiv.symm 2 = 2 := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [this]
      simp only [Nat.reduceMul, Nat.cast_ofNat]
    . rw [h]
      have : (3:Object) = (3:Nat) := by rfl
      rw [this]
      rw [mem_preimage]
      rw [mem_triple]
      right
      right
      simp_all only [Object.ofnat_eq]
      have : nat_equiv.symm 3 = 3 := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [this]
      simp only [Nat.reduceMul, Nat.cast_ofNat]

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
  have : 1 ∉ image f_3_4_2 (preimage f_3_4_2 {1, 2, 3}) := by
    by_contra! h
    rw [mem_image] at h
    obtain ⟨x, hx⟩ := h
    rw [mem_preimage] at hx
    obtain ⟨ h1, h2 ⟩ := hx
    rw [f_3_4_2] at h2
    simp at h2
    have : 2 * nat_equiv.symm x = 1 := by
      rw [← SetTheory.Object.natCast_inj]
      exact h2
    omega
  by_contra h
  rw [h] at this
  rw [mem_triple] at this
  tauto


/-- Example 3.4.6 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by sorry

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by sorry

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := SetTheory.pow

/-- I could not make this a coercion because of a technical `semiOutParam` issue. -/
abbrev SetTheory.Set.object_of {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

theorem SetTheory.Set.power_set_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, object_of f = F := SetTheory.power_set_axiom X Y F

/-- Example 3.4.8 -/
abbrev f_3_4_8_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_8_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_8_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_8_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_8 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = object_of f_3_4_8_a
    ∨ F = object_of f_3_4_8_b ∨ F = object_of f_3_4_8_c ∨ F = object_of f_3_4_8_d := by sorry

/-- Lemma 3.4.9.  One needs to provide a suitable definition of the power set here. -/
abbrev SetTheory.Set.powerset (X:Set) : Set := sorry

theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by sorry

/-- Remark 3.4.10 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by sorry

/-- Axiom 3.11 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.11 -/
theorem SetTheory.Set.example_3_4_11 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  sorry

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by sorry

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by intro x y y' ⟨ h1, h2⟩; simp at h1 h2; rw [h1,h2]))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]
  constructor
  . intro h
    obtain ⟨ S, hx, hS ⟩ := h
    rw [replacement_axiom] at hS
    obtain ⟨ α, hα ⟩ := hS
    simp_all
    use α.val, α.property
  intro h
  obtain ⟨ α, hx ⟩ := h
  refine ⟨ A α, hx, ?_ ⟩
  rw [replacement_axiom]
  use α

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by sorry

/-- Connection with Mathlib indexed union
-/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by sorry

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by sorry

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  sorry

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by sorry

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage (image f S)` and `S`. -/
-- theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) : sorry := by sorry

/- Exercise 3.4.2.  State and prove an assertion connecting `image (preimage f U)` and `U`. -/
-- theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (U: Set) : sorry := by sorry

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by sorry

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by sorry

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by sorry

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`
  sorry

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`
  sorry

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by sorry

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by sorry

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by sorry

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by sorry

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by sorry

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = object_of f := by
  sorry

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  sorry

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by sorry

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by sorry

end Chapter3
