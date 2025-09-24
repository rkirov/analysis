import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

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
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
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
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ _, hx ⟩; simp_all
    . grind [specification_axiom]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
  have : 1 ∉ image f_3_4_2 (preimage f_3_4_2 {1, 2, 3}) := by
    by_contra! h
    rw [mem_image] at h
    obtain ⟨x, hx⟩ := h
    rw [mem_preimage] at hx
    obtain ⟨ h1, h2 ⟩ := hx
    rw [f_3_4_2] at h2
    simp only [Object.ofnat_eq] at h2
    have : 2 * nat_equiv.symm x = 1 := by
      rw [← SetTheory.Object.natCast_inj]
      exact h2
    omega
  by_contra h
  rw [h] at this
  rw [mem_triple] at this
  tauto

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by sorry

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0, 1}:Set) ^ X).replace (P :=
    fun f x ↦ x = preimage (Classical.choose ((power_set_axiom f.val).mp f.property)) ({0} : Set))
    (by intro x y y' a; simp_all only)

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by sorry

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  apply ext
  intro x
  rw [union_axiom]
  constructor
  . intro h
    obtain ⟨ X, hx, hs ⟩ := h
    rw [mem_triple] at hs
    rcases hs with h | h | h <;>
    . simp only [EmbeddingLike.apply_eq_iff_eq] at h
      rw [h] at hx
      rw [mem_pair] at hx
      rw [mem_quad]
      tauto
  . intro h
    rw [mem_quad] at h
    rcases h with h | h | h | h
    . use (({2,3}:Set)); rw [h]; aesop
    . use (({2,3}:Set)); rw [h]; aesop
    . use (({4,5}:Set)); rw [h]; aesop
    . use (({4,5}:Set)); rw [h]; aesop


/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by grind))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]; grind
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

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
  constructor
  . intro h
    rw [iInter, iInter'] at h
    rw [specification_axiom''] at h
    obtain ⟨ h1, h2 ⟩ := h
    intro a
    have h3 := h2 a
    exact h3
  . intro h
    rw [iInter, iInter']
    rw [specification_axiom'']
    use h (nonempty_choose hI)

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_image] at h
    obtain ⟨ x', hx, hxf ⟩ := h
    rw [← hxf]
    rw [mem_preimage]
    rw [hf.2]
    exact hx
  . intro h
    rw [mem_preimage'] at h
    obtain ⟨ x', hx', hfx' ⟩  := h
    rw [mem_image]
    use (f x')
    constructor
    . exact hfx'
    . rw [hf.1]
      exact hx'


/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X): S ⊆ preimage f (image f S) := by
  intro x
  rw [mem_preimage']
  intro h
  set x' : X := ⟨ x, hS x h ⟩
  use x'
  constructor
  . rfl
  . rw [mem_image]
    use x'

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set): image f (preimage f U) ⊆ U := by
  intro x h
  rw [mem_image] at h
  obtain ⟨ y, hy, hf ⟩ := h
  rw [mem_preimage] at hy
  rw [← hf]
  exact hy


/- Exercise 3.4.2.  State and prove an assertion connecting `image f f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set): preimage f (image f (preimage f U)) = preimage f U := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_preimage'] at ⊢ h
    obtain ⟨ y, hy, hf ⟩ := h
    use y
    constructor
    . exact hy
    . exact (image_of_preimage f U) _ hf
  . intro h
    rw [mem_preimage'] at h
    obtain ⟨ y, hy, hf ⟩ := h
    apply preimage_of_image
    . exact preimage_in_domain f U
    . rw [mem_preimage']
      use y

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
  intro y hy
  rw [mem_inter]
  rw [mem_image] at ⊢ hy
  obtain ⟨ x, hx, hf ⟩ := hy
  rw [mem_inter] at hx
  constructor
  . use x
    constructor
    . exact hx.1
    . exact hf
  . rw [mem_image]
    use x
    constructor
    . exact hx.2
    . exact hf

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
  intro y hy
  rw [mem_sdiff] at hy
  obtain ⟨ h1, h2 ⟩ := hy
  rw [mem_image] at h1 ⊢
  obtain ⟨ x, hx, hf ⟩ := h1
  use x
  constructor
  . rw [mem_sdiff]
    constructor
    . exact hx
    . contrapose! h2
      rw [mem_image]
      use x
  . exact hf

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
  apply ext
  intro y
  rw [mem_union, mem_image]
  constructor
  . intro h
    obtain ⟨ x, hx, hf ⟩ := h
    rw [mem_union] at hx
    cases hx with
    | inl h =>
      left
      rw [mem_image]
      use x
    | inr h =>
      right
      rw [mem_image]
      use x
  . intro h
    repeat rw [mem_image] at h
    cases h with
    | inl h =>
      obtain ⟨ x, hx, hf ⟩ := h
      use x
      constructor
      . rw [mem_union]
        left
        exact hx
      . exact hf
    | inr h =>
      obtain ⟨ x, hx, hf ⟩ := h
      use x
      constructor
      . rw [mem_union]
        right
        exact hx
      . exact hf

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  apply isFalse
  push_neg
  use {0, 1, 2}
  use {0, 1}
  use fun x ↦ if x = ⟨0, by simp⟩ then ⟨0, by simp⟩ else
    if x = ⟨1, by simp⟩ then ⟨1, by simp⟩ else ⟨0, by simp⟩
  use {0, 1}
  use {1, 2}
  have :{0, 1} ∩ {1, 2} = ({1}:Set) := by
    apply ext
    intro x
    rw [mem_inter, mem_pair, mem_pair, mem_singleton]
    aesop
  rw [this]
  by_contra h
  rw [ext_iff] at h
  specialize h 0
  rw [mem_inter] at h
  repeat rw [mem_image] at h
  simp only [mem_singleton, Subtype.exists, Subtype.mk.injEq, mem_triple, exists_and_left,
    exists_prop, exists_eq_left, ofNat_inj', one_ne_zero, OfNat.one_ne_ofNat, or_false, or_true,
    ↓reduceIte, and_false, mem_pair, exists_eq_or_imp, zero_ne_one, OfNat.zero_ne_ofNat, or_self,
    and_self, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, iff_true] at h

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  apply isFalse
  push_neg
  use {0, 1, 2}
  use {0, 1}
  use fun x ↦ if x = ⟨0, by simp⟩ then ⟨0, by simp⟩ else
    if x = ⟨1, by simp⟩ then ⟨1, by simp⟩ else ⟨0, by simp⟩
  use {0, 1}
  use {1, 2}
  have :{0, 1} \ {1, 2} = ({0}:Set) := by
    apply ext
    intro x
    rw [mem_sdiff, mem_pair, mem_pair, mem_singleton]
    aesop
  rw [this]
  by_contra h
  rw [ext_iff] at h
  specialize h 0
  rw [mem_sdiff] at h
  repeat rw [mem_image] at h
  simp only [mem_singleton, Subtype.exists, Subtype.mk.injEq, mem_triple, exists_and_left,
    exists_prop, exists_eq_left, ofNat_inj', zero_ne_one, OfNat.zero_ne_ofNat, or_self, or_false,
    ↓reduceIte, and_self, mem_pair, exists_eq_or_imp, one_ne_zero, OfNat.one_ne_ofNat, or_true,
    and_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, not_true_eq_false, iff_false] at h

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

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
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
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by sorry

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by sorry

end Chapter3
