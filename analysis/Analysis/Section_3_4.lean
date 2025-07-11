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

theorem SetTheory.Set.image_in_codomain {X Y: Set} (f: X → Y) (U: Set) :
    image f U ⊆ Y := by
  rw [SetTheory.Set.subset_def]
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
    -- todo: simplify so that one can use <;>
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

theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h
    by_cases hx: x ∈ X
    . set x': X := ⟨ x, hx ⟩
      use x'
      have : x = x'.val := by rfl
      constructor
      . exact this
      . rw [this] at h
        rw [mem_preimage] at h
        exact h
    . exfalso
      rw [preimage] at h
      have := X.specification_axiom h
      contradiction
  . intro h
    obtain ⟨ x', hx', hfx' ⟩ := h
    rw [← hx']
    rw [mem_preimage]
    exact hfx'

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
    simp only [Object.ofnat_eq] at h2
    have : 2 * nat_equiv.symm x = 1 := by
      rw [← SetTheory.Object.natCast_inj]
      exact h2
    omega
  by_contra h
  rw [h] at this
  rw [mem_triple] at this
  tauto

/-- Example 3.4.6 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext x
  constructor
  . intro h
    simp only [Set.mem_preimage, Set.mem_insert_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, sq_eq_one_iff, Int.reduceNeg, Set.mem_singleton_iff] at h
    simp only [Int.reduceNeg, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h with h | h | h
    . tauto
    . tauto
    . have : x ^ 2 = 4 → x = 2 ∨ x = -2 := by
        -- norm_num, omega, aesop all fail :(
        have h2 : (x - 2) * (x + 2) = 0 := by
          ring_nf
          simp_all only [sub_self, Int.reduceNeg, neg_add_cancel]
        intro a
        simp_all only [sub_self, mul_eq_zero, Int.reduceNeg]
        cases h2 with
        | inl h =>
          left
          rw [← Int.add_left_inj (-2)]
          simp only [Int.reduceNeg, add_neg_cancel]
          exact h
        | inr h =>
          right
          rw [← Int.add_left_inj 2]
          simp
          exact h
      have this := this h
      tauto
  . intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    simp only [Set.mem_preimage, Set.mem_insert_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, sq_eq_one_iff, Int.reduceNeg, Set.mem_singleton_iff]
    rcases h with h | h | h | h | h <;> (rw [h]; tauto)

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  have : -2 ∈ (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) := by simp
  by_contra! h
  rw [h] at this
  contradiction

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
    ∨ F = object_of f_3_4_8_b ∨ F = object_of f_3_4_8_c ∨ F = object_of f_3_4_8_d := by
  rw [power_set_axiom]
  constructor
  . intro h
    obtain ⟨ x, hx ⟩ := h
    rw [← hx]
    by_cases h0: x ⟨4, by simp⟩ = ⟨0, by simp⟩
    . by_cases h1: x ⟨7, by simp⟩ = ⟨0, by simp⟩
      . left
        congr
        ext y
        have xin := y.property
        rw [mem_pair] at xin
        cases xin with
        | inl h =>
          have : y = ⟨4, by simp⟩ := by aesop
          rw [this]
          simp only [h0]
        | inr =>
          have : y = ⟨7, by simp⟩ := by aesop
          rw [this]
          simp only [h1]
      . have h2 : x ⟨7, by simp⟩ = ⟨1, by simp⟩ := by
          have hin := (x ⟨7, by simp⟩).property
          rw [mem_pair] at hin
          cases hin with
          | inl h =>
            exfalso
            have :x ⟨7, by simp⟩ = ⟨0, by simp⟩ := by ext; rw [h]
            contradiction
          | inr h => ext; rw [h]
        right
        left
        congr
        ext y
        congr
        have yin := y.property
        rw [mem_pair] at yin
        unfold f_3_4_8_b
        cases yin with
        | inl h =>
          have : y = ⟨ 4, by simp⟩ := by aesop
          rw [this]
          simp only [h0, ↓reduceIte]
        | inr h =>
          have : y = ⟨ 7, by simp⟩ := by aesop
          rw [this]
          have ne : 7 ≠ 4 := by norm_num
          simp only [h2, ne, ofNat_inj', ↓reduceIte]
    . have h1 : x ⟨4, by simp⟩ = ⟨1, by simp⟩ := by
        have hin := (x ⟨4, by simp⟩).property
        rw [mem_pair] at hin
        cases hin with
          | inl h =>
            exfalso
            have :x ⟨4, by simp⟩ = ⟨0, by simp⟩ := by ext; rw [h]
            contradiction
          | inr h => ext; rw [h]
      . by_cases h2: x ⟨7, by simp⟩ = ⟨0, by simp⟩
        . right; right; left;
          congr
          unfold f_3_4_8_c
          ext y
          have hy := y.property
          rw [mem_pair] at hy
          rcases hy <;> aesop
        . have h2' : x ⟨7, by simp⟩ = ⟨1, by simp⟩ := by
            have hin := (x ⟨7, by simp⟩).property
            rw [mem_pair] at hin
            cases hin with
              | inl h =>
                exfalso
                have :x ⟨7, by simp⟩ = ⟨0, by simp⟩ := by ext; rw [h]
                contradiction
              | inr h => ext; rw [h]
          right; right; right;
          congr
          unfold f_3_4_8_d
          ext y
          have hy := y.property
          rw [mem_pair] at hy
          rcases hy <;> aesop
  . intro h
    rcases h with h | h | h | h
    . use f_3_4_8_a; exact h.symm
    . use f_3_4_8_b; exact h.symm
    . use f_3_4_8_c; exact h.symm
    . use f_3_4_8_d; exact h.symm

/-- Lemma 3.4.9.  One needs to provide a suitable definition of the power set here. -/
abbrev SetTheory.Set.powerset (X:Set) : Set :=
  (({0, 1}:Set) ^ X).replace (P :=
    fun f x ↦ x = preimage (Classical.choose ((power_set_axiom f.val).mp f.property)) ({0} : Set))
    (by intro x y y' a; simp_all only)

open Classical
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  rw [powerset, replacement_axiom]
  constructor
  . intro h
    obtain ⟨ x, hx ⟩ := h
    rw [hx]
    simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq_left']
    exact preimage_in_domain _ _
  . intro h
    obtain ⟨ x', ⟨ hy, hysub⟩ ⟩ := h
    rw [hy]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.exists]
    set f : X → ({0, 1}:Set) := fun x ↦ if (x:Object) ∈ x' then ⟨0, by simp⟩ else ⟨1, by simp⟩ with hf
    use (function_to_object _ _ f)
    use (by rw [power_set_axiom]; use f)
    simp only [EmbeddingLike.apply_eq_iff_eq, choose_eq]
    apply SetTheory.Set.ext
    intro x
    constructor
    . intro hx
      set x'' : x' := ⟨x , hx⟩ with hx''
      have : (x'':Object) ∈ ↑(preimage f ({0}:Set)) := by
        rw [mem_preimage f ({0}:Set) ⟨x, (hysub _ hx)⟩]
        unfold f
        simp only [hx, ↓reduceIte, mem_singleton, f, x'']
      simp only [this, f, x'']
    . intro h
      have := preimage_in_domain f ({0}:Set)
      have hx := this x h
      set y: X := ⟨x, hx⟩ with hy
      have hpre: ↑y ∈ preimage f {0} := by simp_all only [f, y]
      rw [mem_preimage] at hpre
      rw [hf] at hpre
      simp only [mem_singleton, f, y] at hpre
      split at hpre
      next h1 => exact h1
      next _ => simp_all only [ofNat_inj', one_ne_zero, f, y]


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
    ∨ x = ({a,b,c}:Set) := by
  constructor
  . intro h
    rw [mem_powerset] at h
    obtain ⟨Y, hx, hY⟩ := h
    rw [hx]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    by_cases hc : c ∈ Y
    · by_cases hb : b ∈ Y
      · by_cases ha : a ∈ Y
        . right; right; right; right; right; right; right;
          apply ext
          intro y
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
        . right; right; right; right; right; right; left;
          apply ext
          intro y
          simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
      . by_cases ha : a ∈ Y
        . right; right; right; right; right; left;
          apply ext
          intro y
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
        . right; right; right; left;
          apply ext
          intro y
          simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
    . by_cases hb : b ∈ Y
      · by_cases ha : a ∈ Y
        . right; right; right; right; left;
          apply ext
          intro y
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
        . right; right; left;
          apply ext
          intro y
          simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
      . by_cases ha : a ∈ Y
        . right; left;
          apply ext
          intro y
          constructor
          . intro h; have hc := hY _ h; aesop
          . intro h; aesop
        . left
          apply ext
          intro y
          simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]
          contrapose! ha
          have := hY _ ha
          rw [mem_triple] at this
          aesop
  . intro h
    rcases h with h | h | h | h | h | h | h | h
    -- packing on one line for easier copy / paste
    -- todo: figure out how to use extract set from hypothesis and use <;>
    . rw [mem_powerset]; use ∅; constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]
    . rw [mem_powerset]; use ({a}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]; tauto;
    . rw [mem_powerset]; use ({b}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]; tauto;
    . rw [mem_powerset]; use ({c}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]; tauto;
    . rw [mem_powerset]; use ({a, b}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]; tauto;
    . rw [mem_powerset]; use ({a, c}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]; tauto;
    . rw [mem_powerset]; use ({b, c}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple]; tauto;
    . rw [mem_powerset]; use ({a, b, c}:Set); constructor; exact h; rw [subset_def]; intro x; simp [emptyset_mem, mem_singleton, mem_pair, mem_triple];

/-- Axiom 3.11 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.11 -/
theorem SetTheory.Set.example_3_4_11 :
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
  ext x
  simp
  constructor
  . intro h
    rw [union_axiom] at h
    obtain ⟨ s, hs, hS ⟩ := h
    use s
    constructor
    . use s
    . exact hs
  . intro h
    obtain ⟨ s, ⟨ hs, ⟨ hs', hs''⟩ ⟩, hS ⟩ := h
    rw [union_axiom]
    use hs
    constructor
    . rw [hs'] at hS
      simp only [Set.mem_setOf_eq] at hS
      exact hS
    . exact hs''

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

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext
  intro x
  rw [mem_iUnion]
  constructor
  . intro h
    obtain ⟨ a, ha ⟩ := h
    have hapos := a.property
    rw [mem_triple] at hapos
    rcases hapos with haeq | haeq | haeq
    . have ha' : a = ⟨1, by simp⟩ := by
        simp [← coe_inj]
        rw [haeq]
      rw [ha'] at ha
      rw [index_example] at ha
      aesop
    . have ha' : a = ⟨2, by simp⟩ := by
        simp [← coe_inj]
        rw [haeq]
      rw [ha'] at ha
      rw [index_example] at ha
      aesop
    . have ha' : a = ⟨3, by simp⟩ := by
        simp [← coe_inj]
        rw [haeq]
      rw [ha'] at ha
      rw [index_example] at ha
      aesop
  . intro h
    rw [mem_quad] at h
    rcases h with h | h | h | h
    . use ⟨1, by simp⟩ ; rw [index_example] ; aesop
    . use ⟨1, by simp⟩ ; rw [index_example] ; aesop
    . use ⟨3, by simp⟩ ; rw [index_example] ; aesop
    . use ⟨3, by simp⟩ ; rw [index_example] ; aesop

/-- Connection with Mathlib indexed union
-/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext x
  simp
  constructor
  . intro h
    rw [mem_iUnion] at h
    obtain ⟨ a, ha ⟩ := h
    use a
    use a.property
  . intro h
    obtain ⟨ a, ha, hi ⟩ := h
    rw [mem_iUnion]
    use ⟨a, ha⟩

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  apply ext
  intro x
  simp only [not_mem_empty, iff_false]
  rw [mem_iUnion]
  push_neg
  simp only [Subtype.forall, not_mem_empty, IsEmpty.forall_iff, implies_true]

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


/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`. -/
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
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_inter]
    repeat rw [mem_preimage'] at ⊢ h
    obtain ⟨ x', hx', hf ⟩ := h
    rw [mem_inter] at hf
    obtain ⟨ ha, hb ⟩ := hf
    constructor
    . use x'
    . rw [mem_preimage']
      use x'
  . intro h
    rw [mem_inter] at h
    rw [mem_preimage'] at ⊢ h
    rw [mem_preimage'] at h
    obtain ⟨ ha, hb ⟩ := h
    obtain ⟨ xa, hxa, hfa ⟩ := ha
    obtain ⟨ xb, hxb, hfb ⟩ := hb
    use xa
    constructor
    . exact hxa
    . rw [mem_inter]
      constructor
      . exact hfa
      . have : xa = xb := by
          rw [← coe_inj]
          rw [hxa, hxb]
        rw [this]
        exact hfb

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_union]
    rw [mem_preimage', mem_preimage']
    rw [mem_preimage'] at h
    obtain ⟨ x', hx', hf ⟩ := h
    rw [mem_union] at hf
    cases hf with
    | inl ha =>
      left
      use x'
    | inr hb =>
      right
      use x'
  . intro h
    rw [mem_union] at h
    rw [mem_preimage', mem_preimage'] at h
    rw [mem_preimage']
    cases h with
    | inl ha =>
      obtain ⟨ xa, hxa, hfa ⟩ := ha
      use xa
      constructor
      . exact hxa
      . rw [mem_union]
        left
        exact hfa
    | inr hb =>
      obtain ⟨ xb, hxb, hfb ⟩ := hb
      use xb
      constructor
      . exact hxb
      . rw [mem_union]
        right
        exact hfb

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_preimage'] at h
    obtain ⟨ x', hx', hf ⟩ := h
    rw [mem_sdiff] at ⊢ hf
    obtain ⟨ ha, hb ⟩ := hf
    constructor
    . rw [mem_preimage']
      use x'
    . contrapose! hb
      rw [mem_preimage'] at hb
      obtain ⟨ x'', hx'', hf ⟩ := hb
      have : x' = x'' := by
        rw [← coe_inj]
        rw [hx', hx'']
      rw [this]
      exact hf
  . intro h
    rw [mem_sdiff] at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [mem_preimage'] at ⊢ h1
    obtain ⟨ x , hx, hf ⟩ := h1
    use x
    constructor
    . exact hx
    . rw [mem_sdiff]
      constructor
      . exact hf
      . contrapose! h2
        rw [mem_preimage']
        use x

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
  constructor
  . intro h
    rw [Function.Surjective]
    intro y'
    obtain ⟨ y, hy ⟩ := y'
    specialize h {y}
    have : {y} ⊆ Y := by
      intro x hx
      rw [mem_singleton] at hx
      rw [hx]
      exact hy
    have h2 := h this
    rw [ext_iff] at h2
    specialize h2 y
    rw [mem_singleton] at h2
    simp only [iff_true] at h2
    rw [mem_image] at h2
    obtain ⟨x, hx, hf⟩ := h2
    use x
    rw [← coe_inj]
    rw [hf]
  . intro h
    rw [Function.Surjective] at h
    intro S hS
    apply subset_antisymm
    . exact image_of_preimage f S
    . intro s hs
      rw [mem_image]
      have hy := hS _ hs
      specialize h ⟨ s, hy ⟩
      obtain ⟨ x, hx ⟩ := h
      use x
      rw [hx]
      constructor
      . rw [mem_preimage]
        rw [hx]
        exact hs
      . rfl

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
  constructor
  . intro h
    rw [Function.Injective]
    intro a b ha
    specialize h {b.val}
    have :{b.val} ⊆ X := by
      intro x
      rw [mem_singleton]
      intro h
      rw [h]
      exact b.property
    have h1 := h this
    have : a.val ∈ preimage f (image f {↑b}) := by
      rw [mem_preimage]
      rw [ha]
      rw [mem_image]
      use b
      constructor <;> simp only [mem_singleton]
    rw [h1] at this
    rw [mem_singleton] at this
    rw [coe_inj] at this
    exact this
  . intro h
    rw [Function.Injective] at h
    intro S hS
    apply subset_antisymm
    . intro s
      rw [mem_preimage']
      intro hx
      obtain ⟨ x', hx', hf' ⟩ := hx
      rw [mem_image] at hf'
      obtain ⟨ x'', hx'', hf'' ⟩ := hf'
      have := h ((coe_inj _ _ _).mp hf'')
      rw [← hx']
      rw [← this]
      exact hx''
    . exact preimage_of_image f S hS

set_option pp.proofs true
open Classical
/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = object_of f := by
  use union ((powerset X).replace (P := fun X' Xout ↦
    have hX' := (mem_powerset _).mp X'.property
    Xout = union ((powerset Y).replace (P := fun Y' Yout ↦
      have hY' := (mem_powerset _).mp Y'.property
      Yout = set_to_object (Classical.choose hY' ^ Classical.choose hX')
    ) (by intro x y y' a; simp_all only))
  ) (by intro x y y' a; simp_all only))
  intro F
  constructor
  . intro h
    rw [union_axiom] at h
    obtain ⟨ S, hS, h ⟩ := h
    rw [replacement_axiom] at h
    obtain ⟨ X', hX ⟩ := h
    extract_lets hl at hX
    obtain ⟨ X'', hX'', hPx ⟩ := hl
    simp only [EmbeddingLike.apply_eq_iff_eq] at hX
    use X''
    rw [hX] at hS
    rw [union_axiom] at hS
    obtain ⟨ S', hS', h ⟩ := hS
    rw [replacement_axiom] at h
    obtain ⟨ Y', hY' ⟩ := h
    simp only [EmbeddingLike.apply_eq_iff_eq] at hY'
    rw [hY'] at hS'
    rw [power_set_axiom] at hS'
    obtain ⟨ f, hf ⟩ := hS'
    have h2 := Y'.property
    rw [mem_powerset] at h2
    obtain ⟨ Y'', hY'', hPy ⟩ := h2
    use Y''
    constructor
    . assumption
    . constructor
      . assumption
      .
        let f' : X'' → Y'' := fun x ↦ ⟨f ⟨x, (by
          -- why doesn't this work
          rw [Classical.choose_eq]
        )⟩, by
          rw [Classical.choose_eq]
        ⟩
        use f'
        rw [← hf]
        congr
        rw [Classical.choose_eq]
  . intro h
    obtain ⟨X', Y', hX', hY', f, hf⟩ := h
    rw [union_axiom]
    -- S should be
    -- have : (∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ Y':Set, Y' ⊆ Y ∧ ∃ f: X' → Y', F = object_of f) := by sorry
    -- use choose this
    -- but I am not sure if that makes sense

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {set_to_object X, set_to_object Y}
  intro x
  rw [union_axiom]
  constructor
  . intro h
    obtain ⟨ S, hx, hS⟩ := h
    rw [mem_pair] at hS
    simp only [EmbeddingLike.apply_eq_iff_eq] at hS
    cases hS with
    | inl h => rw [← h]; left; exact hx
    | inr h => rw [← h]; right; exact hx
  . intro h
    cases h with
    | inl h =>
      use X
      constructor
      . exact h
      . simp only [mem_pair, EmbeddingLike.apply_eq_iff_eq, true_or]
    | inr h =>
      use Y
      constructor
      . exact h
      . simp only [mem_pair, EmbeddingLike.apply_eq_iff_eq, or_true]

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
  repeat rw [iInter']
  apply ext
  intro x
  constructor
  . intro h
    rw [specification_axiom''] at ⊢ h
    obtain ⟨ h , ha⟩ := h
    have hb := ha β'
    use hb
  . intro h
    rw [specification_axiom''] at ⊢ h
    obtain ⟨ h , ha⟩ := h
    have hb := ha β
    use hb

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp only [mem_union, α.property, true_or]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp only [mem_union, α.property, or_true]⟩)
    = iUnion (I ∪ J) A := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_union] at h
    cases h with
    | inl h =>
      rw [mem_iUnion] at h ⊢
      obtain ⟨a, ha ⟩ := h
      use ⟨ a, by simp [a.property] ⟩
    | inr h =>
      rw [mem_iUnion] at h ⊢
      obtain ⟨a, ha ⟩ := h
      use ⟨ a, by simp [a.property] ⟩
  . intro h
    rw [mem_union]
    rw [mem_iUnion] at h
    repeat rw [mem_iUnion]
    obtain ⟨ a, ha ⟩ := h
    have hij := a.property
    rw [mem_union] at hij
    cases hij with
    | inl h =>
      left
      use ⟨a, h⟩
    | inr h =>
      right
      use ⟨a, h⟩

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
  contrapose! hI
  rw [eq_empty_iff_forall_notMem] at hI
  apply ext
  intro x
  simp only [not_mem_empty, iff_false]
  contrapose! hJ
  specialize hI x
  exfalso
  have : x ∈ I ∪ J := by rw [mem_union]; left; exact hJ
  contradiction

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_inter] at h
    obtain ⟨ ha , hb ⟩ := h
    rw [mem_iInter] at ha hb ⊢
    intro i
    have hi := i.property
    rw [mem_union] at hi
    cases hi with
    | inl h =>
      specialize ha ⟨ i, h ⟩
      exact ha
    | inr h =>
      specialize hb ⟨ i, h ⟩
      exact hb
  . intro h
    rw [mem_inter]
    rw [mem_iInter] at h
    repeat rw [mem_iInter]
    constructor <;>
    . intro i
      specialize h ⟨ i, by simp [i.property] ⟩
      exact h

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_sdiff] at h
    rw [mem_iInter]
    intro i
    rw [mem_sdiff]
    constructor
    . exact h.1
    . have h2 := h.2
      contrapose! h2
      rw [mem_iUnion]
      use i
  . intro h
    rw [mem_sdiff]
    rw [mem_iInter] at h
    have h2 := nonempty_def hI
    obtain ⟨i, hi⟩ := h2
    have h' := h ⟨i, hi⟩
    rw [mem_sdiff] at h'
    constructor
    . exact h'.1
    . rw [mem_iUnion]
      push_neg
      intro i
      specialize h i
      rw [mem_sdiff] at h
      exact h.2

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
  apply ext
  intro x
  rw [mem_sdiff]
  constructor
  . intro h
    obtain ⟨ h1, h2 ⟩ := h
    rw [mem_iUnion]
    simp only [mem_iInter, Subtype.forall, not_forall] at h2
    obtain ⟨i, Ai, hi⟩ := h2
    use ⟨i, Ai⟩
    rw [mem_sdiff]
    constructor
    . exact h1
    . exact hi
  . intro h
    rw [mem_iUnion] at h
    obtain ⟨ i, hi ⟩ := h
    rw [mem_sdiff] at hi
    constructor
    . exact hi.1
    . have h2 := hi.2
      contrapose! h2
      rw [mem_iInter] at h2
      specialize h2 i
      exact h2

end Chapter3
