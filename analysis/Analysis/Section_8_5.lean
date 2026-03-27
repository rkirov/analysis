import Mathlib.Tactic
import Analysis.Section_8_4

/-!
# Analysis I, Section 8.5: Ordered sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of `PartialOrder`, `LinearOrder`, and `WellFoundedLT`, with some API.
- Strong induction.
- Zorn's lemma.

-/

namespace Chapter8

/-- Definition 8.5.1 - Here we just review the Mathlib `PartialOrder` class. -/

example {X:Type} [PartialOrder X] (x:X) : x ≤ x := le_refl x
example {X:Type} [PartialOrder X] {x y:X} (h₁: x ≤ y) (h₂: y ≤ x) : x = y := antisymm h₁ h₂
example {X:Type} [PartialOrder X] {x y z:X} (h₁: x ≤ y) (h₂: y ≤ z) : x ≤ z := le_trans h₁ h₂
example {X:Type} [PartialOrder X] (x y:X) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

def PartialOrder.mk {X:Type} [LE X]
  (hrefl: ∀ x:X, x ≤ x)
  (hantisymm: ∀ x y:X, x ≤ y → y ≤ x → x = y)
  (htrans: ∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) : PartialOrder X :=
{
  le := (· ≤ ·)
  le_refl := hrefl
  le_antisymm := hantisymm
  le_trans := htrans
}

example {X:Type} : PartialOrder (Set X) := by infer_instance
example {X:Type} (A B: Set X) : A ≤ B ↔ A ⊆ B := by rfl

/-- Definition 8.5.3.  Here we just review the Mathlib `LinearOrder` class. -/
example {X:Type} [LinearOrder X] : PartialOrder X := by infer_instance
def IsTotal (X:Type) [PartialOrder X] : Prop := ∀ x y:X, x ≤ y ∨ y ≤ x
example {X:Type} [LinearOrder X] : IsTotal X := le_total

open Classical in
noncomputable def LinearOrder.mk {X:Type} [PartialOrder X]
  (htotal: IsTotal X) : LinearOrder X :=
{
   le_total := htotal
   toDecidableLE := decRel LE.le
}

/- Examples 8.5.4 -/
#check inferInstanceAs (LinearOrder ℕ)
#check inferInstanceAs (LinearOrder ℚ)
#check inferInstanceAs (LinearOrder ℝ)
#check inferInstanceAs (LinearOrder EReal)


noncomputable def LinearOrder.subtype {X:Type} [LinearOrder X] (A: Set X) : LinearOrder A :=
LinearOrder.mk (by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  have : x ≤ y ∨ y ≤ x := le_total x y
  exact this
 )

theorem IsTotal.subtype {X:Type} [PartialOrder X] {A: Set X} (hA: IsTotal X) : IsTotal A := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA x y; simp_all

theorem IsTotal.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) (hAB: B ⊆ A) : IsTotal B := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA ⟨ x, hAB hx ⟩ ⟨ y, hAB hy ⟩; simp_all

abbrev X_8_5_4 : Set (Set ℕ) := { {1,2}, {2}, {2,3}, {2,3,4}, {5} }
example : ¬ IsTotal X_8_5_4 := by
  rw [IsTotal]
  push_neg
  use ⟨({2} : Set ℕ), by simp⟩
  use ⟨({5} : Set ℕ), by simp⟩
  constructor
  . simp
  . simp

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's `IsMax` and `IsMin`. -/
theorem IsMax.iff {X:Type} [PartialOrder X] (x:X) :
  IsMax x ↔ ¬ ∃ y, x < y := by rw [isMax_iff_forall_not_lt]; grind

theorem IsMin.iff {X:Type} [PartialOrder X] (x:X) :
  IsMin x ↔ ¬ ∃ y, x > y := by rw [isMin_iff_forall_not_lt]; grind

/-- Examples 8.5.6 -/
example : IsMin (⟨ {2}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMin.iff]; push_neg; intro ⟨x, hx⟩ hlt
  simp [X_8_5_4] at hx; obtain rfl | rfl | rfl | rfl | rfl := hx <;> simp_all <;> grind
example : IsMax (⟨ {1,2}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMax.iff]; push_neg; intro ⟨x, hx⟩ hlt
  simp [X_8_5_4] at hx
  obtain rfl | rfl | rfl | rfl | rfl := hx <;> simp_all [Set.ssubset_def]
  all_goals (obtain ⟨h, _⟩ := hlt; have := h (show (1:ℕ) ∈ {1, 2} by simp); simp_all)
example : IsMax (⟨ {2,3,4}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMax.iff]; push_neg; intro ⟨x, hx⟩ hlt
  simp [X_8_5_4] at hx
  obtain rfl | rfl | rfl | rfl | rfl := hx <;> simp_all [Set.ssubset_def]
  obtain ⟨h, _⟩ := hlt; have := h (show (3:ℕ) ∈ {2, 3, 4} by simp); simp_all
example : IsMin (⟨ {5}, by aesop ⟩ : X_8_5_4) ∧ IsMax (⟨ {5}, by aesop ⟩ : X_8_5_4) := by
  refine ⟨?_, ?_⟩
  · rw [IsMin.iff]; push_neg; intro ⟨x, hx⟩ hlt
    simp [X_8_5_4] at hx; obtain rfl | rfl | rfl | rfl | rfl := hx <;> simp_all <;> grind
  · rw [IsMax.iff]; push_neg; intro ⟨x, hx⟩ hlt
    simp [X_8_5_4] at hx; obtain rfl | rfl | rfl | rfl | rfl := hx <;> simp_all <;> grind
example : ¬ IsMin (⟨ {2,3}, by aesop ⟩ : X_8_5_4) ∧ ¬ IsMax (⟨ {2,3}, by aesop ⟩ : X_8_5_4) := by
  simp only [IsMin.iff, IsMax.iff, not_not]
  exact ⟨⟨⟨{2}, by simp⟩, by constructor <;> simp⟩, ⟨⟨{2,3,4}, by simp⟩, by constructor <;> simp⟩⟩

/-- Example 8.5.7 -/
example : IsMin (0:ℕ) := by
  rw [IsMin.iff]; push_neg; omega
example (n:ℕ) : ¬ IsMax n := by
  simp only [IsMax.iff, not_not]; exact ⟨n + 1, by omega⟩
example (n:ℤ): ¬ IsMin n ∧ ¬ IsMax n := by
  simp only [IsMin.iff, IsMax.iff, not_not]
  exact ⟨⟨n - 1, by omega⟩, ⟨n + 1, by omega⟩⟩

/-- Definition 8.5.8.  We use `[LinearOrder X] [WellFoundedLT X]` to describe well-ordered sets. -/
theorem WellFoundedLT.iff (X:Type) [LinearOrder X] :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := by
  unfold WellFoundedLT IsMin
  rw [isWellFounded_iff, WellFounded.wellFounded_iff_has_min]
  peel with A hA; constructor
  . intro ⟨ x, hxA, h ⟩; use ⟨ x, hxA ⟩; intro ⟨ y, hy ⟩ this; specialize h y hy
    simp at *; order
  intro ⟨ ⟨ x, hx ⟩, h ⟩; refine ⟨ _, hx, ?_ ⟩; intro y hy; specialize h (b := ⟨ _, hy ⟩)
  simp at h; contrapose! h; simp [h]; order

theorem WellFoundedLT.iff' {X:Type} [PartialOrder X] (h: IsTotal X) :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := @iff X (LinearOrder.mk h)

/-- Example 8.5.9 -/
example : WellFoundedLT ℕ := by
  rw [WellFoundedLT.iff]
  intro A hA; use ⟨ _, (Nat.min_spec hA).1 ⟩
  simp [IsMin]; grind [Nat.min_spec]

/-- Exercise 8.1.2 -/
example : ¬ WellFoundedLT ℤ := by
  rw [WellFoundedLT.iff]
  push_neg
  use .univ
  simp
  intro n
  use n - 1
  omega
example : ¬ WellFoundedLT ℚ := by
  rw [WellFoundedLT.iff]
  push_neg
  use .univ
  simp
  intro q
  use q - 1
  linarith
example : ¬ WellFoundedLT ℝ := by
  rw [WellFoundedLT.iff]
  push_neg
  use .univ
  simp
  intro r
  use r - 1
  linarith

/-- Exercise 8.5.8 -/
theorem IsMax.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMax x := by
  obtain ⟨a⟩ := ‹Nonempty X›
  by_cases ha : IsMax a
  · exact ⟨a, ha⟩
  · rw [IsMax.iff] at ha; push_neg at ha; obtain ⟨b, hb⟩ := ha
    have hne : Nonempty ({a}ᶜ : Set X) := ⟨⟨b, by simp [ne_of_gt hb]⟩⟩
    obtain ⟨⟨m, hm⟩, hmax⟩ := IsMax.ofFinite (X := ({a}ᶜ : Set X))
    use m
    have key : ∀ x : X, x ≠ a → x ≤ m := by
      intro x hx
      have h := le_total (α := ({a}ᶜ : Set X)) ⟨x, by simp [hx]⟩ ⟨m, hm⟩
      rcases h with h | h
      · exact h
      · exact hmax h
    intro y hy
    by_cases hay : y = a
    · exact hay ▸ le_trans (le_of_lt hb) (key b (ne_of_gt hb))
    · exact key y hay
  termination_by Nat.card X
  decreasing_by
    simp only [Nat.card_coe_set_eq, gt_iff_lt]
    rw [← Set.ncard_univ]; exact Set.ncard_lt_ncard (by constructor <;> simp) (Set.toFinite _)

theorem IsMin.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMin x := by
  obtain ⟨a⟩ := ‹Nonempty X›
  by_cases ha : IsMin a
  · exact ⟨a, ha⟩
  · rw [IsMin.iff] at ha; push_neg at ha; obtain ⟨b, hb⟩ := ha
    have hne : Nonempty ({a}ᶜ : Set X) := ⟨⟨b, by simp [ne_of_lt hb]⟩⟩
    obtain ⟨⟨m, hm⟩, hmin⟩ := IsMin.ofFinite (X := ({a}ᶜ : Set X))
    use m
    have key : ∀ x : X, x ≠ a → m ≤ x := by
      intro x hx
      have h := le_total (α := ({a}ᶜ : Set X)) ⟨m, hm⟩ ⟨x, by simp [hx]⟩
      rcases h with h | h
      · exact h
      · exact hmin h
    intro y hy
    by_cases hay : y = a
    · exact hay ▸ le_trans (key b (ne_of_lt hb)) (le_of_lt hb)
    · exact key y hay
  termination_by Nat.card X
  decreasing_by
    simp
    rw [← Set.ncard_univ]; exact Set.ncard_lt_ncard (by constructor <;> simp) (Set.toFinite _)

/-- Exercise 8.5.8 --/
theorem WellFoundedLT.ofFinite {X:Type} [LinearOrder X] [Finite X] : WellFoundedLT X := by
  rw [WellFoundedLT.iff]
  intro A hA
  haveI : Nonempty A := hA.coe_sort
  exact IsMin.ofFinite

example {X:Type} [LinearOrder X] [WellFoundedLT X] (A: Set X) : WellFoundedLT A := by
  rw [WellFoundedLT.iff]; intro B hB
  obtain ⟨⟨x, hxB⟩, hmin⟩ := (WellFoundedLT.iff X).mp ‹_› (Subtype.val '' B) (by aesop)
  simp at hxB; obtain ⟨hxA, hxB'⟩ := hxB
  exact ⟨⟨⟨x, hxA⟩, hxB'⟩, fun ⟨⟨y, hy⟩, hyB⟩ hle =>
    hmin (b := ⟨y, by simp; exact ⟨hy, hyB⟩⟩) hle⟩

theorem WellFoundedLT.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) [hwell: WellFoundedLT A] (hAB: B ⊆ A) : WellFoundedLT B := by
  set hAlin : LinearOrder A := LinearOrder.mk hA
  set hBlin : LinearOrder B := LinearOrder.mk (hA.subset hAB)
  rw [iff] at hwell ⊢; intro C hC
  have ⟨ ⟨ ⟨ x, hx ⟩, hx' ⟩, hmin ⟩ := hwell ((B.embeddingOfSubset _ hAB) '' C) (by aesop)
  simp at hx'; choose y hy hyC this using hx'; use ⟨ _, hyC ⟩
  simp_all [IsMin, Set.embeddingOfSubset]; grind

/-- Proposition 8.5.10 / Exercise 8.5.10 -/
theorem WellFoundedLT.strong_induction {X:Type} [LinearOrder X] [WellFoundedLT X] {P:X → Prop}
  (h: ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  let Y := { n : X | ∃ m ≤ n , ¬ P m }
  have := (WellFoundedLT.iff X).mp inferInstance
  specialize this Y
  by_cases hY : Y.Nonempty
  . exfalso
    specialize this hY
    obtain ⟨m, hm⟩ := this
    specialize h m
    have hk : ∀ k < m.val, P k := by
      intro k hk
      by_contra hP
      have hkY : k ∈ Y := ⟨k, le_refl k, hP⟩
      have hkm : (⟨k, hkY⟩ : Y) ≤ m := hk.le
      have hmk : m ≤ ⟨k, hkY⟩ := hm hkm
      exact absurd hk (not_lt.mpr hmk)
    have hmn : ¬ P m := by
      obtain ⟨k, hkm, hkP⟩ := m.prop
      rcases hkm.eq_or_lt with rfl | hlt
      · exact hkP
      · exact absurd (hk k hlt) hkP
    exact hmn (h hk)
  . intro n
    by_contra hn
    exact hY ⟨n, n, le_refl n, hn⟩

/-- Definition 8.5.12 (Upper bounds and strict upper bounds) -/
abbrev IsUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  ∀ y ∈ A, y ≤ x

/-- Connection with Mathlib's `upperBounds` -/
theorem IsUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsUpperBound A x ↔ x ∈ upperBounds A := by simp [IsUpperBound, upperBounds]

abbrev IsStrictUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  IsUpperBound A x ∧ x ∉ A

theorem IsStrictUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ ∀ y ∈ A, y < x := by
  simp [IsStrictUpperBound, IsUpperBound]
  constructor
  · intro ⟨h1, h2⟩ y hy
    exact lt_of_le_of_ne (h1 y hy) (fun h => h2 (h ▸ hy))
  · intro h
    constructor
    · intro y hy
      exact (h y hy).le
    · intro hx
      exact absurd (h x hx) (lt_irrefl x)

theorem IsStrictUpperBound.iff' {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A := by
  simp [IsStrictUpperBound, IsUpperBound.iff]

example : IsUpperBound (.Icc 1 2: Set ℝ) 2 := by
  intro y hy
  simp at hy
  exact hy.2

example : ¬ IsStrictUpperBound (.Icc 1 2: Set ℝ) 2 := by
  rw [IsStrictUpperBound.iff]
  push_neg
  use 2
  simp

example : IsStrictUpperBound (.Icc 1 2: Set ℝ) 3 := by
  rw [IsStrictUpperBound.iff]
  intro y hy
  simp at hy
  exact lt_of_le_of_lt hy.2 (by norm_num)

/-- A convenient way to simplify the notion of having `x₀` as a minimal element.-/
theorem IsMin.iff_lowerbound {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) (x₀ : X) : (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩:Y)) ↔ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . rintro ⟨ hx₀, hmin ⟩; simp [IsMin, hx₀] at *
    peel hmin with x hx _; specialize hY ⟨ _, hx ⟩ ⟨ _, hx₀ ⟩; aesop
  intro h; use h.1; simp [IsMin]; aesop

theorem IsMin.iff_lowerbound' {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) : (∃ x₀ : Y, IsMin x₀) ↔ ∃ x₀, x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . intro ⟨ ⟨ x₀, hx₀ ⟩, hmin ⟩
    have : ∃ (hx₀ : x₀ ∈ Y), IsMin (⟨ _, hx₀ ⟩:Y) := by use hx₀
    rw [iff_lowerbound hY x₀] at this; use x₀
  intro ⟨ x₀, hx₀, hmin ⟩; choose hx₀ _ using (iff_lowerbound hY x₀).mpr ⟨ hx₀, hmin ⟩; use ⟨ _, hx₀ ⟩

/-- Exercise 8.5.11 -/
example {X:Type} [PartialOrder X] {Y Y':Set X} (hY: IsTotal Y) (hY': IsTotal Y') (hY_well: WellFoundedLT Y)
    (hY'_well: WellFoundedLT Y') (hYY': IsTotal (Y ∪ Y': Set X)) : WellFoundedLT (Y ∪ Y': Set X) := by
  rw [WellFoundedLT.iff' hYY']
  intro A ⟨a₀, ha₀⟩
  have hY_wf := (WellFoundedLT.iff' hY).mp hY_well
  have hY'_wf := (WellFoundedLT.iff' hY').mp hY'_well
  let pY : Set Y := { y | ∃ a ∈ A, (a : X) = (y : X) }
  let pY' : Set Y' := { y' | ∃ a ∈ A, (a : X) = (y' : X) }
  -- min of pY is ≤ all A-elements in Y; similarly for pY'
  have minY (y₀ : pY) (hy₀ : IsMin y₀) (b : ↑(Y ∪ Y')) (hbA : b ∈ A) (hbY : (b : X) ∈ Y) :
      (y₀.val : X) ≤ (b : X) := by
    have : (⟨_, hbY⟩ : Y) ∈ pY := ⟨b, hbA, rfl⟩
    rcases hY (⟨_, hbY⟩ : Y) y₀.val with h | h
    · exact hy₀ (b := ⟨_, ‹_›⟩) h
    · exact h
  have minY' (y₀' : pY') (hy₀' : IsMin y₀') (b : ↑(Y ∪ Y')) (hbA : b ∈ A) (hbY' : (b : X) ∈ Y') :
      (y₀'.val : X) ≤ (b : X) := by
    have : (⟨_, hbY'⟩ : Y') ∈ pY' := ⟨b, hbA, rfl⟩
    rcases hY' (⟨_, hbY'⟩ : Y') y₀'.val with h | h
    · exact hy₀' (b := ⟨_, ‹_›⟩) h
    · exact h
  -- Main argument: find min of each nonempty projection, compare, return the smaller
  -- Helper to produce min of A from mins of both projections
  have both (y₀ : pY) (hy₀ : IsMin y₀) (y₀' : pY') (hy₀' : IsMin y₀') : ∃ x : A, IsMin x := by
    obtain ⟨a, haA, ha_eq⟩ := y₀.property
    obtain ⟨a', ha'A, ha'_eq⟩ := y₀'.property
    rcases hYY' ⟨_, Set.mem_union_left _ y₀.val.property⟩ ⟨_, Set.mem_union_right _ y₀'.val.property⟩ with hle | hle
    · -- y₀ ≤ y₀': use the A-element corresponding to y₀
      refine ⟨⟨a, haA⟩, fun ⟨b, hbA⟩ hba => ?_⟩
      show (a : X) ≤ (b : X)
      rcases b.property with hbY | hbY'
      · calc (a : X) = (y₀.val : X) := ha_eq
          _ ≤ (b : X) := minY y₀ hy₀ b hbA hbY
      · calc (a : X) = (y₀.val : X) := ha_eq
          _ ≤ (y₀'.val : X) := hle
          _ ≤ (b : X) := minY' y₀' hy₀' b hbA hbY'
    · -- y₀' ≤ y₀: use the A-element corresponding to y₀'
      refine ⟨⟨a', ha'A⟩, fun ⟨b, hbA⟩ hba => ?_⟩
      show (a' : X) ≤ (b : X)
      rcases b.property with hbY | hbY'
      · calc (a' : X) = (y₀'.val : X) := ha'_eq
          _ ≤ (y₀.val : X) := hle
          _ ≤ (b : X) := minY y₀ hy₀ b hbA hbY
      · calc (a' : X) = (y₀'.val : X) := ha'_eq
          _ ≤ (b : X) := minY' y₀' hy₀' b hbA hbY'
  -- Case split: which projections are nonempty
  rcases a₀.property with ha₀Y | ha₀Y'
  · have hpY : pY.Nonempty := ⟨⟨_, ha₀Y⟩, a₀, ha₀, rfl⟩
    obtain ⟨y₀, hy₀⟩ := hY_wf pY hpY
    by_cases hpY' : pY'.Nonempty
    · obtain ⟨y₀', hy₀'⟩ := hY'_wf pY' hpY'
      exact both y₀ hy₀ y₀' hy₀'
    · obtain ⟨a, haA, ha_eq⟩ := y₀.property
      refine ⟨⟨a, haA⟩, fun ⟨b, hbA⟩ _ => ?_⟩
      show (a : X) ≤ (b : X)
      rcases b.property with hbY | hbY'
      · calc (a : X) = (y₀.val : X) := ha_eq
          _ ≤ (b : X) := minY y₀ hy₀ b hbA hbY
      · exact absurd ⟨⟨_, hbY'⟩, ⟨_, hbA, rfl⟩⟩ hpY'
  · have hpY' : pY'.Nonempty := ⟨⟨_, ha₀Y'⟩, a₀, ha₀, rfl⟩
    obtain ⟨y₀', hy₀'⟩ := hY'_wf pY' hpY'
    by_cases hpY : pY.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hY_wf pY hpY
      exact both y₀ hy₀ y₀' hy₀'
    · obtain ⟨a', ha'A, ha'_eq⟩ := y₀'.property
      refine ⟨⟨a', ha'A⟩, fun ⟨b, hbA⟩ _ => ?_⟩
      show (a' : X) ≤ (b : X)
      rcases b.property with hbY | hbY'
      · exact absurd ⟨⟨_, hbY⟩, ⟨_, hbA, rfl⟩⟩ hpY
      · calc (a' : X) = (y₀'.val : X) := ha'_eq
          _ ≤ (b : X) := minY' y₀' hy₀' b hbA hbY'

set_option maxHeartbeats 1000000 in
/-- Lemma 8.5.14-/
theorem WellFoundedLT.partialOrder {X:Type} [PartialOrder X] (x₀ : X) : ∃ Y : Set X, IsTotal Y ∧ WellFoundedLT Y ∧ (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩: Y)) ∧ ¬ ∃ x, IsStrictUpperBound Y x := by
  -- This proof is based on the original text with some technical simplifications.

  -- The class of well-ordered subsets `Y` of `X` that contain `x₀` as a minimal element is not named in the text,
  -- but it is convenient to give it a name (`Ω₀`) for the formalization.  Here we use `IsMin.iff_lowerbound` to
  -- simplify the notion of minimality.
  let Ω₀ := { Y : Set X | IsTotal Y ∧ WellFoundedLT Y ∧ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x}
  suffices : ∃ Y ∈ Ω₀, ¬ ∃ x, IsStrictUpperBound Y x
  . have ⟨ Y, ⟨ hY, hY'⟩, hstrict ⟩ := this; use Y, hY
    rw [IsMin.iff_lowerbound hY x₀]; tauto
  by_contra! hs
  let s : Ω₀ → X := fun Y ↦ (hs Y Y.property).choose
  replace hs (Y:Ω₀) : IsStrictUpperBound Y (s Y) := (hs Y Y.property).choose_spec

  have hpt: {x₀} ∈ Ω₀ := by
    have htotal : IsTotal ({x₀}: Set X) := by simp [IsTotal]
    let _lin : LinearOrder ({x₀}: Set X) := LinearOrder.mk htotal
    simp [Ω₀, htotal]; apply WellFoundedLT.ofFinite
  let pt : Ω₀ := ⟨ _, hpt ⟩

  -- The operation of sending a set `Y` in `Ω₀` to the smaller set `{y ∈ Y.val | y < x}`, which is also
  -- in `Ω₀` if `x ∈ Y.val \ {x₀}`, is not named explicitly in the text, but we give it a name `F` for
  -- the formalization.
  have hF {Y:Set X} (hY: Y ∈ Ω₀) {x:X} (hxy : x ∈ Y \ {x₀}) : {y ∈ Y | y < x} ∈ Ω₀ := by
    simp [Ω₀, IsTotal] at hY ⊢; choose _ hmin using hY.2.2; simp_all
    split_ands
    . convert WellFoundedLT.subset (hwell := hY.2) (B := {y ∈ Y | y < x}) _ _
      . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩; simp; solve_by_elim [hY.1]
      intro _; simp; tauto
    have := hmin _ hxy.1; contrapose! hxy; order
  classical
  let F : Ω₀ → X → Ω₀ := fun Y x ↦ if hxy : x ∈ Y.val \ {x₀} then ⟨ {y ∈ (Y:Set X) | y < x}, hF Y.property hxy ⟩ else pt
  replace hF {Y : Ω₀} {x : X} (hxy : x ∈ (Y:Set X) \ {x₀}) : F Y x = { y ∈ (Y:Set X) | y < x } := by
    simp_all [F]

  -- The set `Ω` captures the notion of a `good set`.
  set Ω := { Y : Ω₀ | ∀ x ∈ (Y:Set X) \ {x₀}, x = s (F Y x) }
  have hΩ : pt ∈ Ω := by
    unfold pt Ω
    simp [Ω₀, F]

  -- Exercise 8.5.13
  have ex_8_5_13 {Y Y':Ω} (x:X) (h: x ∈ (Y':Set X) \ Y) : IsStrictUpperBound Y x := by
    have hYΩ₀ := Y.val.property; have hY'Ω₀ := Y'.val.property
    have hYΩ := Y.property; have hY'Ω := Y'.property
    change IsTotal _ ∧ _ ∧ _ ∧ _ at hYΩ₀ hY'Ω₀
    obtain ⟨ hYtot, hYwell, hYx₀, hYmin ⟩ := hYΩ₀
    obtain ⟨ hY'tot, hY'well, hY'x₀, hY'min ⟩ := hY'Ω₀
    let I : Set X := (Y : Set X) ∩ Y'
    have no_first_difference : ∀ (A B : Ω), ∀ d, d ∈ (A:Set X) → d ∉ (B:Set X) → d ≠ x₀ →
        (∀ c, c < d → (c ∈ (A:Set X) ↔ c ∈ (B:Set X))) →
        ∀ a ∈ (B:Set X), d ≤ a → False := by
      intro A B d hdA hdB hdx₀ hagree a haB hda
      have hAΩ₀ := A.val.property; have hBΩ₀ := B.val.property
      have hAΩ := A.property; have hBΩ := B.property
      change IsTotal _ ∧ _ ∧ _ ∧ _ at hAΩ₀ hBΩ₀
      obtain ⟨ hAtot, hAwell, hAx₀, hAmin ⟩ := hAΩ₀
      obtain ⟨ hBtot, hBwell, hBx₀, hBmin ⟩ := hBΩ₀
      have hdAx₀ : d ∈ (A:Set X) \ {x₀} := ⟨hdA, by simp [hdx₀]⟩
      have hdsA : d = s (F A.val d) := hAΩ d hdAx₀
      have hFAd : (F A.val d : Set X) = {c ∈ (A:Set X) | c < d} := by rw [hF hdAx₀]
      have hseg : {c ∈ (A:Set X) | c < d} = {c ∈ (B:Set X) | c < d} := by
        ext c; simp only [Set.mem_sep_iff]
        exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(hagree c h2).mp h1, h2⟩,
               fun ⟨h1, h2⟩ ↦ ⟨(hagree c h2).mpr h1, h2⟩⟩
      set Blin := LinearOrder.mk hBtot
      set T : Set (B:Set X) := { y | d ≤ y.val }
      have hTne : T.Nonempty := ⟨⟨a, haB⟩, hda⟩
      obtain ⟨⟨⟨m, hmB⟩, hmdT⟩, hminm⟩ := ((WellFoundedLT.iff _).mp hBwell) T hTne
      change d ≤ m at hmdT
      replace hminm : ∀ c ∈ (B:Set X), d ≤ c → m ≤ c := by
        intro c hcB hdc
        have h := hminm (b := ⟨⟨c, hcB⟩, hdc⟩)
        exact (hBtot ⟨c, hcB⟩ ⟨m, hmB⟩).elim (fun hle ↦ h hle) id
      have hno_between : ∀ c ∈ (B:Set X), c < m → c < d := by
        suffices ∀ (c : ↥(B:Set X)), (c:X) < m → (c:X) < d from
          fun c hcB hcm ↦ this ⟨c, hcB⟩ hcm
        intro c₀; apply hBwell.wf.induction c₀; intro ⟨c, hcB⟩ ih hcm
        by_contra hcd
        have hdc : ¬(d ≤ c) := fun hdc ↦ absurd (hminm c hcB hdc) (not_le_of_gt hcm)
        have hcne : c ≠ d := fun h ↦ hdB (h ▸ hcB)
        have hcx₀ : c ≠ x₀ := fun h ↦ hcd (lt_of_le_not_ge (h ▸ hAmin d hdA) (h ▸ hdc))
        have hcBx₀ : c ∈ (B:Set X) \ {x₀} := ⟨hcB, by simp [hcx₀]⟩
        have ih_sub : {c' ∈ (B:Set X) | c' < c} ⊆ {c' ∈ (B:Set X) | c' < d} :=
          fun c' ⟨hc'B, hc'c⟩ ↦ ⟨hc'B, ih ⟨c', hc'B⟩ hc'c (lt_trans hc'c hcm)⟩
        have dsub : {c' ∈ (B:Set X) | c' < d} ⊆ {c' ∈ (B:Set X) | c' < c} := by
          intro c' ⟨hc'B, hc'd⟩; refine ⟨hc'B, ?_⟩
          rcases hBtot ⟨c', hc'B⟩ ⟨c, hcB⟩ with h | h
          · refine lt_of_le_of_ne (show c' ≤ c from h) ?_; rintro rfl; exact hcd hc'd
          · exfalso; exact hcd (lt_of_le_not_ge (le_trans (show c ≤ c' from h) (le_of_lt hc'd)) hdc)
        have heq : {c' ∈ (B:Set X) | c' < c} = {c' ∈ (B:Set X) | c' < d} :=
          Set.Subset.antisymm ih_sub dsub
        have hFeq : F B.val c = F A.val d :=
          Subtype.val_injective (by rw [hF hcBx₀, hFAd, heq, hseg])
        exact hcne ((hBΩ c hcBx₀).trans (hFeq ▸ hdsA.symm))
      have hmBx₀ : m ∈ (B:Set X) \ {x₀} := by
        refine ⟨hmB, by simp [show m ≠ x₀ from fun h ↦ hdx₀ (le_antisymm (h ▸ hmdT) (hAmin d hdA))]⟩
      have hFeq : F B.val m = F A.val d := by
        apply Subtype.val_injective; rw [hF hmBx₀, hFAd]
        ext c; simp only [Set.mem_sep_iff]
        exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(hagree c (hno_between c h1 h2)).mpr h1, hno_between c h1 h2⟩,
               fun ⟨h1, h2⟩ ↦ ⟨(hagree c h2).mp h1, lt_of_lt_of_le h2 hmdT⟩⟩
      have : m = d := by rw [hBΩ m hmBx₀, hFeq, ← hdsA]
      exact hdB (this ▸ hmB)
    have step1_mem {A B : Ω} {a b : X}
        (haA : a ∈ (A : Set X)) (haB : a ∈ (B : Set X)) (hba : b < a) :
        b ∈ (A : Set X) → b ∈ (B : Set X) := by
      intro hbA; by_contra hbB
      have hAΩ₀ := A.val.property; have hBΩ₀ := B.val.property
      change IsTotal _ ∧ _ ∧ _ ∧ _ at hAΩ₀ hBΩ₀
      obtain ⟨hAtot, hAwell, hAx₀, hAmin⟩ := hAΩ₀
      obtain ⟨hBtot, hBwell, hBx₀, hBmin⟩ := hBΩ₀
      set Alin := LinearOrder.mk hAtot
      set S : Set (A : Set X) := { c | c.val < a ∧ c.val ∉ (B : Set X) }
      obtain ⟨⟨⟨d, hdA⟩, ⟨hda, hdB⟩⟩, hminS⟩ := ((WellFoundedLT.iff _).mp hAwell) S
        ⟨⟨b, hbA⟩, hba, hbB⟩
      replace hminS : ∀ c ∈ (A : Set X), c < a → c ∉ (B : Set X) → d ≤ c := by
        intro c hcA hca hcB
        exact (hAtot ⟨c, hcA⟩ ⟨d, hdA⟩).elim
          (fun hle ↦ hminS (b := ⟨⟨c, hcA⟩, hca, hcB⟩) hle) id
      have hdx₀ : d ≠ x₀ := fun h ↦ hdB (h ▸ hBx₀)
      have hcB_of_A : ∀ c, c ∈ (A : Set X) → c < d → c ∈ (B : Set X) := by
        intro c hcA hcd; by_contra hcB
        exact absurd (hminS c hcA (lt_trans hcd hda) hcB) (not_le_of_gt hcd)
      have hcA_of_B : ∀ c, c ∈ (B : Set X) → c < d → c ∈ (A : Set X) := by
        by_contra h_neg; push_neg at h_neg
        obtain ⟨c₀, hc₀B, hc₀d, hc₀A⟩ := h_neg
        set Blin := LinearOrder.mk hBtot
        obtain ⟨⟨⟨e, heB⟩, ⟨hed, heA⟩⟩, hminS'⟩ := ((WellFoundedLT.iff _).mp hBwell)
          (show Set (B : Set X) from { c | c.val < d ∧ c.val ∉ (A : Set X) })
          ⟨⟨c₀, hc₀B⟩, hc₀d, hc₀A⟩
        replace hminS' : ∀ c ∈ (B : Set X), c < d → c ∉ (A : Set X) → e ≤ c := by
          intro c hcB hcd hcA
          exact (hBtot ⟨c, hcB⟩ ⟨e, heB⟩).elim
            (fun hle ↦ hminS' (b := ⟨⟨c, hcB⟩, hcd, hcA⟩) hle) id
        have hagree : ∀ c, c < e → (c ∈ (B : Set X) ↔ c ∈ (A : Set X)) := by
          intro c hce; exact ⟨
            fun hcB ↦ by by_contra hcA
                         exact absurd (hminS' c hcB (lt_trans hce hed) hcA) (not_le_of_gt hce),
            fun hcA ↦ hcB_of_A c hcA (lt_trans hce hed)⟩
        exact no_first_difference B A e heB heA (fun h ↦ heA (h ▸ hAx₀)) hagree d hdA hed.le
      exact no_first_difference A B d hdA hdB hdx₀
        (fun c hcd ↦ ⟨fun h ↦ hcB_of_A c h hcd, fun h ↦ hcA_of_B c h hcd⟩) a haB hda.le

    -- Step 1: initial segments agree for elements of Y ∩ Y'.
    have step1 : ∀ a ∈ I, {b ∈ (Y:Set X) | b < a} = {b ∈ (Y':Set X) | b < a} := by
      -- Suffices to show ∀ b < a, b ∈ Y ↔ b ∈ Y'.
      suffices ∀ a ∈ I, ∀ b, b < a → (b ∈ (Y:Set X) ↔ b ∈ (Y':Set X)) by
        intro a ha; ext b; simp only [Set.mem_sep_iff]
        exact ⟨fun ⟨h1, h2⟩ ↦ ⟨(this a ha b h2).mp h1, h2⟩,
               fun ⟨h1, h2⟩ ↦ ⟨(this a ha b h2).mpr h1, h2⟩⟩
      intro a haI b hba
      have haY : a ∈ (Y : Set X) := haI.1
      have haY' : a ∈ (Y' : Set X) := haI.2
      constructor
      · exact step1_mem (A := Y) (B := Y') haY haY' hba
      · exact step1_mem (A := Y') (B := Y) haY' haY hba

    -- Step 2: Y ∩ Y' is good.
    have hIΩ₀ : I ∈ Ω₀ := by
      have hItot : IsTotal I := by
        intro ⟨a, ha⟩ ⟨b, hb⟩
        exact hYtot ⟨a, ha.1⟩ ⟨b, hb.1⟩
      have hIwell : WellFoundedLT I := by
        haveI : WellFoundedLT (Y : Set X) := hYwell
        exact WellFoundedLT.subset (A := (Y : Set X)) (B := I) hYtot (by intro x hx; exact hx.1)
      refine ⟨hItot, hIwell, ?_, ?_⟩
      · exact ⟨hYx₀, hY'x₀⟩
      · intro z hzI
        exact hYmin z hzI.1
    let I0 : Ω₀ := ⟨I, hIΩ₀⟩
    have step2 : I0 ∈ Ω := by
      change ∀ z ∈ (I0 : Set X) \ {x₀}, z = s (F I0 z)
      intro z hzI
      have hzY : z ∈ (Y : Set X) \ {x₀} := ⟨hzI.1.1, hzI.2⟩
      have hzI' : z ∈ I \ {x₀} := hzI
      have hseg : {b ∈ (Y : Set X) | b < z} = {b ∈ I | b < z} := by
        ext b
        constructor
        · rintro ⟨hbY, hbz⟩
          have hbY' : b ∈ (Y' : Set X) := by
            have : b ∈ {b ∈ (Y' : Set X) | b < z} := by
              rw [← step1 z hzI.1]
              exact ⟨hbY, hbz⟩
            exact this.1
          exact ⟨⟨hbY, hbY'⟩, hbz⟩
        · rintro ⟨hbI, hbz⟩
          exact ⟨hbI.1, hbz⟩
      have hFeq : F Y.val z = F I0 z := by
        apply Subtype.val_injective
        rw [hF hzY, hF hzI', hseg]
      have hzgood : z = s (F Y.val z) := hYΩ z hzY
      rwa [hFeq] at hzgood

    -- Steps 3+4: Y ⊆ Y' (otherwise s(I0) lands in both Y\Y' and Y'\Y — contradiction).
    have step4 : (Y : Set X) ⊆ Y' := by
      by_contra hsub; rw [Set.not_subset] at hsub
      -- Take the min d of Y \ Y'. Show {c ∈ Y | c < d} = I, hence d = s(I0).
      obtain ⟨d₁, hd₁Y, hd₁Y'⟩ := hsub
      set Ylin := LinearOrder.mk hYtot
      set S₁ : Set (Y:Set X) := {c | (c:X) ∉ (Y':Set X)}
      obtain ⟨⟨⟨d, hdY⟩, hdY'⟩, hminS⟩ := ((WellFoundedLT.iff _).mp hYwell) S₁
        ⟨⟨d₁, hd₁Y⟩, hd₁Y'⟩
      replace hminS : ∀ c ∈ (Y:Set X), c ∉ (Y':Set X) → d ≤ c := by
        intro c hcY hcY'
        exact (hYtot ⟨c, hcY⟩ ⟨d, hdY⟩).elim (fun h ↦ hminS (b := ⟨⟨c, hcY⟩, hcY'⟩) h) id
      have hdx₀ : d ≠ x₀ := fun hd ↦ hdY' (hd ▸ hY'x₀)
      have hsegL : {c ∈ (Y:Set X) | c < d} = I := by
        ext c; constructor
        · rintro ⟨hcY, hcd⟩
          exact ⟨hcY, by by_contra hcY'; exact absurd (hminS c hcY hcY') (not_le_of_gt hcd)⟩
        · intro ⟨hcY, hcY'⟩
          refine ⟨hcY, ?_⟩
          rcases hYtot ⟨c, hcY⟩ ⟨d, hdY⟩ with hcd | hdc
          · exact lt_of_le_of_ne hcd fun h ↦ hdY' (h ▸ hcY')
          · exact absurd ((step1 c ⟨hcY, hcY'⟩).subset ⟨hdY, lt_of_le_of_ne hdc
              fun h ↦ hdY' (h ▸ hcY')⟩).1 hdY'
      have hdYx₀ : d ∈ (Y:Set X) \ {x₀} := ⟨hdY, by simp [hdx₀]⟩
      have hFeqL : F Y.val d = I0 := Subtype.val_injective (by rw [hF hdYx₀, hsegL])
      have hd_eq : d = s I0 := by have := hYΩ d hdYx₀; rwa [hFeqL] at this
      -- Same for the min d' of Y' \ Y: {c ∈ Y' | c < d'} = I, hence d' = s(I0) = d.
      set Y'lin := LinearOrder.mk hY'tot
      set S₂ : Set (Y':Set X) := {c | (c:X) ∉ (Y:Set X)}
      obtain ⟨⟨⟨d', hd'Y'⟩, hd'Y⟩, hminS'⟩ := ((WellFoundedLT.iff _).mp hY'well) S₂
        ⟨⟨x, h.1⟩, h.2⟩
      replace hminS' : ∀ c ∈ (Y':Set X), c ∉ (Y:Set X) → d' ≤ c := by
        intro c hcY' hcY
        exact (hY'tot ⟨c, hcY'⟩ ⟨d', hd'Y'⟩).elim (fun h ↦ hminS' (b := ⟨⟨c, hcY'⟩, hcY⟩) h) id
      have hd'x₀ : d' ≠ x₀ := fun hd ↦ hd'Y (hd ▸ hYx₀)
      have hsegR : {c ∈ (Y':Set X) | c < d'} = I := by
        ext c; constructor
        · rintro ⟨hcY', hcd⟩
          exact ⟨by by_contra hcY; exact absurd (hminS' c hcY' hcY) (not_le_of_gt hcd), hcY'⟩
        · intro ⟨hcY, hcY'⟩
          refine ⟨hcY', ?_⟩
          rcases hY'tot ⟨c, hcY'⟩ ⟨d', hd'Y'⟩ with hcd | hdc
          · exact lt_of_le_of_ne hcd fun h ↦ hd'Y (h ▸ hcY)
          · exact absurd ((step1 c ⟨hcY, hcY'⟩).symm.subset ⟨hd'Y', lt_of_le_of_ne hdc
              fun h ↦ hd'Y (h ▸ hcY)⟩).1 hd'Y
      have hd'Y'x₀ : d' ∈ (Y':Set X) \ {x₀} := ⟨hd'Y', by simp [hd'x₀]⟩
      have hFeqR : F Y'.val d' = I0 := Subtype.val_injective (by rw [hF hd'Y'x₀, hsegR])
      have hd'_eq : d' = s I0 := by have := hY'Ω d' hd'Y'x₀; rwa [hFeqR] at this
      -- d = d' = s(I0), but d ∉ Y' and d' ∈ Y'.
      exact hdY' (hd_eq ▸ hd'_eq ▸ hd'Y')

    -- Step 5: every `y ∈ Y` is below `x`.
    have step5 : IsStrictUpperBound Y x := by
      rw [IsStrictUpperBound.iff]
      intro y hyY
      have hyY' : y ∈ (Y' : Set X) := step4 hyY
      rcases hY'tot ⟨y, hyY'⟩ ⟨x, h.1⟩ with hyx | hxy
      · exact lt_of_le_of_ne hyx (by intro hxy'; exact h.2 (hxy' ▸ hyY))
      · have hxy' : x < y := by
          exact lt_of_le_of_ne hxy (by intro hxy'; exact h.2 (hxy'.symm ▸ hyY))
        have hxY : x ∈ (Y : Set X) := by
          have : x ∈ {b ∈ (Y : Set X) | b < y} := by
            rw [step1 y ⟨hyY, hyY'⟩]
            exact ⟨h.1, hxy'⟩
          exact this.1
        exact (h.2 hxY).elim
    exact step5

  have : IsTotal Ω := by
    unfold IsTotal; by_contra!; obtain ⟨ ⟨ ⟨ Y, hY1 ⟩, hY2 ⟩, ⟨ ⟨ Y', hY'1⟩, hY'2 ⟩, h1, h2 ⟩ := this
    simp_all [Set.not_subset]
    choose x₁ hx₁ hx₁' using h1; choose x₂ hx₂ hx₂' using h2
    observe h1 : IsStrictUpperBound Y x₂
    observe h2 : IsStrictUpperBound Y' x₁
    simp [IsStrictUpperBound.iff] at h1 h2
    specialize h1 _ hx₁; specialize h2 _ hx₂; order
  set Y_infty : Set X := ⋃ Y:Ω, Y
  have hmem : x₀ ∈ Y_infty := by simp [Y_infty]; use pt; grind
  have hmin {x:X} (hx: x ∈ Y_infty) : x₀ ≤ x := by
    unfold Y_infty at hx
    obtain ⟨ Y, hY, hxY ⟩ := hx
    simp at hY
    have hYΩ₀ := hY.1
    have hYΩ := hY.2
    unfold Ω₀ at hYΩ₀
    obtain ⟨ _, _, _, hYmin ⟩ := hYΩ₀
    exact hYmin x hxY
  have htotal : IsTotal Y_infty := by
    intro ⟨ x, hx ⟩ ⟨ x', hx'⟩; simp [Y_infty] at hx hx'
    obtain ⟨ Y, ⟨ hYΩ₀, hYΩ ⟩, hxY ⟩ := hx; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx'
    specialize this ⟨ _, hYΩ ⟩ ⟨ _, hY'Ω ⟩; simp [Ω₀] at this ⊢ hYΩ₀ hY'Ω₀
    obtain this | this := this
    . replace hY'Ω₀ := hY'Ω₀.1 ⟨ _, this hxY ⟩ ⟨ _, hxY' ⟩; simpa using hY'Ω₀
    replace hYΩ₀ := hYΩ₀.1 ⟨ _, hxY ⟩ ⟨ _, this hxY' ⟩; simpa using hYΩ₀
  have hwell : WellFoundedLT Y_infty := by
    rw [iff' htotal]; intro A ⟨ ⟨a, ha⟩, haA ⟩
    simp [Y_infty] at ha; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, haY ⟩ := ha
    simp [Ω₀, iff' hYΩ₀.1] at hYΩ₀
    choose b hb hbY hbmin using hYΩ₀.2.1 {x:Y | ∃ x':A, (x:X) = x'} (by use ⟨ _, haY ⟩; simp [ha, haA])
    simp at hbY; choose hbY_infty hbA using hbY
    rw [IsMin.iff_lowerbound' (IsTotal.subtype htotal)]
    use ⟨ _, hbY_infty ⟩, hbA; intro ⟨ x, hx ⟩ hxA
    simp [Y_infty] at hx ⊢; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx
    by_cases hxY : x ∈ Y
    · have hxmem : ⟨x, hxY⟩ ∈ {x : ↑Y | ∃ x' : A, (x : X) = ↑↑x'} :=
        ⟨⟨⟨x, hx⟩, hxA⟩, rfl⟩
      rcases hYΩ₀.1 ⟨b, hb⟩ ⟨x, hxY⟩ with h | h
      · exact h
      · have := hbmin (b := ⟨⟨x, hxY⟩, hxmem⟩) h; simpa using this
    · have := ex_8_5_13 (Y := ⟨_, hYΩ⟩) (Y' := ⟨_, hY'Ω⟩) x ⟨hxY', hxY⟩
      rw [IsStrictUpperBound.iff] at this
      exact le_of_lt (this _ hb)
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := ⟨htotal, hwell, hmem, fun _ h ↦ hmin h⟩
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have hsub : IsStrictUpperBound Y_infty sY_infty := hs ⟨_, hY_inftyΩ₀⟩
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Set.mem_union, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · exact htotal ⟨x, hx⟩ ⟨y, hy⟩
    · left; exact le_of_lt ((IsStrictUpperBound.iff ..).mp hsub x hx)
    · right; exact le_of_lt ((IsStrictUpperBound.iff ..).mp hsub y hy)
    · left; exact le_refl _
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    rw [iff' hYs_total]; intro A ⟨⟨a, ha⟩, haA⟩
    by_cases hA : ∃ y ∈ A, (y : X) ∈ Y_infty
    · obtain ⟨⟨y, hy⟩, hyA, hyY⟩ := hA
      set B : Set ↑Y_infty := {z | ⟨z, Set.mem_union_left _ z.property⟩ ∈ A}
      have hBne : B.Nonempty := ⟨⟨y, hyY⟩, by simp [B]; convert hyA using 1⟩
      obtain ⟨⟨⟨m, hm⟩, hmB⟩, hmmin⟩ := ((iff' htotal).mp hwell) B hBne
      simp [B] at hmB
      use ⟨⟨m, Set.mem_union_left _ hm⟩, hmB⟩
      intro ⟨⟨z, hz⟩, hzA⟩ hzm
      simp only [Set.mem_union, Set.mem_singleton_iff] at hz
      rcases hz with hzY | rfl
      · have hzB : ⟨z, hzY⟩ ∈ B := by simp [B]; convert hzA using 1
        exact hmmin (b := ⟨⟨z, hzY⟩, hzB⟩) hzm
      · exact absurd (lt_of_le_of_lt hzm ((IsStrictUpperBound.iff ..).mp hsub m hm)) (lt_irrefl _)
    · push_neg at hA
      have haS : a = sY_infty := by
        simp only [Set.mem_union, Set.mem_singleton_iff] at ha
        exact ha.elim (fun h ↦ absurd h (hA _ haA)) id
      use ⟨⟨a, ha⟩, haA⟩; intro ⟨⟨z, hz⟩, hzA⟩ hzm
      simp only [Set.mem_union, Set.mem_singleton_iff] at hz
      rcases hz with hzY | rfl
      · exact absurd hzY (hA _ hzA)
      · subst haS; exact hzm
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := .inl hmem
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by
    rintro x (hx | rfl)
    · exact hmin hx
    · exact le_of_lt ((IsStrictUpperBound.iff ..).mp hsub _ hmem)
  have hYs_Ω₀ : (Y_infty ∪ {sY_infty}) ∈ Ω₀ := by
    simpa [-Set.union_singleton, Ω₀, hYs_total, hYs_well, hYs_mem]
  specialize hs ⟨ _, hY_inftyΩ₀ ⟩
  simp [IsStrictUpperBound.iff] at hs
  have hYs_Ω : ⟨ _, hYs_Ω₀ ⟩ ∈ Ω := by
    simp [Ω, -Set.mem_insert_iff, -and_imp]
    rintro x ⟨ (rfl | hx), hxx₀ ⟩
    . unfold sY_infty; congr 1
      symm; apply Subtype.val_injective; convert hF _
      . ext; simp; constructor
        . grind
        rintro ⟨ _ | _, _ ⟩
        . order
        assumption
      simp; specialize hs (y := x₀) (by simp [hmem]); order
    have hx' := hx; simp [Y_infty] at hx'; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, hxY ⟩ := hx'
    have hYΩ' := hYΩ; simp [Ω] at hYΩ
    convert hYΩ _ hxY hxx₀ using 2
    apply Subtype.val_injective
    rw [hF, hF]
    . ext y; simp [Y_infty]; intro hyx; constructor
      . rintro (rfl | ⟨ Y', ⟨hY'Ω₀, hY'Ω⟩, hyY' ⟩)
        . specialize hs _ hx; order
        by_contra!
        specialize ex_8_5_13 (Y := ⟨_, hYΩ'⟩) (Y' := ⟨_, hY'Ω⟩) y (by grind)
        rw [IsStrictUpperBound.iff] at ex_8_5_13
        specialize ex_8_5_13 x (by simp [hxY]); order
      grind
    all_goals simp [hxY, hx, hxx₀]
  have hs_mem : sY_infty ∈ Y_infty := Set.mem_iUnion_of_mem ⟨ _, hYs_Ω ⟩ (by simp)
  specialize hs _ hs_mem; order


/-- Lemma 8.5.15 (Zorn's lemma) / Exercise 8.5.14 -/
theorem Zorns_lemma {X:Type} [PartialOrder X] [Nonempty X]
  (hchain: ∀ Y:Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x:X, IsMax x := by
  by_contra hmax
  push_neg at hmax
  have h : ∀ S : Set X, (∃ x: X, IsUpperBound S x) → ∃ y, IsStrictUpperBound S y := by
    intro S hB
    obtain ⟨x, hx⟩ := hB
    have := hmax x
    simp at this
    obtain ⟨y, hy⟩ := this
    use y
    rw [IsStrictUpperBound.iff]
    rw [IsUpperBound.iff] at hx
    intro z hzS
    have : z ≤ x := hx hzS
    exact lt_of_le_of_lt (hx hzS) hy
  have hnon : Nonempty X := inferInstance
  obtain ⟨x⟩ := hnon
  obtain ⟨Y, hTotal, hWellFounded, hxMin, hNonStrictUpper⟩ := WellFoundedLT.partialOrder x
  have hxY : x ∈ Y := hxMin.choose
  have hNonempty : Y.Nonempty := by exact Set.nonempty_of_mem hxY
  specialize hchain Y ⟨hTotal, hNonempty⟩
  specialize h Y hchain
  contradiction

/-- Exercise 8.5.1 -/
def empty_set_partial_order [h₀: LE Empty] : Decidable (∃ h : PartialOrder Empty, h.le = h₀.le) := by
  sorry

def empty_set_linear_order [h₀: LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  sorry

def empty_set_well_order [h₀: LT Empty]: Decidable (Nonempty (WellFoundedLT Empty)) := by
  sorry

/-- Exercise 8.5.2 -/
example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ ¬ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) := by sorry

example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x y:X, x ≤ y → y ≤ x → x = y) := by sorry

example : ∃ (X:Type) (h₀: LE X), (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x:X, x ≤ x) := by sorry

/-- Exercise 8.5.3 -/
example : ∃ (h₀: PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by sorry

example : ¬ ∃ (h₀: LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by sorry

/-- Exercise 8.5.4 -/
example : ¬ ∃ x : {x:ℝ| x > 0}, IsMin x := by sorry

/-- Exercise 8.5.5 -/
example {X Y:Type} [PartialOrder Y] (f:X → Y) : ∃ h₀: PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by sorry

def Ex_8_5_5_b : Decidable (∀ (X Y:Type) (h: LinearOrder Y) (f:X → Y), ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  sorry

-- Final part of Exercise 8.5.5; if the answer to the previous part is "no", modify the hypotheses to make it true.

/-- Exercise 8.5.6 -/
abbrev OrderIdeals (X: Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

def OrderIdeals.iso {X: Type} [PartialOrder X] : X ≃o OrderIdeals X := {
  toFun x := ⟨ .Iic x, by simp ⟩
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
  map_rel_iff' := by sorry
  }

/-- Exercise 8.5.7 -/
example {Y:Type} [PartialOrder Y] {x y:Y} (hx: IsMin x) (hy: IsMin y) : x = y := by
  sorry

example {Y:Type} [PartialOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
 sorry

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x) (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by sorry


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's `Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by sorry
  le_antisymm := by sorry
  le_trans := by sorry
}

instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) := by sorry

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
  WellFoundedLT (Lex' (X × Y)) := by sorry


end Chapter8
