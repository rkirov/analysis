import Mathlib.Tactic
import Analysis.Section_8_3
import Analysis.Section_8_4

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.5: Ordered sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of {name}`PartialOrder`, {name}`LinearOrder`, and {name}`WellFoundedLT`, with some API.
- Strong induction.
- Zorn's lemma.

-/

namespace Chapter8

/-- Definition 8.5.1 - Here we just review the Mathlib {name}`PartialOrder` class. -/

example {X:Type} [PartialOrder X] (x:X) : x ≤ x := le_refl x
example {X:Type} [PartialOrder X] {x y:X} (h₁: x ≤ y) (h₂: y ≤ x) : x = y := antisymm h₁ h₂
example {X:Type} [PartialOrder X] {x y z:X} (h₁: x ≤ y) (h₂: y ≤ z) : x ≤ z := le_trans h₁ h₂
example {X:Type} [PartialOrder X] (x y:X) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

@[implicit_reducible] def PartialOrder.mk {X:Type} [LE X]
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

/-- Definition 8.5.3.  Here we just review the Mathlib {name}`LinearOrder` class. -/
example {X:Type} [LinearOrder X] : PartialOrder X := by infer_instance
def IsTotal (X:Type) [PartialOrder X] : Prop := ∀ x y:X, x ≤ y ∨ y ≤ x
example {X:Type} [LinearOrder X] : IsTotal X := le_total

open Classical in
@[implicit_reducible] noncomputable def LinearOrder.mk {X:Type} [PartialOrder X]
  (htotal: IsTotal X) : LinearOrder X :=
{
   le_total := htotal
   toDecidableLE := decRel LE.le
}

/- Examples 8.5.4 -/
#check (inferInstance : LinearOrder ℕ)
#check (inferInstance : LinearOrder ℚ)
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : LinearOrder EReal)


@[implicit_reducible] noncomputable def LinearOrder.subtype {X:Type} [LinearOrder X] (A: Set X) : LinearOrder A :=
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

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's {name}`IsMax` and {name}`IsMin`. -/
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
    simp only [Nat.card_coe_set_eq]
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
    exact Fintype.card_subtype_lt fun x ↦ x rfl

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
  rw [iff' hA] at hwell; rw [iff' (hA.subset hAB)]; intro C hC
  have ⟨ ⟨ ⟨ x, hx ⟩, hx' ⟩, hmin ⟩ := hwell ((B.embeddingOfSubset _ hAB) '' C) (by aesop)
  simp at hx'; choose y hy hyC this using hx'; use ⟨ _, hyC ⟩
  simp_all [IsMin, Set.embeddingOfSubset]
  intro a ha_B ha_C
  apply hmin _ (hAB ha_B) <;> trivial

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

/-- Connection with Mathlib's {name}`upperBounds` -/
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

/-- A convenient way to simplify the notion of having {name}`x₀` as a minimal element.-/
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
    intro x hx hn
    simp at hx
    contradiction

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
    intro x hx hxx₀
    rcases hx with rfl | hx
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
  apply isTrue
  use {
    le := fun x _ ↦ True
    le_refl := by simp
    le_antisymm := by intro x; exact Empty.elim x
    le_trans := by simp
    lt_iff_le_not_ge := by simp
  }
  ext x y
  exfalso
  exact Aesop.BuiltinRules.empty_false x

def empty_set_linear_order [h₀: LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  apply isTrue
  use {
    le := fun x _ ↦ True
    le_refl := by simp
    le_antisymm := by intro x; exact Empty.elim x
    le_trans := by simp
    lt_iff_le_not_ge := by simp
    le_total := by intro x; exact Empty.elim x
    min_def := by simp
    max_def := by simp
    toDecidableLE := by
      intro x y
      exact isTrue trivial
  }
  ext x y
  exfalso
  exact Aesop.BuiltinRules.empty_false x

def empty_set_well_order [h₀: LT Empty]: Decidable (Nonempty (WellFoundedLT Empty)) :=
  isTrue ⟨⟨⟨fun a ↦ a.elim⟩⟩⟩

/-- Exercise 8.5.2 -/
example : ∃ (X:Type) (_: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧
    ¬ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) := by
  -- use x = x, 0 <= 1 <= 2, but not 0 <= 2
  use Fin 3, ⟨fun x y ↦ x = y ∨ (x.val + 1 = y.val)⟩
  refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
  · intro x y hxy hyx
    rcases hxy with rfl | hxy
    · rfl
    · rcases hyx with rfl | hyx
      · omega
      · exfalso; omega
  · push_neg
    use 0, 1, 2
    simp

example : ∃ (X:Type) (_: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧
    ¬ (∀ x y:X, x ≤ y → y ≤ x → x = y) := by
  -- use x = x, and 0 <= 1 <= 0
  use Fin 2, ⟨fun _ _ ↦ True⟩
  refine ⟨fun _ ↦ trivial, fun _ _ _ _ _ ↦ trivial, ?_⟩
  push_neg
  exact ⟨0, 1, trivial, trivial, by decide⟩

example : ∃ (X:Type) (_: LE X), (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧
    (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x:X, x ≤ x) := by
  -- use just 0
  use Fin 1, ⟨fun _ _ ↦ False⟩
  refine ⟨fun _ _ h ↦ h.elim, fun _ _ _ h ↦ h.elim, ?_⟩
  push_neg
  exact ⟨0, id⟩

/-- Exercise 8.5.3 -/
@[reducible]
def PNat.divOrder : PartialOrder PNat where
  le x y := ∃ n : PNat, y = n * x
  lt x y := (∃ n : PNat, y = n * x) ∧ ¬∃ n : PNat, x = n * y
  le_refl := by simp
  le_antisymm := by
    intro x y hxy hyx
    obtain ⟨n, rfl⟩ := hxy
    obtain ⟨m, hyx⟩ := hyx
    have hmn : m * n = 1 := by
      have h : m * n * x = 1 * x := by rw [mul_assoc, ← hyx, one_mul]
      exact mul_right_cancel h
    have : n = 1 := by
      have h1 := congr_arg PNat.val hmn
      simp [PNat.mul_coe] at h1
      exact h1.2
    subst n
    simp
  le_trans := by
    intro x y z hxy hyz
    obtain ⟨n, rfl⟩ := hxy
    obtain ⟨m, rfl⟩ := hyz
    use n * m
    ring
  lt_iff_le_not_ge := by
    intro x y; exact Iff.rfl

example : ∃ (h₀: PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) :=
  ⟨PNat.divOrder, rfl⟩

example : ¬ ∃ (h₀: LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  -- use 2 and 3 as counter example
  intro ⟨h₀, h⟩
  have h1 : h₀.le 2 3 ∨ h₀.le 3 2 := h₀.le_total 2 3
  rw [h] at h1
  rcases h1 with ⟨n, hn⟩ | ⟨n, hn⟩
  · have := congr_arg PNat.val hn; simp at this; omega
  · have := congr_arg PNat.val hn; simp at this; omega

/-- Exercise 8.5.4 -/
example : ¬ ∃ x : {x:ℝ| x > 0}, IsMin x := by
  push_neg
  intro m hm
  rw [IsMin.iff] at hm
  push_neg at hm
  specialize hm ⟨m.val / 2, by
    simp
    exact m.prop
  ⟩
  simp at hm
  change m.val ≤ m.val / 2 at hm; have : m.val > 0 := m.prop; linarith

/-- Exercise 8.5.5 -/
example {X Y:Type} [PartialOrder Y] (f:X → Y) : ∃ h₀: PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  use {
    le := fun x y ↦ f x < f y ∨ x = y
    le_refl := by simp
    le_antisymm := by
      intro x y hxy hyx
      rcases hxy with hxy | rfl
      . rcases hyx with hyx | rfl
        . exact absurd (hxy.trans hyx) (lt_irrefl _)
        . rfl
      . rfl
    le_trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | rfl
      . rcases hyz with hyz | rfl
        . left
          exact hxy.trans hyz
        . left
          exact hxy
      . exact hyz
  }
  rfl

def Ex_8_5_5_b : Decidable (∀ (X Y:Type) (_: LinearOrder Y) (f:X → Y), ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  apply isFalse
  push_neg
  -- use Fin 2 to Fin 1 as counter example.
  use Fin 2, Fin 1, inferInstance, fun _ ↦ 0
  intro h₀ heq
  have : ∀ x y : Fin 2, h₀.le x y ↔ x = y := by
    intro x y
    have := congr_fun (congr_fun heq x) y; simp at this; exact this
  have htf := h₀.le_total (0 : Fin 2) 1
  rcases htf with h | h <;> simp_all

theorem Ex_8_5_5_b' (X Y:Type) (_: LinearOrder Y) (f:X → Y) (hf: Function.Injective f):
    ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  have le_iff : ∀ x y, (f x < f y ∨ x = y) ↔ f x ≤ f y := by
    intro x y
    constructor
    · rintro (hlt | rfl)
      · exact hlt.le
      · exact le_refl _
    · intro hle
      rcases hle.eq_or_lt with heq | hlt
      · right; exact hf heq
      · left; exact hlt
  use {
    le := fun x y ↦ f x < f y ∨ x = y
    le_refl := by simp
    le_antisymm := by
      intro x y hxy hyx
      rw [le_iff] at hxy hyx
      exact hf (le_antisymm hxy hyx)
    le_trans := by
      intro x y z hxy hyz
      rw [le_iff] at *
      exact le_trans hxy hyz
    le_total := by
      intro x y
      rw [le_iff, le_iff]
      exact le_total (f x) (f y)
    lt_iff_le_not_ge := by
      intro x y
      simp only [le_iff]
    min_def := by intro x y; simp only
    max_def := by intro x y; simp only
    toDecidableLE := by
      intro x y
      exact decidable_of_iff (f x ≤ f y) (le_iff x y).symm
  }
  rfl

/-- Exercise 8.5.6 -/
abbrev OrderIdeals (X: Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

noncomputable def OrderIdeals.iso {X: Type} [PartialOrder X] : X ≃o OrderIdeals X := {
  toFun x := ⟨ .Iic x, by simp ⟩
  invFun I := Classical.choose I.2
  left_inv := by
    intro x
    have h := Classical.choose_spec (show (⟨.Iic x, ⟨x, Set.mem_univ _, rfl⟩⟩ : OrderIdeals X).1 ∈
        .Iic '' .univ from ⟨x, Set.mem_univ _, rfl⟩)
    exact Set.Iic_injective h.2
  right_inv := by
    intro ⟨I, hI⟩
    ext : 1
    exact (Classical.choose_spec hI).2
  map_rel_iff' := by simp
  }

/-- Exercise 8.5.7 -/
example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMin x) (hy: IsMin y) : x = y := by
  rcases le_total x y with h | h
  · exact le_antisymm h (hy h)
  · exact le_antisymm (hx h) h

example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
  rcases le_total x y with h | h
  · exact le_antisymm h (hx h)
  · exact le_antisymm (hy h) h

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x)
  (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by
  classical
  by_contra h
  haveI : Infinite X := not_finite_iff_infinite.mp h
  let x0 : Set.univ := Classical.choose (hmin Set.univ (by simp))
  have hx0min : IsMin x0 := Classical.choose_spec (hmin Set.univ (by simp))
  have hx0min' : IsMin x0.1 := by simpa [IsMin] using hx0min
  let next : (Yf : {Y : Set X // Y.Finite}) → {x : X // x ∈ (Yf.1)ᶜ} := fun Yf =>
    Classical.choose (hmin Yf.1ᶜ (Yf.2.infinite_compl.nonempty))
  have hnextmin : ∀ Yf, IsMin (next Yf) := by
    intro Yf
    exact Classical.choose_spec (hmin Yf.1ᶜ (Yf.2.infinite_compl.nonempty))
  let Y : ℕ → {Y : Set X // Y.Finite} :=
    Nat.rec ⟨{x0.1}, Set.finite_singleton x0.1⟩
      (fun _ Yn => ⟨insert (next Yn).1 Yn.1, Yn.2.insert (next Yn).1⟩)
  let x : ℕ → X := Nat.rec x0.1 (fun n _ => (next (Y n)).1)
  have hY_eq : ∀ n, (Y n).1 = Set.Iic (x n) := by
    intro n
    induction n with
    | zero =>
        ext z
        constructor
        · intro hz
          simp at hz
          rcases hz with rfl
          exact le_rfl
        · intro hz
          have : z = x0.1 := le_antisymm hz (hx0min' hz)
          simp [Y, this]
    | succ n ih =>
        ext z
        change (z = (next (Y n)).1 ∨ z ∈ (Y n).1) ↔ z ≤ (next (Y n)).1
        constructor
        · intro hz
          rcases hz with rfl | hz
          · exact le_rfl
          · have hzle : z ≤ x n := by simpa [ih] using hz
            have hnotle : ¬ (next (Y n)).1 ≤ x n := by simpa [ih] using (next (Y n)).2
            exact hzle.trans (lt_of_not_ge hnotle).le
        · intro hz
          by_cases hzx : z = (next (Y n)).1
          · exact Or.inl hzx
          · right
            by_contra hznot
            have hzcomp : z ∈ (Y n).1ᶜ := hznot
            have hxle : (next (Y n)).1 ≤ z := by
              simpa using hnextmin (Y n)
                (show (⟨z, hzcomp⟩ : {x : X // x ∈ (Y n).1ᶜ}) ≤ next (Y n) from hz)
            exact hzx (le_antisymm hz hxle)
  have hstep : ∀ n, x n < x (n + 1) := by
    intro n
    have hnotle : ¬ x (n + 1) ≤ x n := by simpa [x, hY_eq n] using (next (Y n)).2
    exact lt_of_not_ge hnotle
  let Yinf : Set X := Set.range x
  obtain ⟨⟨y, hyY⟩, hymax⟩ := hmax Yinf ⟨x 0, Set.mem_range_self 0⟩
  rcases hyY with ⟨m, rfl⟩
  have hback : x (m + 1) ≤ x m := by
    simpa [Yinf, x] using hymax
      (show (⟨x m, Set.mem_range_self m⟩ : Yinf) ≤ ⟨x (m + 1), Set.mem_range_self (m + 1)⟩ from
        (hstep m).le)
  exact (not_le_of_gt (hstep m)) hback


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's {name}`Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by
    intro ⟨x, y⟩
    simp only
    tauto
  le_antisymm := by
    intro ⟨x, y⟩ ⟨x', y'⟩ hxy hyx
    simp only at hxy hyx
    rcases hxy with hxy | ⟨rfl, hxy⟩
    · rcases hyx with hyx | ⟨rfl, _⟩
      · exact absurd (hxy.trans hyx) (lt_irrefl _)
      · exact absurd hxy (lt_irrefl _)
    · rcases hyx with hyx | ⟨_, hyx⟩
      · exact absurd hyx (lt_irrefl _)
      · congr 1; exact le_antisymm hxy hyx
  le_trans := by
    intro ⟨x, y⟩ ⟨x', y'⟩ ⟨x'', y''⟩ hxy hyz
    simp only at hxy hyz ⊢
    rcases hxy with hxy | ⟨rfl, hxy⟩ <;> rcases hyz with hyz | ⟨rfl, hyz⟩
    · left; exact hxy.trans hyz
    · left; exact hxy
    · left; exact hyz
    · right; exact ⟨rfl, le_trans hxy hyz⟩
}

instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) := {
  Lex'.partialOrder with
  le_total := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    rcases lt_trichotomy x x' with h | rfl | h
    · left; left; exact h
    · rcases le_total y y' with h | h
      · left; right; exact ⟨rfl, h⟩
      · right; right; exact ⟨rfl, h⟩
    · right; left; exact h
  lt := fun ⟨x, y⟩ ⟨x', y'⟩ ↦ (x < x') ∨ (x = x' ∧ y < y')
  lt_iff_le_not_ge := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    simp only
    constructor
    · rintro (h | ⟨rfl, h⟩)
      · refine ⟨Or.inl h, fun h' ↦ ?_⟩
        rcases h' with h' | ⟨rfl, h'⟩
        · exact absurd (h.trans h') (lt_irrefl _)
        · exact absurd h (lt_irrefl _)
      · refine ⟨Or.inr ⟨rfl, h.le⟩, fun h' ↦ ?_⟩
        rcases h' with h' | ⟨_, h'⟩
        · exact absurd h' (lt_irrefl _)
        · exact absurd h (not_lt.mpr h')
    · rintro ⟨h1 | ⟨rfl, h1⟩, h2⟩
      · left; exact h1
      · right; exact ⟨rfl, lt_of_le_not_ge h1 (fun h ↦ h2 (Or.inr ⟨rfl, h⟩))⟩
  toDecidableLE := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    exact decidable_of_iff (x < x' ∨ (x = x' ∧ y ≤ y')) Iff.rfl
}

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
    WellFoundedLT (Lex' (X × Y)) := by
  -- Every nonempty subset A has a minimum: pick min first coord x₀, then min second coord y₀
  -- among elements with first coord x₀.
  have hminX := (WellFoundedLT.iff X).mp ‹_›
  have hminY := (WellFoundedLT.iff Y).mp ‹_›
  have htot : IsTotal (Lex' (X × Y)) := @le_total _ Lex'.linearOrder
  exact (WellFoundedLT.iff' htot).mpr fun A ⟨⟨a₁, a₂⟩, ha⟩ ↦ by
    -- Project to first coordinates, find minimum x₀
    let πA : Set X := { x | ∃ y, (x, y) ∈ A }
    obtain ⟨⟨x₀, ⟨y₁, hy₁⟩⟩, hx₀min⟩ := hminX πA ⟨a₁, a₂, ha⟩
    -- Among elements of A with first coord x₀, find minimum y₀
    let fib : Set Y := { y | (x₀, y) ∈ A }
    obtain ⟨⟨y₀, hy₀mem⟩, hy₀min⟩ := hminY fib ⟨y₁, hy₁⟩
    change (x₀, y₀) ∈ A at hy₀mem
    -- (x₀, y₀) is the minimum of A
    refine ⟨⟨(x₀, y₀), hy₀mem⟩, fun ⟨⟨x', y'⟩, hxy'⟩ hle ↦ ?_⟩
    -- goal: (x₀, y₀) ≤ (x', y') in lex order, given (x', y') ≤ (x₀, y₀)
    show x₀ < x' ∨ (x₀ = x' ∧ y₀ ≤ y')
    -- from hle: x' < x₀ ∨ (x' = x₀ ∧ y' ≤ y₀)
    rcases hle with hx_lt | ⟨rfl, hy_le⟩
    · -- x' < x₀: but x₀ is min of πA and x' ∈ πA, so x₀ ≤ x'
      exact absurd hx_lt (not_lt.mpr (hx₀min (b := ⟨x', y', hxy'⟩) (le_of_lt hx_lt)))
    · -- x' = x₀: y' ≤ y₀ and y₀ is min of fiber, so y₀ ≤ y'
      exact Or.inr ⟨rfl, hy₀min (b := ⟨y', hxy'⟩) hy_le⟩

/-- Exercise 8.5.15 -/
theorem inj_trichotomy {X Y : Type} (h: ¬ ∃ f : X → Y, Function.Injective f) :
    ∃ g : Y → X, Function.Injective g := by
  -- Represent partial injections as graphs: subsets of Y × X that are
  -- functional (each y maps to at most one x) and injective (each x from at most one y).
  classical
  let IsPartialInj (G : Set (Y × X)) : Prop :=
    (∀ y x₁ x₂, (y, x₁) ∈ G → (y, x₂) ∈ G → x₁ = x₂) ∧
    (∀ y₁ y₂ x, (y₁, x) ∈ G → (y₂, x) ∈ G → y₁ = y₂)
  let S := { G : Set (Y × X) | IsPartialInj G }
  -- S is nonempty (∅ is a partial injection)
  have hSne : Nonempty S := ⟨⟨∅, fun _ _ _ h ↦ h.elim, fun _ _ _ h ↦ h.elim⟩⟩
  -- Chains in S have upper bounds (their union)
  have chain_ub : ∀ C : Set S, IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
    intro C ⟨htot, hCne⟩
    refine ⟨⟨⋃ G ∈ C, (G : S).val, ?_⟩, fun ⟨G, hG⟩ hGC ↦ ?_⟩
    · constructor
      · intro y x₁ x₂ h₁ h₂
        rw [Set.mem_iUnion₂] at h₁ h₂
        obtain ⟨⟨G₁, hG₁⟩, hG₁C, hyx₁⟩ := h₁
        obtain ⟨⟨G₂, hG₂⟩, hG₂C, hyx₂⟩ := h₂
        rcases htot ⟨⟨G₁, hG₁⟩, hG₁C⟩ ⟨⟨G₂, hG₂⟩, hG₂C⟩ with hsub | hsub
        · exact hG₂.1 y x₁ x₂ (hsub hyx₁) hyx₂
        · exact hG₁.1 y x₁ x₂ hyx₁ (hsub hyx₂)
      · intro y₁ y₂ x h₁ h₂
        rw [Set.mem_iUnion₂] at h₁ h₂
        obtain ⟨⟨G₁, hG₁⟩, hG₁C, hy₁x⟩ := h₁
        obtain ⟨⟨G₂, hG₂⟩, hG₂C, hy₂x⟩ := h₂
        rcases htot ⟨⟨G₁, hG₁⟩, hG₁C⟩ ⟨⟨G₂, hG₂⟩, hG₂C⟩ with hsub | hsub
        · exact hG₂.2 y₁ y₂ x (hsub hy₁x) hy₂x
        · exact hG₁.2 y₁ y₂ x hy₁x (hsub hy₂x)
    · show G ⊆ ⋃ G' ∈ C, (G' : S).val
      intro p hp
      exact Set.mem_biUnion hGC hp
  -- By Zorn's lemma, get a maximal partial injection
  obtain ⟨⟨G₀, hG₀S⟩, hG₀max⟩ := Zorns_lemma chain_ub
  replace hG₀max : ∀ G ∈ S, G₀ ⊆ G → G ⊆ G₀ := by
    intro G hGS hG₀G
    exact hG₀max (b := ⟨G, hGS⟩) hG₀G
  -- Extract the domain and the partial function
  let dom : Set Y := { y | ∃ x, (y, x) ∈ G₀ }
  have hfunc : ∀ y ∈ dom, ∃! x, (y, x) ∈ G₀ := by
    intro y ⟨x, hx⟩
    exact ⟨x, hx, fun x' hx' => (hG₀S.1 y x' x hx' hx)⟩
  -- Build the function on dom
  let f₀ : dom → X := fun ⟨y, hy⟩ => (hfunc y hy).choose
  have hf₀_mem : ∀ (y : Y) (hy : y ∈ dom), (y, f₀ ⟨y, hy⟩) ∈ G₀ :=
    fun y hy => (hfunc y hy).choose_spec.1
  have hf₀_inj : Function.Injective f₀ := by
    intro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ heq
    have := hG₀S.2 y₁ y₂ (f₀ ⟨y₁, hy₁⟩) (hf₀_mem y₁ hy₁) (heq ▸ hf₀_mem y₂ hy₂)
    exact Subtype.ext this
  -- Claim: dom = Set.univ
  suffices hdom : dom = Set.univ by
    have hmem : ∀ y, y ∈ dom := fun y => hdom ▸ Set.mem_univ y
    let g : Y → X := fun y => f₀ ⟨y, hmem y⟩
    refine ⟨g, fun y₁ y₂ (heq : g y₁ = g y₂) => ?_⟩
    have := @hf₀_inj ⟨y₁, hmem y₁⟩ ⟨y₂, hmem y₂⟩ heq
    exact congrArg Subtype.val this
  -- Suppose dom ≠ Set.univ; find y₀ ∉ dom
  by_contra hdom
  obtain ⟨y₀, hy₀⟩ := (Set.ne_univ_iff_exists_notMem dom).mp hdom
  -- If range of f₀ = Set.univ, we'd get an injection X → Y, contradicting h
  have hrange : ¬ Function.Surjective f₀ := by
    intro hsurj
    apply h
    refine ⟨fun x => (hsurj x).choose.val, fun x₁ x₂ heq => ?_⟩
    -- heq : (hsurj x₁).choose.val = (hsurj x₂).choose.val
    have heq_sub : (hsurj x₁).choose = (hsurj x₂).choose := Subtype.ext heq
    have h₁ := (hsurj x₁).choose_spec  -- f₀ ... = x₁
    have h₂ := (hsurj x₂).choose_spec  -- f₀ ... = x₂
    rw [heq_sub] at h₁
    exact h₁.symm.trans h₂
  -- So there exists x₀ not in the range of f₀
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ y : dom, f₀ y ≠ x₀ := by
    by_contra hall
    push_neg at hall
    exact hrange (fun x => ⟨(hall x).choose, (hall x).choose_spec⟩)
  -- Extend G₀ by adding (y₀, x₀)
  let G₁ := G₀ ∪ {(y₀, x₀)}
  have hG₁S : G₁ ∈ S := by
    constructor
    · intro y x₁ x₂ hyx₁ hyx₂
      rcases hyx₁ with hyx₁ | hyx₁ <;> rcases hyx₂ with hyx₂ | hyx₂
      · exact hG₀S.1 y x₁ x₂ hyx₁ hyx₂
      · simp at hyx₂; obtain ⟨rfl, rfl⟩ := hyx₂
        exact absurd ⟨x₁, hyx₁⟩ hy₀
      · simp at hyx₁; obtain ⟨rfl, rfl⟩ := hyx₁
        exact absurd ⟨x₂, hyx₂⟩ hy₀
      · simp at hyx₁ hyx₂; exact hyx₁.2.trans hyx₂.2.symm
    · intro y₁ y₂ x hy₁x hy₂x
      rcases hy₁x with hy₁x | hy₁x <;> rcases hy₂x with hy₂x | hy₂x
      · exact hG₀S.2 y₁ y₂ x hy₁x hy₂x
      · simp at hy₂x; obtain ⟨rfl, rfl⟩ := hy₂x
        exfalso; exact hx₀ ⟨y₁, ⟨x, hy₁x⟩⟩
          ((hfunc y₁ ⟨x, hy₁x⟩).choose_spec.2 x hy₁x).symm
      · simp at hy₁x; obtain ⟨rfl, rfl⟩ := hy₁x
        exfalso; exact hx₀ ⟨y₂, ⟨x, hy₂x⟩⟩
          ((hfunc y₂ ⟨x, hy₂x⟩).choose_spec.2 x hy₂x).symm
      · simp at hy₁x hy₂x; exact hy₁x.1.trans hy₂x.1.symm
  have hG₀_sub : G₀ ⊆ G₁ := Set.subset_union_left
  have hG₀_ne : G₀ ≠ G₁ := by
    intro heq
    have : (y₀, x₀) ∈ G₀ := heq ▸ Set.mem_union_right G₀ rfl
    exact hy₀ ⟨x₀, this⟩
  have hG₁_sub := hG₀max G₁ hG₁S hG₀_sub
  exact hG₀_ne (Set.Subset.antisymm hG₀_sub hG₁_sub)

/-- Corollary of Exercise 8.5.15: cardinalities are totally ordered. -/
theorem LeCard_total (X Y : Type) : LeCard X Y ∨ LeCard Y X := by
  by_cases h : LeCard X Y
  · left; exact h
  · right; exact inj_trichotomy h

/-- Exercise 8.5.16: The set of partial orderings on X, ordered by "coarser than", is itself
a partial order. -/
instance PartialOrder.coarserOrder (X : Type) : PartialOrder (PartialOrder X) where
  le p1 p2 := ∀ x y : X, p1.le x y → p2.le x y
  le_refl := by simp
  le_trans p1 p2 p3 h12 h23 := by
    intro x y h
    exact h23 x y (h12 x y h)
  le_antisymm p1 p2 h12 h21 := by
    ext x y
    exact ⟨h12 x y, h21 x y⟩

/-- The divisibility ordering on PNat (Exercise 8.5.3) is coarser than the usual ordering. -/
example : PNat.divOrder ≤ (inferInstance : PartialOrder PNat) := by
  intro x y h
  obtain ⟨n, rfl⟩ := h
  show x ≤ n * x
  exact Nat.le_mul_of_pos_left x n.pos

/-- The discrete ordering (x ≤ y ↔ x = y) is the unique minimal element. -/
@[reducible]
def PartialOrder.discrete (X : Type) : PartialOrder X where
  le x y := x = y
  le_refl := fun _ ↦ rfl
  le_antisymm := fun _ _ h _ ↦ h
  le_trans := fun _ _ _ h1 h2 ↦ h1.trans h2

theorem PartialOrder.discrete_isBot (X : Type) (p : PartialOrder X) :
    PartialOrder.discrete X ≤ p := by
  intro x y h
  subst x
  rfl

theorem PartialOrder.discrete_isMin (X : Type) :
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE (PartialOrder.discrete X) :=
  fun _ _ ↦ discrete_isBot X _

theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) : p = discrete X :=
  le_antisymm (h (discrete_isBot X p)) (discrete_isBot X p)

/-- A partial ordering is maximal in the coarser order iff it is a total ordering. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) :
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by
  constructor
  · -- If p is maximal, it must be total
    intro hmax
    by_contra htot
    rw [Chapter8.IsTotal] at htot; push_neg at htot
    obtain ⟨x, y, hxy, hyx⟩ := htot
    -- Construct q: a ≤q b iff a ≤p b, or (a ≤p x ∧ y ≤p b)
    let q : PartialOrder X := {
      le := fun a b ↦ p.le a b ∨ (p.le a x ∧ p.le y b)
      lt := fun a b ↦ (p.le a b ∨ (p.le a x ∧ p.le y b)) ∧ ¬(p.le b a ∨ (p.le b x ∧ p.le y a))
      le_refl := fun a ↦ Or.inl (p.le_refl a)
      le_antisymm := by
        intro a b hab hba
        rcases hab with hab | ⟨hax, hyb⟩ <;> rcases hba with hba | ⟨hbx, hya⟩
        · exact p.le_antisymm a b hab hba
        · -- a ≤p b, b ≤p x, y ≤p a → y ≤p x, contradiction
          exact absurd (p.le_trans _ _ _ (p.le_trans _ _ _ hya hab) hbx) hyx
        · exact absurd (p.le_trans _ _ _ (p.le_trans _ _ _ hyb hba) hax) hyx
        · exact absurd (p.le_trans _ _ _ hya hax) hyx
      le_trans := by
        intro a b c hab hbc
        rcases hab with hab | ⟨hax, hyb⟩ <;> rcases hbc with hbc | ⟨hbx, hyc⟩
        · exact Or.inl (p.le_trans _ _ _ hab hbc)
        · exact Or.inr ⟨p.le_trans _ _ _ hab hbx, hyc⟩
        · exact Or.inr ⟨hax, p.le_trans _ _ _ hyb hbc⟩
        · exact Or.inr ⟨hax, hyc⟩
      lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl
    }
    -- q is strictly finer than p (p ≤ q but q ≠ p)
    have hpq : p ≤ q := fun a b h ↦ Or.inl h
    have hqp : ¬ q ≤ p := by
      intro hqp
      exact hxy (hqp x y (Or.inr ⟨p.le_refl x, p.le_refl y⟩))
    exact hqp (hmax hpq)
  · -- If p is total, it's maximal: any finer q must equal p
    intro htot q hpq a b hab
    rcases htot a b with h | h
    · exact h
    · -- h : b ≤p a, hab : a ≤q b, so b ≤q a, antisymmetry gives a = b
      have := q.le_antisymm a b hab (hpq b a h)
      exact this ▸ p.le_refl a

/-- Given any partial ordering, there exists a finer total ordering (by Zorn's lemma). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) :
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by
  classical
  -- Apply Zorn's to the set of partial orders finer than p
  let S := { q : PartialOrder X | p ≤ q }
  have hSne : Nonempty S := ⟨⟨p, le_refl p⟩⟩
  have chain_ub : ∀ C : Set S, Chapter8.IsTotal C ∧ C.Nonempty →
      ∃ ub, IsUpperBound C ub := by
    intro C ⟨htot, ⟨⟨q₀, hq₀⟩, hq₀C⟩⟩
    -- Upper bound: x ≤ y iff x ≤_q y for some q in C
    let ub_le : X → X → Prop := fun x y ↦ ∃ q ∈ C, (q : S).val.le x y
    have hub_refl : ∀ x, ub_le x x := fun x ↦ ⟨⟨q₀, hq₀⟩, hq₀C, q₀.le_refl x⟩
    have hub_antisymm : ∀ x y, ub_le x y → ub_le y x → x = y := by
      intro x y ⟨⟨q₁, hq₁S⟩, hq₁C, hxy⟩ ⟨⟨q₂, hq₂S⟩, hq₂C, hyx⟩
      rcases htot ⟨⟨q₁, hq₁S⟩, hq₁C⟩ ⟨⟨q₂, hq₂S⟩, hq₂C⟩ with h | h
      · exact q₂.le_antisymm x y (h x y hxy) hyx
      · exact q₁.le_antisymm x y hxy (h y x hyx)
    have hub_trans : ∀ x y z, ub_le x y → ub_le y z → ub_le x z := by
      intro x y z ⟨⟨q₁, hq₁S⟩, hq₁C, hxy⟩ ⟨⟨q₂, hq₂S⟩, hq₂C, hyz⟩
      rcases htot ⟨⟨q₁, hq₁S⟩, hq₁C⟩ ⟨⟨q₂, hq₂S⟩, hq₂C⟩ with h | h
      · exact ⟨⟨q₂, hq₂S⟩, hq₂C, q₂.le_trans x y z (h x y hxy) hyz⟩
      · exact ⟨⟨q₁, hq₁S⟩, hq₁C, q₁.le_trans x y z hxy (h y z hyz)⟩
    let ub : PartialOrder X := {
      le := ub_le
      lt := fun x y ↦ ub_le x y ∧ ¬ ub_le y x
      le_refl := hub_refl
      le_antisymm := hub_antisymm
      le_trans := hub_trans
      lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl
    }
    have hub_ge_p : p ≤ ub := fun x y h ↦ ⟨⟨q₀, hq₀⟩, hq₀C, hq₀ x y h⟩
    refine ⟨⟨ub, hub_ge_p⟩, fun ⟨q, hqS⟩ hqC x y hxy ↦ ?_⟩
    exact ⟨⟨q, hqS⟩, hqC, hxy⟩
  obtain ⟨⟨q, hpq⟩, hqmax⟩ := Zorns_lemma chain_ub
  refine ⟨q, hpq, (isMax_iff_isTotal X q).mp fun q' hle ↦ ?_⟩
  -- hqmax : IsMax (⟨q, hpq⟩ : S), need to show q' ≤ q
  -- q' is finer than q, so q' is finer than p, so ⟨q', _⟩ ∈ S
  have hpq' : p ≤ q' := le_trans hpq hle
  exact hqmax (b := ⟨q', hpq'⟩) hle

/-- Exercise 8.5.17: Use Zorn's lemma to reprove Exercise 8.4.2 -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  classical
  -- Ω = sets Y such that Y ∩ X α has at most 1 element for all α
  let Ω := { Y : Set U | ∀ α, (Y ∩ X α).Subsingleton }
  have hΩne : Nonempty Ω := ⟨⟨∅, fun α ↦ by simp⟩⟩
  -- Chains have upper bounds: take the union
  have chain_ub : ∀ C : Set Ω, Chapter8.IsTotal C ∧ C.Nonempty →
      ∃ ub, IsUpperBound C ub := by
    intro C ⟨htot, ⟨Y₀, hY₀C⟩⟩
    refine ⟨⟨⋃ Y ∈ C, (Y : Ω).val, fun α a ⟨haU, haX⟩ b ⟨hbU, hbX⟩ ↦ ?_⟩,
      fun Y hYC x hx ↦ Set.mem_biUnion hYC hx⟩
    rw [Set.mem_iUnion₂] at haU hbU
    obtain ⟨⟨Ya, hYa⟩, hYaC, haYa⟩ := haU
    obtain ⟨⟨Yb, hYb⟩, hYbC, hbYb⟩ := hbU
    rcases htot ⟨⟨Ya, hYa⟩, hYaC⟩ ⟨⟨Yb, hYb⟩, hYbC⟩ with hsub | hsub
    · exact hYb α ⟨hsub haYa, haX⟩ ⟨hbYb, hbX⟩
    · exact hYa α ⟨haYa, haX⟩ ⟨hsub hbYb, hbX⟩
  -- Zorn gives a maximal Z ∈ Ω
  obtain ⟨⟨Z, hZΩ⟩, hZmax⟩ := Zorns_lemma chain_ub
  -- Z hits every X α
  suffices hhit : ∀ α, (Z ∩ X α).Nonempty by
    use Z; intro α
    obtain ⟨z, hz⟩ := hhit α
    rw [Nat.card_eq_one_iff_exists]
    exact ⟨⟨z, hz⟩, fun ⟨b, hb⟩ ↦ Subtype.ext (hZΩ α hb hz)⟩
  -- If Z misses some X α₀, extend Z by adding an element of X α₀
  intro α₀
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  obtain ⟨x₀⟩ := hne α₀
  let Z' := Z ∪ {x₀.val}
  have hZ'Ω : Z' ∈ Ω := by
    intro α a ⟨haZ', haX⟩ b ⟨hbZ', hbX⟩
    rcases haZ' with haZ | haZ <;> rcases hbZ' with hbZ | hbZ
    · exact hZΩ α ⟨haZ, haX⟩ ⟨hbZ, hbX⟩
    · -- a ∈ Z, b = x₀ ∈ X α₀; since b ∈ X α, α = α₀ (by disjointness), so a ∈ Z ∩ X α₀ = ∅
      simp at hbZ; subst hbZ
      by_cases heq : α = α₀
      · exact absurd ⟨haZ, heq ▸ haX⟩ (Set.eq_empty_iff_forall_notMem.mp hempty a)
      · exact absurd x₀.property
          (Set.disjoint_left.mp (h (Set.mem_univ α) (Set.mem_univ α₀) heq) hbX)
    · -- a = x₀ ∈ X α₀, b ∈ Z; symmetric case
      simp at haZ; subst haZ
      by_cases heq : α = α₀
      · exact absurd ⟨hbZ, heq ▸ hbX⟩ (Set.eq_empty_iff_forall_notMem.mp hempty b)
      · exact absurd x₀.property
          (Set.disjoint_left.mp (h (Set.mem_univ α) (Set.mem_univ α₀) heq) haX)
    · simp at haZ hbZ; exact haZ.trans hbZ.symm
  have hZZ' : Z ⊆ Z' := Set.subset_union_left
  have hZ'neZ : ¬ Z' ⊆ Z := by
    intro hsub
    have : x₀.val ∈ Z := hsub (Set.mem_union_right _ rfl)
    exact Set.eq_empty_iff_forall_notMem.mp hempty x₀.val ⟨this, x₀.property⟩
  exact hZ'neZ (hZmax (b := ⟨Z', hZ'Ω⟩) hZZ')

/-- Exercise 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X:Type} [PartialOrder X] :
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by
  -- Apply Zorn's lemma to {S : Set X // IsTotal S}, ordered by inclusion.
  have : Nonempty {S : Set X // IsTotal S} :=
    ⟨⟨∅, fun ⟨_, h⟩ => h.elim⟩⟩
  have chain_ub : ∀ C : Set {S : Set X // IsTotal S},
      IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
    intro C ⟨hCtotal, hCne⟩
    refine ⟨⟨⋃ S ∈ C, S.val, ?_⟩, fun ⟨S, hS⟩ hSC => Set.subset_biUnion_of_mem hSC⟩
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp [Set.mem_iUnion] at hx hy
    obtain ⟨i, ⟨hi_total, hiC⟩, hxi⟩ := hx
    obtain ⟨j, ⟨hj_total, hjC⟩, hyj⟩ := hy
    rcases hCtotal ⟨⟨i, hi_total⟩, hiC⟩ ⟨⟨j, hj_total⟩, hjC⟩ with hij | hji
    · exact hj_total ⟨x, hij hxi⟩ ⟨y, hyj⟩
    · exact hi_total ⟨x, hxi⟩ ⟨y, hji hyj⟩
  obtain ⟨⟨M, hMtotal⟩, hMmax⟩ := Zorns_lemma chain_ub
  exact ⟨M, hMtotal, fun N hNtotal hMN => hMmax (b := ⟨N, hNtotal⟩) hMN⟩

theorem zorns_lemma_of_hausdorff {X:Type} [PartialOrder X] [Nonempty X]
  (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
  (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x:X, IsMax x := by
  obtain ⟨M, hMtotal, hMmax⟩ := hhausdorff
  have hMne : M.Nonempty := by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    by_contra h
    push_neg at h
    have : IsTotal ({x₀} : Set X) := fun ⟨a, ha⟩ ⟨b, hb⟩ => by
      simp [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; left; rfl
    have := hMmax this (by simp [h])
    simp [h] at this
  obtain ⟨x, hx⟩ := hchain M ⟨hMtotal, hMne⟩
  refine ⟨x, fun y hxy => ?_⟩
  -- M ∪ {y} is total (since y ≥ x ≥ everything in M), so maximality forces y ∈ M, hence y ≤ x.
  have hMy : IsTotal (M ∪ {y} : Set X) := by
    have hMy_ub : ∀ a ∈ M, a ≤ y := fun a ha => le_trans (hx a ha) hxy
    intro ⟨a, ha⟩ ⟨b, hb⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hMtotal ⟨a, ha⟩ ⟨b, hb⟩
    · left; show a ≤ b; exact Set.mem_singleton_iff.mp hb ▸ hMy_ub a ha
    · right; show b ≤ a; exact Set.mem_singleton_iff.mp ha ▸ hMy_ub b hb
    · left; show a ≤ b; rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  have hle := hMmax hMy Set.subset_union_left
  exact hx y (hle (Set.mem_union_right _ rfl))

-- Exercise 8.5.19

/-- A well-ordered subset of X: a subset Y with a linear order and well-foundedness. -/
structure WellOrderedSubset (X : Type) where
  carrier : Set X
  ord : LinearOrder carrier
  wf : @WellFoundedLT carrier ord.toLT

/-- `(W, ≤)` is an initial segment of `(W', ≤')` if `W ⊆ W'`, the orderings agree on W,
and `W = {y ∈ W' : y <' x}` for some `x ∈ W`'. -/
def WellOrderedSubset.IsInitialSegment {X : Type} (W W' : WellOrderedSubset X) : Prop :=
  ∃ x : W'.carrier,
    W.carrier = Subtype.val '' {z : W'.carrier | W'.ord.lt z x} ∧
    ∀ (a b : W.carrier) (ha : a.1 ∈ W'.carrier) (hb : b.1 ∈ W'.carrier),
      W.ord.le a b ↔ W'.ord.le ⟨a, ha⟩ ⟨b, hb⟩

theorem WellOrderedSubset.IsInitialSegment.subset {X : Type} {W W' : WellOrderedSubset X}
    (h : W.IsInitialSegment W') : W.carrier ⊂ W'.carrier := by
  obtain ⟨x, heq, _⟩ := h
  constructor
  · rw [heq]
    rintro _ ⟨z, _, rfl⟩
    exact z.2
  · rw [Set.not_subset]
    refine ⟨x.1, x.2, ?_⟩
    rw [heq]
    rintro ⟨z, hz, hzeq⟩
    exact absurd (Subtype.val_injective hzeq ▸ hz) (@lt_irrefl _ W'.ord.toPreorder x)

/-- The ordering on well-ordered subsets: equal or initial segment. -/
instance WellOrderedSubset.instPartialOrder (X : Type) : PartialOrder (WellOrderedSubset X) where
  le W W' := W = W' ∨ W.IsInitialSegment W'
  le_refl := fun W ↦ Or.inl rfl
  le_antisymm := by
    intro W W' h1 h2
    rcases h1 with rfl | h1
    · rfl
    rcases h2 with rfl | h2
    · rfl
    exact (h1.subset.asymm h2.subset).elim
  le_trans := by
    intro W W' W'' h1 h2
    rcases h1 with rfl | h1
    · exact h2
    rcases h2 with rfl | h2
    · exact Or.inr h1
    right
    have hsub : W.carrier ⊆ W'.carrier := h1.subset.1
    have hsub' : W'.carrier ⊆ W''.carrier := h2.subset.1
    obtain ⟨x', heqW, hordW⟩ := h1
    obtain ⟨x'', heqW', hordW'⟩ := h2
    -- Helper: transfer < between W' and W'' using the ≤-iff
    have lt_transfer (a b : W'.carrier) (ha : a.1 ∈ W''.carrier) (hb : b.1 ∈ W''.carrier) :
        W'.ord.lt a b ↔ W''.ord.lt ⟨a.1, ha⟩ ⟨b.1, hb⟩ := by
      constructor <;> intro hab
      · exact @lt_of_le_not_ge _ W''.ord.toPreorder _ _
          ((hordW' a b ha hb).mp (@le_of_lt _ W'.ord.toPreorder _ _ hab))
          (fun hle ↦ @lt_irrefl _ W'.ord.toPreorder _
            (@le_antisymm _ W'.ord.toPartialOrder _ _
              (@le_of_lt _ W'.ord.toPreorder _ _ hab) ((hordW' b a hb ha).mpr hle) ▸ hab))
      · exact @lt_of_le_not_ge _ W'.ord.toPreorder _ _
          ((hordW' a b ha hb).mpr (@le_of_lt _ W''.ord.toPreorder _ _ hab))
          (fun hle ↦ @lt_irrefl _ W''.ord.toPreorder _
            (@le_antisymm _ W''.ord.toPartialOrder _ _
              (@le_of_lt _ W''.ord.toPreorder _ _ hab) ((hordW' b a hb ha).mp hle) ▸ hab))
    refine ⟨⟨x'.1, hsub' x'.2⟩, ?_, ?_⟩
    · ext y
      constructor
      · intro hy
        rw [heqW] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact ⟨⟨z.1, hsub' z.2⟩,
          (lt_transfer z x' (hsub' z.2) (hsub' x'.2)).mp hz, rfl⟩
      · rintro ⟨⟨z, hzW''⟩, hlt, rfl⟩
        have hx'W'' : x'.1 ∈ W''.carrier := hsub' x'.2
        have hx'lt : W''.ord.lt ⟨x'.1, hx'W''⟩ x'' := by
          have hx'mem : x'.1 ∈ Subtype.val '' {z : W''.carrier | W''.ord.lt z x''} :=
            heqW' ▸ x'.2
          obtain ⟨w, hw, hweq⟩ := hx'mem
          have : w = ⟨x'.1, hx'W''⟩ := Subtype.ext hweq
          exact this ▸ hw
        have hzW' : z ∈ W'.carrier := by
          rw [heqW']
          exact ⟨⟨z, hzW''⟩, @lt_trans _ W''.ord.toPreorder _ _ _ hlt hx'lt, rfl⟩
        rw [heqW]
        exact ⟨⟨z, hzW'⟩,
          (lt_transfer ⟨z, hzW'⟩ x' hzW'' hx'W'').mpr hlt, rfl⟩
    · intro a b haW'' hbW''
      rw [hordW a b (hsub a.2) (hsub b.2),
        hordW' ⟨a.1, hsub a.2⟩ ⟨b.1, hsub b.2⟩ haW'' hbW'']

/-- The empty well-ordered subset. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

theorem WellOrderedSubset.empty_isMin (X : Type) :
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE (empty X) := by
  intro W hle
  rcases hle with rfl | ⟨x, _, _⟩
  · rfl
  · exact x.2.elim

/-- The maximal elements are precisely the well-orderings of all of X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) :
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by
  constructor
  · -- → : if W is maximal then W.carrier = univ
    intro hmax
    by_contra hne
    push_neg at hne
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem W.carrier).mp hne
    -- Construct W' = W ∪ {x} with x as maximum element
    have hmem_insert : ∀ y, y ∈ insert x W.carrier → y = x ∨ y ∈ W.carrier := by
      intro y hy; exact Set.mem_insert_iff.mp hy
    have hx_mem : x ∈ insert x W.carrier := Set.mem_insert x W.carrier
    have hsub : W.carrier ⊆ insert x W.carrier := Set.subset_insert x W.carrier
    haveI : DecidableEq X := Classical.decEq _
    let carrier' : Set X := insert x W.carrier
    let newLE (a b : carrier') : Prop :=
      if hb : b.1 = x then True
      else if ha : a.1 = x then False
      else W.ord.le
        ⟨a.1, (hmem_insert a.1 a.2).resolve_left ha⟩
        ⟨b.1, (hmem_insert b.1 b.2).resolve_left hb⟩
    let newLT (a b : carrier') : Prop :=
      if ha : a.1 = x then False
      else if hb : b.1 = x then True
      else W.ord.lt
        ⟨a.1, (hmem_insert a.1 a.2).resolve_left ha⟩
        ⟨b.1, (hmem_insert b.1 b.2).resolve_left hb⟩
    have lt_iff_le_not_le : ∀ a b : carrier', newLT a b ↔ newLE a b ∧ ¬newLE b a := by
      intro a b; simp only [newLE, newLT]
      split_ifs <;> first | (simp; done) | exact @lt_iff_le_not_ge _ W.ord.toPreorder _ _
    have le_refl' : ∀ a : carrier', newLE a a := by
      intro a; simp only [newLE]; split_ifs with h
      exact W.ord.le_refl _
    have le_antisymm' : ∀ a b : carrier', newLE a b → newLE b a → a = b := by
      intro a b hab hba; simp only [newLE] at hab hba
      split_ifs at hab hba
      · exact Subtype.ext (‹_ = x›.trans ‹_ = x›.symm)
      · have heq := @le_antisymm _ W.ord.toPartialOrder _ _ hab hba
        exact Subtype.ext (congrArg (fun (s : W.carrier) => s.1) heq)
    have le_trans' : ∀ a b c : carrier', newLE a b → newLE b c → newLE a c := by
      intro a b c hab hbc; simp only [newLE] at hab hbc ⊢
      split_ifs at hab hbc ⊢;
        first | trivial | exact hab.elim | exact hbc.elim
              | exact @le_trans _ W.ord.toPreorder _ _ _ hab hbc
    have le_total' : ∀ a b : carrier', newLE a b ∨ newLE b a := by
      intro a b; simp only [newLE]
      split_ifs <;>
        first | exact Or.inl trivial | exact Or.inr trivial | exact @le_total _ W.ord _ _
    let W'ord : LinearOrder carrier' :=
      { le := newLE
        lt := newLT
        le_refl := le_refl'
        le_antisymm := le_antisymm'
        le_trans := le_trans'
        le_total := le_total'
        lt_iff_le_not_ge := lt_iff_le_not_le
        toDecidableLE := fun a b ↦ Classical.dec _
        toDecidableEq := fun a b ↦ Classical.dec _
        toDecidableLT := fun a b ↦ Classical.dec _ }
    -- Helper: newLT is definitionally equal to W'ord's <
    have hlt_eq : ∀ a b : carrier', (W'ord.lt a b) = newLT a b := fun _ _ => rfl
    have wf' : @WellFoundedLT _ W'ord.toLT := by
      constructor; constructor
      -- First show all W.carrier elements are accessible
      have acc_W : ∀ (a : X) (ha : a ∈ carrier') (_ : a ∈ W.carrier),
          Acc W'ord.lt ⟨a, ha⟩ := by
        intro a ha haW
        refine W.wf.wf.induction (C := fun a' => ∀ ha : a'.1 ∈ carrier',
            Acc W'ord.lt ⟨a'.1, ha⟩) ⟨a, haW⟩ ?_ ha
        intro ⟨a', haW'⟩ ih ha'
        constructor; intro ⟨b, hb⟩ hlt
        rw [hlt_eq] at hlt; simp only [newLT] at hlt
        split_ifs at hlt with hbx hax'
        · exact absurd (hax' ▸ haW') hx
        · exact ih ⟨b, (hmem_insert b hb).resolve_left hbx⟩ hlt
            (hsub ((hmem_insert b hb).resolve_left hbx))
      intro ⟨a, ha⟩
      by_cases hax : a = x
      · subst hax; constructor; intro ⟨b, hb⟩ hlt
        rw [hlt_eq] at hlt; simp only [newLT] at hlt
        split_ifs at hlt with hbx
        exact acc_W b (hsub ((hmem_insert b hb).resolve_left hbx))
          ((hmem_insert b hb).resolve_left hbx)
      · exact acc_W a ha ((hmem_insert a ha).resolve_left hax)
    let W' : WellOrderedSubset X :=
      { carrier := carrier'
        ord := W'ord
        wf := wf' }
    have hiseg : W.IsInitialSegment W' := by
      refine ⟨⟨x, hx_mem⟩, ?_, ?_⟩
      · ext y
        simp only [Set.mem_image, Set.mem_setOf]
        constructor
        · intro hy
          refine ⟨⟨y, hsub hy⟩, ?_, rfl⟩
          show newLT ⟨y, hsub hy⟩ ⟨x, hx_mem⟩
          simp only [newLT]
          split_ifs with hyx
          · exact absurd (hyx ▸ hy) hx
        · rintro ⟨⟨z, hz⟩, hlt, rfl⟩
          show z ∈ W.carrier
          have hzx : z ≠ x := by
            intro heq; rw [hlt_eq] at hlt; simp only [newLT, heq, dite_true] at hlt
          exact (hmem_insert z hz).resolve_left hzx
      · intro a b ha hb
        show W.ord.le a b ↔ newLE ⟨a.1, ha⟩ ⟨b.1, hb⟩
        simp only [newLE]
        have hax : a.1 ≠ x := fun h => hx (h ▸ a.2)
        have hbx : b.1 ≠ x := fun h => hx (h ▸ b.2)
        simp only [hbx, dite_false, hax, dite_false]
    have hle : (instPartialOrder X).toPreorder.toLE.le W W' := Or.inr hiseg
    have hle' := hmax hle
    rcases hle' with heq | hiseg'
    · exact hx (heq ▸ hx_mem)
    · exact absurd hiseg.subset.1 hiseg'.subset.2
  · -- ← : if W.carrier = univ then W is maximal
    intro hfull W' hle
    rcases hle with rfl | h
    · rfl
    · have : W.carrier = W'.carrier := h.subset.1.antisymm (hfull ▸ Set.subset_univ _)
      exact absurd (this.symm ▸ Set.Subset.refl _) h.subset.2

/-- The well-ordering principle: every set has a well-ordering (by Zorn's lemma). -/
theorem well_ordering_principle (X : Type) :
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT := by
  haveI : Nonempty (WellOrderedSubset X) := ⟨WellOrderedSubset.empty X⟩
  suffices hchain : ∀ Y : Set (WellOrderedSubset X),
      Chapter8.IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x by
    obtain ⟨W, hmax⟩ := Zorns_lemma hchain
    have hfull := (WellOrderedSubset.isMax_iff_full X W).mp hmax
    have hmem : ∀ x : X, x ∈ W.carrier := fun x => hfull ▸ Set.mem_univ x
    let f : X → W.carrier := fun x => ⟨x, hmem x⟩
    have hf : Function.Injective f := fun a b h => congrArg Subtype.val h
    refine ⟨@LinearOrder.lift' X W.carrier W.ord f hf, ?_⟩
    exact ⟨InvImage.wf f W.wf.wf⟩
  intro Y ⟨htotal, hne⟩
  -- Construct the union well-ordered subset
  haveI : DecidableEq X := Classical.decEq _
  let unionCarrier : Set X := ⋃ W ∈ Y, W.carrier
  -- For any two elements in the union, find a common W containing both
  have common_member : ∀ a b : unionCarrier,
      ∃ W ∈ Y, a.1 ∈ W.carrier ∧ b.1 ∈ W.carrier := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨Wa, hWaY, haWa⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨Wb, hWbY, hbWb⟩ := Set.mem_iUnion₂.mp hb
    rcases htotal ⟨Wa, hWaY⟩ ⟨Wb, hWbY⟩ with h | h
    · -- Wa ≤ Wb
      exact ⟨Wb, hWbY, by rcases h with rfl | h; exact haWa; exact h.subset.1 haWa, hbWb⟩
    · -- Wb ≤ Wa
      exact ⟨Wa, hWaY, haWa, by rcases h with rfl | h; exact hbWb; exact h.subset.1 hbWb⟩
  -- The ordering is well-defined: if a, b ∈ W and a, b ∈ W', the orderings agree
  have ord_agree : ∀ (W W' : WellOrderedSubset X) (_ : W ∈ Y) (_ : W' ∈ Y)
      (a b : X) (haW : a ∈ W.carrier) (hbW : b ∈ W.carrier)
      (haW' : a ∈ W'.carrier) (hbW' : b ∈ W'.carrier),
      W.ord.le ⟨a, haW⟩ ⟨b, hbW⟩ ↔ W'.ord.le ⟨a, haW'⟩ ⟨b, hbW'⟩ := by
    intro W W' hWY hW'Y a b haW hbW haW' hbW'
    rcases htotal ⟨W, hWY⟩ ⟨W', hW'Y⟩ with h | h
    · rcases h with rfl | h
      · rfl
      · obtain ⟨_, _, hord⟩ := h
        exact hord ⟨a, haW⟩ ⟨b, hbW⟩ haW' hbW'
    · rcases h with rfl | h
      · rfl
      · obtain ⟨_, _, hord⟩ := h
        exact (hord ⟨a, haW'⟩ ⟨b, hbW'⟩ haW hbW).symm
  -- Define the ordering on the union using a chosen common W
  let unionLE (a b : unionCarrier) : Prop :=
    (common_member a b).choose.ord.le
      ⟨a.1, (common_member a b).choose_spec.2.1⟩
      ⟨b.1, (common_member a b).choose_spec.2.2⟩
  -- unionLE doesn't depend on the choice of W, by ord_agree
  have unionLE_eq : ∀ (a b : unionCarrier) (W : WellOrderedSubset X) (hWY : W ∈ Y)
      (haW : a.1 ∈ W.carrier) (hbW : b.1 ∈ W.carrier),
      unionLE a b ↔ W.ord.le ⟨a.1, haW⟩ ⟨b.1, hbW⟩ := by
    intro a b W hWY haW hbW
    exact ord_agree _ W (common_member a b).choose_spec.1 hWY a.1 b.1
      (common_member a b).choose_spec.2.1 (common_member a b).choose_spec.2.2 haW hbW
  -- Build the LinearOrder on unionCarrier
  have le_refl' : ∀ a : unionCarrier, unionLE a a := by
    intro a
    have ⟨W, hWY, haW, _⟩ := common_member a a
    rw [unionLE_eq a a W hWY haW haW]
    exact W.ord.le_refl _
  have le_antisymm' : ∀ a b : unionCarrier, unionLE a b → unionLE b a → a = b := by
    intro a b hab hba
    have ⟨W, hWY, haW, hbW⟩ := common_member a b
    rw [unionLE_eq a b W hWY haW hbW] at hab
    rw [unionLE_eq b a W hWY hbW haW] at hba
    exact Subtype.ext (congrArg (fun (s : W.carrier) => s.1)
      (@le_antisymm _ W.ord.toPartialOrder _ _ hab hba))
  have le_trans' : ∀ a b c : unionCarrier, unionLE a b → unionLE b c → unionLE a c := by
    intro a b c hab hbc
    -- Find a common W for all three
    have ⟨Wab, hWabY, haWab, hbWab⟩ := common_member a b
    have ⟨Wbc, hWbcY, hbWbc, hcWbc⟩ := common_member b c
    -- Get a W containing all three: take the bigger of Wab, Wbc
    rcases htotal ⟨Wab, hWabY⟩ ⟨Wbc, hWbcY⟩ with h | h
    · -- Wab ≤ Wbc: use Wbc as the common member
      have haWbc : a.1 ∈ Wbc.carrier := by
        rcases h with rfl | h; exact haWab; exact h.subset.1 haWab
      rw [unionLE_eq a b Wbc hWbcY haWbc hbWbc] at hab
      rw [unionLE_eq b c Wbc hWbcY hbWbc hcWbc] at hbc
      rw [unionLE_eq a c Wbc hWbcY haWbc hcWbc]
      exact @le_trans _ Wbc.ord.toPreorder _ _ _ hab hbc
    · -- Wbc ≤ Wab: use Wab as the common member
      have hcWab : c.1 ∈ Wab.carrier := by
        rcases h with rfl | h; exact hcWbc; exact h.subset.1 hcWbc
      rw [unionLE_eq a b Wab hWabY haWab hbWab] at hab
      rw [unionLE_eq b c Wab hWabY hbWab hcWab] at hbc
      rw [unionLE_eq a c Wab hWabY haWab hcWab]
      exact @le_trans _ Wab.ord.toPreorder _ _ _ hab hbc
  have le_total' : ∀ a b : unionCarrier, unionLE a b ∨ unionLE b a := by
    intro a b
    have ⟨W, hWY, haW, hbW⟩ := common_member a b
    rw [unionLE_eq a b W hWY haW hbW, unionLE_eq b a W hWY hbW haW]
    exact @le_total _ W.ord _ _
  -- Build the LinearOrder
  let unionOrd : LinearOrder unionCarrier :=
    { le := unionLE
      le_refl := le_refl'
      le_antisymm := le_antisymm'
      le_trans := le_trans'
      le_total := le_total'
      toDecidableLE := fun a b => Classical.dec _
      toDecidableEq := fun a b => Classical.dec _
      toDecidableLT := fun a b => Classical.dec _ }
  -- Helper: transfer lt between union and individual W
  have union_lt_iff : ∀ (a b : unionCarrier) (W : WellOrderedSubset X) (hWY : W ∈ Y)
      (haW : a.1 ∈ W.carrier) (hbW : b.1 ∈ W.carrier),
      unionOrd.lt a b ↔ W.ord.lt ⟨a.1, haW⟩ ⟨b.1, hbW⟩ := by
    intro a b W hWY haW hbW
    show unionLE a b ∧ ¬unionLE b a ↔ W.ord.lt ⟨a.1, haW⟩ ⟨b.1, hbW⟩
    rw [unionLE_eq a b W hWY haW hbW, unionLE_eq b a W hWY hbW haW,
      @lt_iff_le_not_ge _ W.ord.toPreorder]
  -- Initial segments are downward-closed
  have iseg_downward : ∀ (W W' : WellOrderedSubset X), W.IsInitialSegment W' →
      ∀ (a : X) (haW : a ∈ W.carrier) (b : X) (hbW' : b ∈ W'.carrier)
      (haW' : a ∈ W'.carrier),
      W'.ord.lt ⟨b, hbW'⟩ ⟨a, haW'⟩ → b ∈ W.carrier := by
    intro W W' ⟨x, hcarr, _⟩ a haW b hbW' haW' hlt
    rw [hcarr]
    have : W'.ord.lt ⟨a, haW'⟩ x := by
      rw [hcarr] at haW; obtain ⟨z, hz, hzeq⟩ := haW
      exact hzeq ▸ hz
    exact ⟨⟨b, hbW'⟩, @lt_trans _ W'.ord.toPreorder _ _ _ hlt this, rfl⟩
  -- Prove well-foundedness via the min-element characterization
  have unionWF : @WellFoundedLT _ unionOrd.toLT := by
    constructor
    rw [WellFounded.wellFounded_iff_has_min]
    intro S ⟨⟨a, ha⟩, haS⟩
    -- Pick any Wa ∈ Y containing a
    obtain ⟨Wa, hWaY, haWa⟩ := Set.mem_iUnion₂.mp ha
    -- Restrict S to elements in Wa
    set SWa : Set Wa.carrier := {x | ∃ h : x.1 ∈ unionCarrier, ⟨x.1, h⟩ ∈ S}
    have hSWa : SWa.Nonempty :=
      ⟨⟨a, haWa⟩, Set.mem_iUnion₂.mpr ⟨Wa, hWaY, haWa⟩, haS⟩
    -- Take the minimum of SWa in Wa's well-ordering
    set m := Wa.wf.wf.min SWa hSWa
    have hmSWa := Wa.wf.wf.min_mem SWa hSWa
    obtain ⟨hmU, hmS⟩ := hmSWa
    -- m is minimal in all of S
    refine ⟨⟨m.1, hmU⟩, hmS, ?_⟩
    intro ⟨x, hx⟩ hxS hxlt
    -- x < m in the union order. We show x ∈ Wa, contradicting minimality of m.
    obtain ⟨W, hWY, hmW, hxW⟩ := common_member ⟨m.1, hmU⟩ ⟨x, hx⟩
    have hxltW : W.ord.lt ⟨x, hxW⟩ ⟨m.1, hmW⟩ :=
      (union_lt_iff ⟨x, hx⟩ ⟨m.1, hmU⟩ W hWY hxW hmW).mp hxlt
    -- x ∈ Wa: either W ≤ Wa (so x ∈ Wa) or Wa ≤ W (initial segment pulls x into Wa)
    have hxWa : x ∈ Wa.carrier := by
      rcases htotal ⟨W, hWY⟩ ⟨Wa, hWaY⟩ with h | h
      · rcases h with rfl | h; exact hxW; exact h.subset.1 hxW
      · rcases h with rfl | h; exact hxW
        exact iseg_downward Wa W h m.1 m.2 x hxW hmW hxltW
    exact WellFounded.not_lt_min Wa.wf.wf SWa (⟨hx, hxS⟩ : ⟨x, hxWa⟩ ∈ SWa)
      ((union_lt_iff ⟨x, hx⟩ ⟨m.1, hmU⟩ Wa hWaY hxWa m.2).mp hxlt)
  -- Construct the upper bound
  let U : WellOrderedSubset X :=
    { carrier := unionCarrier
      ord := unionOrd
      wf := unionWF }
  -- Check if some Wi already covers everything
  by_cases hex : ∃ Wi ∈ Y, Wi.carrier = unionCarrier
  · -- Use that Wi directly as upper bound
    obtain ⟨Wi, hWiY, hWicarr⟩ := hex
    use Wi; rw [IsUpperBound.iff]; intro Wj hWjY
    rcases htotal ⟨Wj, hWjY⟩ ⟨Wi, hWiY⟩ with h | h
    · exact h
    · -- Wi ≤ Wj → Wi.carrier ⊆ Wj.carrier, but Wj.carrier ⊆ unionCarrier = Wi.carrier
      rcases h with rfl | h
      · exact le_refl _
      · -- h : Wi.IsInitialSegment Wj, so Wi.carrier ⊂ Wj.carrier
        -- But Wj.carrier ⊆ unionCarrier = Wi.carrier, contradiction
        have : Wj.carrier ⊆ Wi.carrier :=
          hWicarr ▸ fun x hx => Set.mem_iUnion₂.mpr ⟨Wj, hWjY, hx⟩
        exact absurd this h.subset.2
  · -- No Wi covers everything, so all have Wi.carrier ⊊ unionCarrier
    push_neg at hex
    use U; rw [IsUpperBound.iff]; intro Wi hWiY
    have hsub : Wi.carrier ⊆ unionCarrier :=
      fun x hx => Set.mem_iUnion₂.mpr ⟨Wi, hWiY, hx⟩
    have hssub : Wi.carrier ⊂ unionCarrier :=
      ⟨hsub, fun h => hex Wi hWiY (hsub.antisymm h)⟩
    right
    -- Find min of {z ∈ unionCarrier | z ∉ Wi.carrier}
    let diffSet : Set unionCarrier := {z | z.1 ∉ Wi.carrier}
    have hdiffNe : diffSet.Nonempty := by
      have ⟨y, hyU, hyni⟩ := Set.not_subset.mp hssub.2; exact ⟨⟨y, hyU⟩, hyni⟩
    obtain ⟨⟨x₀, hx₀U⟩, hx₀diff, hx₀min⟩ := unionWF.wf.has_min diffSet hdiffNe
    -- x₀ is the initial segment witness: Wi.carrier = {y ∈ U.carrier | y <_U x₀}
    refine ⟨⟨x₀, hx₀U⟩, ?_, ?_⟩
    · -- Wi.carrier = Subtype.val '' {z : U.carrier | U.ord.lt z ⟨x₀, hx₀U⟩}
      -- Key fact: z < x₀ in unionOrd ↔ z ∈ Wi.carrier
      have mem_Wi_of_lt : ∀ z (hzU : z ∈ unionCarrier),
          unionOrd.lt ⟨z, hzU⟩ ⟨x₀, hx₀U⟩ → z ∈ Wi.carrier := by
        intro z hzU hlt
        by_contra hzni
        exact hx₀min ⟨z, hzU⟩ hzni hlt
      have lt_x₀_of_mem : ∀ y (hy : y ∈ Wi.carrier),
          unionOrd.lt ⟨y, hsub hy⟩ ⟨x₀, hx₀U⟩ := by
        intro y hy
        refine lt_of_not_ge fun hle => hx₀diff ?_
        obtain ⟨W, hWY, hx₀W, hyW⟩ := common_member ⟨x₀, hx₀U⟩ ⟨y, hsub hy⟩
        rcases htotal ⟨W, hWY⟩ ⟨Wi, hWiY⟩ with h | h
        · rcases h with rfl | h; exact hx₀W; exact h.subset.1 hx₀W
        · rcases h with rfl | h; exact hx₀W
          have hyW' : y ∈ W.carrier := h.subset.1 hy
          obtain ⟨w, hWicarr, _⟩ := h
          have hyltw : W.ord.lt ⟨y, hyW'⟩ w := by
            rw [hWicarr] at hy; obtain ⟨z, hz, rfl⟩ := hy; exact hz
          rw [hWicarr]
          exact ⟨⟨x₀, hx₀W⟩,
            @lt_of_le_of_lt _ W.ord.toPreorder _ _ _
              ((unionLE_eq ⟨x₀, hx₀U⟩ ⟨y, hsub hy⟩ W hWY hx₀W hyW').mp hle) hyltw,
            rfl⟩
      ext y; simp only [Set.mem_image, Set.mem_setOf]
      constructor
      · intro hy; exact ⟨⟨y, hsub hy⟩, lt_x₀_of_mem y hy, rfl⟩
      · rintro ⟨⟨z, hzU⟩, hlt, rfl⟩; exact mem_Wi_of_lt z hzU hlt
    · -- Orderings agree on Wi.carrier
      intro a b haU hbU
      exact (unionLE_eq ⟨a.1, haU⟩ ⟨b.1, hbU⟩ Wi hWiY a.2 b.2).symm

/-- Exercise 8.5.19: Well-ordering principle implies axiom of choice.
Well-order the disjoint union `Σ i, X i`, then pick the minimum of each fiber. -/
theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type}
    (hne : ∀ i, Nonempty (X i)) : Nonempty (∀ i, X i) := by
  obtain ⟨l, hwf⟩ := hwo ((i : I) × X i)
  refine ⟨fun i => ?_⟩
  set S : Set ((i : I) × X i) := Set.range (Sigma.mk i)
  -- `.some` here uses Classical.choice to extract a witness from `Nonempty (X i)`.
  -- This is an artifact of Lean's Prop/Type distinction — in set theory "nonempty"
  -- carries a witness. The actual *selection* is done by `WellFounded.min` below.
  have hS : S.Nonempty := ⟨⟨i, (hne i).some⟩, ⟨_, rfl⟩⟩
  set m := @WellFounded.min _ l.toLT.lt hwf.wf S hS
  have hm := @WellFounded.min_mem _ l.toLT.lt hwf.wf S hS
  have h1 : m.1 = i := by
    obtain ⟨x, hx⟩ := hm
    exact (Sigma.mk.inj hx).1.symm
  exact h1 ▸ m.2

/-- Exercise 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧ (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by
  -- The poset: pairwise disjoint subcollections of Ω, ordered by ⊆
  let P := {Ω' : Set (Set X) | Ω' ⊆ Ω ∧ Ω'.Pairwise Disjoint}
  haveI : Nonempty P := ⟨⟨∅, Set.empty_subset _, Set.pairwise_empty _⟩⟩
  -- Zorn: every chain has an upper bound
  have hchain : ∀ C : Set P, Chapter8.IsTotal C ∧ C.Nonempty →
      ∃ x, IsUpperBound C x := by
    intro C ⟨htotal, hCne⟩
    -- Upper bound: union of all collections in the chain
    let ub : Set (Set X) := ⋃ S ∈ C, (S : P).1
    have hub_sub : ub ⊆ Ω := by
      intro A hA; obtain ⟨⟨S, hS⟩, hSC, hAS⟩ := Set.mem_iUnion₂.mp hA
      exact hS.1 hAS
    have hub_disj : ub.Pairwise Disjoint := by
      intro A hA B hB hAB
      obtain ⟨⟨SA, hSA⟩, hSAC, hASA⟩ := Set.mem_iUnion₂.mp hA
      obtain ⟨⟨SB, hSB⟩, hSBC, hBSB⟩ := Set.mem_iUnion₂.mp hB
      -- SA and SB are in the chain, so one contains the other
      rcases htotal ⟨⟨SA, hSA⟩, hSAC⟩ ⟨⟨SB, hSB⟩, hSBC⟩ with hle | hle
      · exact hSB.2 (hle hASA) hBSB hAB
      · exact hSA.2 hASA (hle hBSB) hAB
    use ⟨ub, hub_sub, hub_disj⟩
    rw [IsUpperBound.iff]
    intro ⟨S, hS⟩ hSC
    show S ⊆ ub
    exact fun A hAS => Set.mem_iUnion₂.mpr ⟨⟨S, hS⟩, hSC, hAS⟩
  -- Apply Zorn to get a maximal element
  obtain ⟨⟨Ω', hΩ'sub, hΩ'disj⟩, hmax⟩ := Zorns_lemma hchain
  refine ⟨Ω', hΩ'sub, hΩ'disj, ?_⟩
  -- Show every C ∈ Ω intersects some A ∈ Ω'
  intro C hCΩ
  by_contra hall
  push_neg at hall
  -- hall : ∀ A ∈ Ω', (C ∩ A) = ∅ (after rewriting)
  have hCdisj : ∀ A ∈ Ω', Disjoint C A := by
    intro A hAΩ'
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hall A hAΩ'
  -- Ω' ∪ {C} is still pairwise disjoint and ⊆ Ω
  have hins_sub : insert C Ω' ⊆ Ω := by
    intro A hA; rcases Set.mem_insert_iff.mp hA with rfl | h
    · exact hCΩ
    · exact hΩ'sub h
  have hins_disj : (insert C Ω').Pairwise Disjoint := by
    intro A hA B hB hAB
    rcases Set.mem_insert_iff.mp hA with rfl | hA' <;>
      rcases Set.mem_insert_iff.mp hB with rfl | hB'
    · exact absurd rfl hAB
    · exact hCdisj B hB'
    · exact (hCdisj A hA').symm
    · exact hΩ'disj hA' hB' hAB
  -- So insert C Ω' is a strictly larger element of P
  have hle : (⟨Ω', hΩ'sub, hΩ'disj⟩ : P) ≤ ⟨insert C Ω', hins_sub, hins_disj⟩ :=
    Set.subset_insert C Ω'
  have hle' := hmax hle
  -- hle' : insert C Ω' ⊆ Ω', so C ∈ Ω'
  have hCΩ' : C ∈ Ω' := hle' (Set.mem_insert C Ω')
  -- But C ∩ C = ∅, i.e., C = ∅, contradicting ∅ ∉ Ω
  have hCC := hall C hCΩ'
  rw [Set.inter_self] at hCC
  exact hne (hCC ▸ hCΩ)

/-- Converse of Exercise 8.5.20: the maximal disjoint subcollection property implies
Exercise 8.4.2, hence is equivalent to the axiom of choice. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U} (h : Set.PairwiseDisjoint .univ X)
    (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  -- Tao's hint: pair sets {inl α, inr x} in I ⊕ U
  let pair (α : I) (x : U) : Set (I ⊕ U) := {Sum.inl α, Sum.inr x}
  let Ω : Set (Set (I ⊕ U)) := {S | ∃ α, ∃ x ∈ X α, S = pair α x}
  have hΩne : ∅ ∉ Ω := by
    rintro ⟨α, x, _, heq⟩
    exact (Set.insert_nonempty _ _).ne_empty heq.symm
  obtain ⟨Ω', hΩ'sub, hΩ'disj, hΩ'inter⟩ := hmds (I ⊕ U) Ω hΩne
  have Ω'_form : ∀ A ∈ Ω', ∃ α, ∃ x ∈ X α, A = pair α x := fun A hA => hΩ'sub hA
  -- If two pairs in Ω intersect, they share the same α (using pairwise disjointness of X)
  have pair_inter_α : ∀ α β x y, x ∈ X α → y ∈ X β →
      (pair α x ∩ pair β y).Nonempty → α = β := by
    intro α β x y hxα hyβ ⟨z, hzl, hzr⟩
    simp only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hzl hzr
    rcases hzl with rfl | rfl <;> rcases hzr with heq | heq
    · exact Sum.inl.inj heq
    · exact absurd heq (by simp)
    · exact absurd heq (by simp)
    · have := Sum.inr.inj heq; subst this
      by_contra hne'
      exact Set.disjoint_left.mp
        (h (Set.mem_univ α) (Set.mem_univ β) hne') hxα hyβ
  -- For each α, there exists a unique y ∈ X α with pair α y ∈ Ω'
  have exists_unique : ∀ α, ∃! y, y ∈ X α ∧ pair α y ∈ Ω' := by
    intro α
    obtain ⟨⟨x₀, hx₀⟩⟩ := hne α
    obtain ⟨A, hAΩ', hinter⟩ := hΩ'inter _ (show pair α x₀ ∈ Ω from ⟨α, x₀, hx₀, rfl⟩)
    obtain ⟨β, y, hyX, hAeq⟩ := Ω'_form A hAΩ'
    have hαβ := pair_inter_α α β x₀ y hx₀ hyX (hAeq ▸ hinter)
    subst hαβ
    exact ⟨y, ⟨hyX, hAeq ▸ hAΩ'⟩, fun y' ⟨_, hy'Ω'⟩ => by
      by_contra hne'
      have : (pair α y ∩ pair α y').Nonempty :=
        ⟨Sum.inl α, Set.mem_insert _ _, Set.mem_insert _ _⟩
      have hdisj := hΩ'disj (hAeq ▸ hAΩ') hy'Ω' (fun heq => hne' (by
        have : Sum.inr y ∈ pair α y' := heq ▸ Set.mem_insert_iff.mpr (Or.inr rfl)
        simp [pair] at this; exact this.symm))
      exact Set.disjoint_left.mp hdisj (Set.mem_insert _ _) (Set.mem_insert _ _)⟩
  -- Define Y
  let Y : Set U := {u | ∃ α, u ∈ X α ∧ pair α u ∈ Ω'}
  use Y; intro α
  obtain ⟨y, ⟨hyX, hyΩ'⟩, huniq⟩ := exists_unique α
  have hYXα : Y ∩ X α = {y} := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨β, huXβ, hupairΩ'⟩, huXα⟩
      have hαβ : α = β := by
        by_contra hne'
        exact Set.disjoint_left.mp
          (h (Set.mem_univ α) (Set.mem_univ β) hne') huXα huXβ
      subst hαβ
      exact huniq u ⟨huXβ, hupairΩ'⟩
    · rintro rfl; exact ⟨⟨α, hyX, hyΩ'⟩, hyX⟩
  rw [hYXα]; exact Nat.card_unique

end Chapter8
