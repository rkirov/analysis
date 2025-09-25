import Mathlib.Tactic
import Analysis.Section_5_6
import Mathlib.Data.Set.Basic
open scoped Pointwise -- to use `s + t` for sets


/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers `Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers `ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers `ℚ`.

From this point onwards, `Chapter5.Real` will be deprecated, and we will use the standard real
numbers `ℝ` instead.  In particular, one should use the full Mathlib API for `ℝ` for all
subsequent chapters, in lieu of the `Chapter5.Real` API.

Filling the sorries here requires both the Chapter5.Real API and the Mathlib API for the standard
natural numbers `ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

@[ext]
structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, hq1, hq2⟩ := rat_between (x:=x - 1) (y:=x) (by linarith)
  use q
  rw [Set.mem_setOf_eq]
  exact hq2

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq1, hq2⟩ := rat_between (x:=x) (y:=x + 1) (by linarith)
  use q
  rw [mem_upperBounds]
  intro y hy
  rw [Set.mem_setOf_eq] at hy
  have : (y:Real) < (q:Real) := by linarith
  norm_cast at this
  exact this.le

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by
  rw [isLowerSet_iff]
  intro q r hr hq
  rw [Set.mem_setOf_eq] at hq ⊢
  have : (r:Real) < (q:Real) := by norm_cast
  linarith

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  rw [Set.mem_setOf_eq] at hq
  obtain ⟨q', hq1, hq2⟩ := rat_between (x:=(q:Real)) (y:=x) hq
  use q'
  constructor
  . rw [Set.mem_setOf_eq]
    exact hq2
  . norm_cast at hq1

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by
  obtain ⟨q, hq⟩ := c.nonempty
  use (q:Real)
  rw [Set.mem_image]
  simp only [Rat.cast_inj, exists_eq_right]
  exact hq

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by
  obtain ⟨q, hq⟩ := c.bounded
  use (q:Real)
  rw [mem_upperBounds] at hq ⊢
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨r, hr1, hr2⟩ := hy
  specialize hq r hr1
  subst y
  norm_cast

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv x := by
    unfold toCut DedekindCut.toReal
    dsimp [DedekindCut.toSet_Real]
    dsimp [toSet_Rat]
    apply IsLUB.csSup_eq
    . rw [isLUB_def]
      constructor
      . rw [upperBounds, Set.mem_setOf_eq]
        intro q hq
        rw [Set.mem_image] at hq
        obtain ⟨r, hr1, hr2⟩ := hq
        simp at hr1
        subst q
        exact hr1.le
      . intro y hy
        by_contra h
        simp at h
        rw [upperBound_def] at hy
        have ⟨q, hq1, hq2⟩ := rat_between (x:=y) (y:=x) h
        specialize hy q
        simp at hy
        specialize hy hq2
        linarith
    . simp
      exact toSet_Rat_nonempty x

  right_inv c := by
    unfold toCut DedekindCut.toReal
    dsimp [DedekindCut.toSet_Real]
    dsimp [toSet_Rat]
    ext q
    simp
    set S := (fun (q:ℚ) ↦ (q:Real)) '' c.E
    have S_def (q:ℚ): q ∈ c.E ↔ (q:Real) ∈ S := by
      unfold S
      simp
    have S_def' (r:Real): r ∈ S ↔ ∃ q ∈ c.E, (q:Real) = r := by
      unfold S
      simp
    rw [S_def]
    have S_bdd : BddAbove S := by exact DedekindCut.toSet_Real_bounded c
    have S_nonempty : Set.Nonempty S := by exact DedekindCut.toSet_Real_nonempty c
    have hlub := ExtendedReal.sSup_of_bounded S_nonempty S_bdd
    rw [isLUB_def] at hlub
    obtain ⟨h1, h2⟩ := hlub
    rw [upperBound_def] at h1
    constructor
    . intro h
      have : ¬ (q:Real) ∈ upperBounds S := by
        intro h'
        specialize h2 (q:Real) h'
        linarith
      rw [upperBound_def] at this
      push_neg at this
      obtain ⟨s, hs1, hs2⟩ := this
      rw [S_def'] at hs1
      obtain ⟨q', hq1, rfl⟩ := hs1
      norm_cast at hs2
      have := c.lower hs2.le hq1
      rwa [S_def] at this
    . intro h
      obtain ⟨q', hq1, hq2⟩ := c.nomax q (by unfold S at h; simp at h; exact h)
      rw [S_def] at hq1
      specialize h1 q' hq1
      have : (q:Real) < (q':Real) := by norm_cast
      linarith
end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

-- same theorems as above, but use `exists_rat_btwn`
lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by
  have : x - 1 < x := by linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn this
  use q
  rw [Set.mem_setOf_eq]
  exact hq2

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (x:=x) (y:=x + 1) (by linarith)
  use q
  rw [mem_upperBounds]
  intro y hy
  rw [Set.mem_setOf_eq] at hy
  have : (y:Real) < (q:Real) := by linarith
  norm_cast at this
  exact this.le


lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by
  rw [Chapter5.isLowerSet_iff]
  intro q r hr hq
  rw [Set.mem_setOf_eq] at hq ⊢
  have : (r:Real) < (q:Real) := by norm_cast
  linarith

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hq
  rw [Set.mem_setOf_eq] at hq
  obtain ⟨q', hq1, hq2⟩ := exists_rat_btwn (x:=(q:Real)) (y:=x) hq
  use q'
  constructor
  . rw [Set.mem_setOf_eq]
    exact hq2
  . norm_cast at hq1

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by
  obtain ⟨q, hq⟩ := c.nonempty
  use (q:ℝ)
  rw [Set.mem_image]
  simp only [Rat.cast_inj, exists_eq_right]
  exact hq

lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by
  obtain ⟨q, hq⟩ := c.bounded
  use (q:ℝ)
  rw [mem_upperBounds] at hq ⊢
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨r, hr1, hr2⟩ := hy
  specialize hq r hr1
  subst y
  norm_cast

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5

noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv x := by
    unfold toCut Chapter5.DedekindCut.toR
    dsimp [Chapter5.DedekindCut.toSet_R]
    dsimp [toSet_Rat]
    apply IsLUB.csSup_eq
    . rw [isLUB_iff_le_iff]
      intro b
      constructor
      . rw [upperBounds, Set.mem_setOf_eq]
        intro q r
        simp
        intro y hy hyq
        subst r
        linarith
      . intro h
        rw [upperBounds] at h
        simp at h
        by_contra h'
        simp at h'
        have ⟨q, hq1, hq2⟩ := exists_rat_btwn (x:=b) (y:=x) h'
        specialize h q hq2
        linarith
    . simp
      exact toSet_Rat_nonempty x
  right_inv c := by
    unfold toCut Chapter5.DedekindCut.toR
    dsimp [Chapter5.DedekindCut.toSet_R]
    dsimp [toSet_Rat]
    ext q
    simp
    set S := (fun (q:ℚ) ↦ (q:Real)) '' c.E
    have S_def (q:ℚ): q ∈ c.E ↔ (q:Real) ∈ S := by
      unfold S
      simp
    have S_def' (r:Real): r ∈ S ↔ ∃ q ∈ c.E, (q:Real) = r := by
      unfold S
      simp
    rw [S_def]
    have S_bdd : BddAbove S := by exact Chapter5.DedekindCut.toSet_R_bounded c
    have S_nonempty : Set.Nonempty S := by exact Chapter5.DedekindCut.toSet_R_nonempty c
    have hlub := isLUB_csSup S_nonempty S_bdd
    rw [isLUB_iff_le_iff] at hlub

    constructor
    . intro h
      have : ¬ (q:ℝ) ∈ upperBounds S := by
        intro h'
        specialize hlub q
        simp [h'] at hlub
        linarith
      rw [upperBounds] at this
      simp at this
      obtain ⟨s, hs1, hs2⟩ := this
      rw [S_def'] at hs1
      obtain ⟨q', hq1, rfl⟩ := hs1
      norm_cast at hs2
      have := c.lower hs2.le hq1
      rwa [S_def] at this
    . intro h
      specialize hlub (q:ℝ)
      rw [upperBounds] at hlub
      simp at hlub
      obtain ⟨q', hq1, hq2⟩ := c.nomax q (by unfold S at h; simp at h; exact h)
      rw [S_def] at hq1
      by_contra h'
      simp at h'
      rw [hlub] at h'
      specialize h' hq1
      have : (q:Real) < (q':Real) := by norm_cast
      linarith

namespace Chapter5

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

/-- The isomorphism preserves order and ring operations -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := by
    intro x y
    symm
    rw [Equiv.toFun_as_coe]
    rw [Real.equivR_iff]
    ext q
    simp
    sorry

  map_mul' := by sorry
  map_le_map_iff' := by sorry

theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.ratPow_of_equivR (x:Real) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by
  sorry


end Chapter5
