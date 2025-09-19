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
    dsimp [toCut, Chapter5.DedekindCut.toR, Chapter5.DedekindCut.toSet_R, toSet_Rat]
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
    dsimp [toCut, Chapter5.DedekindCut.toR, Chapter5.DedekindCut.toSet_R, toSet_Rat]
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



/-- The isomorphism preserves order and ring operations -/
noncomputable abbrev Real.equivR : Real ≃ ℝ :=
  Real.equivCut.trans _root_.Real.equivCut.symm


lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

theorem Real.coe_equiv_coe (q:ℚ) : equivR (q:Real) = (q:ℝ) := by
  symm
  rw [equivR_iff]
  simp only [DedekindCut.mk.injEq]
  dsimp [toCut, toSet_Rat, _root_.Real.toCut, _root_.Real.toSet_Rat]
  ext r
  simp

theorem Real.equivR_add_q (x y : ℚ) : equivR ((x: Real) + (y: Real)) = equivR (x:Real) + equivR (y: Real) := by
  rw [show (x:Real) + (y:Real) = ((x + y: ℚ):Real) by norm_cast]
  rw [Real.coe_equiv_coe, Real.coe_equiv_coe, Real.coe_equiv_coe]
  norm_cast

theorem Real.equivR_mul_q (x y : ℚ) : equivR ((x: Real) * (y: Real)) = equivR (x:Real) * equivR (y: Real) := by
  rw [show (x:Real) * (y:Real) = ((x * y: ℚ):Real) by norm_cast]
  rw [Real.coe_equiv_coe, Real.coe_equiv_coe, Real.coe_equiv_coe]
  norm_cast

theorem Real.equivR_lt_q (x y : ℚ) : equivR (x: Real) < equivR (y: Real) ↔ (x: Real) < (y: Real) := by
  rw [coe_equiv_coe, coe_equiv_coe]
  rw [Real.ratCast_lt]
  exact gt_of_coe y x

theorem Sequence.IsCauchy_CauSeq (a: ℕ -> ℚ) (ha: Sequence.IsCauchy a) :
    IsCauSeq abs (fun (n: ℕ) ↦ (a n : ℝ)) := by
  dsimp [IsCauSeq]
  intro ε hε
  rw [IsCauchy.coe] at ha
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (x:=0) (y:=ε) hε
  norm_cast at hq1
  specialize ha q hq1
  obtain ⟨N, hN⟩ := ha
  use N
  intro j hj
  specialize hN j hj N (by rfl)
  rw [Section_4_3.dist_eq] at hN
  suffices h : |(a j : ℝ) - (a N : ℝ)| ≤ (q:ℝ) by
    linarith
  norm_cast

theorem Real.LIM_lt_LIM {a b : ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b):
    LIM a < LIM b ↔ ∃ ε:ℚ, ε > 0 ∧ ∃ N, ∀ n ≥ N, a n < b n - ε := by
  sorry

theorem R.lim_le_lim {a b : ℕ → ℝ} (ha : IsCauSeq abs a) (hb : IsCauSeq abs b):
    CauSeq.lim ⟨a, ha⟩ ≤ CauSeq.lim ⟨b, hb⟩ ↔ ∃ ε:ℚ, ε > 0 ∧ ∃ N, ∀ n ≥ N, a n < b n - ε
      ∨ ∀ ε:ℚ, ε > 0 → ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε
     := by
  sorry

theorem R.lim_lt_lim {a b : ℕ → ℝ} (ha : IsCauSeq abs a) (hb : IsCauSeq abs b):
    CauSeq.lim ⟨a, ha⟩ < CauSeq.lim ⟨b, hb⟩ ↔ ∃ ε:ℚ, ε > 0 ∧ ∃ N, ∀ n ≥ N, a n < b n - ε := by
  sorry

theorem Real.equivR_LIM (a: ℕ -> ℚ) (ha: Sequence.IsCauchy a) :
    equivR (LIM a) = CauSeq.lim ⟨fun (n: ℕ) ↦ (a n :ℝ), Sequence.IsCauchy_CauSeq a ha⟩ := by
  symm
  rw [equivR_iff]
  dsimp [toCut, toSet_Rat, _root_.Real.toCut, _root_.Real.toSet_Rat]
  simp_all
  ext q
  simp
  rw [ratCast_def]
  rw [Real.LIM_lt_LIM (Sequence.IsCauchy.const q) ha]
  have hca := Sequence.IsCauchy_CauSeq a ha
  have : CauSeq.lim (CauSeq.const _root_.abs (q:ℝ)) = (q:ℝ) := CauSeq.lim_const (q:ℝ)
  rw [← this]
  -- rw [R.lim_lt_lim] -- why doesn't apply, maybe const is problem?
  sorry

theorem Real.equivR_add (x y : Real) : equivR (x + y) = equivR x + equivR y := by
  obtain ⟨q, hq, rfl⟩ := Real.eq_lim x
  obtain ⟨r, hr, rfl⟩ := Real.eq_lim y
  rw [LIM_add hq hr]
  rw [equivR_LIM _ hq, equivR_LIM _ hr, equivR_LIM _ (Sequence.IsCauchy.add hq hr)]
  rw [CauSeq.lim_add]
  congr
  ext n
  simp only [Pi.add_apply, Rat.cast_add]

theorem Real.equivR_mul (x y : Real) : equivR (x * y) = equivR x * equivR y := by
  obtain ⟨q, hq, rfl⟩ := Real.eq_lim x
  obtain ⟨r, hr, rfl⟩ := Real.eq_lim y
  rw [LIM_mul hq hr]
  rw [equivR_LIM _ hq, equivR_LIM _ hr, equivR_LIM _ (Sequence.IsCauchy.mul hq hr)]
  rw [CauSeq.lim_mul]
  congr
  ext n
  simp only [Pi.mul_apply, Rat.cast_mul]

theorem Real.equivR_le {x y : Real} : equivR x ≤ equivR y ↔ x ≤ y := by
  obtain ⟨q, hq, rfl⟩ := Real.eq_lim x
  obtain ⟨r, hr, rfl⟩ := Real.eq_lim y
  rw [equivR_LIM _ hq, equivR_LIM _ hr]
  rw [R.lim_le_lim]
  sorry

noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := equivR_add
  map_mul' := equivR_mul
  map_le_map_iff' := equivR_le

theorem Real.equivR_z : equivR 0 = 0 := by
  exact map_zero equivR_ordered_ring

theorem Real.equivR_one : equivR 1 = 1 := by
  exact map_one equivR_ordered_ring

theorem Real.eq_of_equivR (x y : Real) : x = y ↔ equivR x = equivR y := by
  exact Iff.symm (EmbeddingLike.apply_eq_iff_eq equivR)

theorem Real.le_of_equivR (x y : Real) : x ≤ y ↔ equivR x ≤ equivR y := by
  exact Iff.symm (map_le_map_iff equivR_ordered_ring)

theorem Real.lt_of_equivR (x y : Real) : x < y ↔ equivR x < equivR y := by
  exact Iff.symm (map_lt_map_iff equivR_ordered_ring)

theorem Real.mul_of_equivR (x y : Real) : equivR x * equivR y = equivR (x * y) := by
  have := equivR_ordered_ring.map_mul' x y
  simp_all

theorem Real.pos_of_equivR (x : Real) : 0 < x ↔ 0 < equivR x := by
  conv_rhs => rw [← Real.equivR_z]
  rw [← Real.lt_of_equivR]


-- Showing equivalence of the different pows

theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  induction' n with n ih
  . symm
    rw [equivR_iff]
    simp
    ext q
    simp
    norm_cast
  . rw [pow_succ]
    rw [_root_.pow_succ]
    rw [← mul_of_equivR]
    rw [ih]

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  by_cases h : n ≥ 0
  . lift n to ℕ using h
    exact Real.pow_of_equivR x n
  . push_neg at h
    have hn_pos : 0 < -n := Int.neg_pos.mpr h
    set m := Int.natAbs n with hm_def
    have : n = - (m:ℤ) := by
      have := Int.eq_neg_natAbs_of_nonpos h.le
      linarith
    rw [this]
    simp only [zpow_neg]
    simp only [_root_.zpow_neg, inv_eq_one_div]
    simp only [one_div]
    -- odd dance, because equivR_ordered_ring and equivR
    -- are the same function, but the former has more structure
    change equivR_ordered_ring (x ^ m)⁻¹ = (equivR_ordered_ring x ^ ↑m)⁻¹
    rw [map_inv₀ equivR_ordered_ring]
    congr
    exact Real.pow_of_equivR x m

lemma root_inv {x y: ℝ} {n: ℕ} (hx: x > 0) (hy: y > 0) (hn : n ≠ 0) : x^(1/(n:ℝ)) = y ↔ x = y ^ n := by
  constructor
  . intro h
    subst y
    rw [show (x ^ (1/(n:ℝ))) ^ n = (x ^ (1/(n:ℝ))) ^ (n:ℝ) by
      symm
      exact Real.rpow_natCast _ _
    ]
    rw [← Real.rpow_mul hx.le]
    field_simp [hx]
  . intro h
    subst x
    rw [← Real.rpow_natCast _ _]
    rw [← Real.rpow_mul _]
    field_simp [hn]
    exact hy.le

theorem Real.ratPow_natCast {x:Real} {n:ℕ} (hx: x > 0) : (x^(n:ℚ)) = x^n := by
  induction' n with n ih
  . simp
    exact rfl
  . push_cast
    rw [ratPow_add]
    rw [← pow_add]
    rw [ih]
    congr!
    . simp
      exact ratPow_one hx
    . exact hx

set_option maxHeartbeats 1000000 in
theorem Real.pow_of_equivR_inv {x:Real} {n:ℕ} (hx: x > 0) (hn: n ≠ 0): equivR (x^(1/(n:ℚ))) = (equivR x)^(1/(n:ℝ)) := by
  symm
  rw [root_inv (by exact (pos_of_equivR x).mp hx) (by
    apply (pos_of_equivR _).mp
    exact Real.ratPow_nonneg hx _
  ) hn]
  rw [← Real.pow_of_equivR]
  congr
  rw [show (x ^ (1/(n:ℚ))) ^ n = (x ^ (1/(n:ℚ))) ^ (n:ℚ) by
    rw [ratPow_natCast]
    rw [ratPow_eq_root hx (by omega)]
    have : n ≥ 1 := by omega
    exact Real.root_pos' hx this
  ]
  rw [Real.ratPow_ratPow hx]
  field_simp
  exact Eq.symm (ratPow_one hx)

theorem Real.ratPow_of_equivR (x:Real) (hx: x > 0) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by
  rw [← Rat.num_div_den q]
  have hqnz: q.den ≥ 1 := by
    have := q.den_nz
    omega
  rw [ratPow_def hx _ hqnz]
  rw [Real.zpow_of_equivR]
  rw [show equivR x ^ ((((q.num:ℚ) / (q.den:ℚ)): ℚ ): ℝ) = (equivR x ^ (((1 / q.den):ℚ):ℝ)) ^ q.num by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul _ _]
    congr
    field_simp
    exact ((pos_of_equivR x).mp hx).le
  ]
  congr
  rw [← ratPow_eq_root hx hqnz]
  rw [pow_of_equivR_inv hx q.den_nz]
  congr!
  push_cast
  rfl

end Chapter5
