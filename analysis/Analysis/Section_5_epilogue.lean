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

/-- Addition of Dedekind cuts -/
def DedekindCut.add (D D' : DedekindCut) : DedekindCut where
  E := {q : ℚ | ∃ r ∈ D.E, ∃ s ∈ D'.E, q = r + s}
  nonempty := by
    obtain ⟨r, hr⟩ := D.nonempty
    obtain ⟨s, hs⟩ := D'.nonempty
    use r + s
    use r, hr, s, hs
  bounded := by
    obtain ⟨M, hM⟩ := D.bounded
    obtain ⟨N, hN⟩ := D'.bounded
    use M + N
    rw [mem_upperBounds] at ⊢ hM hN
    intro q hq
    simp at hq
    obtain ⟨r, hr1, s, hs1, hq⟩ := hq
    have hr2 := hM r hr1
    have hs2 := hN s hs1
    linarith
  lower := by
    rw [isLowerSet_iff]
    intro q p hp hq
    simp at hq ⊢
    obtain ⟨r, hr1, s, hs1, hq⟩ := hq
    use r - (q - p)
    have : (r - (q - p)) < r := by linarith
    have hr2 := D.lower this.le hr1
    use hr2
    use s, hs1
    linarith
  nomax := by
    intro q hq
    simp at hq ⊢
    obtain ⟨r, hr1, s, hs1, hq⟩ := hq
    obtain ⟨r', hr'1, hr'2⟩ := D.nomax r hr1
    obtain ⟨s', hs'1, hs'2⟩ := D'.nomax s hs1
    use r' + s'
    constructor
    . use r', hr'1, s', hs'1
    . linarith

instance : Add DedekindCut := ⟨DedekindCut.add⟩

theorem DedekindCut.add_def (x: ℚ) (D D' : DedekindCut) : x ∈ (D + D').E ↔ ∃ r ∈ D.E, ∃ s ∈ D'.E, x = r + s := by
  rfl

instance DedekindCut.instZero : Zero DedekindCut where
  zero := Real.toCut 0

instance : LE DedekindCut := ⟨fun D D' ↦ D.E ⊆ D'.E⟩
instance : LT DedekindCut := ⟨fun D D' ↦ D.E ⊂ D'.E⟩

def DedekindCut.neg (D : DedekindCut) : DedekindCut where
  E := {q : ℚ | ∃ r ∉ D.E, q = -r}
  nonempty := by
    obtain ⟨r, hr⟩ := D.bounded
    rw [mem_upperBounds] at hr
    use -r
    simp
    by_contra h
    have := D.nomax r h
    obtain ⟨r', hr'1, hr'2⟩ := this
    specialize hr r' hr'1
    linarith

  bounded := by
    obtain ⟨M, hM⟩ := D.bounded
    rw [mem_upperBounds] at hM
    have : M ∉ D.E := by
      by_contra h
      have := D.nomax M h
      obtain ⟨r', hr'1, hr'2⟩ := this
      specialize hM r' hr'1
      linarith
    use -M
    rw [mem_upperBounds]
    intro x hx
    simp at hx
    obtain ⟨r, hr1, hr2⟩ := hx
    sorry

  lower := by
    rw [isLowerSet_iff]
    intro q p hp hq
    simp at hq ⊢
    obtain ⟨r, hr1, hr2⟩ := hq
    subst q
    use -p
    simp
    contrapose! hr1
    have := D.lower
    rw [isLowerSet_iff] at this
    specialize this (-p) r (by linarith) hr1
    exact this

  nomax := by
    sorry

noncomputable instance DedekindCut.instNeg : Neg DedekindCut where
  neg := DedekindCut.neg

theorem DedekindCut.le_def (D D' : DedekindCut) : D ≤ D' ↔ D.E ⊆ D'.E := by
  rfl

open Classical in
def DedekindCut.mul (D D' : DedekindCut) : DedekindCut where
  -- need to change to include negative cuts.
  E :=
    if D ≥ 0 then
      if D' ≥ 0 then
        {q : ℚ | ∃ r ∈ D.E, ∃ s ∈ D'.E, 0 ≤ r ∧ 0 ≤ s ∧ q ≤ r * s}
      else (-mul D (-D')).E
    else if D' ≥ 0 then
        (-mul (-D) D').E
      else
        (mul (-D) (-D')).E

  nonempty := by
    sorry
  bounded := by
    sorry
  lower := by
    sorry
  nomax := by
    sorry

instance : Mul DedekindCut := ⟨DedekindCut.mul⟩


theorem DedekindCut.mul_def (x: ℚ) (D D' : DedekindCut) : x ∈ (D * D').E ↔ ∃ r ∈ D.E, ∃ s ∈ D'.E, 0 ≤ r ∧ 0 ≤ s ∧ x ≤ r * s := by
  rfl

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

/-- The isomorphism between the Chapter 5 reals and the Mathlib reals. -/
-- noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

-- In order to use this definition, we need some machinery
-----

-- We start by showing it works for ratCasts
theorem Real.equivR_ratCast {q: ℚ} : equivR q = (q: ℝ) := by
  sorry

lemma Real.equivR_nat {n: ℕ} : equivR n = (n: ℝ) := equivR_ratCast
lemma Real.equivR_int {n: ℤ} : equivR n = (n: ℝ) := equivR_ratCast

----

-- We then want to set up a way to convert from the Real `LIM` to the ℝ `Real.mk`
-- To do this we need a few things:

-- Convertion between the notions of Cauchy Sequences
theorem Sequence.IsCauchy.to_IsCauSeq {a: ℕ → ℚ} (ha: IsCauchy a) : IsCauSeq _root_.abs a := by
  sorry

-- Convertion of an `IsCauchy` to a `CauSeq`
abbrev Sequence.IsCauchy.CauSeq {a: ℕ → ℚ} : (ha: IsCauchy a) → CauSeq ℚ _root_.abs :=
  (⟨a, ·.to_IsCauSeq⟩)

-- We then set up the conversion from Sequence.Equiv to CauSeq.LimZero because
-- it is the equivalence relation
example {a b: CauSeq ℚ abs} : a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

theorem Sequence.Equiv.LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) (h:Equiv a b)
  : CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    sorry

-- We can now use it to convert between different functions in Real.mk
theorem Real.mk_eq_mk {a b: ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab: Sequence.Equiv a b)
  : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)

-- Both directions of the equivalence
theorem Sequence.Equiv_iff_LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b)
  : Equiv a b ↔ CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    refine ⟨(·.LimZero ha hb), ?_⟩
    sorry

----
-- We create some cauchy sequences with useful properties

-- We show that for any sequence, it will eventually be arbitrarily close to its LIM
open Real in
theorem Sequence.difference_approaches_zero {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) :
  ∀ε > 0, ∃N, ∀n ≥ N, |LIM a - a n| ≤ (ε: ℚ) := by
    sorry

-- There exists a Cauchy sequence entirely above the LIM
theorem Real.exists_equiv_above {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, LIM a ≤ b n := by
    sorry

-- There exists a Cauchy sequence entirely below the LIM
theorem Real.exists_equiv_below {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, b n ≤ LIM a := by
    sorry

----

-- useful theorems for the following proof
#check Real.mk_le
#check Real.mk_le_of_forall_le
#check Real.mk_const

-- Transform a `Real` to an `ℝ` by going through Cauchy Sequences
-- we can use the conversion of Real.mk_eq to use different sequences to show different parts
theorem Real.equivR_eq' {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : (LIM a).equivR = Real.mk ha.CauSeq := by
    by_cases hq: ∃(q: ℚ), q = LIM a
    · sorry
    show sSup (Rat.cast '' (LIM a).toSet_Rat) = _
    refine IsLUB.csSup_eq ⟨?_, ?_⟩ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
    · -- show that `Real.mk ha.CauSeq` is an upper bound
      intro _ hy
      obtain ⟨y, hy, h⟩ := Set.mem_image _ _ _ |>.mp hy
      rw [← h, show (y: ℝ) = Real.mk (CauSeq.const _ y) from rfl]
      sorry
    -- show that for any other upper bound, `Real.mk ha.CauSeq` is smaller
    intro M hM
    sorry

lemma Real.equivR_eq (x: Real) : ∃(a : ℕ → ℚ) (ha: Sequence.IsCauchy a),
  x = LIM a ∧ x.equivR = Real.mk ha.CauSeq := by
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    exact ⟨a, ha, rfl, equivR_eq' ha⟩

lemma Real.toCut_add (x y : Real) : x.toCut + y.toCut = (x + y).toCut := by
  dsimp [toCut]
  ext q
  simp [DedekindCut.add_def]
  constructor
  . intro h
    obtain ⟨r, hr1, s, hs1, hq⟩ := h
    have : (q:Real) = (r:Real) + (s:Real) := by norm_cast
    linarith
  . intro h
    obtain ⟨r, hr1, hr2⟩ := rat_between (x:=x - (x + y - q)) (y:=x) (by linarith)
    use r, hr2
    use q - r, by
      ring_nf at hr1
      have : (q:Real) - (r:Real) < y := by linarith
      norm_cast at this
    simp

-- copy/paste with Real replaced by ℝ, and rat_between replaced by exists_rat_btwn
lemma R.toCut_add (x y : ℝ) : x.toCut + y.toCut = (x + y).toCut := by
  dsimp [_root_.Real.toCut]
  ext q
  simp [DedekindCut.add_def]
  constructor
  . intro h
    obtain ⟨r, hr1, s, hs1, hq⟩ := h
    have : (q:ℝ) = (r:ℝ) + (s:ℝ) := by norm_cast
    linarith
  . intro h
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (x:=x - (x + y - q)) (y:=x) (by linarith)
    use r, hr2
    use q - r, by
      ring_nf at hr1
      have : (q:ℝ) - (r:ℝ) < y := by linarith
      norm_cast at this
    simp

noncomputable abbrev Real.equivCut_ordered_ring : Real ≃+*o DedekindCut where
  toEquiv := Real.equivCut
  map_add' := by
    intro x y
    simp
    rw [Real.toCut_add]
  map_mul' := sorry
  map_le_map_iff' := by
    intro x y
    simp
    rw [DedekindCut.le_def]
    constructor
    . intro h
      dsimp [toCut, toSet_Rat] at h
      by_contra h'
      simp at h'
      obtain ⟨q, hq1, hq2⟩ := rat_between (x:=y) (y:=x) h'
      simp at h
      specialize h q hq2
      linarith
    . intro h
      dsimp [toCut, toSet_Rat]
      intro q hq
      simp at hq ⊢
      exact lt_of_lt_of_le hq h

noncomputable abbrev R.equivCut_ordered_ring : ℝ ≃+*o DedekindCut where
  toEquiv := _root_.Real.equivCut
  map_add' := by
    intro x y
    simp
    rw [R.toCut_add]
  map_mul' := sorry
  map_le_map_iff' := by
    intro x y
    simp
    rw [DedekindCut.le_def]
    constructor
    . intro h
      dsimp [_root_.Real.toSet_Rat] at h
      by_contra h'
      simp at h'
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (x:=y) (y:=x) h'
      simp at h
      specialize h q hq2
      linarith
    . intro h
      dsimp [_root_.Real.toSet_Rat]
      intro q hq
      simp at hq ⊢
      exact lt_of_lt_of_le hq h

/-- The isomorphism preserves order and ring operations -/
noncomputable abbrev Real.equivR : Real ≃+*o ℝ :=
  Real.equivCut_ordered_ring.trans R.equivCut_ordered_ring.symm

-- helpers for converting properties between Real and ℝ
lemma Real.equivR_map_mul {x y : Real} : equivR (x * y) = equivR x * equivR y :=
  equivR_ordered_ring.map_mul _ _

lemma Real.equivR_map_inv {x: Real} : equivR (x⁻¹) = (equivR x)⁻¹ :=
  map_inv₀ equivR_ordered_ring _

theorem Real.equivR_map_pos {x: Real} : 0 < x ↔ 0 < equivR x := by sorry

theorem Real.equivR_map_nonneg {x: Real} : 0 ≤ x ↔ 0 ≤ equivR x := by sorry

lemma Real.equivR_iff' (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  constructor
  · intro h
    subst h
    unfold equivR
    exact _root_.Real.equivCut.right_inv (x.toCut)
  · intro h
    rw [(_root_.Real.equivCut.left_inv y).symm]
    unfold equivR
    simp
    rw [h]
    rfl

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
    rw [map_mul]
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
    rw [map_div₀]
    have : equivR 1 = 1 := by
      exact map_one equivR
    rw [this]
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

theorem Real.equivR_z : equivR 0 = 0 := by
  exact map_zero equivR

theorem Real.eq_of_equivR (x y : Real) : x = y ↔ equivR x = equivR y := by
  exact Iff.symm (EmbeddingLike.apply_eq_iff_eq equivR)

theorem Real.le_of_equivR (x y : Real) : x ≤ y ↔ equivR x ≤ equivR y := by
  exact Iff.symm (map_le_map_iff equivR)

theorem Real.lt_of_equivR (x y : Real) : x < y ↔ equivR x < equivR y := by
  exact Iff.symm (map_lt_map_iff equivR)

theorem Real.pos_of_equivR (x : Real) : 0 < x ↔ 0 < equivR x := by
  conv_rhs => rw [← Real.equivR_z]
  rw [← Real.lt_of_equivR]

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
