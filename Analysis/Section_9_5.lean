import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.5: Left and right limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits.
-/

namespace Chapter9

/-- Definition 9.5.1.  We give left and right limits the "junk" value of 0 if the limit does not exist. -/
abbrev RightLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: LeftLimitExists X f x₀ then h.choose else 0

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Ioi x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Iio x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: RightLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: LeftLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

/-- Example 9.5.2.  The second part of this example is no longer operative as we assign "junk" values to our functions instead of leaving them undefined. -/
theorem real_sign_right_limit : right_limit .univ Real.sign 0 = 1 := by
  apply (right_limit.eq ?_ ?_).2
  · intro ε hε
    refine ⟨ε / 2, ⟨trivial, show (0:ℝ) < ε / 2 by linarith⟩, ?_⟩
    rw [show (0:ℝ) - ε / 2 = -(ε / 2) from by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.sign_of_pos hx.2).symm

theorem real_sign_left_limit: left_limit .univ Real.sign 0 = -1 := by
  apply (left_limit.eq ?_ ?_).2
  · intro ε hε
    refine ⟨-ε / 2, ⟨trivial, show -ε / 2 < (0:ℝ) by linarith⟩, ?_⟩
    rw [show (0:ℝ) - -ε / 2 = ε / 2 from by ring, abs_of_pos (by linarith)]
    linarith
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.sign_of_neg hx.2).symm

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: RightLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: LeftLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Iio x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (left_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

/-- Proposition 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: x₀ ∈ X)
  (had_left: AdherentPt x₀ (X ∩ .Iio x₀)) (had_right: AdherentPt x₀ (X ∩ .Ioi x₀)) :
  ContinuousWithinAt f X x₀ ↔ (RightLimitExists X f x₀ ∧ right_limit X f x₀ = f x₀) ∧ (LeftLimitExists X f x₀ ∧ left_limit X f x₀ = f x₀) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h
    have htR : (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (f x₀)) :=
      h.mono_left (nhdsWithin_mono _ Set.inter_subset_left)
    have htL : (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (f x₀)) :=
      h.mono_left (nhdsWithin_mono _ Set.inter_subset_left)
    exact ⟨right_limit.eq had_right htR, left_limit.eq had_left htL⟩
  intro ⟨ ⟨ hre, hright⟩, ⟨ hle, lheft ⟩ ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f x₀).out 0 2
  rw [this]
  intro ε hε
  apply right_limit.eq' at hre
  apply left_limit.eq' at hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.CloseNear, Real.CloseFn] at hre hle
  choose δ_plus hδ_plus hre using hre ε hε
  choose δ_minus hδ_minus hle using hle ε hε
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  obtain hlt | rfl | hgt := lt_trichotomy x x₀
  . apply hle
    . exact hx
    . exact hlt
    . linarith [abs_lt.mp hxx₀, min_le_right δ_plus δ_minus]
    . linarith [abs_lt.mp hxx₀, min_le_right δ_plus δ_minus]
  . simp
    exact hε
  apply hre
  . exact hx
  . exact hgt
  . linarith [abs_lt.mp hxx₀, min_le_left δ_plus δ_minus]
  . linarith [abs_lt.mp hxx₀, min_le_left δ_plus δ_minus]

abbrev HasJumpDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : HasJumpDiscontinuity .univ Real.sign 0 := by
  rw [HasJumpDiscontinuity]
  constructor
  . use 1
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.sign_of_pos hx.2).symm
  . constructor
    . use (-1)
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (Real.sign_of_neg hx.2).symm
    . simp [real_sign_right_limit, real_sign_left_limit]
      linarith

abbrev HasRemovableDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀
  ∧ right_limit X f x₀ ≠ f x₀

example : HasRemovableDiscontinuity .univ f_9_3_17 0 := by
  have h0 := (Convergesto.iff _ _ _ _).mp Convergesto.f_9_3_17_remove
  have had_right : AdherentPt 0 (Set.univ ∩ Set.Ioi 0) := by
    intro ε hε
    refine ⟨ε / 2, ⟨trivial, show (0:ℝ) < ε / 2 by linarith⟩, ?_⟩
    rw [show (0:ℝ) - ε / 2 = -(ε / 2) from by ring, abs_neg, abs_of_pos (by linarith)]; linarith
  have had_left : AdherentPt 0 (Set.univ ∩ Set.Iio 0) := by
    intro ε hε
    refine ⟨-ε / 2, ⟨trivial, show -ε / 2 < (0:ℝ) by linarith⟩, ?_⟩
    rw [show (0:ℝ) - -ε / 2 = ε / 2 from by ring, abs_of_pos (by linarith)]; linarith
  have htR : (nhdsWithin 0 (Set.univ ∩ Set.Ioi 0)).Tendsto f_9_3_17 (nhds 0) :=
    h0.mono_left (nhdsWithin_mono _ (fun x ⟨_, hx⟩ => ⟨trivial, ne_of_gt hx⟩))
  have htL : (nhdsWithin 0 (Set.univ ∩ Set.Iio 0)).Tendsto f_9_3_17 (nhds 0) :=
    h0.mono_left (nhdsWithin_mono _ (fun x ⟨_, hx⟩ => ⟨trivial, ne_of_lt hx⟩))
  obtain ⟨hR, hrv⟩ := right_limit.eq had_right htR
  obtain ⟨hL, hlv⟩ := left_limit.eq had_left htL
  refine ⟨hR, hL, ?_, ?_⟩
  · rw [hrv, hlv]
  · rw [hrv]; simp [f_9_3_17]

private theorem not_right_limit_inv : ¬ RightLimitExists .univ (fun x ↦ 1/x) 0 := by
  intro ⟨L, hL⟩
  rw [←Convergesto.iff] at hL
  rw [Convergesto.iff_conv] at hL
  set a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha_mem : ∀ n, a n ∈ Set.univ ∩ Set.Ioi 0 :=
    fun n => ⟨trivial, by simp [a]; positivity⟩
  have ha_conv : Filter.Tendsto a Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq := hL a ha_mem ha_conv
  simp only [a, one_div, inv_inv] at hseq
  have hdiv : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨⌈b⌉₊, fun m hm => by
      have h1 := Nat.le_ceil b
      have h2 : (⌈b⌉₊ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
      linarith⟩)
  exact absurd hseq (not_tendsto_nhds_of_tendsto_atTop hdiv L)

example : ¬ HasRemovableDiscontinuity .univ (fun x ↦ 1/x) 0 := by
  intro ⟨hR, _⟩; exact not_right_limit_inv hR

example : ¬ HasJumpDiscontinuity .univ (fun x ↦ 1/x) 0 := by
  intro ⟨hR, _⟩; exact not_right_limit_inv hR

/- Exercise 9.5.1: Write down a definition of what it would mean for a limit of a function to be `+∞` or `-∞`, apply to `fun x ↦ 1/x`, and state and prove a version of Proposition 9.3.9. -/
abbrev ConvergesToPosInf (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin x₀ X) Filter.atTop

abbrev ConvergesToNegInf (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin x₀ X) Filter.atBot

theorem converges_to_pos_inf_def (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToPosInf X f x₀ ↔ ∀ M, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → f x > M := by
  constructor
  · intro h M
    have hev : ∀ᶠ x in nhdsWithin x₀ X, M < f x := by
      have : {x : ℝ | M < x} ∈ Filter.atTop :=
        Filter.eventually_atTop.mpr ⟨M + 1, fun b hb => by linarith⟩
      exact h this
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hev⟩ := hev
    exact ⟨δ, hδ, fun x hx hdist => hev (by rwa [Real.dist_eq]) hx⟩
  · intro h
    rw [ConvergesToPosInf]
    rw [Filter.tendsto_atTop]
    intro M
    obtain ⟨δ, hδ, hM⟩ := h M
    rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    use Metric.ball x₀ δ, Metric.ball_mem_nhds x₀ hδ
    intro x ⟨hdist, hx⟩
    exact le_of_lt (hM x hx (by rwa [Metric.mem_ball, Real.dist_eq] at hdist))

theorem converges_to_neg_inf_def (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToNegInf X f x₀ ↔ ∀ M, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → f x < M := by
  constructor
  · intro h M
    have hev : ∀ᶠ x in nhdsWithin x₀ X, f x < M := by
      have : {x : ℝ | x < M} ∈ Filter.atBot :=
        Filter.eventually_atBot.mpr ⟨M - 1, fun b hb => by linarith⟩
      exact h this
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hev⟩ := hev
    exact ⟨δ, hδ, fun x hx hdist => hev (by rwa [Real.dist_eq]) hx⟩
  · intro h
    rw [ConvergesToNegInf]
    rw [Filter.tendsto_atBot]
    intro M
    obtain ⟨δ, hδ, hM⟩ := h M
    rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    use Metric.ball x₀ δ, Metric.ball_mem_nhds x₀ hδ
    intro x ⟨hdist, hx⟩
    exact le_of_lt (hM x hx (by rwa [Metric.mem_ball, Real.dist_eq] at hdist))

example : ConvergesToPosInf (.Ioi 0) (fun x ↦ 1/x) 0 := by
  rw [converges_to_pos_inf_def]
  intro M
  use 1 / (|M| + 1), by positivity
  intro x hx hdist
  rw [Set.mem_Ioi] at hx
  have hx' : x < 1 / (|M| + 1) := by
    rw [sub_zero] at hdist; rw [abs_of_pos hx] at hdist; linarith
  have : |M| + 1 < 1 / x := by
    rwa [lt_one_div (by positivity) hx]
  linarith [le_abs_self M]

example : ConvergesToNegInf (.Iio 0) (fun x ↦ 1/x) 0 := by
  rw [converges_to_neg_inf_def]
  intro M
  use 1 / (|M| + 1), by positivity
  intro x hx hdist
  rw [Set.mem_Iio] at hx
  rw [sub_zero] at hdist; rw [abs_of_neg hx] at hdist
  -- We have -x < 1/(|M|+1) and x < 0, so 1/x < -(|M|+1) ≤ M
  have hxneg : -x < 1 / (|M| + 1) := by linarith
  have h1 : 1 / x < -(|M| + 1) := by
    rw [div_lt_iff_of_neg hx, neg_mul]
    have : (|M| + 1) * (-x) < 1 := by
      calc (|M| + 1) * (-x) < (|M| + 1) * (1 / (|M| + 1)) := by nlinarith [abs_nonneg M]
        _ = 1 := by field_simp
    linarith
  linarith [neg_abs_le M]

theorem converges_to_pos_inf_iff (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToPosInf X f x₀ ↔
  ∀ (a: ℕ → ℝ) (_: ∀ (n:ℕ), a n ∈ X) (_: Filter.atTop.Tendsto a (nhds x₀)),
    Filter.atTop.Tendsto (fun n ↦ f (a n)) Filter.atTop := by
  constructor
  · intro h a ha hconv
    rw [converges_to_pos_inf_def] at h
    rw [Filter.tendsto_atTop]
    intro M
    obtain ⟨δ, hδ, hM⟩ := h M
    rw [Metric.tendsto_nhds] at hconv
    obtain ⟨N, hN⟩ := (hconv δ hδ).exists_forall_of_atTop
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn =>
      le_of_lt (hM (a n) (ha n) (by specialize hN n hn; rwa [Real.dist_eq] at hN))⟩
  · intro h
    rw [converges_to_pos_inf_def]
    by_contra hc
    push_neg at hc
    obtain ⟨M, hc⟩ := hc
    have hc' : ∀ n : ℕ, ∃ x ∈ X, |x - x₀| < 1 / ((n : ℝ) + 1) ∧ f x ≤ M := by
      intro n; exact hc (1 / ((n : ℝ) + 1)) (by positivity)
    choose b hbX hbdist hfb using hc'
    have hbconv : Filter.Tendsto b Filter.atTop (nhds x₀) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (fun n ↦ dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
      intro n; rw [Real.dist_eq]; exact le_of_lt (hbdist n)
    have := h b hbX hbconv
    rw [Filter.tendsto_atTop] at this
    obtain ⟨N, hN⟩ := (this (M + 1)).exists_forall_of_atTop
    linarith [hfb N, hN N le_rfl]

theorem converges_to_neg_inf_iff (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToNegInf X f x₀ ↔
  ∀ (a: ℕ → ℝ) (_: ∀ (n:ℕ), a n ∈ X) (_: Filter.atTop.Tendsto a (nhds x₀)),
    Filter.atTop.Tendsto (fun n ↦ f (a n)) Filter.atBot := by
  constructor
  · intro h a ha hconv
    rw [converges_to_neg_inf_def] at h
    rw [Filter.tendsto_atBot]
    intro M
    obtain ⟨δ, hδ, hM⟩ := h M
    rw [Metric.tendsto_nhds] at hconv
    obtain ⟨N, hN⟩ := (hconv δ hδ).exists_forall_of_atTop
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn =>
      le_of_lt (hM (a n) (ha n) (by specialize hN n hn; rwa [Real.dist_eq] at hN))⟩
  · intro h
    rw [converges_to_neg_inf_def]
    by_contra hc
    push_neg at hc
    obtain ⟨M, hc⟩ := hc
    have hc' : ∀ n : ℕ, ∃ x ∈ X, |x - x₀| < 1 / ((n : ℝ) + 1) ∧ M ≤ f x := by
      intro n; exact hc (1 / ((n : ℝ) + 1)) (by positivity)
    choose b hbX hbdist hfb using hc'
    have hbconv : Filter.Tendsto b Filter.atTop (nhds x₀) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (fun n ↦ dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
      intro n; rw [Real.dist_eq]; exact le_of_lt (hbdist n)
    have := h b hbX hbconv
    rw [Filter.tendsto_atBot] at this
    obtain ⟨N, hN⟩ := (this (M - 1)).exists_forall_of_atTop
    linarith [hfb N, hN N le_rfl]

end Chapter9
