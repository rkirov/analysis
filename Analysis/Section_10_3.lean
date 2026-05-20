import Mathlib.Tactic
import Analysis.Section_10_2

/-!
# Analysis I, Section 10.3: Monotone functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relations between monotonicity and differentiability.

-/

namespace Chapter10

/-- Proposition 10.3.1 / Exercise 10.3.1 -/
theorem derivative_of_monotone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Monotone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≥ 0 := by
  have hL : HasDerivWithinAt f (derivWithin f X x₀) X x₀ := hderiv.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hL
  haveI : (nhdsWithin x₀ (X \ {x₀})).NeBot := hx₀.neBot
  apply ge_of_tendsto' hL
  intro x
  rw [slope_def_field]
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · have h1 : f x ≤ f x₀ := hmono hlt.le
    have h2 : x - x₀ < 0 := sub_neg.mpr hlt
    exact div_nonneg_of_nonpos (by linarith) h2.le
  · simp [heq]
  · have h1 : f x₀ ≤ f x := hmono hgt.le
    have h2 : 0 < x - x₀ := sub_pos.mpr hgt
    exact div_nonneg (by linarith) h2.le

theorem derivative_of_antitone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Antitone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≤ 0 := by
  have hneg := derivative_of_monotone X hx₀ hmono.neg hderiv.neg
  rw [derivWithin.fun_neg] at hneg
  linarith

/-- Proposition 10.3.3 / Exercise 10.3.4 -/
theorem strictMono_of_positive_derivative {a b:ℝ} {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  intro x hx y hy hxy
  have hxy_sub_Icc : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
  have hxy_sub_Ioo : Set.Ioo x y ⊆ Set.Ioo a b :=
    fun z hz ↦ ⟨lt_of_le_of_lt hx.1 hz.1, lt_of_lt_of_le hz.2 hy.2⟩
  have hcont_xy : ContinuousOn f (.Icc x y) :=
    (hderiv.continuousOn).mono hxy_sub_Icc
  have hderiv_Ioo : DifferentiableOn ℝ f (.Ioo x y) :=
    (hderiv.mono (hxy_sub_Ioo.trans Set.Ioo_subset_Icc_self))
  obtain ⟨c, hc, hderiv_c⟩ := _root_.HasDerivWithinAt.mean_value hxy hcont_xy hderiv_Ioo
  have hc_Ioo_ab : c ∈ Set.Ioo a b := hxy_sub_Ioo hc
  have hdiff_at_c : DifferentiableWithinAt ℝ f (.Icc a b) c :=
    hderiv c (Set.Ioo_subset_Icc_self hc_Ioo_ab)
  have heq : derivWithin f (.Ioo x y) c = derivWithin f (.Icc a b) c := by
    rw [derivWithin_subset (hxy_sub_Ioo.trans Set.Ioo_subset_Icc_self)
        (isOpen_Ioo.uniqueDiffWithinAt hc) hdiff_at_c]
  have hL := hderiv_c.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hc)
  rw [heq] at hL
  have hpos_c : derivWithin f (.Icc a b) c > 0 := hpos c hc_Ioo_ab
  have hslope_pos : (f y - f x) / (y - x) > 0 := by rw [← hL]; exact hpos_c
  have hyx_pos : y - x > 0 := by linarith
  have : f y - f x > 0 := by
    have := mul_pos hslope_pos hyx_pos
    rwa [div_mul_cancel₀ _ (sub_ne_zero.mpr (by linarith))] at this
  linarith

theorem strictAnti_of_negative_derivative {a b:ℝ} {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  have hderiv' : DifferentiableOn ℝ (fun x ↦ -f x) (.Icc a b) := hderiv.neg
  have hpos' : ∀ x ∈ Set.Ioo a b, derivWithin (fun y ↦ -f y) (.Icc a b) x > 0 := by
    intro x hx
    rw [derivWithin.fun_neg]
    linarith [hneg x hx]
  have hmono := strictMono_of_positive_derivative hderiv' hpos'
  have := hmono.neg
  simpa using this

/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by
  set f : ℝ → ℝ := fun x ↦ if x < 0 then x else x^3 with hf_def
  use f
  have hcont : Continuous f := by
    apply continuous_if (p := fun x => x < 0)
    · intro a ha
      have ha0 : a = 0 := by
        have : frontier {x : ℝ | x < 0} = {0} := by
          show frontier (Set.Iio (0:ℝ)) = {0}
          rw [frontier_Iio]
        rw [this] at ha
        simpa using ha
      simp [ha0]
    · exact continuousOn_id
    · exact (continuous_pow 3).continuousOn
  refine ⟨hcont, ?_, ?_⟩
  · intro x y hxy
    show (if x < 0 then x else x^3) < (if y < 0 then y else y^3)
    rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
    · have hx_neg : x < 0 := lt_trans hxy hy_neg
      simp [hx_neg, hy_neg, hxy]
    · have hx_neg : x < 0 := hy_zero ▸ hxy
      simp [hx_neg, hy_zero]
    · by_cases hx_neg : x < 0
      · simp [hx_neg, not_lt.mpr hy_pos.le]
        have : x^3 ≤ 0 := by nlinarith [sq_nonneg x]
        have : (0:ℝ) < y^3 := by positivity
        linarith
      · push_neg at hx_neg
        simp [not_lt.mpr hx_neg, not_lt.mpr hy_pos.le]
        exact Odd.strictMono_pow (by decide) hxy
  · intro hdiff
    have hderiv_at : HasDerivAt f (deriv f 0) 0 := hdiff.hasDerivAt
    have h_left : HasDerivWithinAt f 1 (Set.Iic 0) 0 := by
      have heq : Set.EqOn f id (Set.Iic 0) := by
        intro x hx
        simp [f]
        rcases lt_or_eq_of_le (Set.mem_Iic.mp hx) with hlt | heq
        · simp [hlt]
        · simp [heq]
      have hid : HasDerivWithinAt (id : ℝ → ℝ) (1:ℝ) (Set.Iic 0) 0 := hasDerivWithinAt_id _ _
      exact hid.congr heq (by simp [f])
    have h_right : HasDerivWithinAt f 0 (Set.Ici 0) 0 := by
      have heq : Set.EqOn f (fun x => x^3) (Set.Ici 0) := by
        intro x hx
        simp [f, not_lt.mpr (Set.mem_Ici.mp hx)]
      have hpow : HasDerivAt (fun x : ℝ => x^3) ((3:ℕ) * (0:ℝ)^(3-1)) 0 := by
        simpa using hasDerivAt_pow 3 (0:ℝ)
      have hpow' : HasDerivWithinAt (fun x : ℝ => x^3) 0 (Set.Ici 0) 0 := by
        have := hpow.hasDerivWithinAt (s := Set.Ici (0:ℝ))
        simpa using this
      exact hpow'.congr heq (by simp [f])
    have hderiv_left : HasDerivWithinAt f (deriv f 0) (Set.Iic 0) 0 :=
      hderiv_at.hasDerivWithinAt
    have hderiv_right : HasDerivWithinAt f (deriv f 0) (Set.Ici 0) 0 :=
      hderiv_at.hasDerivWithinAt
    have h1 : deriv f 0 = 1 := by
      have hu : UniqueDiffWithinAt ℝ (Set.Iic (0:ℝ)) 0 := uniqueDiffOn_Iic 0 _ (by simp)
      exact hu.eq_deriv _ hderiv_left h_left
    have h0 : deriv f 0 = 0 := by
      have hu : UniqueDiffWithinAt ℝ (Set.Ici (0:ℝ)) 0 := uniqueDiffOn_Ici 0 _ (by simp)
      exact hu.eq_deriv _ hderiv_right h_right
    linarith

/-- Exercise 10.3.3 -/
example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by
  use fun x ↦ x^3
  refine ⟨?_, ?_, ?_⟩
  . intro x y hxy
    simp
    exact Odd.strictMono_pow (by decide) hxy
  . exact differentiable_pow 3
  . simp

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  set X : Set ℝ := Set.Icc 0 1 ∪ Set.Icc 2 3 with hX_def
  use X
  set g : ℝ → ℝ := fun x ↦ if x ≤ 1 then x else x - 100 with hg_def
  use g
  have hg_left : ∀ x ∈ Set.Icc (0:ℝ) 1, g x = x := by
    intro x hx
    simp [g, hx.2]
  have hg_right : ∀ x ∈ Set.Icc (2:ℝ) 3, g x = x - 100 := by
    intro x hx
    have : ¬ x ≤ 1 := by linarith [hx.1]
    simp [g, this]
  have hnhds_left : ∀ x ∈ Set.Icc (0:ℝ) 1, Set.Icc (0:ℝ) 1 ∈ nhdsWithin x X := by
    intro x ⟨hx1, hx2⟩
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio (3/2), isOpen_Iio, Set.mem_Iio.mpr (by linarith), ?_⟩
    rintro y ⟨hy_lt, hy_in⟩
    rcases hy_in with hy | hy
    · exact hy
    · exfalso; have := hy.1; linarith [Set.mem_Iio.mp hy_lt]
  have hnhds_right : ∀ x ∈ Set.Icc (2:ℝ) 3, Set.Icc (2:ℝ) 3 ∈ nhdsWithin x X := by
    intro x ⟨hx1, hx2⟩
    rw [mem_nhdsWithin]
    refine ⟨Set.Ioi (3/2), isOpen_Ioi, Set.mem_Ioi.mpr (by linarith), ?_⟩
    rintro y ⟨hy_lt, hy_in⟩
    rcases hy_in with hy | hy
    · exfalso; have := hy.2; linarith [Set.mem_Ioi.mp hy_lt]
    · exact hy
  have heq_left : ∀ x ∈ Set.Icc (0:ℝ) 1, g =ᶠ[nhdsWithin x X] (id : ℝ → ℝ) := by
    intro x hx
    filter_upwards [hnhds_left x hx] with y hy using hg_left y hy
  have heq_right : ∀ x ∈ Set.Icc (2:ℝ) 3,
      g =ᶠ[nhdsWithin x X] (fun y => y - 100) := by
    intro x hx
    filter_upwards [hnhds_right x hx] with y hy using hg_right y hy
  refine ⟨?_, ?_, ?_⟩
  . intro x hx
    rcases hx with hx | hx
    · exact (differentiableWithinAt_id).congr_of_eventuallyEq (heq_left x hx)
        (hg_left x hx)
    · have hdiff : DifferentiableWithinAt ℝ (fun y : ℝ => y - 100) X x :=
        (differentiableAt_id.sub_const 100).differentiableWithinAt
      exact hdiff.congr_of_eventuallyEq (heq_right x hx) (hg_right x hx)
  . intro x hx
    rcases hx with hx | hx
    · rw [(heq_left x hx).derivWithin_eq (hg_left x hx)]
      have hu : UniqueDiffWithinAt ℝ X x := by
        apply (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1) x hx).mono_nhds
        rw [nhdsWithin_le_iff]
        exact Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => Or.inl hy)
      simp [derivWithin_id _ _ hu]
    · rw [(heq_right x hx).derivWithin_eq (hg_right x hx)]
      have hu : UniqueDiffWithinAt ℝ X x := by
        apply (uniqueDiffOn_Icc (by norm_num : (2:ℝ) < 3) x hx).mono_nhds
        rw [nhdsWithin_le_iff]
        exact Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => Or.inr hy)
      have hderivW : derivWithin (fun y : ℝ => y - 100) X x = 1 := by
        have : HasDerivWithinAt (fun y : ℝ => y - 100) 1 X x :=
          ((hasDerivAt_id x).sub_const 100).hasDerivWithinAt
        exact this.derivWithin hu
      rw [hderivW]; norm_num
  . rw [StrictMonoOn]
    push_neg
    refine ⟨0, ?_, 2, ?_, ?_, ?_⟩
    · show (0:ℝ) ∈ X; left; simp
    · show (2:ℝ) ∈ X; right; norm_num
    · norm_num
    · show g 2 ≤ g 0
      rw [hg_right 2 (by norm_num), hg_left 0 (by simp)]
      norm_num

end Chapter10
