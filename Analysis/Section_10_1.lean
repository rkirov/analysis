import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
/-!
# Analysis I, Section 10.1: Basic definitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`HasDerivWithinAt`, {name}`derivWithin`, and {name}`DifferentiableWithinAt`.

Note that the Mathlib conventions differ slightly from that in the text, in that
differentiability is defined even at points that are not limit points of the domain;
derivatives in such cases may not be unique, but {name}`derivWithin` still selects one such
derivative in such cases (or {lean}`0`, if no derivative exists).

-/

namespace Chapter10

variable (x₀ : ℝ)

/-- Definition 10.1.1 (Differentiability at a point).  For the Mathlib notion {name}`HasDerivWithinAt`, the
hypothesis that {name}`x₀` is a limit point is not needed. -/
theorem _root_.HasDerivWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ)
  (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔ (nhdsWithin x₀ (X \ {x₀})).Tendsto (fun x ↦ (f x - f x₀) / (x - x₀))
   (nhds L) :=  by
  rw [hasDerivWithinAt_iff_tendsto_slope, iff_iff_eq, slope_fun_def_field]

theorem _root_.DifferentiableWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ) :
  DifferentiableWithinAt ℝ f X x₀ ↔ ∃ L, HasDerivWithinAt f L X x₀ := by
  constructor
  . intro h; use derivWithin f X x₀; exact h.hasDerivWithinAt
  intro ⟨ L, h ⟩; exact h.differentiableWithinAt

theorem _root_.DifferentiableWithinAt.of_hasDeriv {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ} {L:ℝ}
  (hL: HasDerivWithinAt f L X x₀) : DifferentiableWithinAt ℝ f X x₀ := by
  rw [DifferentiableWithinAt.iff]; use L


theorem derivative_unique {X: Set ℝ} {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀}))) {f: ℝ → ℝ} {L L':ℝ}
  (hL: HasDerivWithinAt f L X x₀) (hL': HasDerivWithinAt f L' X x₀) :
  L = L' := by
    rw [_root_.HasDerivWithinAt.iff] at hL hL'
    rw [ClusterPt.eq_1] at hx₀
    solve_by_elim [tendsto_nhds_unique]

#check DifferentiableWithinAt.hasDerivWithinAt

theorem derivative_unique' (X: Set ℝ) {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀}))) {f: ℝ → ℝ} {L :ℝ}
  (hL: HasDerivWithinAt f L X x₀)
  (hdiff : DifferentiableWithinAt ℝ f X x₀):
  L = derivWithin f X x₀ := by
  solve_by_elim [derivative_unique, DifferentiableWithinAt.hasDerivWithinAt]


/-- Example 10.1.3 -/
theorem xsq_has_deriv (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^2) (2 * x₀) .univ x₀ := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  use ε, hε
  intro x hx hxd
  obtain ⟨_, hxne⟩ := hx
  have hxne' : x - x₀ ≠ 0 := sub_ne_zero.mpr hxne
  have heq : (x^2 - x₀^2) / (x - x₀) = x + x₀ := by field_simp; ring
  rw [heq, Real.dist_eq] at *
  have : x + x₀ - 2 * x₀ = x - x₀ := by ring
  rw [this]; exact hxd

example (x₀:ℝ) : DifferentiableWithinAt ℝ (fun x ↦ x^2) .univ x₀ := by
  rw [_root_.DifferentiableWithinAt.iff]
  use 2 * x₀
  exact xsq_has_deriv x₀

example (x₀:ℝ) : derivWithin (fun x ↦ x^2) .univ x₀ = 2 * x₀ := by
  exact (xsq_has_deriv x₀).derivWithin uniqueDiffWithinAt_univ

/-- Remark 10.1.4 -/
example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (hfg: f = g):
  DifferentiableWithinAt ℝ f X x₀ ↔ DifferentiableWithinAt ℝ g X x₀ := by rw [hfg]


example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (L:ℝ) (hfg: f = g):
  HasDerivWithinAt f L X x₀ ↔ HasDerivWithinAt g L X x₀ := by rw [hfg]

example : ∃ (X: Set ℝ) (x₀ :ℝ) (f g: ℝ → ℝ) (L:ℝ) (_: f x₀ = g x₀),
  HasDerivWithinAt f L X x₀ ∧ ¬ HasDerivWithinAt g L X x₀ := by
  use .univ, 0, fun _ ↦ 0, fun x ↦ x, 0, by simp
  constructor
  . exact hasDerivWithinAt_const 0 Set.univ 0
  . have : HasDerivWithinAt id 1 .univ (0:ℝ) := hasDerivWithinAt_id 0 .univ
    intro h
    have h' := derivative_unique (by
      have : Set.univ \ ({0}:Set ℝ) = {0}ᶜ := by ext; simp
      rw [this]; exact mem_closure_iff_clusterPt.mp (by simp)) h this
    linarith

/-- Example 10.1.6 -/

abbrev f_10_1_6 : ℝ → ℝ := abs

theorem abs_right_lim : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  use ε, hε
  intro x hx hxd
  simp at hx
  rw [f_10_1_6]
  simp
  rw [abs_of_pos hx]
  rw [Real.dist_eq]
  grind

theorem abs_left_lim : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds (-1)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  use ε, hε
  intro x hx hxd
  simp at hx
  rw [f_10_1_6]
  simp
  rw [abs_of_neg hx]
  rw [Real.dist_eq]
  grind

theorem abs_has_no_deriv : ¬ ∃ L, (nhdsWithin 0 (.univ \ {0})).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
   (nhds L) := by
  simp [Metric.tendsto_nhdsWithin_nhds]
  push Not
  intro L
  by_cases hL : L = 1
  . rw [f_10_1_6]
    use 1/2, by linarith
    intro x hx
    use -x / 2
    constructor
    . linarith
    . constructor
      . grind
      . rw [Real.dist_eq]
        rw [hL]
        have : |-x / 2| = x / 2 := by grind
        rw [this]
        grind
  . use |L - 1|, by grind
    intro x hx
    use x / 2
    constructor
    . linarith
    . constructor
      . grind
      . rw [f_10_1_6]
        rw [Real.dist_eq]
        have : 0 < x / 2 := by linarith
        rw [abs_of_pos this]
        grind

example : ¬ DifferentiableWithinAt ℝ f_10_1_6 (.univ) 0 := by
  rw [DifferentiableWithinAt.iff]
  intro ⟨L, hL⟩
  rw [HasDerivWithinAt.iff] at hL
  exact abs_has_no_deriv ⟨L, hL⟩

theorem abs_has_right_deriv : HasDerivWithinAt f_10_1_6 1 (.Ioi 0) 0 := by
  rw [HasDerivWithinAt.iff]
  have h : (Set.Ioi (0:ℝ)) \ {0} = Set.Ioi 0 := by ext; simp
  rw [h]; exact abs_right_lim

theorem abs_has_left_deriv : HasDerivWithinAt f_10_1_6 (-1) (.Iio 0) 0 := by
  rw [HasDerivWithinAt.iff]
  have h : (Set.Iio (0:ℝ)) \ {0} = Set.Iio 0 := by ext; simp
  rw [h]; exact abs_left_lim

example : DifferentiableWithinAt ℝ f_10_1_6 (.Ioi 0) 0 :=
  abs_has_right_deriv.differentiableWithinAt

example : derivWithin f_10_1_6 (.Ioi 0) 0 = 1 :=
  abs_has_right_deriv.derivWithin (uniqueDiffWithinAt_Ioi 0)

example : DifferentiableWithinAt ℝ f_10_1_6 (.Iio 0) 0 :=
  abs_has_left_deriv.differentiableWithinAt

example : derivWithin f_10_1_6 (.Iio 0) 0 = -1 :=
  abs_has_left_deriv.derivWithin (uniqueDiffWithinAt_Iio 0)

/-- Proposition 10.1.7 (Newton's approximation) / Exercise 10.1.2 -/
theorem _root_.HasDerivWithinAt.iff_approx_linear (X: Set ℝ) (x₀ :ℝ) (f: ℝ → ℝ) (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → |f x - f x₀ - L * (x - x₀)| ≤ ε * |x - x₀| := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hball⟩ := h ε hε
    use δ, hδ
    intro x hxX hxd
    by_cases hxe : x = x₀
    · subst hxe; simp
    · have hbe := hball ⟨hxX, hxe⟩ (by rw [Real.dist_eq]; exact hxd)
      rw [Real.dist_eq] at hbe
      have hne : x - x₀ ≠ 0 := sub_ne_zero.mpr hxe
      have key : (f x - f x₀) / (x - x₀) - L = (f x - f x₀ - L * (x - x₀)) / (x - x₀) := by
        field_simp
      rw [key, abs_div] at hbe
      have habs : |x - x₀| > 0 := abs_pos.mpr hne
      rw [div_lt_iff₀ habs] at hbe
      linarith
  · intro h ε hε
    obtain ⟨δ, hδ, hball⟩ := h (ε/2) (by linarith)
    use δ, hδ
    intro x ⟨hxX, hxe⟩ hxd
    have hne : x - x₀ ≠ 0 := sub_ne_zero.mpr hxe
    have habs : |x - x₀| > 0 := abs_pos.mpr hne
    rw [Real.dist_eq] at hxd
    have hbe := hball x hxX hxd
    have key : (f x - f x₀) / (x - x₀) - L = (f x - f x₀ - L * (x - x₀)) / (x - x₀) := by
      field_simp
    rw [Real.dist_eq, key, abs_div, div_lt_iff₀ habs]
    nlinarith [hbe, habs]

/-- Proposition 10.1.10 / Exercise 10.1.3 -/
theorem _root_.ContinuousWithinAt.of_differentiableWithinAt {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ}
  (h: DifferentiableWithinAt ℝ f X x₀) :
  ContinuousWithinAt f X x₀ := by
  rw [DifferentiableWithinAt.iff] at h
  obtain ⟨L, hL⟩ := h
  rw [_root_.HasDerivWithinAt.iff_approx_linear] at hL
  rw [ContinuousWithinAt]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  specialize hL 1 (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := hL
  simp at hball
  use min (ε / (2 * (1 + |L|))) δ, (by positivity)
  intro x hxX hxd
  rw [Real.dist_eq] at hxd
  specialize hball x hxX (by grind)
  rw [Real.dist_eq]
  have key : |f x - f x₀| ≤ |f x - f x₀ - L * (x - x₀)| + |L * (x - x₀)| := by grind
  calc _ ≤ |f x - f x₀ - L * (x - x₀)| + |L * (x - x₀)| := key
    _ ≤ |x - x₀| + |L * (x - x₀)| := by gcongr
    _ ≤ (1 + |L|) * |x - x₀| := by rw [abs_mul]; ring_nf; rfl
    _ ≤ (1 + |L|) * (ε / (2 * (1 + |L|))) := by
      gcongr
      apply le_of_lt
      rw [lt_inf_iff] at hxd
      exact hxd.1
    _ ≤ ε / 2 := by field_simp; rfl
    _ < ε := by linarith

/-Definition 10.1.11 (Differentiability on a domain)-/
#check DifferentiableOn.eq_1

/-- Corollary 10.1.12 -/
theorem _root_.ContinuousOn.of_differentiableOn {X: Set ℝ} {f: ℝ → ℝ}
  (h: DifferentiableOn ℝ f X) :
  ContinuousOn f X := by
  solve_by_elim [ContinuousWithinAt.of_differentiableWithinAt]

/-- Theorem 10.1.13 (a) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_const (X: Set ℝ) (x₀ : ℝ) (c:ℝ) :
  HasDerivWithinAt (fun _ ↦ c) 0 X x₀ := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds]
  simp
  intro ε hε
  use ε, hε
  intro _ _ _ _
  exact hε

/-- Theorem 10.1.13 (b) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_id (X: Set ℝ) (x₀ : ℝ) :
  HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  use ε, hε
  intro x hx hxd
  rw [Real.dist_eq] at hxd ⊢
  have : x ≠ x₀ := by rw [Set.mem_diff] at hx; exact hx.2
  have key : (x - x₀) ≠ 0 := by contrapose! this; linarith
  field_simp [this]
  simp
  exact hε

/-- Theorem 10.1.13 (c) (Sum rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_add {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f + g) (f'x₀ + g'x₀) X x₀ := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds] at hf hg ⊢
  intro ε hε
  specialize hf (ε/2) (by linarith)
  specialize hg (ε/2) (by linarith)
  obtain ⟨δf, hδf, hballf⟩ := hf
  obtain ⟨δg, hδg, hballg⟩ := hg
  use min δf δg, (by positivity)
  intro x hx hxd
  specialize hballf hx (by simp only [lt_inf_iff] at hxd; exact hxd.1)
  specialize hballg hx (by simp only [lt_inf_iff] at hxd; exact hxd.2)
  have hsum : ((f + g) x - (f + g) x₀) / (x - x₀) = (f x - f x₀)/(x - x₀) + (g x - g x₀)/(x - x₀) := by
    simp [Pi.add_apply]; ring
  rw [hsum, Real.dist_eq] at *
  have : (f x - f x₀)/(x - x₀) + (g x - g x₀)/(x - x₀) - (f'x₀ + g'x₀) =
    ((f x - f x₀)/(x - x₀) - f'x₀) + ((g x - g x₀)/(x - x₀) - g'x₀) := by ring
  rw [this]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)


/-- Theorem 10.1.13 (d) (Product rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_mul {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f * g) (f'x₀ * (g x₀) + (f x₀) * g'x₀) X x₀ := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds] at hf hg ⊢
  intro ε hε
  -- εf bounds |Df - f'x₀| where Df = (f x - f x₀)/(x - x₀); similarly εg.
  set εf : ℝ := min 1 (ε / (3 * (1 + |g x₀|)))
  set εg : ℝ := min 1 (ε / (3 * (1 + |f x₀|)))
  have hεf : εf > 0 := by positivity
  have hεg : εg > 0 := by positivity
  specialize hf εf hεf
  specialize hg εg hεg
  obtain ⟨δf, hδf, hballf⟩ := hf
  obtain ⟨δg, hδg, hballg⟩ := hg
  -- δC bounds the cross term (g x - g x₀) · Df by making |x - x₀| small.
  set δC : ℝ := ε / (3 * (1 + |g'x₀|) * (1 + |f'x₀|))
  have hδC : δC > 0 := by positivity
  use min (min δf δg) (min 1 δC), (by positivity)
  intro x hx hxd
  have hxdf : dist x x₀ < δf := lt_of_lt_of_le hxd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hxdg : dist x x₀ < δg := lt_of_lt_of_le hxd (le_trans (min_le_left _ _) (min_le_right _ _))
  have hxd1 : dist x x₀ < 1 := lt_of_lt_of_le hxd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hxdC : dist x x₀ < δC := lt_of_lt_of_le hxd (le_trans (min_le_right _ _) (min_le_right _ _))
  specialize hballf hx hxdf
  specialize hballg hx hxdg
  have hxne : x ≠ x₀ := (Set.mem_diff _ |>.mp hx).2
  have hxne' : x - x₀ ≠ 0 := sub_ne_zero.mpr hxne
  -- Notation for the two error terms and the difference quotients.
  set A : ℝ := (f x - f x₀) / (x - x₀) - f'x₀
  set B : ℝ := (g x - g x₀) / (x - x₀) - g'x₀
  rw [Real.dist_eq] at hballf hballg hxd1 hxdC ⊢
  change |A| < εf at hballf
  change |B| < εg at hballg
  -- Key algebraic identity: split (fg)' - target into three controllable terms.
  have hkey : ((f * g) x - (f * g) x₀) / (x - x₀) - (f'x₀ * g x₀ + f x₀ * g'x₀)
      = g x₀ * A + f x₀ * B + (g x - g x₀) * ((f x - f x₀) / (x - x₀)) := by
    have hgx : g x - g x₀ = (x - x₀) * (B + g'x₀) := by
      simp only [B]; field_simp; ring
    simp only [Pi.mul_apply]
    field_simp
    simp only [A, B]
    field_simp
    ring
  rw [hkey]
  -- Bound each piece.
  have hεf_le : εf ≤ ε / (3 * (1 + |g x₀|)) := min_le_right _ _
  have hεg_le : εg ≤ ε / (3 * (1 + |f x₀|)) := min_le_right _ _
  have hεf1 : εf ≤ 1 := min_le_left _ _
  have hεg1 : εg ≤ 1 := min_le_left _ _
  -- Term 1: |g x₀ · A| < ε/3
  have hT1 : |g x₀ * A| < ε / 3 := by
    rw [abs_mul]
    have hbound : (1 + |g x₀|) * εf ≤ ε / 3 := by
      calc (1 + |g x₀|) * εf
          ≤ (1 + |g x₀|) * (ε / (3 * (1 + |g x₀|))) := by gcongr
        _ = ε / 3 := by
            have : (1 + |g x₀|) ≠ 0 := by positivity
            field_simp
    have hstrict : |g x₀| * |A| < (1 + |g x₀|) * εf := by
      apply mul_lt_mul' (by linarith [abs_nonneg (g x₀)]) hballf
        (abs_nonneg A) (by linarith [abs_nonneg (g x₀)])
    linarith
  -- Term 2: |f x₀ · B| < ε/3
  have hT2 : |f x₀ * B| < ε / 3 := by
    rw [abs_mul]
    have hbound : (1 + |f x₀|) * εg ≤ ε / 3 := by
      calc (1 + |f x₀|) * εg
          ≤ (1 + |f x₀|) * (ε / (3 * (1 + |f x₀|))) := by gcongr
        _ = ε / 3 := by
            have : (1 + |f x₀|) ≠ 0 := by positivity
            field_simp
    have hstrict : |f x₀| * |B| < (1 + |f x₀|) * εg := by
      apply mul_lt_mul' (by linarith [abs_nonneg (f x₀)]) hballg
        (abs_nonneg B) (by linarith [abs_nonneg (f x₀)])
    linarith
  -- Cross term: |(g x - g x₀) · ((f x - f x₀)/(x - x₀))| < ε/3
  have hgdiff : |g x - g x₀| ≤ |x - x₀| * (1 + |g'x₀|) := by
    have heq : g x - g x₀ = (x - x₀) * (B + g'x₀) := by
      simp only [B]; field_simp; ring
    rw [heq, abs_mul]
    have hBb : |B + g'x₀| ≤ 1 + |g'x₀| := by
      calc |B + g'x₀|
          ≤ |B| + |g'x₀| := abs_add_le _ _
        _ ≤ εg + |g'x₀| := by linarith
        _ ≤ 1 + |g'x₀| := by linarith
    exact mul_le_mul_of_nonneg_left hBb (abs_nonneg _)
  have hfdiff : |(f x - f x₀) / (x - x₀)| ≤ 1 + |f'x₀| := by
    have : (f x - f x₀) / (x - x₀) = A + f'x₀ := by simp only [A]; ring
    rw [this]
    calc |A + f'x₀|
        ≤ |A| + |f'x₀| := abs_add_le _ _
      _ ≤ εf + |f'x₀| := by linarith
      _ ≤ 1 + |f'x₀| := by linarith
  have hT3 : |(g x - g x₀) * ((f x - f x₀) / (x - x₀))| < ε / 3 := by
    rw [abs_mul]
    calc |g x - g x₀| * |(f x - f x₀) / (x - x₀)|
        ≤ (|x - x₀| * (1 + |g'x₀|)) * (1 + |f'x₀|) := by
          apply mul_le_mul hgdiff hfdiff (abs_nonneg _)
          exact mul_nonneg (abs_nonneg _) (by linarith [abs_nonneg (g'x₀)])
      _ = |x - x₀| * ((1 + |g'x₀|) * (1 + |f'x₀|)) := by ring
      _ < δC * ((1 + |g'x₀|) * (1 + |f'x₀|)) := by
          gcongr
      _ = ε / 3 := by
          simp only [δC]
          have h1 : (1 + |g'x₀|) ≠ 0 := by positivity
          have h2 : (1 + |f'x₀|) ≠ 0 := by positivity
          field_simp
  calc |g x₀ * A + f x₀ * B + (g x - g x₀) * ((f x - f x₀) / (x - x₀))|
      ≤ |g x₀ * A + f x₀ * B| + |(g x - g x₀) * ((f x - f x₀) / (x - x₀))| := abs_add_le _ _
    _ ≤ |g x₀ * A| + |f x₀ * B| + |(g x - g x₀) * ((f x - f x₀) / (x - x₀))| := by
        linarith [abs_add_le (g x₀ * A) (f x₀ * B)]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- Theorem 10.1.13 (e) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_smul {X: Set ℝ} {x₀ f'x₀: ℝ} (c:ℝ)
  {f: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) :
  HasDerivWithinAt (c • f) (c * f'x₀) X x₀ := by
  rw [_root_.HasDerivWithinAt.iff, Metric.tendsto_nhdsWithin_nhds] at hf ⊢
  intro ε hε
  specialize hf (ε / (|c| + 1)) (by positivity)
  obtain ⟨δ, hδ, hball⟩ := hf
  use δ, hδ
  intro x hx hxd
  specialize hball hx hxd
  simp
  rw [Real.dist_eq] at hball ⊢
  have key : |(c * f x - c * f x₀) / (x - x₀) - c * f'x₀| = |c| * |(f x - f x₀) / (x - x₀) - f'x₀| := by
    rw [← abs_mul]
    ring_nf
  rw [key]
  calc _ ≤ |c| * (ε / (|c| + 1)) := by gcongr
      _ < ε := by field_simp; linarith

/-- Theorem 10.1.13 (f) (Difference rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_sub {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f - g) (f'x₀ - g'x₀) X x₀ := by
  rw [show (f - g) = (f + (-1:ℝ) • g) by funext; simp; ring_nf]
  apply HasDerivWithinAt.of_add hf
  rw [show -g'x₀ = (-1:ℝ) * g'x₀ by ring]
  exact HasDerivWithinAt.of_smul (-1) hg

/-- Theorem 10.1.13 (g) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_inv {X: Set ℝ} {x₀ g'x₀: ℝ}
  {g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (1/g) (-g'x₀ / (g x₀)^2) X x₀ := by
  sorry

/-- Theorem 10.1.13 (h) (Quotient rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_div {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hf: HasDerivWithinAt f f'x₀ X x₀)
  (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f / g) ((f'x₀ * (g x₀) - (f x₀) * g'x₀) / (g x₀)^2) X x₀ := by
  sorry

example (x₀:ℝ) (hx₀: x₀ ≠ 1): HasDerivWithinAt (fun x ↦ (x-2)/(x-1)) (1 /(x₀-1)^2) (.univ \ {1}) x₀ := by
  sorry

/-- Theorem 10.1.15 (Chain rule) / Exercise 10.1.7 -/
theorem _root_.HasDerivWithinAt.of_comp {X Y: Set ℝ} {x₀ y₀ f'x₀ g'y₀: ℝ}
  {f g: ℝ → ℝ} (hfx₀: f x₀ = y₀) (hfX : ∀ x ∈ X, f x ∈ Y)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  HasDerivWithinAt (g ∘ f) (g'y₀ * f'x₀) X x₀ := by
  sorry

/-- Exercise 10.1.5 -/
theorem _root_.HasDerivWithinAt.of_pow (n:ℕ) (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^n)
(n * x₀^((n:ℤ)-1)) .univ x₀ := by
  sorry

/-- Exercise 10.1.6 -/
theorem _root_.HasDerivWithinAt.of_zpow (n:ℤ) (x₀:ℝ) (hx₀: x₀ ≠ 0) :
  HasDerivWithinAt (fun x ↦ x^n) (n * x₀^(n-1)) (.univ \ {0}) x₀ := by
  sorry



end Chapter10
