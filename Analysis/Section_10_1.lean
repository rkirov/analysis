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
  HasDerivWithinAt (fun x ↦ c) 0 X x₀ := by sorry

/-- Theorem 10.1.13 (b) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_id (X: Set ℝ) (x₀ : ℝ) :
  HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by sorry

/-- Theorem 10.1.13 (c) (Sum rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_add {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f + g) (f'x₀ + g'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (d) (Product rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_mul {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f * g) (f'x₀ * (g x₀) + (f x₀) * g'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (e) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_smul {X: Set ℝ} {x₀ f'x₀: ℝ} (c:ℝ)
  {f: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) :
  HasDerivWithinAt (c • f) (c * f'x₀) X x₀ := by
  sorry

/-- Theorem 10.1.13 (f) (Difference rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_sub {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f - g) (f'x₀ - g'x₀) X x₀ := by
  sorry

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
