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
  rw [_root_.HasDerivWithinAt.iff]
  simp only [sub_self, zero_div]
  exact tendsto_const_nhds

/-- Theorem 10.1.13 (b) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_id (X: Set ℝ) (x₀ : ℝ) :
  HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by
  rw [_root_.HasDerivWithinAt.iff]
  apply Filter.Tendsto.congr' (f₁ := fun _ ↦ 1) _ tendsto_const_nhds
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards with x hx
  field_simp [sub_ne_zero.mpr hx.2]

/-- Theorem 10.1.13 (c) (Sum rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_add {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f + g) (f'x₀ + g'x₀) X x₀ := by
  rw [_root_.HasDerivWithinAt.iff] at hf hg ⊢
  have := hf.add hg
  apply this.congr'
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

/-- Theorem 10.1.13 (d) (Product rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_mul {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f * g) (f'x₀ * (g x₀) + (f x₀) * g'x₀) X x₀ := by
  -- Decompose: ((f·g)(x) - (f·g)(x₀))/(x - x₀) = Df(x) · g(x) + f(x₀) · Dg(x).
  -- The limit of the first factor in the first term is f'x₀, of the second g(x₀)
  -- (continuity of g), giving f'x₀ · g(x₀); the second term has constant f(x₀)
  -- times Dg → g'x₀, giving f(x₀) · g'x₀.
  rw [_root_.HasDerivWithinAt.iff] at hf hg ⊢
  have hgcont : Filter.Tendsto g (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)) := by
    have := ContinuousWithinAt.of_differentiableWithinAt
      (DifferentiableWithinAt.of_hasDeriv (by rw [HasDerivWithinAt.iff]; exact hg))
    rw [ContinuousWithinAt] at this
    exact this.mono_left (nhdsWithin_mono _ Set.diff_subset)
  apply ((hf.mul hgcont).add (tendsto_const_nhds.mul hg)).congr'
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards with x hx
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Theorem 10.1.13 (e) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_smul {X: Set ℝ} {x₀ f'x₀: ℝ} (c:ℝ)
  {f: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) :
  HasDerivWithinAt (c • f) (c * f'x₀) X x₀ := by
  rw [_root_.HasDerivWithinAt.iff] at hf ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  apply (tendsto_const_nhds.mul hf).congr'
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards with x hx
  field_simp

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
  rw [_root_.HasDerivWithinAt.iff] at hg ⊢
  have hgcont : Filter.Tendsto g (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)) := by
    have := ContinuousWithinAt.of_differentiableWithinAt
      (DifferentiableWithinAt.of_hasDeriv (by rw [HasDerivWithinAt.iff]; exact hg))
    rw [ContinuousWithinAt] at this
    exact this.mono_left (nhdsWithin_mono _ Set.diff_subset)
  have hgne : ∀ᶠ x in nhdsWithin x₀ (X \ {x₀}), g x ≠ 0 :=
    hgcont.eventually_ne hgx₀
  have hprod : Filter.Tendsto (fun x ↦ g x * g x₀) (nhdsWithin x₀ (X \ {x₀}))
      (nhds ((g x₀)^2)) := by
    have := hgcont.mul (tendsto_const_nhds (x := g x₀))
    simpa [sq] using this
  have hinv : Filter.Tendsto (fun x ↦ (-1 : ℝ) / (g x * g x₀)) (nhdsWithin x₀ (X \ {x₀}))
      (nhds (-1 / (g x₀)^2)) :=
    tendsto_const_nhds.div hprod (by simp [pow_ne_zero _ hgx₀])
  rw [show (-g'x₀ / (g x₀)^2 : ℝ) = -1 / (g x₀)^2 * g'x₀ by ring]
  apply (hinv.mul hg).congr'
  filter_upwards [hgne, self_mem_nhdsWithin] with x hgxne hx
  have hne : x - x₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_diff_singleton.mp hx).2
  simp only [Pi.div_apply, Pi.one_apply]
  field_simp
  ring

/-- Theorem 10.1.13 (h) (Quotient rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_div {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hf: HasDerivWithinAt f f'x₀ X x₀)
  (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f / g) ((f'x₀ * (g x₀) - (f x₀) * g'x₀) / (g x₀)^2) X x₀ := by
  -- f / g = f * (1/g); apply product + reciprocal rules.
  have hmul := HasDerivWithinAt.of_mul hf (HasDerivWithinAt.of_inv hgx₀ hg)
  rw [show ((f'x₀ * g x₀ - f x₀ * g'x₀) / (g x₀)^2 : ℝ)
      = f'x₀ * (1 / g x₀) + f x₀ * (-g'x₀ / (g x₀)^2) by field_simp; ring]
  rw [HasDerivWithinAt.iff] at hmul ⊢
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Pi.mul_apply, Pi.div_apply, Pi.one_apply]
  ring

example (x₀:ℝ) (hx₀: x₀ ≠ 1): HasDerivWithinAt (fun x ↦ (x-2)/(x-1)) (1 /(x₀-1)^2) (.univ \ {1}) x₀ := by
  have hid : HasDerivWithinAt (fun x : ℝ ↦ x) 1 (.univ \ {1}) x₀ :=
    HasDerivWithinAt.of_id _ _
  have hc2 : HasDerivWithinAt (fun _ : ℝ ↦ (2:ℝ)) 0 (.univ \ {1}) x₀ :=
    HasDerivWithinAt.of_const _ _ _
  have hc1 : HasDerivWithinAt (fun _ : ℝ ↦ (1:ℝ)) 0 (.univ \ {1}) x₀ :=
    HasDerivWithinAt.of_const _ _ _
  have hf : HasDerivWithinAt (fun x : ℝ ↦ x - 2) (1 - 0) (.univ \ {1}) x₀ := hid.of_sub hc2
  have hg : HasDerivWithinAt (fun x : ℝ ↦ x - 1) (1 - 0) (.univ \ {1}) x₀ := hid.of_sub hc1
  have hgx₀ : (fun x : ℝ ↦ x - 1) x₀ ≠ 0 := by
    simp; intro h; exact hx₀ (by linarith)
  -- Pin x₀ explicitly — otherwise Lean infers it from `(fun x ↦ x - 1)`'s shape.
  have hdiv := HasDerivWithinAt.of_div (f := fun x : ℝ ↦ x - 2)
    (g := fun x : ℝ ↦ x - 1) (x₀ := x₀) hgx₀ hf hg
  convert hdiv using 1
  field_simp; ring

/-- Newton's approximation reformulated as an {name}`Eventually` over the filter {lean}`nhdsWithin x₀ X`. -/
theorem _root_.HasDerivWithinAt.iff_eventually (X: Set ℝ) (x₀ :ℝ) (f: ℝ → ℝ) (L:ℝ) :
    HasDerivWithinAt f L X x₀ ↔
    ∀ ε > 0, ∀ᶠ x in nhdsWithin x₀ X, |f x - f x₀ - L * (x - x₀)| ≤ ε * |x - x₀| := by
  rw [HasDerivWithinAt.iff_approx_linear]
  refine forall_congr' fun ε => imp_congr_right fun _ => ?_
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball]
  constructor
  · rintro ⟨δ, hδ, hb⟩
    exact ⟨δ, hδ, fun x hxd hxX => hb x hxX (by rw [← Real.dist_eq]; exact hxd)⟩
  · rintro ⟨δ, hδ, hb⟩
    exact ⟨δ, hδ, fun x hxX hxd => hb x (by rw [Metric.mem_ball, Real.dist_eq]; exact hxd) hxX⟩

/-- Theorem 10.1.15 (Chain rule) / Exercise 10.1.7 -/
theorem _root_.HasDerivWithinAt.of_comp {X Y: Set ℝ} {x₀ y₀ f'x₀ g'y₀: ℝ}
  {f g: ℝ → ℝ} (hfx₀: f x₀ = y₀) (hfX : ∀ x ∈ X, f x ∈ Y)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  HasDerivWithinAt (g ∘ f) (g'y₀ * f'x₀) X x₀ := by
  -- Switch to the IsLittleO formulation; then the chain rule reduces to:
  --   (g(f x) - g y₀ - g'y₀ f'x₀ (x - x₀)) = (error_g composed with f) + g'y₀ · error_f
  -- where each summand is o[nhdsWithin x₀ X] (x - x₀).
  rw [hasDerivWithinAt_iff_isLittleO] at hf hg ⊢
  -- f is continuous at x₀ and lands in Y, so f tends to y₀ along nhdsWithin y₀ Y.
  have hfY : Filter.Tendsto f (nhdsWithin x₀ X) (nhdsWithin y₀ Y) := by
    have hfcont : ContinuousWithinAt f X x₀ := ContinuousWithinAt.of_differentiableWithinAt
      (DifferentiableWithinAt.of_hasDeriv (by rw [hasDerivWithinAt_iff_isLittleO]; exact hf))
    rw [ContinuousWithinAt, hfx₀] at hfcont
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hfcont, Filter.eventually_of_mem self_mem_nhdsWithin hfX⟩
  -- Transport hg's little-o through f: (g(f x) - g y₀ - g'y₀(f x - y₀)) =o[x₀] (f x - y₀).
  have hg_comp := hg.comp_tendsto hfY
  -- f x - y₀ = O(x - x₀) since (f x - f x₀) - f'x₀(x - x₀) is o(x - x₀) and f'x₀(x - x₀) is O.
  have hf_isBigO : (fun x => f x - y₀) =O[nhdsWithin x₀ X] (fun x => x - x₀) := by
    rw [← hfx₀]
    have key : (fun x => f x - f x₀)
        = (fun x => (f x - f x₀ - (x - x₀) • f'x₀) + f'x₀ • (x - x₀)) := by
      funext x; simp only [smul_eq_mul]; ring
    rw [key]
    refine hf.isBigO.add ?_
    exact (Asymptotics.isBigO_refl (fun x : ℝ => x - x₀) (nhdsWithin x₀ X)).const_smul_left f'x₀
  -- Combine: first error term is o(x - x₀) by trans_isBigO.
  have h1 : (fun x => g (f x) - g y₀ - (f x - y₀) • g'y₀) =o[nhdsWithin x₀ X] (fun x => x - x₀) :=
    hg_comp.trans_isBigO hf_isBigO
  -- Second error term: g'y₀ · ((f x - f x₀) - f'x₀(x - x₀)) =o (x - x₀).
  have h2 : (g'y₀ • fun x => f x - f x₀ - (x - x₀) • f'x₀) =o[nhdsWithin x₀ X] (fun x => x - x₀) :=
    hf.const_smul_left g'y₀
  -- Algebraic regrouping shows the chain rule's error equals h1 + h2.
  have hsum : ((fun x => g (f x) - g y₀ - (f x - y₀) • g'y₀)
      + g'y₀ • fun x => f x - f x₀ - (x - x₀) • f'x₀)
      = fun x => (g ∘ f) x - (g ∘ f) x₀ - (x - x₀) • (g'y₀ * f'x₀) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [hfx₀]; ring
  rw [← hsum]
  exact h1.add h2

/-- Exercise 10.1.5 -/
theorem _root_.HasDerivWithinAt.of_pow (n:ℕ) (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^n)
(n * x₀^((n:ℤ)-1)) .univ x₀ := by
  induction n with
  | zero => simp; exact hasDerivAt_const x₀ 1
  | succ n ih =>
    rw [show (fun x ↦ x^(n+1)) = (fun x ↦ x) * (fun x ↦ x^n) by funext; simp; ring]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, zpow_natCast]
    rw [show ((↑n + 1) * x₀ ^ n) = 1 * x₀ ^ n + x₀ * (↑n * x₀ ^ ((n:ℤ) - 1)) by
      ring_nf
      -- After ring_nf, the goal has `x₀^((-1:ℤ) + n)`. Convert to a ℕ-power.
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have heq : x₀ ^ ((-1 : ℤ) + (n : ℤ)) = x₀ ^ (n - 1) := by
          rw [show ((-1 : ℤ) + (n : ℤ)) = ((n - 1 : ℕ) : ℤ) by omega]
          rw [zpow_natCast]
        rw [heq]
        have hn1 : x₀ ^ n = x₀ * x₀ ^ (n - 1) := by
          rw [← pow_succ', Nat.sub_one_add_one h.ne']
        rw [hn1]
        ring]
    apply HasDerivWithinAt.of_mul (HasDerivWithinAt.of_id _ _) ih

/-- Exercise 10.1.6 -/
theorem _root_.HasDerivWithinAt.of_zpow (n:ℤ) (x₀:ℝ) (hx₀: x₀ ≠ 0) :
  HasDerivWithinAt (fun x ↦ x^n) (n * x₀^(n-1)) (.univ \ {0}) x₀ := by
  by_cases hn : n ≥ 0
  . lift n to ℕ using hn
    simp
    have := HasDerivWithinAt.of_pow n x₀
    rw [HasDerivWithinAt.iff] at this ⊢
    apply this.mono_left
    apply nhdsWithin_mono
    simp
  . simp at hn
    -- replace n with -m, m = -n > 0; use 10.1.5 (of_pow) and reciprocal rule (of_inv).
    set m : ℕ := (-n).toNat with hm_def
    have hmpos : 0 < m := by simp [hm_def]; omega
    have hnm : (n : ℤ) = -(m : ℤ) := by simp [hm_def]; omega
    -- f(x) = x^m has derivative m * x₀^(m-1) on Set.univ \ {0}.
    have hpow := HasDerivWithinAt.of_pow m x₀
    have hpow' : HasDerivWithinAt (fun x : ℝ ↦ x^m) ((m : ℝ) * x₀^((m:ℤ)-1))
        (.univ \ {0}) x₀ := by
      rw [HasDerivWithinAt.iff] at hpow ⊢
      exact hpow.mono_left (nhdsWithin_mono _ (by simp))
    have hxm : (fun x : ℝ ↦ x^m) x₀ ≠ 0 := pow_ne_zero _ hx₀
    have hinv := HasDerivWithinAt.of_inv hxm hpow'
    -- `hinv` displays with `npowRec m`, but is defeq to a clean lambda — restate.
    have hinv2 : HasDerivWithinAt (fun x : ℝ ↦ 1 / x^m)
        (-((m : ℝ) * x₀ ^ ((m:ℤ) - 1)) / (x₀^m)^2) (Set.univ \ {0}) x₀ := hinv
    have hfun : (fun x : ℝ ↦ 1 / x^m) = (fun x ↦ x^n) := by
      funext x; simp [hnm, zpow_neg, zpow_natCast]
    rw [hfun] at hinv2
    convert hinv2 using 1
    -- Reconcile the derivative value `n * x₀^(n-1) = -(m * x₀^(m-1))/(x₀^m)²`.
    rw [hnm]; push_cast
    rw [show (-(m:ℤ)) - 1 = -((m:ℤ) + 1) from by ring]
    rw [zpow_neg]
    rw [show ((m:ℤ) + 1) = ((m + 1 : ℕ) : ℤ) from by push_cast; ring]
    rw [zpow_natCast]
    rw [show ((m:ℤ) - 1) = ((m - 1 : ℕ) : ℤ) from by omega]
    rw [zpow_natCast]
    have hxm_pow : x₀^(m+1) = x₀ * x₀^m := by rw [pow_succ']
    have hxm_pow' : x₀^m = x₀ * x₀^(m-1) := by
      rw [← pow_succ', Nat.sub_one_add_one hmpos.ne']
    field_simp
    rw [hxm_pow, hxm_pow']
    ring

end Chapter10
