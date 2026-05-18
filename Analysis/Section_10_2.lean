import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_1
/-!
# Analysis I, Section 10.2: Local maxima, local minima, and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relation between local extrema and derivatives.
- Rolle's theorem.
- mean value theorem.

-/

open Chapter9
namespace Chapter10

/-- Definition 10.2.1 (Local maxima and minima).  Here we use Mathlib's {name}`IsLocalMaxOn` type. -/
theorem IsLocalMaxOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMaxOn_iff, IsLocalMaxOn, IsMaxFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

theorem IsLocalMinOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMinOn_iff, IsLocalMinOn, IsMinFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

/-- Example 10.2.3 -/
abbrev f_10_2_3 : ℝ → ℝ := fun x ↦ x^2 - x^4

example : ¬ IsMinOn f_10_2_3 .univ 0 := by
  simp [isMinOn_iff]
  use 2
  norm_num

theorem f_10_2_3_min_on_1 : IsMinOn f_10_2_3 (.Ioo (-1) 1) 0 := by
  simp [isMinOn_iff]
  intro y hy hy'
  have hy2 : y^2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg y, sq_nonneg (1 - y^2)]

example : IsLocalMinOn f_10_2_3 .univ 0 := by
  simp [IsLocalMinOn.iff]
  use 1
  norm_num
  exact f_10_2_3_min_on_1

/-- Example 10.2.4 -/
example : ¬ ∃ x, IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  simp [isMaxOn_iff]
  intro x
  obtain ⟨y, _⟩ := exists_int_gt x
  use y

example : ¬ ∃ x, IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  simp [isMinOn_iff]
  intro x
  obtain ⟨y, _⟩ := exists_int_lt x
  use y

example (n:ℤ) : IsLocalMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by
  simp [IsLocalMaxOn.iff]
  use 0.5
  norm_num
  rw [isMaxOn_iff]
  intro y hy
  simp at hy
  obtain ⟨⟨k, rfl⟩, h1, h2⟩ := hy
  have hk : k = n := by
    have h1'' : n - 1 < k := by exact_mod_cast (by linarith : (n - 1 : ℝ) < k)
    have h2'' : k < n + 1 := by exact_mod_cast (by linarith : (k : ℝ) < n + 1)
    omega
  simp [hk]

example (n:ℤ) : IsLocalMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by
  simp [IsLocalMinOn.iff]
  use 0.5
  norm_num
  rw [isMinOn_iff]
  intro y hy
  simp at hy
  obtain ⟨⟨k, rfl⟩, h1, h2⟩ := hy
  have hk : k = n := by
    have h1'' : n - 1 < k := by exact_mod_cast (by linarith : (n - 1 : ℝ) < k)
    have h2'' : k < n + 1 := by exact_mod_cast (by linarith : (k : ℝ) < n + 1)
    omega
  simp [hk]

/-- Remark 10.2.5 -/
theorem IsLocalMaxOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMaxOn f X x₀) : IsLocalMaxOn f Y x₀ := by
  rw [IsLocalMaxOn.iff] at h ⊢
  obtain ⟨δ, hδ, hmax⟩ := h
  use δ, hδ
  have : (Y ∩ Set.Ioo (x₀ - δ) (x₀ + δ) ⊆ X ∩ Set.Ioo (x₀ - δ) (x₀ + δ)) := by grind
  exact IsMaxOn.on_subset hmax this

theorem IsLocalMinOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMinOn f X x₀) : IsLocalMinOn f Y x₀ := by
  rw [IsLocalMinOn.iff] at h ⊢
  obtain ⟨δ, hδ, hmin⟩ := h
  use δ, hδ
  have : (Y ∩ Set.Ioo (x₀ - δ) (x₀ + δ) ⊆ X ∩ Set.Ioo (x₀ - δ) (x₀ + δ)) := by grind
  exact IsMinOn.on_subset hmin this

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMaxOn.deriv_eq_zero {a b:ℝ} {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMaxOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  rw [IsLocalMaxOn.iff] at h
  obtain ⟨δ₀, hδ₀, hmax⟩ := h
  rw [isMaxOn_iff] at hmax
  rw [_root_.HasDerivWithinAt.iff_approx_linear] at hderiv
  obtain ⟨ha, hb⟩ := hx₀
  by_contra hL
  rcases lt_or_gt_of_ne hL with hLneg | hLpos
  · obtain ⟨δ₁, hδ₁, hball⟩ := hderiv (-L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (x₀ - a)) with hδdef
    have hδ : δ > 0 := by grind
    set x := x₀ - δ/2 with hxdef
    have hxIoo : x ∈ Set.Ioo a b := by grind
    have hxball : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hfx : f x ≤ f x₀ := hmax x ⟨hxIoo, hxball⟩
    have hxdist : |x - x₀| < δ₁ := by grind
    have hbe := hball x hxIoo hxdist
    have hxneg : x - x₀ < 0 := by rw [hxdef]; linarith
    have habs : |x - x₀| = -(x - x₀) := abs_of_neg hxneg
    rw [habs] at hbe
    have key : f x - f x₀ - L * (x - x₀) ≥ -((-L)/2 * -(x - x₀)) := by
      have := abs_le.mp hbe
      linarith
    nlinarith
  · obtain ⟨δ₁, hδ₁, hball⟩ := hderiv (L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (b - x₀)) with hδdef
    have hδ : δ > 0 := by grind
    set x := x₀ + δ/2 with hxdef
    have hxIoo : x ∈ Set.Ioo a b := by grind
    have hxball : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hfx : f x ≤ f x₀ := hmax x ⟨hxIoo, hxball⟩
    have hxdist : |x - x₀| < δ₁ := by grind
    have hbe := hball x hxIoo hxdist
    have hxpos : x - x₀ > 0 := by rw [hxdef]; linarith
    have habs : |x - x₀| = x - x₀ := abs_of_pos hxpos
    rw [habs] at hbe
    have key : f x - f x₀ - L * (x - x₀) ≥ -(L/2 * (x - x₀)) := by
      have := abs_le.mp hbe
      linarith
    nlinarith

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMinOn.deriv_eq_zero {a b:ℝ} {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMinOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  rw [IsLocalMinOn.iff] at h
  obtain ⟨δ₀, hδ₀, hmin⟩ := h
  rw [isMinOn_iff] at hmin
  rw [_root_.HasDerivWithinAt.iff_approx_linear] at hderiv
  obtain ⟨ha, hb⟩ := hx₀
  by_contra hL
  rcases lt_or_gt_of_ne hL with hLneg | hLpos
  · obtain ⟨δ₁, hδ₁, hball⟩ := hderiv (-L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (b - x₀)) with hδdef
    have hδ : δ > 0 := by grind
    set x := x₀ + δ/2 with hxdef
    have hxIoo : x ∈ Set.Ioo a b := by grind
    have hxball : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hfx : f x ≥ f x₀ := hmin x ⟨hxIoo, hxball⟩
    have hxdist : |x - x₀| < δ₁ := by grind
    have hbe := hball x hxIoo hxdist
    have hxpos : x - x₀ > 0 := by rw [hxdef]; linarith
    have habs : |x - x₀| = x - x₀ := abs_of_pos hxpos
    rw [habs] at hbe
    have key : f x - f x₀ - L * (x - x₀) ≤ -((-L)/2 * (x - x₀)) := by
      have := abs_le.mp hbe
      linarith
    nlinarith
  · obtain ⟨δ₁, hδ₁, hball⟩ := hderiv (L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (x₀ - a)) with hδdef
    have hδ : δ > 0 := by grind
    set x := x₀ - δ/2 with hxdef
    have hxIoo : x ∈ Set.Ioo a b := by grind
    have hxball : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hfx : f x ≥ f x₀ := hmin x ⟨hxIoo, hxball⟩
    have hxdist : |x - x₀| < δ₁ := by grind
    have hbe := hball x hxIoo hxdist
    have hxneg : x - x₀ < 0 := by rw [hxdef]; linarith
    have habs : |x - x₀| = -(x - x₀) := abs_of_neg hxneg
    rw [habs] at hbe
    have key : f x - f x₀ - L * (x - x₀) ≤ -(L/2 * -(x - x₀)) := by
      have := abs_le.mp hbe
      linarith
    nlinarith

theorem IsMaxOn.deriv_eq_zero_counter : ∃ (a b:ℝ) (f:ℝ → ℝ)
  (x₀:ℝ) (_: x₀ ∈ Set.Icc a b) (_: IsMaxOn f (.Icc a b) x₀) (L:ℝ)
  (_: HasDerivWithinAt f L (.Icc a b) x₀), L ≠ 0 := by
  use 0, 1, id, 1, by simp, by
    rw [isMaxOn_iff]
    simp
  use 1
  simp only [ne_eq, one_ne_zero, not_false_eq_true, exists_prop, and_true]
  exact hasDerivWithinAt_id 1 (Set.Icc 0 1)

/-- Theorem 10.2.7 (Rolle's theorem) / Exercise 10.2.4 -/
theorem _root_.HasDerivWithinAt.exist_zero {a b:ℝ} (hab: a < b) {g:ℝ → ℝ}
  (hcont: ContinuousOn g (.Icc a b)) (hderiv: DifferentiableOn ℝ g (.Ioo a b))
  (hgab: g a = g b) : ∃ x ∈ Set.Ioo a b, HasDerivWithinAt g 0 (.Ioo a b) x := by
  sorry

/-- Corollary 10.2.9 (Mean value theorem) / Exercise 10.2.5 -/
theorem _root_.HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) (hderiv: DifferentiableOn ℝ f (.Ioo a b)) :
  ∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (.Ioo a b) x := by
  sorry

/-- Exercise 10.2.2 -/
example : ∃ f:ℝ → ℝ, ContinuousOn f (.Icc (-1) 1) ∧
  IsMaxOn f (.Icc (-1) 1) 0 ∧ ¬ DifferentiableWithinAt ℝ f (.Icc (-1) 1) 0 := by
  sorry

/-- Exercise 10.2.3 -/
example : ∃ f:ℝ → ℝ, DifferentiableOn ℝ f (.Icc (-1) 1) ∧
  HasDerivWithinAt f 0 (.Ioo (-1) 1) 0 ∧
  ¬ IsLocalMaxOn f (.Icc (-1) 1) 0 ∧ ¬ IsLocalMinOn f (.Icc (-1) 1) 0 := by
  sorry

/-- Exercise 10.2.6 -/
theorem lipschitz_bound {M a b:ℝ} (hM: M > 0) (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b))
  (hderiv: DifferentiableOn ℝ f (.Ioo a b))
  (hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (.Ioo a b) x| ≤ M)
  {x y:ℝ} (hx: x ∈ Set.Ioo a b) (hy: y ∈ Set.Ioo a b) :
  |f x - f y| ≤ M * |x - y| := by
  sorry

/-- Exercise 10.2.7 -/
theorem _root_.UniformContinuousOn.of_lipschitz {f:ℝ → ℝ}
  (hcont: ContinuousOn f .univ)
  (hderiv: DifferentiableOn ℝ f .univ)
  (hlip: BddOn (deriv f) .univ) :
  UniformContinuousOn f (.univ) := by
  sorry


end Chapter10
