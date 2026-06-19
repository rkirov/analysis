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
  obtain ⟨x₀, hx₀, hmax⟩ := IsMaxOn.of_continuous_on_compact hab hcont
  obtain ⟨x₁, hx₁, hmin⟩ := IsMinOn.of_continuous_on_compact hab hcont
  by_cases hmax_eq : x₀ = a ∨ x₀ = b
  . by_cases hmin_eq : x₁ = a ∨ x₁ = b
    . have hminmax : g x₁ = g x₀ := by grind
      have : ∀ x ∈ Set.Icc a b, g x = g a := by
        intro x hx
        have h1 : g x ≤ g x₀ := by exact le_of_eq_of_le rfl (hmax hx)
        have h2 : g x ≥ g x₁ := by exact le_of_eq_of_le rfl (hmin hx)
        rw [hminmax] at h2
        have : g x = g x₀ := by linarith
        cases hmax_eq with
        | inl hxa => rw [hxa] at this; simp [this]
        | inr hxb => subst b; linarith
      use (a + b) / 2
      refine ⟨by grind, ?_⟩
      have hconst : HasDerivWithinAt (fun _ ↦ g a) 0 (.Ioo a b) ((a+b)/2) :=
        hasDerivWithinAt_const _ _ _
      refine hconst.congr_of_mem ?_ (by grind)
      intro x hx
      exact this x ⟨hx.1.le, hx.2.le⟩
    . have hx₁Ioo : x₁ ∈ Set.Ioo a b := by
        rcases hx₁ with ⟨h1, h2⟩
        push_neg at hmin_eq
        exact ⟨lt_of_le_of_ne h1 (Ne.symm hmin_eq.1), lt_of_le_of_ne h2 hmin_eq.2⟩
      have hmin' : IsMinOn g (.Ioo a b) x₁ :=
        hmin.on_subset Set.Ioo_subset_Icc_self
      have hlocal : IsLocalMinOn g (.Ioo a b) x₁ := hmin'.localize
      have hg₁ := (hderiv x₁ hx₁Ioo).hasDerivWithinAt
      have hderiv₁ := IsLocalMinOn.deriv_eq_zero hx₁Ioo hlocal hg₁
      use x₁, hx₁Ioo
      rw [hderiv₁] at hg₁
      exact hg₁
  . have hx₀Ioo : x₀ ∈ Set.Ioo a b := by
      rcases hx₀ with ⟨h1, h2⟩
      push_neg at hmax_eq
      exact ⟨lt_of_le_of_ne h1 (Ne.symm hmax_eq.1), lt_of_le_of_ne h2 hmax_eq.2⟩
    have hmax' : IsMaxOn g (.Ioo a b) x₀ :=
      hmax.on_subset Set.Ioo_subset_Icc_self
    have hlocal : IsLocalMaxOn g (.Ioo a b) x₀ := hmax'.localize
    have hg₀ := (hderiv x₀ hx₀Ioo).hasDerivWithinAt
    have hderiv₀ := IsLocalMaxOn.deriv_eq_zero hx₀Ioo hlocal hg₀
    use x₀, hx₀Ioo
    rw [hderiv₀] at hg₀
    exact hg₀

/-- Corollary 10.2.9 (Mean value theorem) / Exercise 10.2.5 -/
theorem _root_.HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) (hderiv: DifferentiableOn ℝ f (.Ioo a b)) :
  ∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (.Ioo a b) x := by
  set g := fun x ↦ f x - (f b - f a) / (b - a) * x
  have hgab : g a = g b := by
    simp [g]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (by linarith)
    field_simp
    ring
  have hgcont : ContinuousOn g (.Icc a b) := by fun_prop
  have hgderiv : DifferentiableOn ℝ g (.Ioo a b) := by fun_prop
  have := _root_.HasDerivWithinAt.exist_zero hab hgcont hgderiv hgab
  obtain ⟨x, hx, hgₓ⟩ := this
  use x, hx
  have hc : HasDerivWithinAt (fun y ↦ (f b - f a) / (b - a) * y) ((f b - f a) / (b - a))
      (Set.Ioo a b) x := by
    simpa using (hasDerivWithinAt_id x (Set.Ioo a b)).const_mul ((f b - f a) / (b - a))
  have hsum := hgₓ.add hc
  have heq : ((fun x ↦ f x - (f b - f a) / (b - a) * x) + fun y ↦ (f b - f a) / (b - a) * y) = f := by
    funext y
    show f y - (f b - f a) / (b - a) * y + (f b - f a) / (b - a) * y = f y
    ring
  simp only [g, heq, zero_add] at hsum
  exact hsum

/-- Exercise 10.2.2 -/
example : ∃ f:ℝ → ℝ, ContinuousOn f (.Icc (-1) 1) ∧
  IsMaxOn f (.Icc (-1) 1) 0 ∧ ¬ DifferentiableWithinAt ℝ f (.Icc (-1) 1) 0 := by
  use fun x ↦ -|x|
  refine ⟨?_, ?_, ?_⟩
  . fun_prop
  . simp [isMaxOn_iff]
  . intro h
    have hnhds : Set.Icc (-1:ℝ) 1 ∈ nhds (0:ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
    have hda : DifferentiableAt ℝ (fun x:ℝ ↦ -|x|) 0 := h.differentiableAt hnhds
    have habs : DifferentiableAt ℝ (fun x:ℝ ↦ |x|) 0 := by simpa using hda.neg
    have habs' : DifferentiableWithinAt ℝ f_10_1_6 .univ 0 := habs.differentiableWithinAt
    rw [DifferentiableWithinAt.iff] at habs'
    obtain ⟨L, hL⟩ := habs'
    rw [_root_.HasDerivWithinAt.iff] at hL
    exact abs_has_no_deriv ⟨L, hL⟩

/-- Exercise 10.2.3 -/
example : ∃ f:ℝ → ℝ, DifferentiableOn ℝ f (.Icc (-1) 1) ∧
  HasDerivWithinAt f 0 (.Ioo (-1) 1) 0 ∧
  ¬ IsLocalMaxOn f (.Icc (-1) 1) 0 ∧ ¬ IsLocalMinOn f (.Icc (-1) 1) 0 := by
  use fun x ↦ x^3
  constructor
  . exact differentiableOn_pow 3
  . constructor
    . have h := hasDerivAt_pow 3 (0:ℝ)
      simp at h
      exact h.hasDerivWithinAt
    . constructor
      . rw [IsLocalMaxOn.iff]
        push Not
        intro δ hδ
        rw [isMaxOn_iff]
        push Not
        use min (δ / 2) (1 / 2)
        simp
        constructor
        . constructor
          . constructor
            . grind
            . grind
          . constructor
            . grind
            . grind
        . positivity
      . rw [IsLocalMinOn.iff]
        push Not
        intro δ hδ
        rw [isMinOn_iff]
        push Not
        use max (-δ / 2) (-1 / 2)
        simp
        constructor
        . constructor
          . constructor
            . grind
            . grind
          . constructor
            . grind
            . grind
        . have h1 : max (-δ / 2) (-1 / 2) < 0 := by
            rw [max_lt_iff]; constructor <;> linarith
          exact Odd.pow_neg (by decide) h1

/-- Exercise 10.2.6 -/
theorem lipschitz_bound {M a b:ℝ} (hM: M > 0) (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b))
  (hderiv: DifferentiableOn ℝ f (.Ioo a b))
  (hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (.Ioo a b) x| ≤ M)
  {x y:ℝ} (hx: x ∈ Set.Ioo a b) (hy: y ∈ Set.Ioo a b) :
  |f x - f y| ≤ M * |x - y| := by
  wlog hxy : x < y
  . simp at hxy
    by_cases hxxy : x = y
    . subst x
      simp
    . have hyx : y < x := by grind
      specialize this hM hab hcont hderiv hlip hy hx hyx
      rw [abs_sub_comm (f y) (f x), abs_sub_comm y x] at this
      exact this
  have hsub : Set.Icc x y ⊆ Set.Ioo a b := by
    intro w ⟨hw1, hw2⟩
    exact ⟨lt_of_lt_of_le hx.1 hw1, lt_of_le_of_lt hw2 hy.2⟩
  have hsubo : Set.Ioo x y ⊆ Set.Ioo a b := fun w hw ↦ hsub ⟨hw.1.le, hw.2.le⟩
  have hcont' : ContinuousOn f (.Icc x y) := hcont.mono (hsub.trans Set.Ioo_subset_Icc_self)
  have hderiv' : DifferentiableOn ℝ f (.Ioo x y) := hderiv.mono hsubo
  obtain ⟨z, hz, hderiv_z⟩ := _root_.HasDerivWithinAt.mean_value hxy hcont' hderiv'
  have hzab : z ∈ Set.Ioo a b := hsubo hz
  have hda : HasDerivAt f ((f y - f x) / (y - x)) z :=
    hderiv_z.hasDerivAt (Ioo_mem_nhds hz.1 hz.2)
  have hda' : HasDerivAt f (derivWithin f (Set.Ioo a b) z) z := by
    have := (hderiv z hzab).hasDerivWithinAt
    exact this.hasDerivAt (Ioo_mem_nhds hzab.1 hzab.2)
  have hslope_eq : (f y - f x) / (y - x) = derivWithin f (Set.Ioo a b) z :=
    hda.unique hda'
  specialize hlip z hzab
  rw [hslope_eq.symm] at hlip
  rw [abs_div] at hlip
  have : |y - x| ≠ 0 := by grind
  field_simp at hlip ⊢
  rw [abs_sub_comm x y, abs_sub_comm (f x) (f y), mul_comm]
  exact hlip

/-- Exercise 10.2.7 -/
theorem _root_.UniformContinuousOn.of_lipschitz {f:ℝ → ℝ}
  (hcont: ContinuousOn f .univ)
  (hderiv: DifferentiableOn ℝ f .univ)
  (hlip: BddOn (deriv f) .univ) :
  UniformContinuousOn f (.univ) := by
  obtain ⟨M, hM⟩ := hlip
  set M' := M + 1
  have hM' : M' > 0 := by
    have h1 : M ≥ 0 := le_trans (abs_nonneg _) (hM 0 (by trivial))
    linarith
  -- Lipschitz constant M' works on any bounded interval, hence globally.
  have hglobal : ∀ x y : ℝ, |f x - f y| ≤ M' * |x - y| := by
    intro x y
    wlog hxy : x < y with H
    · by_cases hxy' : x = y
      · subst hxy'; simp
      · have hyx : y < x := lt_of_le_of_ne (not_lt.mp hxy) (Ne.symm hxy')
        rw [abs_sub_comm (f x), abs_sub_comm x]
        exact H hcont hderiv M hM hM' y x hyx
    have hab : x - 1 < y + 1 := by linarith
    have hxIoo : x ∈ Set.Ioo (x - 1) (y + 1) := by grind
    have hyIoo : y ∈ Set.Ioo (x - 1) (y + 1) := by grind
    have hcont' : ContinuousOn f (.Icc (x - 1) (y + 1)) := hcont.mono (Set.subset_univ _)
    have hderiv' : DifferentiableOn ℝ f (.Ioo (x - 1) (y + 1)) := hderiv.mono (Set.subset_univ _)
    have hlip' : ∀ z ∈ Set.Ioo (x - 1) (y + 1), |derivWithin f (.Ioo (x - 1) (y + 1)) z| ≤ M' := by
      intro z hz
      have hopen : Set.Ioo (x - 1) (y + 1) ∈ nhds z := Ioo_mem_nhds hz.1 hz.2
      rw [derivWithin_of_mem_nhds hopen]
      have := hM z (by trivial)
      linarith
    exact lipschitz_bound hM' hab hcont' hderiv' hlip' hxIoo hyIoo
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  use ε / M', by positivity
  intro x _ y _ hxy
  rw [Real.dist_eq] at hxy ⊢
  calc |f x - f y|
      ≤ M' * |x - y| := hglobal x y
    _ ≤ M' * (ε / M') := by gcongr
    _ = ε := by field_simp


end Chapter10
