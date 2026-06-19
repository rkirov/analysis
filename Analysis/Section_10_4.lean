import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_10_1

/-!
# Analysis I, Section 10.4: Inverse functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The inverse function theorem.

-/

open Chapter9
namespace Chapter10

/-- Lemma 10.4.1 -/
theorem _root_.HasDerivWithinAt.of_inverse {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ * f'x₀ = 1 := by
  -- This proof is written to follow the structure of the original text.
  have h1 : HasDerivWithinAt id (g'y₀ * f'x₀) X x₀ := by
    apply (hf.of_comp hfx₀ hfXY _).congr _ (hgf _ hx₀).symm <;> grind
  observe h2 : HasDerivWithinAt id 1 X x₀
  solve_by_elim [derivative_unique]

theorem _root_.HasDerivWithinAt.of_inverse' {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ = 1/f'x₀ :=
    eq_one_div_of_mul_eq_one_left (hf.of_inverse hfXY hgf hx₀ hfx₀ hcluster hg)

theorem _root_.HasDerivWithinAt.of_inverse_of_zero_deriv {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f 0 X x₀) :
  ¬ DifferentiableWithinAt ℝ g Y y₀ := by
  by_contra this; rw [DifferentiableWithinAt.iff] at this; choose _ hg using this
  apply hf.of_inverse at hg <;> grind

example : ¬ DifferentiableWithinAt ℝ (fun x:ℝ ↦ x^(1/3:ℝ)) (.Ici 0) 0 := by
  apply _root_.HasDerivWithinAt.of_inverse_of_zero_deriv
    (X:= .Ici 0) (Y := .Ici 0) (f := fun x ↦ x^3) (x₀ := 0)
  . simp
  . norm_num
  . simp
    rw [clusterPt_iff_forall_mem_closure]
    intro s hs
    rw [Filter.mem_principal] at hs
    have : closure (Set.Ioi (0:ℝ)) ⊆ closure s := closure_mono hs
    rw [closure_Ioi] at this
    exact this Set.self_mem_Ici
  . have hpow : HasDerivAt (fun x : ℝ => x^3) ((3:ℕ) * (0:ℝ)^(3-1)) 0 := by
      simpa using hasDerivAt_pow 3 (0:ℝ)
    have := hpow.hasDerivWithinAt (s := Set.Ici (0:ℝ))
    simpa using this
  . intro x hx
    simp at hx ⊢
    exact pow_succ_nonneg hx 2
  . intro x hx
    simp at hx ⊢
    suffices h : (x ^ (3:ℝ)) ^ (3⁻¹:ℝ) = x by exact_mod_cast h
    have h1 : (x ^ (3:ℝ)) = (x ^ (3:ℕ)) := by
      rw [show ((3:ℝ) = ((3:ℕ):ℝ)) from by norm_num, Real.rpow_natCast]
    rw [h1, show ((3⁻¹:ℝ) = ((3:ℕ):ℝ)⁻¹) from by norm_num]
    exact Real.pow_rpow_inv_natCast hx (by norm_num)

/-- Theorem 10.4.2 (Inverse function theorem) -/
theorem inverse_function_theorem {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgYX: ∀ y ∈ Y, g y ∈ X)
  (hgf: ∀ x ∈ X, g (f x) = x) (hfg: ∀ y ∈ Y, f (g y) = y)
  {x₀ y₀ f'x₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀) (hne : f'x₀ ≠ 0)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: ContinuousWithinAt g Y y₀) :
    HasDerivWithinAt g (1/f'x₀) Y y₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _]
    intro y hy hconv
    set x : ℕ → ℝ := fun n ↦ g (y n)
    have hy' : ∀ n, y n ∈ Y := by
      intro n
      specialize hy n
      exact hy.1
    have hy₀: y₀ ∈ Y := by aesop
    have hx : ∀ n, x n ∈ X \ {x₀}:= by
      intro n
      simp [x]
      constructor
      . apply hgYX
        exact hy' n
      . by_contra h
        have : f (g (y n)) = f x₀ := by simp [h]
        specialize hfg (y n) (hy' n)
        rw [hfg] at this
        rw [hfx₀] at this
        specialize hy n
        obtain ⟨_, h⟩ := hy
        contradiction
    replace hconv := hconv.comp_of_continuous hg hy'
    have hgy₀ : g y₀ = x₀ := by aesop
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _] at hf
    convert (hf _ hx _).inv₀ _ using 2 with n <;> grind

/-- Exercise 10.4.1(a) -/
example {n:ℕ} : ContinuousOn (fun x:ℝ ↦ x^(1/n:ℝ)) (.Ioi 0) := by
  exact Continuous.exp' (1 / ↑n)

/-- Exercise 10.4.1(b) -/
theorem hasDerivWithinAt_rpow_one_div_natCast {n:ℕ} {x:ℝ} (hx: x ∈ Set.Ioi 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(1/n:ℝ))
  ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) (.Ioi 0) x := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    simp only [Nat.cast_zero, inv_zero, zero_mul, one_div, Real.rpow_zero]
    exact (hasDerivWithinAt_const _ _ 1)
  have hxpos : 0 < x := hx
  have hncast : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  let f := fun x:ℝ ↦ x^n
  let g := fun x:ℝ ↦ x^(1/n:ℝ)
  let x₀ : ℝ := x ^ (1/n:ℝ)
  have hx₀pos : 0 < x₀ := Real.rpow_pos_of_pos hxpos _
  have hx₀ : x₀ ∈ Set.Ioi 0 := hx₀pos
  have hfX : ∀ x ∈ Set.Ioi 0, f x ∈ Set.Ioi 0 := by
    intro x hx
    have : (0:ℝ) < x := hx
    exact pow_pos this n
  have hgY : ∀ y ∈ Set.Ioi 0, g y ∈ Set.Ioi 0 := by
    intro y hy
    have : (0:ℝ) < y := hy
    exact Real.rpow_pos_of_pos this (1/n:ℝ)
  have hgf : ∀ x ∈ Set.Ioi 0, g (f x) = x := by
    intro x hx
    simp only [f, g, ← Real.rpow_natCast x n, ← Real.rpow_mul hx.le]
    rw [show ((n:ℝ) * (1/n) = 1) from by field_simp, Real.rpow_one]
  have hfg : ∀ y ∈ Set.Ioi 0, f (g y) = y := by
    intro y hy
    simp only [f, g, ← Real.rpow_natCast _ n, ← Real.rpow_mul hy.le]
    rw [show ((1/n:ℝ) * n = 1) from by field_simp, Real.rpow_one]
  have hfx₀ : f x₀ = x := hfg x hx
  have hx₀pow : (0:ℝ) < x₀^(n-1) := by positivity
  have hfne : (n:ℝ) * x₀^(n-1) ≠ 0 := by positivity
  have hf : HasDerivWithinAt f ((n:ℝ) * x₀^(n-1)) (.Ioi 0) x₀ :=
    (hasDerivAt_pow n x₀).hasDerivWithinAt
  have hg : ContinuousWithinAt g (.Ioi 0) x :=
    (Real.continuousAt_rpow_const x (1/n:ℝ) (Or.inl (ne_of_gt hxpos))).continuousWithinAt
  have key := inverse_function_theorem hfX hgY hgf hfg hx₀ hfx₀ hfne hf hg
  have hrewrite : 1 / ((n:ℝ) * x₀^(n-1)) = (n:ℝ)⁻¹ * x^((n:ℝ)⁻¹ - 1) := by
    have : (x₀:ℝ)^(n-1) = x^(((n:ℝ)-1) / n) := by
      simp only [x₀, ← Real.rpow_natCast _ (n-1), ← Real.rpow_mul hxpos.le]
      congr 1
      have : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn)]; norm_num
      rw [this]; ring
    rw [this]
    rw [show ((n:ℝ)⁻¹ - 1 = -(((n:ℝ) - 1) / n)) from by field_simp; ring]
    rw [Real.rpow_neg hxpos.le]
    field_simp
  rw [hrewrite] at key
  exact key

/-- Exercise 10.4.2(a) -/
theorem hasDerivWithinAt_rpow_ratCast (q:ℚ) {x:ℝ} (hx: x ∈ Set.Ioi 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(q:ℝ)) (q * x^(q-1:ℝ)) (.Ioi 0) x := by
  have hxpos : (0:ℝ) < x := hx
  set m : ℤ := q.num with hm_def
  set n : ℕ := q.den with hn_def
  have hn0 : n ≠ 0 := q.den_ne_zero
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hq : (q:ℝ) = (m:ℝ) / n := by
    rw [show (q:ℝ) = ((q.num:ℝ) / (q.den:ℝ)) from q.cast_def]
  let f : ℝ → ℝ := fun x ↦ x^(1/n:ℝ)
  have hxinv_pos : (0:ℝ) < x^(1/n:ℝ) := Real.rpow_pos_of_pos hxpos _
  have hf : HasDerivWithinAt f ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹ - 1)) (.Ioi 0) x :=
    hasDerivWithinAt_rpow_one_div_natCast hx
  let h : ℝ → ℝ := fun y ↦ y^m
  have hh : HasDerivWithinAt h ((m:ℝ) * (x^(1/n:ℝ))^(m-1)) (.Ioi 0) (x^(1/n:ℝ)) :=
    (hasDerivAt_zpow m _ (Or.inl (ne_of_gt hxinv_pos))).hasDerivWithinAt
  have hfX : ∀ z ∈ Set.Ioi 0, f z ∈ Set.Ioi 0 := by
    intro z hz; exact Real.rpow_pos_of_pos (show (0:ℝ) < z from hz) _
  have hchain : HasDerivWithinAt (h ∘ f)
      ((m:ℝ) * (x^(1/n:ℝ))^(m-1) * ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹ - 1))) (.Ioi 0) x :=
    hf.of_comp (rfl : f x = x^(1/n:ℝ)) hfX hh
  have hfun_eq : ∀ z ∈ Set.Ioi 0, (h ∘ f) z = z^(q:ℝ) := by
    intro z hz
    have hzpos : (0:ℝ) < z := hz
    simp only [h, f, Function.comp_apply]
    rw [← Real.rpow_intCast (z^(1/n:ℝ)) m, ← Real.rpow_mul hzpos.le, hq]
    congr 1; field_simp
  have hderiv_eq : (m:ℝ) * (x^(1/n:ℝ))^(m-1) * ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹ - 1))
                  = (q:ℝ) * x^((q:ℝ) - 1) := by
    rw [hq]
    have hpow : ((x^(1/n:ℝ))^(m-1:ℤ) : ℝ) = x^((1/n:ℝ) * ((m:ℝ) - 1)) := by
      rw [← Real.rpow_intCast (x^(1/n:ℝ)) (m-1), ← Real.rpow_mul hxpos.le]
      push_cast; ring_nf
    rw [hpow]
    rw [show ((m:ℝ) * x^((1/n:ℝ) * ((m:ℝ)-1)) * ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹ - 1))
            = ((m:ℝ) * (n:ℝ)⁻¹) * (x^((1/n:ℝ) * ((m:ℝ)-1)) * x^((n:ℝ)⁻¹ - 1))) from by ring]
    rw [← Real.rpow_add hxpos]
    rw [show ((1/n:ℝ) * ((m:ℝ)-1) + ((n:ℝ)⁻¹ - 1) = (m:ℝ)/n - 1) from by field_simp; ring]
    ring
  rw [hderiv_eq] at hchain
  exact hchain.congr (fun z hz => (hfun_eq z hz).symm) (hfun_eq x hx).symm

/-- Exercise 10.4.2(b) -/
theorem tendsto_rpow_div (q:ℚ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^(q:ℝ)-1)/(x-1)) (nhds q) := by
  have := hasDerivWithinAt_rpow_ratCast q (Set.mem_Ioi.mpr zero_lt_one)
  rw [HasDerivWithinAt.iff] at this
  simp at this
  exact this

/-- Exercise 10.4.3(a) -/
theorem tendsto_rpow_div_real (α:ℝ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^α-1^α)/(x-1)) (nhds α) := by
  simp only [Real.one_rpow]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨p, hp_lt, hp_α⟩ := exists_rat_btwn (show α - ε/2 < α by linarith)
  obtain ⟨q, hα_q, hq_lt⟩ := exists_rat_btwn (show α < α + ε/2 by linarith)
  have hp_le : (p:ℝ) ≤ α := le_of_lt hp_α
  have hα_le : α ≤ (q:ℝ) := le_of_lt hα_q
  have hP := tendsto_rpow_div p
  have hQ := tendsto_rpow_div q
  rw [Metric.tendsto_nhds] at hP hQ
  filter_upwards [hP (ε/2) (by linarith), hQ (ε/2) (by linarith), self_mem_nhdsWithin]
    with x hxP hxQ hxmem
  obtain ⟨hxpos, hxne⟩ : x > 0 ∧ x ≠ 1 := by
    rcases hxmem with ⟨hpos, hne⟩
    exact ⟨hpos, by grind⟩
  have hsandwich :
      (x^(p:ℝ) - 1)/(x - 1) ≤ (x^α - 1)/(x - 1) ∧
      (x^α - 1)/(x - 1) ≤ (x^(q:ℝ) - 1)/(x - 1) := by
    rcases lt_or_gt_of_ne hxne with hxlt | hxgt
    · have hx_le : x ≤ 1 := le_of_lt hxlt
      have hpα : x^α ≤ x^(p:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hx_le hp_le
      have hαq : x^(q:ℝ) ≤ x^α :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hx_le hα_le
      have hxm1_neg : x - 1 < 0 := by linarith
      constructor
      · rw [div_le_div_right_of_neg hxm1_neg]; linarith
      · rw [div_le_div_right_of_neg hxm1_neg]; linarith
    · have hpα : x^(p:ℝ) ≤ x^α := by
        rw [Real.rpow_le_rpow_left_iff hxgt]; exact hp_le
      have hαq : x^α ≤ x^(q:ℝ) := by
        rw [Real.rpow_le_rpow_left_iff hxgt]; exact hα_le
      have hxm1_pos : 0 < x - 1 := by linarith
      constructor <;> exact (div_le_div_iff_of_pos_right hxm1_pos).mpr (by linarith)
  rw [Real.dist_eq] at hxP hxQ ⊢
  have hxP' := abs_lt.mp hxP
  have hxQ' := abs_lt.mp hxQ
  rw [abs_lt]
  exact ⟨by linarith [hsandwich.1], by linarith [hsandwich.2]⟩

/-- Exercise 10.4.3(b) -/
example (α:ℝ) {x:ℝ} (hx: x ∈ Set.Ioi 0) : HasDerivWithinAt (fun x:ℝ ↦ x^α) (α * x^(α-1)) (.Ioi 0) x := by
  rw [HasDerivWithinAt.iff]
  have hxpos : (0:ℝ) < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have ha : Filter.Tendsto (fun t:ℝ ↦ (t^α - 1)/(t - 1))
              (nhdsWithin 1 (Set.Ioi 0 \ {1})) (nhds α) := by
    have := tendsto_rpow_div_real α
    simp only [Real.one_rpow] at this
    exact this
  have ha' : Filter.Tendsto (fun t:ℝ ↦ x^(α-1) * ((t^α - 1)/(t - 1)))
                (nhdsWithin 1 (Set.Ioi 0 \ {1})) (nhds (x^(α-1) * α)) :=
    ha.const_mul _
  have hsub : Filter.Tendsto (fun y:ℝ ↦ y/x)
                (nhdsWithin x (Set.Ioi 0 \ {x})) (nhdsWithin 1 (Set.Ioi 0 \ {1})) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Filter.Tendsto (fun y:ℝ ↦ y/x) (nhds x) (nhds 1) := by
        have h2 : Filter.Tendsto (fun y:ℝ ↦ y/x) (nhds x) (nhds (x/x)) :=
          (continuous_id.div_const x).tendsto x
        simpa [div_self hxne] using h2
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp at hy ⊢
      constructor
      . field_simp; linarith
      . field_simp; exact hy.2
  have hcomp := ha'.comp hsub
  rw [mul_comm α]
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy_pos : 0 < y := hy.1
  simp only [Function.comp_apply]
  rw [Real.div_rpow hy_pos.le hxpos.le]
  have hx_α : x ^ α ≠ 0 := (Real.rpow_pos_of_pos hxpos α).ne'
  have hxm1 : x ^ (α - 1) = x ^ α / x := by
    rw [show (α - 1 : ℝ) = α + (-1) by ring, Real.rpow_add hxpos, Real.rpow_neg_one]
    ring
  rw [hxm1]
  field_simp

end Chapter10
