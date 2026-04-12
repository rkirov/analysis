import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_9_3
/-!
# Analysis I, Section 9.4: Continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuity of functions, using the Mathlib notions

-/

namespace Chapter9

/--
Definition 9.4.1.  Here we use the Mathlib definition of continuity.  The hypothesis {lean}`x₀ ∈ X` is not needed!
-/
theorem ContinuousWithinAt.iff (X:Set ℝ) (f: ℝ → ℝ)  (x₀:ℝ) :
  ContinuousWithinAt f X x₀ ↔ Convergesto X f (f x₀) x₀ := by
  rw [ContinuousWithinAt.eq_1, Convergesto.iff, nhdsWithin.eq_1]

#check ContinuousOn.eq_1
#check continuousOn_univ
#check continuousWithinAt_univ

/-- Example 9.4.2 --/
example (c x₀:ℝ) : ContinuousWithinAt (fun _ ↦ c) .univ x₀ := by
  rw [ContinuousWithinAt.iff]
  exact Convergesto.const Set.univ x₀ c

example (c x₀:ℝ) : ContinuousAt (fun _ ↦ c) x₀ := by
  rw [ContinuousAt]
  have := Convergesto.const Set.univ x₀ c
  rw [Convergesto.iff] at this
  simp

example (c:ℝ) : ContinuousOn (fun _:ℝ ↦ c) .univ := by
  rw [ContinuousOn.eq_1]
  intro x hx
  exact continuousWithinAt_const

example (c:ℝ) : Continuous (fun _:ℝ ↦ c) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact continuousAt_const

/-- Example 9.4.3 --/
example : Continuous (fun x:ℝ ↦ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact continuousAt_id

/-- Example 9.4.4 --/
example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt Real.sign x₀ := by
  rw [ContinuousAt]
  rcases ne_iff_lt_or_gt.mp h with h | h
  · have hev : ∀ᶠ x in nhds x₀, Real.sign x = -1 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp only [Real.sign, Set.mem_Iio] at hx ⊢
      rw [if_pos hx]
    have : Real.sign x₀ = -1 := by simp [Real.sign, if_pos h]
    rw [this]
    exact tendsto_const_nhds.congr' (by filter_upwards [hev] with x hx; exact hx.symm)
  · have hev : ∀ᶠ x in nhds x₀, Real.sign x = 1 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp only [Real.sign, Set.mem_Ioi] at hx ⊢
      rw [if_neg (not_lt.mpr hx.le), if_pos hx]
    have : Real.sign x₀ = 1 := by simp [Real.sign, if_neg (not_lt.mpr h.le), if_pos h]
    rw [this]
    exact tendsto_const_nhds.congr' (by filter_upwards [hev] with x hx; exact hx.symm)

example  :¬ ContinuousAt Real.sign 0 := by
  intro h
  have hseq : Filter.Tendsto (fun n:ℕ ↦ (1:ℝ)/(↑n+1)) Filter.atTop (nhds 0) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ).atTop_add
      (tendsto_const_nhds (x := (1:ℝ)))).inv_tendsto_atTop
    simp only [inv_eq_one_div] at this
    exact this
  have hcomp := h.tendsto.comp hseq
  simp only [Function.comp_def] at hcomp
  have hsign : (fun n:ℕ ↦ Real.sign (1 / (↑n + 1))) = fun _ ↦ 1 := by
    ext n; exact Real.sign_of_pos (by positivity)
  rw [hsign] at hcomp
  have := tendsto_nhds_unique hcomp tendsto_const_nhds
  simp [Real.sign] at this

/-- Example 9.4.5 --/
example (x₀:ℝ) : ¬ ContinuousAt f_9_3_21 x₀ := by
  intro h
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp h (1/2) (by linarith)
  -- rational in ball: f_9_3_21 = 1
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self x₀ hδ)
  have hq_dist : dist (↑q) x₀ < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have hq_val : f_9_3_21 ↑q = 1 := by simp [f_9_3_21]
  -- irrational in ball: f_9_3_21 = 0
  obtain ⟨y, hy_irr, hy_mem⟩ := dense_irrational.exists_mem_open Metric.isOpen_ball
    ⟨x₀, Metric.mem_ball_self hδ⟩
  rw [Set.mem_setOf_eq] at hy_irr
  have hy_val : f_9_3_21 y = 0 := by
    unfold f_9_3_21; rw [if_neg]; rintro ⟨r, -, hr⟩; exact hy_irr ⟨r, hr⟩
  have h1 := hball hq_dist
  have h2 := hball (show dist y x₀ < δ from hy_mem)
  rw [hq_val] at h1; rw [hy_val] at h2
  rw [Real.dist_eq] at h1 h2
  -- f_9_3_21 x₀ is either 0 or 1; both contradict h1 and h2
  have : f_9_3_21 x₀ = 0 ∨ f_9_3_21 x₀ = 1 := by unfold f_9_3_21; split <;> simp
  rcases this with h | h <;> rw [h] at h1 h2 <;> simp at h1 h2 <;> linarith

/-- Example 9.4.6 --/
noncomputable abbrev f_9_4_6 (x:ℝ) : ℝ := if x ≥ 0 then 1 else 0

example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt f_9_4_6 x₀ := by
  rcases ne_iff_lt_or_gt.mp h with h | h
  · have hev : ∀ᶠ x in nhds x₀, f_9_4_6 x = 0 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp only [f_9_4_6, Set.mem_Iio] at hx ⊢
      rw [if_neg (not_le.mpr hx)]
    exact continuousAt_const.congr (by filter_upwards [hev] with x hx; exact hx.symm)
  · have hev : ∀ᶠ x in nhds x₀, f_9_4_6 x = 1 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp only [f_9_4_6, Set.mem_Ioi] at hx ⊢
      rw [if_pos hx.le]
    exact continuousAt_const.congr (by filter_upwards [hev] with x hx; exact hx.symm)


example : ¬ ContinuousAt f_9_4_6 0 := by
  intro h
  have h' := Metric.continuousAt_iff.mp h (1/2) (by linarith)
  obtain ⟨δ, hδ, hball⟩ := h'
  have h2 := hball (show dist (-δ/2) 0 < δ from by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith)
  have hv1 : f_9_4_6 (-δ / 2) = 0 := by simp [f_9_4_6, show ¬ -δ / 2 ≥ 0 from by linarith]
  have hv2 : f_9_4_6 0 = 1 := by simp [f_9_4_6]
  rw [hv1, hv2] at h2
  norm_num at h2

example : ContinuousWithinAt f_9_4_6 (.Ici 0) 0 := by
  apply ContinuousWithinAt.congr (f := fun _ ↦ 1) continuousWithinAt_const
  · intro x hx; simp [f_9_4_6, show x ≥ 0 from hx]
  · simp [f_9_4_6]

/-- Proposition 9.4.7 / Exercise 9.4.1. -/
theorem ContinuousWithinAt.tfae (X:Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  [
    ContinuousWithinAt f X x₀,
    ∀ a:ℕ → ℝ, (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds x₀) → Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)),
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| < δ → |f x - f x₀| < ε,
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| ≤ δ → |f x - f x₀| ≤ ε
  ].TFAE := by
  tfae_have 1 ↔ 2 := by
    constructor <;> (
      rw [ContinuousWithinAt.iff]
      rw [Convergesto.iff_conv]
      simp
    )
  tfae_have 2 ↔ 3 := by
    rw [← Convergesto.iff_conv]
    unfold Convergesto Real.CloseNear Real.CloseFn
    simp [abs_lt]
    -- funny enough there are just two arguments swapped, but we need to go through a big dance to finish
    -- the proof
    constructor <;> (
      intro h ε hε; obtain ⟨δ, hδ, h⟩ := h ε hε
      exact ⟨δ, hδ, fun x hx h1 h2 => h x hx (by linarith) (by linarith)⟩)
  tfae_have 3 ↔ 4 := by
    constructor
    . intro h ε hε; obtain ⟨δ, hδ, h⟩ := h ε hε
      use δ / 2, by positivity
      intro x hx hδ
      specialize h x hx (by linarith)
      exact h.le
    . intro h ε hε; obtain ⟨δ, hδ, h⟩ := h (ε / 2) (by positivity)
      use δ, hδ
      intro x hx hδ
      specialize h x hx (by linarith)
      linarith
  tfae_finish

/-- Remark 9.4.8 --/
theorem _root_.Filter.Tendsto.comp_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h_cont: ContinuousWithinAt f X x₀) {a: ℕ → ℝ} (ha: ∀ n, a n ∈ X)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)):
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)) := by
  have := (ContinuousWithinAt.tfae X f x₀).out 0 1
  grind

/- Proposition 9.4.9 -/
theorem ContinuousWithinAt.add {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f + g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.add hg using 1

theorem ContinuousWithinAt.sub {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f - g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.sub hg using 1

theorem ContinuousWithinAt.max {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (max f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.max hg using 1

theorem ContinuousWithinAt.min {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (min f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.min hg using 1

theorem ContinuousWithinAt.mul' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f * g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.mul hg using 1

theorem ContinuousWithinAt.div' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}(hM: g x₀ ≠ 0)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f / g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.div hM hg using 1

/-- Proposition 9.4.10 / Exercise 9.4.3  -/
theorem Continuous.exp {a:ℝ} (ha: a>0) : Continuous (fun x:ℝ ↦ a ^ x) := by
  sorry

/-- Proposition 9.4.11 / Exercise 9.4.4 -/
theorem Continuous.exp' (p:ℝ) : ContinuousOn (fun x:ℝ ↦ x ^ p) (.Ioi 0) := by
  sorry

/-- Proposition 9.4.12 -/
theorem Continuous.abs : Continuous (fun x:ℝ ↦ |x|) := by
  sorry -- TODO

/-- Proposition 9.4.13 / Exercise 9.4.5 -/
theorem ContinuousWithinAt.comp {X Y: Set ℝ} {f g:ℝ → ℝ} (hf: ∀ x ∈ X, f x ∈ Y) (x₀:ℝ)
  (hf_cont: ContinuousWithinAt f X x₀) (hg_cont: ContinuousWithinAt g Y (f x₀)): ContinuousWithinAt (g ∘ f) X x₀ := by sorry

/-- Example 9.4.14 -/
example : Continuous (fun x:ℝ ↦ 3*x + 1) := by
  sorry

example : Continuous (fun x:ℝ ↦ (5:ℝ)^x) := by
  sorry

example : Continuous (fun x:ℝ ↦ (5:ℝ)^(3*x+1)) := by
  sorry

example : Continuous (fun x:ℝ ↦ |x^2-8*x+8|^(Real.sqrt 2) / (x^2 + 1)) := by
  sorry

/-- Exercise 9.4.6 -/
theorem ContinuousOn.restrict {X Y:Set ℝ} {f: ℝ → ℝ} (hY: Y ⊆ X) (hf: ContinuousOn f X) : ContinuousOn f Y := by
  sorry

/-- Exercise 9.4.7 -/
theorem Continuous.polynomial {n:ℕ} (c: Fin n → ℝ) : Continuous (fun x:ℝ ↦ ∑ i, c i * x ^ (i:ℕ)) := by
  sorry
