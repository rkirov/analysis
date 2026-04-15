import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_9_3
import Analysis.Section_6_epilogue
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
  rw [continuous_iff_continuousAt]
  intro x
  rw [← continuousWithinAt_univ]
  -- todo: why can't this be inlined
  have := (ContinuousWithinAt.tfae .univ (fun x ↦ a ^ x) x).out 0 2
  rw [this]; clear this
  intro ε hε
  -- ε-δ continuity of `t ↦ a^t` at 0, proved from Section 6.5's
  -- `Sequence.lim_of_roots` (a^(1/(n+1)) → 1) applied to both `a` and `a⁻¹`,
  -- plus monotonicity of rpow. Everything below the bridge to Mathlib's
  -- `Filter.Tendsto` uses only basic rpow arithmetic.
  have ratPow_continuous_at_zero :
      ∀ η > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ → |a ^ t - 1| < η := by
    intro η hη
    -- Transport `lim_of_roots` for `a` and `a⁻¹` into Mathlib's filter form.
    have get_N : ∀ b > (0:ℝ), ∃ N : ℕ, ∀ n ≥ N, |b ^ (1/(n+1:ℝ)) - 1| < η := by
      intro b hb
      have h := (Chapter6.Sequence.tendsto_iff_Tendsto _ _).mp
        (Chapter6.Sequence.lim_of_roots hb)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h η hη
      refine ⟨N, fun n hn => ?_⟩
      have := hN n hn; rwa [Real.dist_eq] at this
    obtain ⟨N₁, hN₁⟩ := get_N a ha
    obtain ⟨N₂, hN₂⟩ := get_N a⁻¹ (inv_pos.mpr ha)
    set N := max N₁ N₂
    refine ⟨1/(N+1:ℝ), by positivity, ?_⟩
    intro t ht
    -- `a^δ` and `a^(-δ)` are both within η of 1.
    have hup : |a ^ (1/(N+1:ℝ)) - 1| < η := hN₁ N (le_max_left _ _)
    have hdn : |a ^ (-(1/(N+1:ℝ))) - 1| < η := by
      have := hN₂ N (le_max_right _ _)
      rwa [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le] at this
    -- Sandwich `a^t` between `a^(-δ)` and `a^δ` (order depending on `a ≥ 1` or `a ≤ 1`).
    obtain ⟨htl, htr⟩ := abs_le.mp ht.le
    rw [abs_lt] at hup hdn ⊢
    rcases le_total 1 a with h1 | h1
    · have h_le := Real.rpow_le_rpow_of_exponent_le h1 htr
      have h_ge := Real.rpow_le_rpow_of_exponent_le h1 htl
      exact ⟨by linarith, by linarith⟩
    · have h_le := Real.rpow_le_rpow_of_exponent_ge ha h1 htl
      have h_ge := Real.rpow_le_rpow_of_exponent_ge ha h1 htr
      exact ⟨by linarith, by linarith⟩
  have hax : a ^ x > 0 := Real.rpow_pos_of_pos ha x
  obtain ⟨δ, hδ, hδbound⟩ := ratPow_continuous_at_zero (ε / a ^ x) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro y _ h1
  -- Key identity: a^y - a^x = a^x * (a^(y-x) - 1).
  have hfactor : a ^ y - a ^ x = a ^ x * (a ^ (y - x) - 1) := by
    rw [Real.rpow_sub ha, mul_sub, mul_one, mul_div_cancel₀ _ hax.ne']
  have hclose : |a ^ (y - x) - 1| < ε / a ^ x :=
    hδbound (y - x) (by simpa [abs_sub_comm] using h1)
  calc |a ^ y - a ^ x|
      = a ^ x * |a ^ (y - x) - 1| := by
        rw [hfactor, abs_mul, abs_of_pos hax]
    _ < a ^ x * (ε / a ^ x) := by gcongr
    _ = ε := mul_div_cancel₀ _ hax.ne'


/-- Proposition 9.4.11 / Exercise 9.4.4 -/
theorem Continuous.exp' (p:ℝ) : ContinuousOn (fun x:ℝ ↦ x ^ p) (.Ioi 0) := by
  -- Base varies, exponent fixed: `u^n → 1` as `u → 1`, by induction using 9.3.14 (mul).
  have hlim_at_1_nat (n : ℕ) : Filter.Tendsto (fun u:ℝ ↦ u ^ n) (nhds 1) (nhds 1) := by
    have key : Convergesto .univ (fun u:ℝ ↦ u ^ n) 1 1 := by
      induction n with
      | zero => simpa using Convergesto.const Set.univ 1 1
      | succ k ih =>
          have := (Convergesto.id Set.univ 1).mul ih
          simpa [pow_succ, mul_comm] using this
    have := (Convergesto.iff _ _ _ _).mp key
    simpa [nhdsWithin_univ] using this
  have hlim_at_1_int (n : ℤ) :
      Filter.Tendsto (fun u:ℝ ↦ u ^ n) (nhdsWithin 1 (Set.Ioi 0)) (nhds 1) := by
    rcases Int.eq_nat_or_neg n with ⟨m, hm | hm⟩
    · subst hm; simpa [zpow_natCast] using (hlim_at_1_nat m).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    · subst hm
      have hnat := (hlim_at_1_nat m).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      have hinv : Filter.Tendsto (fun u:ℝ ↦ (u ^ m)⁻¹) (nhdsWithin 1 (Set.Ioi 0)) (nhds 1) := by
        simpa using hnat.inv₀ (by norm_num)
      refine hinv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u _
      rw [zpow_neg, zpow_natCast]
  -- b-th root at 1: sandwich gives `|u^(1/b) - 1| ≤ |u - 1|` for `u > 0`, `b ≥ 1`.
  have hlim_at_1_root (b : ℕ) (hb : b ≥ 1) :
      Filter.Tendsto (fun u:ℝ ↦ u ^ ((1:ℝ)/b)) (nhdsWithin 1 (Set.Ioi 0)) (nhds 1) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε, hε, fun u hu hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hb' : (0:ℝ) < 1/b := by positivity
    have hble : (1:ℝ)/b ≤ 1 := by rw [div_le_one (by exact_mod_cast hb)]; exact_mod_cast hb
    -- In both branches, `u^(1/b)` lies between `u` and `1`, so `|u^(1/b) - 1| ≤ |u - 1|`.
    rcases le_total 1 u with h1 | h1
    · have hlow : (1:ℝ) ≤ u ^ ((1:ℝ)/b) := Real.one_le_rpow h1 hb'.le
      have hup : u ^ ((1:ℝ)/b) ≤ u := by
        simpa using Real.rpow_le_rpow_of_exponent_le h1 hble
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u - 1)] at hdist
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u ^ ((1:ℝ)/b) - 1)]
      linarith
    · have hlow : u ^ ((1:ℝ)/b) ≤ 1 := Real.rpow_le_one hu.le h1 hb'.le
      have hup : u ≤ u ^ ((1:ℝ)/b) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hu h1 hble
      rw [abs_of_nonpos (by linarith : u - 1 ≤ 0)] at hdist
      rw [abs_of_nonpos (by linarith : u ^ ((1:ℝ)/b) - 1 ≤ 0)]
      linarith
  -- Rational exponent: compose `u ↦ u^q.num` (int) with `v ↦ v^(1/q.den)` (root).
  have hlim_at_1_rat (q : ℚ) :
      Filter.Tendsto (fun u:ℝ ↦ u ^ (q:ℝ)) (nhdsWithin 1 (Set.Ioi 0)) (nhds 1) := by
    have hmap : Filter.Tendsto (fun u:ℝ ↦ (u ^ (q.num:ℤ) : ℝ))
        (nhdsWithin 1 (Set.Ioi 0)) (nhdsWithin 1 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hlim_at_1_int q.num)
        (by filter_upwards [self_mem_nhdsWithin] with u hu using zpow_pos (a := u) hu _)
    refine ((hlim_at_1_root q.den q.pos).comp hmap).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Function.comp_apply]
    rw [show (q:ℝ) = (q.num:ℝ) / (q.den:ℝ) by rw [Rat.cast_def],
        ← Real.rpow_intCast u q.num, ← Real.rpow_mul hu.le]
    congr 1; field_simp
  -- Real exponent `p`: squeeze `u^p` between `u^q₁` and `u^q₂` for rationals q₁ < p < q₂.
  have hlim_at_1 : Filter.Tendsto (fun u:ℝ ↦ u ^ p) (nhdsWithin 1 (Set.Ioi 0)) (nhds 1) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨q₁, -, hq₁r⟩ := exists_rat_btwn (show p - 1 < p by linarith)
    obtain ⟨q₂, hq₂l, -⟩ := exists_rat_btwn (show p < p + 1 by linarith)
    obtain ⟨δ₁, hδ₁, h₁⟩ :=
      (Metric.tendsto_nhdsWithin_nhds.mp (hlim_at_1_rat q₁)) ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ :=
      (Metric.tendsto_nhdsWithin_nhds.mp (hlim_at_1_rat q₂)) ε hε
    refine ⟨min δ₁ δ₂, by positivity, fun u hu hdist => ?_⟩
    have hu' : (0:ℝ) < u := hu
    have hd₁ := h₁ hu (lt_of_lt_of_le hdist (min_le_left _ _))
    have hd₂ := h₂ hu (lt_of_lt_of_le hdist (min_le_right _ _))
    rw [Real.dist_eq] at hd₁ hd₂ ⊢; rw [abs_lt] at hd₁ hd₂ ⊢
    rcases le_total 1 u with h1 | h1
    · exact ⟨by linarith [Real.rpow_le_rpow_of_exponent_le h1 hq₁r.le],
             by linarith [Real.rpow_le_rpow_of_exponent_le h1 hq₂l.le]⟩
    · exact ⟨by linarith [Real.rpow_le_rpow_of_exponent_ge hu' h1 hq₂l.le],
             by linarith [Real.rpow_le_rpow_of_exponent_ge hu' h1 hq₁r.le]⟩
  -- Full continuity: `x^p = (x/y)^p · y^p`, and `x/y → 1` as `x → y`.
  intro y hy
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hy' : (0:ℝ) < y := hy
  have hyp : (0:ℝ) < y ^ p := Real.rpow_pos_of_pos hy' _
  obtain ⟨η, hη, hηbd⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hlim_at_1) (ε / y ^ p) (by positivity)
  refine ⟨η * y, by positivity, fun x hx hdist => ?_⟩
  have hx' : (0:ℝ) < x := hx
  have hxy : (0:ℝ) < x / y := div_pos hx' hy'
  have hdist_ratio : dist (x / y) 1 < η := by
    rw [Real.dist_eq, show (x / y - 1 : ℝ) = (x - y) / y by field_simp,
        abs_div, abs_of_pos hy', div_lt_iff₀ hy']
    rw [Real.dist_eq] at hdist; linarith
  have hclose := hηbd hxy hdist_ratio
  have hfactor : x ^ p = (x / y) ^ p * y ^ p := by
    rw [← Real.mul_rpow hxy.le hy'.le]; congr 1; field_simp
  rw [Real.dist_eq] at hclose ⊢
  calc |x ^ p - y ^ p|
      = |(x / y) ^ p - 1| * y ^ p := by
        rw [hfactor]; rw [show (x / y) ^ p * y ^ p - y ^ p = ((x / y) ^ p - 1) * y ^ p by ring,
          abs_mul, abs_of_pos hyp]
    _ < (ε / y ^ p) * y ^ p := by gcongr
    _ = ε := by field_simp

/-- Proposition 9.4.12 -/
theorem Continuous.abs : Continuous (fun x:ℝ ↦ |x|) := by
  sorry -- TODO

/-- Proposition 9.4.13 / Exercise 9.4.5 -/
theorem ContinuousWithinAt.comp {X Y: Set ℝ} {f g:ℝ → ℝ} (hf: ∀ x ∈ X, f x ∈ Y) (x₀:ℝ)
  (hf_cont: ContinuousWithinAt f X x₀) (hg_cont: ContinuousWithinAt g Y (f x₀)):
  ContinuousWithinAt (g ∘ f) X x₀ := by
  -- cool filter proof, but probably the book intented the proof below.
  -- rw [ContinuousWithinAt] at hg_cont ⊢
  -- have hf_within : Filter.Tendsto f (nhdsWithin x₀ X) (nhdsWithin (f x₀) Y) := by
  --   exact ContinuousWithinAt.tendsto_nhdsWithin hf_cont hf
  -- exact hg_cont.comp hf_within
  rw [ContinuousWithinAt.iff] at hf_cont hg_cont ⊢
  rw [Convergesto] at hf_cont hg_cont ⊢
  intro ε hε
  specialize hg_cont ε hε
  rw [Real.CloseNear] at hg_cont ⊢
  obtain ⟨δ', hδ', h'⟩ := hg_cont
  specialize hf_cont δ' hδ'
  rw [Real.CloseNear] at hf_cont
  obtain ⟨δ, hδ, h⟩ := hf_cont
  use δ, hδ
  rw [Real.CloseFn] at h h' ⊢
  simp at h h' ⊢
  intro x hx h1 h2
  specialize h' (f x) (hf x hx)
  specialize h x hx h1 h2
  rw [abs_lt] at h
  exact h' (by linarith) (by linarith)

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
