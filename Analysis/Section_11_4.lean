import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4: Basic properties of the Riemann integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral.

-/

namespace Chapter11
open Chapter9

/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem lower_inter_add {I: BoundedInterval} {f g:ℝ → ℝ}
  (hf: BddOn f I) (hg: BddOn g I) :
  lower_integral (f + g) I ≥ lower_integral f I + lower_integral g I := by
  have hfg : BddOn (f + g) I := BddOn.add f g I hf hg
  -- Each lower sum for `f` plus each lower sum for `g` is a lower sum for `f + g`
  -- (the sum of two minorants is a minorant, and `integ` is additive), so the sup
  -- for `f + g` dominates the sumset of the two sups.
  repeat rw [lower_integral]
  rw [← csSup_add (integral_bound_lower_nonempty hf) (integral_bound_above hf)
        (integral_bound_lower_nonempty hg) (integral_bound_above hg)]
  apply csSup_le_csSup (integral_bound_above hfg)
    ((integral_bound_lower_nonempty hf).add (integral_bound_lower_nonempty hg))
  rintro x hx
  obtain ⟨a, ⟨g₁, ⟨hmin₁, hpc₁⟩, rfl⟩, b, ⟨g₂, ⟨hmin₂, hpc₂⟩, rfl⟩, rfl⟩ := Set.mem_add.mp hx
  exact ⟨g₁ + g₂, ⟨fun x hx ↦ add_le_add (hmin₁ x hx) (hmin₂ x hx), hpc₁.add hpc₂⟩,
    PiecewiseConstantOn.integ_add hpc₁ hpc₂⟩

theorem upper_inter_add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: BddOn f I) (hg: BddOn g I) :
  upper_integral (f + g) I ≤ upper_integral f I + upper_integral g I := by
  have hfg : BddOn (f + g) I := BddOn.add f g I hf hg
  repeat rw [upper_integral]
  rw [← csInf_add (integral_bound_upper_nonempty hf) (integral_bound_below hf)
        (integral_bound_upper_nonempty hg) (integral_bound_below hg)]
  apply csInf_le_csInf (integral_bound_below hfg)
    ((integral_bound_upper_nonempty hf).add (integral_bound_upper_nonempty hg))
  rintro x hx
  obtain ⟨a, ⟨g₁, ⟨hmaj₁, hpc₁⟩, rfl⟩, b, ⟨g₂, ⟨hmaj₂, hpc₂⟩, rfl⟩, rfl⟩ := Set.mem_add.mp hx
  exact ⟨g₁ + g₂, ⟨fun x hx ↦ add_le_add (hmaj₁ x hx) (hmaj₂ x hx), hpc₁.add hpc₂⟩,
    PiecewiseConstantOn.integ_add hpc₁ hpc₂⟩

theorem IntegrableOn.add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  have hle : lower_integral (f + g) I ≥ lower_integral f I + lower_integral g I := lower_inter_add hf.1 hg.1
  have hge : upper_integral (f + g) I ≤ upper_integral f I + upper_integral g I := upper_inter_add hf.1 hg.1
  have : IntegrableOn (f + g) I := by
    unfold IntegrableOn at hf hg
    have hb : BddOn (f + g) I := BddOn.add f g I hf.1 hg.1
    rw [IntegrableOn]
    use hb
    have hle' : lower_integral (f + g) I ≤ upper_integral (f + g) I := lower_integral_le_upper hb
    linarith
  use this
  have hlf := hf.2
  have hlg := hg.2
  have hluadd := this.2
  repeat rw [integ]
  linarith

open scoped Pointwise in
theorem mul_const_upper_pos {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hc: 0 < c) :
  upper_integral (c • f) I = c * upper_integral f I := by
  repeat rw [upper_integral]
  -- Scaling by `c > 0` is a bijection on majorants (`g ↦ c⁻¹ • g`), so the set of
  -- majorant integrals for `c • f` is exactly `c •` the set for `f`.
  have hset : (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g (c • f) I ∧ PiecewiseConstantOn g I}
      = c • ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_smul_set]
    constructor
    · rintro ⟨g, ⟨hmaj, hpc⟩, rfl⟩
      refine ⟨_, ⟨c⁻¹ • g, ⟨fun x hx ↦ ?_, hpc.smul c⁻¹⟩, rfl⟩, ?_⟩
      · have h := hmaj x hx
        simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
        rwa [le_inv_mul_iff₀ hc]
      · rw [PiecewiseConstantOn.integ_smul c⁻¹ hpc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨t, ⟨g, ⟨hmaj, hpc⟩, rfl⟩, rfl⟩
      refine ⟨c • g, ⟨fun x hx ↦ ?_, hpc.smul c⟩, ?_⟩
      · have h := hmaj x hx
        simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
        exact mul_le_mul_of_nonneg_left h hc.le
      · rw [PiecewiseConstantOn.integ_smul c hpc, smul_eq_mul]
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

open scoped Pointwise in
theorem mul_const_lower_pos {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hc: 0 < c) :
  lower_integral (c • f) I = c * lower_integral f I := by
  repeat rw [lower_integral]
  have hset : (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g (c • f) I ∧ PiecewiseConstantOn g I}
      = c • ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_smul_set]
    constructor
    · rintro ⟨g, ⟨hmin, hpc⟩, rfl⟩
      refine ⟨_, ⟨c⁻¹ • g, ⟨fun x hx ↦ ?_, hpc.smul c⁻¹⟩, rfl⟩, ?_⟩
      · have h := hmin x hx
        simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
        rwa [inv_mul_le_iff₀ hc]
      · rw [PiecewiseConstantOn.integ_smul c⁻¹ hpc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨t, ⟨g, ⟨hmin, hpc⟩, rfl⟩, rfl⟩
      refine ⟨c • g, ⟨fun x hx ↦ ?_, hpc.smul c⟩, ?_⟩
      · have h := hmin x hx
        simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
        exact mul_le_mul_of_nonneg_left h hc.le
      · rw [PiecewiseConstantOn.integ_smul c hpc, smul_eq_mul]
  rw [hset, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]

theorem IntegrableOn.smul_pos {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) (hc: 0 < c):
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  constructor
  . rw [IntegrableOn] at hf ⊢
    have : BddOn (c • f) I := by
      choose M hM using hf.1
      use c * |M|
      intro x hx
      specialize hM _ hx
      simp
      rw [abs_of_pos hc]
      field_simp
      have : M ≤ |M| := le_abs_self M
      linarith
    use this
    rw [mul_const_upper_pos c hc]
    rw [← hf.2]
    rw [mul_const_lower_pos c hc]
  exact mul_const_upper_pos c hc

theorem lower_neg_of_upper {I: BoundedInterval} {f:ℝ → ℝ} :
  lower_integral (-f) I = -upper_integral f I := by
  rw [lower_integral, upper_integral, ← Real.sSup_neg]
  -- the minorants of `-f` are exactly the negations of the majorants of `f`
  congr 1
  ext y
  simp only [Set.mem_neg, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, ⟨hmin, hpc⟩, rfl⟩
    refine ⟨-g, ⟨fun x hx ↦ ?_, ?_⟩, ?_⟩
    · have h := hmin x hx; simp only [Pi.neg_apply] at h ⊢; linarith
    · rw [← neg_one_smul ℝ g]; exact hpc.smul (-1)
    · rw [← neg_one_smul ℝ g, PiecewiseConstantOn.integ_smul (-1) hpc]; ring
  · rintro ⟨g, ⟨hmaj, hpc⟩, hy⟩
    refine ⟨-g, ⟨fun x hx ↦ ?_, ?_⟩, ?_⟩
    · have h := hmaj x hx; simp only [Pi.neg_apply] at h ⊢; linarith
    · rw [← neg_one_smul ℝ g]; exact hpc.smul (-1)
    · rw [← neg_one_smul ℝ g, PiecewiseConstantOn.integ_smul (-1) hpc, hy]; ring

theorem upper_neg_of_lower {I: BoundedInterval} {f:ℝ → ℝ} :
  upper_integral (-f) I = -lower_integral f I := by
  rw [upper_integral, lower_integral, ← Real.sInf_neg]
  congr 1
  ext y
  simp only [Set.mem_neg, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, ⟨hmaj, hpc⟩, rfl⟩
    refine ⟨-g, ⟨fun x hx ↦ ?_, ?_⟩, ?_⟩
    · have h := hmaj x hx; simp only [Pi.neg_apply] at h ⊢; linarith
    · rw [← neg_one_smul ℝ g]; exact hpc.smul (-1)
    · rw [← neg_one_smul ℝ g, PiecewiseConstantOn.integ_smul (-1) hpc]; ring
  · rintro ⟨g, ⟨hmin, hpc⟩, hy⟩
    refine ⟨-g, ⟨fun x hx ↦ ?_, ?_⟩, ?_⟩
    · have h := hmin x hx; simp only [Pi.neg_apply] at h ⊢; linarith
    · rw [← neg_one_smul ℝ g]; exact hpc.smul (-1)
    · rw [← neg_one_smul ℝ g, PiecewiseConstantOn.integ_smul (-1) hpc, hy]; ring

theorem IntegrableOn.neg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I := by
  constructor
  . rw [IntegrableOn] at hf ⊢
    have : BddOn (-f) I := by
      choose M hM using hf.1
      use |M|
      intro x hx
      specialize hM _ hx
      simp only [Pi.neg_apply, abs_neg]
      have : M ≤ |M| := le_abs_self M
      linarith
    use this
    rw [lower_neg_of_upper, upper_neg_of_lower]
    rw [← hf.2]
  . repeat rw [integ]
    rw [upper_neg_of_lower]
    simp
    exact hf.2

/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem IntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  by_cases hc: c > 0
  . exact IntegrableOn.smul_pos c hf hc
  . by_cases hc_zero: c = 0
    . simp [hc_zero]
      have hpc0 : PiecewiseConstantOn (fun _ ↦ (0:ℝ)) I := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      have hint0 := integ_of_piecewise_const hpc0
      have hzerou : upper_integral 0 I = 0 := by
        show integ (fun _ ↦ (0:ℝ)) I = 0
        rw [hint0.2]; show PiecewiseConstantOn.integ (fun _ ↦ (0:ℝ)) I = 0
        rw [PiecewiseConstantOn.integ_const, zero_mul]
      have hzerol : lower_integral 0 I = 0 := by
        show lower_integral (fun _ ↦ (0:ℝ)) I = 0
        rw [hint0.1.2]; exact hzerou
      constructor
      . rw [IntegrableOn] at hf ⊢
        have : BddOn (fun _ ↦ 0) I := by
          use 0; intro x hx; simp
        use this
        rw [hzerou, hzerol]
      . rw [integ, hzerou]
    . -- c < 0: write c • f = -((-c) • f), with -c > 0
      have hcpos : 0 < -c := by linarith [lt_of_le_of_ne (not_lt.mp hc) hc_zero]
      have hpos := IntegrableOn.smul_pos (-c) hf hcpos
      have hneg := IntegrableOn.neg hpos.1
      have heq : -((-c) • f) = c • f := by rw [neg_smul, neg_neg]
      refine ⟨heq ▸ hneg.1, ?_⟩
      rw [← heq, hneg.2, hpos.2]
      ring

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem IntegrableOn.sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  have hng := IntegrableOn.neg hg
  have hadd := IntegrableOn.add hf hng.1
  rw [show f - g = f + (-g) from sub_eq_add_neg f g]
  exact ⟨hadd.1, by rw [hadd.2, hng.2]; ring⟩

/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem IntegrableOn.nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  have hpc0 : PiecewiseConstantOn (fun _ ↦ (0:ℝ)) I := (ConstantOn.of_const' 0 I).piecewiseConstantOn
  have hmin : MinorizesOn (fun _ ↦ (0:ℝ)) f I := fun x hx ↦ hf_nonneg x hx
  have hval : hpc0.integ' = 0 := by
    show PiecewiseConstantOn.integ (fun _ ↦ (0:ℝ)) I = 0
    rw [PiecewiseConstantOn.integ_const, zero_mul]
  have hle := integ_le_lower_integral hf.1 hmin hpc0
  rw [hval] at hle
  rw [integ, ← hf.2]
  exact hle

/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem IntegrableOn.mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: MajorizesOn g f I) :
  integ f I ≤ integ g I := by
  have hsub := IntegrableOn.sub hg hf
  have hnn : 0 ≤ integ (g - f) I :=
    IntegrableOn.nonneg hsub.1 (fun x hx ↦ by simp only [Pi.sub_apply]; linarith [h x hx])
  rw [hsub.2] at hnn
  linarith

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const (c:ℝ) (I: BoundedInterval) :
  IntegrableOn (fun _ ↦ c) I ∧ integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hpc : PiecewiseConstantOn (fun _ ↦ c) I := (ConstantOn.of_const' c I).piecewiseConstantOn
  have hint := integ_of_piecewise_const hpc
  refine ⟨hint.1, ?_⟩
  rw [hint.2]
  show PiecewiseConstantOn.integ (fun _ ↦ c) I = c * |I|ₗ
  rw [PiecewiseConstantOn.integ_const]

/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  IntegrableOn f I ∧ integ f I = (constant_value_on f I) * |I|ₗ := by
  have hpc := hf.piecewiseConstantOn
  have hint := integ_of_piecewise_const hpc
  refine ⟨hint.1, ?_⟩
  rw [hint.2]
  show PiecewiseConstantOn.integ f I = (constant_value_on f I) * |I|ₗ
  rw [PiecewiseConstantOn.integ_const' hf]

open Classical in
theorem of_extend_lower {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  lower_integral (fun x ↦ if x ∈ I then f x else 0) J = lower_integral f I := by
  set F : ℝ → ℝ := fun x ↦ if x ∈ I then f x else 0 with hF
  have hFI : ∀ x ∈ I, F x = f x := fun x hx ↦ by rw [hF]; exact if_pos hx
  have hFout : ∀ x, x ∉ I → F x = 0 := fun x hx ↦ by rw [hF]; exact if_neg hx
  have hFbdd : BddOn F J := by
    choose M hM using h.1
    refine ⟨|M|, fun x hx ↦ ?_⟩
    by_cases hxi : x ∈ I
    · rw [hFI x hxi]; exact le_trans (hM x hxi) (le_abs_self M)
    · rw [hFout x hxi, abs_zero]; exact abs_nonneg M
  unfold lower_integral
  apply le_antisymm
  · -- restrict a minorant `g` of `F` on `J` to `I`: it minorizes `f`, and dropping the
    -- (nonpositive) part of `g` outside `I` only increases the integral.
    apply csSup_le (integral_bound_lower_nonempty hFbdd)
    rintro a ⟨g, ⟨hgmin, hgpc⟩, rfl⟩
    have hgI : PiecewiseConstantOn g I := by
      obtain ⟨P, hP⟩ := hgpc
      refine ⟨P.restrict_inter I hIJ, fun L hL ↦ ?_⟩
      obtain ⟨K', hK'P, rfl⟩ := Finset.mem_image.mp hL
      rw [BoundedInterval.inter_eq]
      exact (hP K' hK'P).mono Set.inter_subset_right
    have hgminI : MinorizesOn g f I := fun x hx ↦ by
      have hgx := hgmin x (hIJ x hx); rwa [hFI x hx] at hgx
    have hmem : PiecewiseConstantOn.integ g I ∈
        (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} :=
      ⟨g, ⟨hgminI, hgI⟩, rfl⟩
    have hle1 : PiecewiseConstantOn.integ g J ≤ PiecewiseConstantOn.integ g I := by
      have hG'pc : PiecewiseConstantOn (fun x ↦ if x ∈ I then g x else 0) J :=
        PiecewiseConstantOn.of_extend hIJ hgI
      rw [← PiecewiseConstantOn.integ_of_extend hIJ hgI]
      refine PiecewiseConstantOn.integ_mono ?_ hgpc hG'pc
      intro x hx
      show g x ≤ if x ∈ I then g x else 0
      split
      next => exact le_refl _
      next hxi => have hgx := hgmin x hx; rwa [hFout x hxi] at hgx
    calc PiecewiseConstantOn.integ g J
        ≤ PiecewiseConstantOn.integ g I := hle1
      _ ≤ _ := le_csSup (integral_bound_above h.1) hmem
  · -- extend a minorant of `f` on `I` by zero: it minorizes `F` on `J` with the same integral.
    apply csSup_le_csSup (integral_bound_above hFbdd) (integral_bound_lower_nonempty h.1)
    rintro a ⟨g, ⟨hgmin, hgpc⟩, rfl⟩
    refine ⟨fun x ↦ if x ∈ I then g x else 0,
      ⟨fun x hx ↦ ?_, PiecewiseConstantOn.of_extend hIJ hgpc⟩,
      PiecewiseConstantOn.integ_of_extend hIJ hgpc⟩
    show (if x ∈ I then g x else 0) ≤ F x
    split
    next hxi => rw [hFI x hxi]; exact hgmin x hxi
    next hxi => exact (hFout x hxi).ge


open Classical in
theorem of_extend_upper {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  upper_integral (fun x ↦ if x ∈ I then f x else 0) J = upper_integral f I := by
  set F : ℝ → ℝ := fun x ↦ if x ∈ I then f x else 0 with hF
  have hFI : ∀ x ∈ I, F x = f x := fun x hx ↦ by rw [hF]; exact if_pos hx
  have hFout : ∀ x, x ∉ I → F x = 0 := fun x hx ↦ by rw [hF]; exact if_neg hx
  have hFbdd : BddOn F J := by
    choose M hM using h.1
    refine ⟨|M|, fun x hx ↦ ?_⟩
    by_cases hxi : x ∈ I
    · rw [hFI x hxi]; exact le_trans (hM x hxi) (le_abs_self M)
    · rw [hFout x hxi, abs_zero]; exact abs_nonneg M
  unfold upper_integral
  apply le_antisymm
  · -- extend a majorant of `f` on `I` by zero: it majorizes `F` on `J` with the same integral.
    apply csInf_le_csInf (integral_bound_below hFbdd) (integral_bound_upper_nonempty h.1)
    rintro a ⟨g, ⟨hgmaj, hgpc⟩, rfl⟩
    refine ⟨fun x ↦ if x ∈ I then g x else 0,
      ⟨fun x hx ↦ ?_, PiecewiseConstantOn.of_extend hIJ hgpc⟩,
      PiecewiseConstantOn.integ_of_extend hIJ hgpc⟩
    show F x ≤ (if x ∈ I then g x else 0)
    split
    next hxi => rw [hFI x hxi]; exact hgmaj x hxi
    next hxi => exact (hFout x hxi).le
  · -- restrict a majorant `g` of `F` on `J` to `I`: it majorizes `f`, and dropping the
    -- (nonnegative) part of `g` outside `I` only decreases the integral.
    apply le_csInf (integral_bound_upper_nonempty hFbdd)
    rintro a ⟨g, ⟨hgmaj, hgpc⟩, rfl⟩
    have hgI : PiecewiseConstantOn g I := by
      obtain ⟨P, hP⟩ := hgpc
      refine ⟨P.restrict_inter I hIJ, fun L hL ↦ ?_⟩
      obtain ⟨K', hK'P, rfl⟩ := Finset.mem_image.mp hL
      rw [BoundedInterval.inter_eq]
      exact (hP K' hK'P).mono Set.inter_subset_right
    have hgmajI : MajorizesOn g f I := fun x hx ↦ by
      have hgx := hgmaj x (hIJ x hx); rwa [hFI x hx] at hgx
    have hmem : PiecewiseConstantOn.integ g I ∈
        (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} :=
      ⟨g, ⟨hgmajI, hgI⟩, rfl⟩
    have hle1 : PiecewiseConstantOn.integ g I ≤ PiecewiseConstantOn.integ g J := by
      rw [← PiecewiseConstantOn.integ_of_extend hIJ hgI]
      refine PiecewiseConstantOn.integ_mono ?_ (PiecewiseConstantOn.of_extend hIJ hgI) hgpc
      intro x hx
      show (if x ∈ I then g x else 0) ≤ g x
      split
      next => exact le_refl _
      next hxi => have hgx := hgmaj x hx; rwa [hFout x hxi] at hgx
    calc sInf ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
        ≤ PiecewiseConstantOn.integ g I := csInf_le (integral_bound_below h.1) hmem
      _ ≤ PiecewiseConstantOn.integ g J := hle1

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  have : BddOn (fun x ↦ if x ∈ I then f x else 0) J := by
    choose M hM using h.1
    use |M|; intro x hx
    by_cases hxi: x ∈ I
    . simp [hxi]
      specialize hM _ hxi
      have : |M| ≥ M := le_abs_self M
      linarith
    . simp [hxi]
  use this
  rw [of_extend_lower hIJ h, of_extend_upper hIJ h]
  exact h.2

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend' {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  repeat rw [integ]
  exact of_extend_upper hIJ h

/-- The restriction of an integrable function to one half of a join is integrable.
This is the integrability half of Theorem 11.4.1(h): the integral identity follows
separately from the extension theorems. -/
theorem IntegrableOn.restrict_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) : IntegrableOn f I := by
  have hIK : I ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_right
  have hbI : BddOn f I := by
    obtain ⟨M, hM⟩ := h.1; exact ⟨M, fun x hx ↦ hM x (hIK x hx)⟩
  refine ⟨hbI, le_antisymm (lower_integral_le_upper hbI) ?_⟩
  -- `upper ≤ lower`: a minorant `p` and majorant `q` of `f` on `K` restrict to `I`, and the
  -- gap `integ q I - integ p I` is bounded by the (smaller) gap on `K`, which is `< ε`.
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨q, hqmaj, hqpc, hqint⟩ :=
    lt_of_gt_upper_integral h.1 (show upper_integral f K < upper_integral f K + ε/2 by linarith)
  obtain ⟨p, hpmin, hppc, hpint⟩ :=
    gt_of_lt_lower_integral h.1 (show upper_integral f K - ε/2 < lower_integral f K by rw [h.2]; linarith)
  have hqI : PiecewiseConstantOn q I := ((PiecewiseConstantOn.of_join hIJK q).mp hqpc).1
  have hpI : PiecewiseConstantOn p I := ((PiecewiseConstantOn.of_join hIJK p).mp hppc).1
  have hqJ : PiecewiseConstantOn q J := ((PiecewiseConstantOn.of_join hIJK q).mp hqpc).2
  have hpJ : PiecewiseConstantOn p J := ((PiecewiseConstantOn.of_join hIJK p).mp hppc).2
  have hub : upper_integral f I ≤ PiecewiseConstantOn.integ q I :=
    upper_integral_le_integ hbI (fun x hx ↦ hqmaj x (hIK x hx)) hqI
  have hlb : PiecewiseConstantOn.integ p I ≤ lower_integral f I :=
    integ_le_lower_integral hbI (fun x hx ↦ hpmin x (hIK x hx)) hpI
  have hqsplit := PiecewiseConstantOn.integ_of_join hIJK hqpc
  have hpsplit := PiecewiseConstantOn.integ_of_join hIJK hppc
  have hpqJ : PiecewiseConstantOn.integ p J ≤ PiecewiseConstantOn.integ q J :=
    PiecewiseConstantOn.integ_mono
      (fun x hx ↦ le_trans (hpmin x (hJK x hx)) (hqmaj x (hJK x hx))) hpJ hqJ
  linarith

open Classical in
/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem IntegrableOn.join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  have hIK : I ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_right
  have hJIK : K.joins J I :=
    ⟨by rw [Set.inter_comm]; exact hIJK.1,
     by rw [hIJK.2.1, Set.union_comm], by rw [hIJK.2.2, add_comm]⟩
  have hI : IntegrableOn f I := restrict_of_join hIJK h
  have hJ : IntegrableOn f J := restrict_of_join hJIK h
  refine ⟨hI, hJ, ?_⟩
  -- `f` agrees on `K` with `(1_I · f) + (1_J · f)`, whose integral splits by the extension theorems.
  have key := (IntegrableOn.of_extend hIK hI).add (IntegrableOn.of_extend hJK hJ)
  rw [IntegrableOn.of_extend' hIK hI, IntegrableOn.of_extend' hJK hJ] at key
  have hEqOn : Set.EqOn
      ((fun x ↦ if x ∈ I then f x else 0) + (fun x ↦ if x ∈ J then f x else 0)) f K := by
    intro x hx
    have hxIJ : x ∈ (I:Set ℝ) ∪ (J:Set ℝ) := by rw [← hIJK.2.1]; exact hx
    simp only [Pi.add_apply]
    rcases hxIJ with hxI | hxJ
    · have hmI : x ∈ I := hxI
      have hxnJ : x ∉ J := fun hJ' ↦
        (Set.mem_empty_iff_false x).mp (hIJK.1 ▸ Set.mem_inter hxI hJ')
      rw [if_pos hmI, if_neg hxnJ, add_zero]
    · have hmJ : x ∈ J := hxJ
      have hxnI : x ∉ I := fun hI' ↦
        (Set.mem_empty_iff_false x).mp (hIJK.1 ▸ Set.mem_inter hI' hxJ)
      rw [if_neg hxnI, if_pos hmJ, zero_add]
  rw [integ_congr hEqOn] at key
  exact key.2

/-- A variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.mono' {I J: BoundedInterval} (hIJ: J ⊆ I)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : IntegrableOn f J := by
  by_cases hJne : (J:Set ℝ).Nonempty
  · -- Split `I = L ⊔ M` and `M = J ⊔ R`, then restrict twice through the joins.
    obtain ⟨L, M, R, hILM, hMJR⟩ := BoundedInterval.exists_join_split hIJ hJne
    have hIML : I.joins M L :=
      ⟨by rw [Set.inter_comm]; exact hILM.1,
       by rw [hILM.2.1, Set.union_comm], by rw [hILM.2.2, add_comm]⟩
    exact restrict_of_join hMJR (restrict_of_join hIML h)
  · -- Empty `J`: every integral over it is squeezed to `0`.
    have hvac : ∀ x ∈ (J:Set ℝ), |f x| ≤ (0:ℝ) := fun x hx ↦ absurd ⟨x, hx⟩ hJne
    have hbdd : BddOn f J := ⟨0, hvac⟩
    refine ⟨hbdd, le_antisymm (lower_integral_le_upper hbdd) ?_⟩
    have h1 := le_lower_integral hvac
    have h2 := upper_integral_le hvac
    simp only [neg_zero, zero_mul] at h1 h2
    linarith

/-- Any bounded interval is its open interior {lit}`Ioo I.a I.b` flanked by a subsingleton endpoint
piece on each side, realized as two successive joins {lit}`I = J ⊔ (Ioo I.a I.b ⊔ J')`. The endpoint
pieces have length zero, hence are subsingletons. -/
theorem BoundedInterval.join_ab (I: BoundedInterval) :
    ∃ J M J': BoundedInterval, Subsingleton J.toSet ∧ Subsingleton J'.toSet ∧
      I.joins J M ∧ M.joins (BoundedInterval.Ioo I.a I.b) J' := by
  have hlen : |BoundedInterval.Ioo I.a I.b|ₗ = |I|ₗ := rfl
  by_cases hab : I.a < I.b
  · have hne : (BoundedInterval.Ioo I.a I.b : Set ℝ).Nonempty := by
      rw [BoundedInterval.set_Ioo]; exact Set.nonempty_Ioo.mpr hab
    obtain ⟨L, M, R, hILM, hMJR⟩ := BoundedInterval.exists_join_split (BoundedInterval.Ioo_subset I) hne
    refine ⟨L, M, R, BoundedInterval.length_of_subsingleton.mpr ?_,
      BoundedInterval.length_of_subsingleton.mpr ?_, hILM, hMJR⟩
    · have h1 := hILM.2.2; have h2 := hMJR.2.2; rw [hlen] at h2
      have := L.length_nonneg; have := R.length_nonneg; linarith
    · have h1 := hILM.2.2; have h2 := hMJR.2.2; rw [hlen] at h2
      have := L.length_nonneg; have := R.length_nonneg; linarith
  · push_neg at hab
    have hIz : |I|ₗ = 0 := max_eq_right (sub_nonpos.mpr hab)
    have hooe : (BoundedInterval.Ioo I.a I.b : Set ℝ) = ∅ := by
      rw [BoundedInterval.set_Ioo, Set.Ioo_eq_empty (not_lt.mpr hab)]
    refine ⟨I, ∅, ∅, BoundedInterval.length_of_subsingleton.mpr hIz,
      BoundedInterval.length_of_subsingleton.mpr
        (BoundedInterval.length_of_empty BoundedInterval.coe_empty),
      ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · rw [BoundedInterval.coe_empty, Set.inter_empty]
    · rw [BoundedInterval.coe_empty, Set.union_empty]
    · rw [BoundedInterval.length_of_empty BoundedInterval.coe_empty, hIz]; ring
    · rw [BoundedInterval.coe_empty, Set.inter_empty]
    · rw [BoundedInterval.coe_empty, hooe, Set.union_empty]
    · rw [BoundedInterval.length_of_empty BoundedInterval.coe_empty, hlen, hIz]; ring

/-- The integral over a subsingleton interval (a point or the empty set) vanishes. -/
theorem integ_of_subsingleton {K : BoundedInterval} {f : ℝ → ℝ} (hK : Subsingleton (K:Set ℝ)) :
    integ f K = 0 := by
  have hlen : |K|ₗ = 0 := BoundedInterval.length_of_subsingleton.mp hK
  obtain ⟨M, hM⟩ : BddOn f K := by
    by_cases hne : (K:Set ℝ).Nonempty
    · obtain ⟨p, hp⟩ := hne
      rw [Set.subsingleton_coe] at hK
      exact ⟨|f p|, fun x hx ↦ by rw [hK hx hp]⟩
    · exact ⟨0, fun x hx ↦ absurd ⟨x, hx⟩ hne⟩
  have hup := upper_integral_le hM
  have hlo := le_lower_integral hM
  have hlu := lower_integral_le_upper ⟨M, hM⟩
  rw [hlen, mul_zero] at hup
  rw [hlen, mul_zero] at hlo
  show upper_integral f K = 0
  linarith

/-- A further variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.eq {I J: BoundedInterval} (hIJ: J ⊆ I)
  (ha: J.a = I.a) (hb: J.b = I.b)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : integ f J = integ f I := by
  -- Each interval has the same integral as its open interior: the two endpoint pieces vanish.
  have key : ∀ {K : BoundedInterval}, IntegrableOn f K →
      integ f K = integ f (BoundedInterval.Ioo K.a K.b) := by
    intro K hK
    obtain ⟨A, M, B, hA, hB, hKAM, hMAB⟩ := BoundedInterval.join_ab K
    have hjoin1 := IntegrableOn.join hKAM hK
    have hjoin2 := IntegrableOn.join hMAB hjoin1.2.1
    rw [hjoin1.2.2, hjoin2.2.2, integ_of_subsingleton hA, integ_of_subsingleton hB]
    ring
  rw [key (IntegrableOn.mono' hIJ h), key h, ha, hb]

/-- A handy little lemma for "epsilon of room" type arguments -/
lemma nonneg_of_le_const_mul_eps {x C:ℝ} (h: ∀ ε>0, x ≤ C * ε) : x ≤ 0 := by
  by_cases hC: C > 0
  . by_contra!
    specialize h (x/(2*C)) (by positivity); convert_to x ≤ x/2 at h; grind
    linarith
  specialize h 1 ?_ <;> grind

/-- Theorem 11.4.3 (Max and min preserve integrability)-/
theorem IntegrableOn.max {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊔ g) I  := by
  -- This proof is written to follow the structure of the original text.
  unfold IntegrableOn at hf hg
  have hmax_bound : BddOn (f ⊔ g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M ⊔ M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sup_apply]
    exact abs_max_le_max_abs_abs.trans (sup_le_sup hM hM')
  have lower_le_upper : 0 ≤ upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I := by linarith [lower_integral_le_upper hmax_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I ≤ 4*ε := by
    choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I
    by grind)
    choose g' hg'min hg'const hg'int using gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by grind)
    choose f'' hf''max hf''const hf''int using lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by grind)
    choose g'' hg''max hg''const hg''int using lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by grind)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := hf''_integ.1.sub hf'_integ.1
    have hg''g'_integ := hg''_integ.1.sub hg'_integ.1
    have hh_IntegrableOn.eq := hf''f'_integ.1.add hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.max hg''const
    have hf''g''_maj : MajorizesOn (f'' ⊔ g'') (f ⊔ g) I := by
      intro x hx
      have hfx := hf''max x hx
      have hgx := hg''max x hx
      simp [hfx, hgx]
      by_contra
      simp at this
      obtain ⟨hfxg, hfxg'⟩ := this
      linarith
    have hf'g'_const := hf'const.max hg'const
    have hf'g'_maj : MinorizesOn (f' ⊔ g') (f ⊔ g) I := by
      intro x hx
      have hfx := hf'min x hx
      have hgx := hg'min x hx
      simp [hfx, hgx]
      by_contra
      simp at this
      obtain ⟨hfxg, hfxg'⟩ := this
      linarith
    have hff'g''_ge := upper_integral_le_integ hmax_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmax_bound hf'g'_maj hf'g'_const
    have : MinorizesOn (f'' ⊔ g'') (f' ⊔ g' + h) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf''max _ hx; specialize hg''max _ hx
      simp [h]; split_ands <;> linarith [le_max_left (f' x) (g' x), le_max_right (f' x) (g' x)]
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := hf'g'_integ.1.add hh_IntegrableOn.eq.1
    rw [MinorizesOn.iff] at this
    linarith [hf''g''_integ.1.mono hf'g'h_integ.1 this]
  exact ⟨ hmax_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩



/-- Theorem 11.4.5 / Exercise 11.4.3.  The objective here is to create a shorter proof than the one above.-/
theorem IntegrableOn.min {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊓ g) I  := by
  have heq : -((-f) ⊔ (-g)) = f ⊓ g := by rw [neg_sup, neg_neg, neg_neg]
  rw [← heq]
  exact ((hf.neg.1.max hg.neg.1).neg).1

/-- Corollary 11.4.4 -/
theorem IntegrableOn.abs {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (abs f) I := by
  have := (IntegrableOn.const 0 I).1
  convert ((hf.max this).sub (hf.min this)).1 using 1
  ext x; obtain h | h := (show f x ≤ 0 ∨ f x ≥ 0 by grind) <;> simp [h]

/-- Theorem 11.4.5 (Products preserve Riemann integrability).
It is convenient to first establish the non-negative case.-/
theorem integ_of_mul_nonneg {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I) (hg_nonneg: MajorizesOn g 0 I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hI : (I:Set ℝ).Nonempty
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    simp_all [Set.not_nonempty_iff_eq_empty]
  unfold IntegrableOn at hf hg
  choose M₁ hM₁ using hf.1
  choose M₂ hM₂ using hg.1
  have hM₁pos : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ hI.some hI.some_mem)
  have hM₂pos : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ hI.some hI.some_mem)
  have hmul_bound : BddOn (f * g) I := by
    use M₁ * M₂; peel hM₁ with x hx hM₁; specialize hM₂ _ hx
    simp [abs_mul]; apply mul_le_mul hM₁ hM₂ <;> positivity
  have lower_le_upper : 0 ≤ upper_integral (f * g) I - lower_integral (f * g) I := by
    linarith [lower_integral_le_upper hmul_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f * g) I - lower_integral (f * g) I ≤ 2*(M₁+M₂)*ε := by
    have : ∃ f', MinorizesOn f' f I ∧ PiecewiseConstantOn f' I ∧ integ f I - ε < PiecewiseConstantOn.integ f' I ∧ MajorizesOn f' 0 I := by
      choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by linarith)
      use max f' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hf_nonneg with x hx _; specialize hf'min _ hx; aesop
      . exact hf'const.max hzero
      . apply lt_of_lt_of_le hf'int (hf'const.integ_mono _ (hf'const.max hzero)); simp
      intro _; simp
    choose f' hf'min hf'const hf'int hf'_nonneg using this
    have : ∃ g', MinorizesOn g' g I ∧ PiecewiseConstantOn g' I ∧ integ g I - ε < PiecewiseConstantOn.integ g' I ∧ MajorizesOn g' 0 I := by
      obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
      use max g' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hg_nonneg with x hx _; specialize hg'min _ hx; aesop
      . exact hg'const.max hzero
      . apply lt_of_lt_of_le hg'int (hg'const.integ_mono _ (hg'const.max hzero)); simp
      intro _; simp
    choose g' hg'min hg'const hg'int hg'_nonneg using this
    have : ∃ f'', MajorizesOn f'' f I ∧ PiecewiseConstantOn f'' I ∧ PiecewiseConstantOn.integ f'' I < integ f I + ε ∧ MinorizesOn f'' (fun _ ↦ M₁) I := by
      obtain ⟨ f'', hf''maj, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε  by linarith)
      use min f'' (fun _ ↦ M₁)
      have hM₁_piece := (ConstantOn.of_const' M₁ I).piecewiseConstantOn
      split_ands
      . peel hM₁ with x hx hM₁; rw [abs_le'] at hM₁
        simp [hf''maj _ hx, hM₁.1]
      . exact hf''const.min hM₁_piece
      . apply lt_of_le_of_lt ((hf''const.min hM₁_piece).integ_mono _ hf''const) hf''int
        simp
      intro _; simp
    choose f'' hf''maj hf''const hf''int hf''bound using this
    have : ∃ g'', MajorizesOn g'' g I ∧ PiecewiseConstantOn g'' I ∧ PiecewiseConstantOn.integ g'' I < integ g I + ε ∧ MinorizesOn g'' (fun _ ↦ M₂) I := by
      obtain ⟨ g'', hg''maj, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by linarith)
      use min g'' (fun _ ↦ M₂)
      have hM₂_piece := (ConstantOn.of_const' M₂ I).piecewiseConstantOn
      split_ands
      . peel hM₂ with x hx hM₂; rw [abs_le'] at hM₂
        simp [hg''maj _ hx, hM₂.1]
      . exact hg''const.min hM₂_piece
      . apply lt_of_le_of_lt ((hg''const.min hM₂_piece).integ_mono _ hg''const) hg''int
        simp
      intro _ _; simp
    choose g'' hg''maj hg''const hg''int hg''bound using this
    have hf'g'_const := hf'const.mul hg'const
    have hf'g'_maj : MinorizesOn (f' * g') (f * g) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx;
      specialize hf'_nonneg _ hx; specialize hg'_nonneg _ hx
      simp at *; apply mul_le_mul hf'min hg'min <;> grind
    have hf''g''_const := hf''const.mul hg''const
    have hf''g''_maj : MajorizesOn (f'' * g'') (f * g) I := by
      peel hf''maj with x hx hf''maj; specialize hg''maj _ hx
      specialize hg_nonneg _ hx; specialize hf_nonneg _ hx
      simp at *; apply mul_le_mul hf''maj hg''maj <;> grind
    have hupper_le := upper_integral_le_integ hmul_bound hf''g''_maj hf''g''_const
    have hlower_ge := integ_le_lower_integral hmul_bound hf'g'_maj hf'g'_const
    have hh_const := hf''g''_const.sub hf'g'_const
    have hh_integ := hf''g''_const.integ_sub hf'g'_const
    have hhmin : MinorizesOn (f'' * g'' - f' * g') (M₁ • (g''-g') + M₂ • (f''-f')) I := by
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        _ = (f'' x) * (g'' x - g' x) + (g' x) * (f'' x - f' x) := by ring
        _ ≤ _ := by gcongr <;> grind
    have hg''g'_const := hg''const.sub hg'const
    have hg''g'_integ := hg''const.integ_sub hg'const
    have hM₁g''g'_const := hg''g'_const.smul M₁
    have hM₁g''g_integ := hg''g'_const.integ_smul M₁
    have hf''f'_const := hf''const.sub hf'const
    have hf''f_integ := hf''const.integ_sub hf'const
    have hM₂f''f'_const := hf''f'_const.smul M₂
    have hM₂f''f_integ := hf''f'_const.integ_smul M₂
    have hsum_const := hM₁g''g'_const.add hM₂f''f'_const
    have hsum_integ := hM₁g''g'_const.integ_add hM₂f''f'_const
    have hsum_bound := hh_const.integ_mono hhmin hsum_const
    calc
      _ ≤ M₁ * PiecewiseConstantOn.integ (g'' - g') I + M₂ * PiecewiseConstantOn.integ (f'' - f') I := by linarith
      _ ≤ M₁ * (2*ε) + M₂ * (2*ε) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨ hmul_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩


theorem integ_of_mul {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  set fplus := max f (fun _ ↦ 0)
  set fminus := -min f (fun _ ↦ 0)
  set gplus := max g (fun _ ↦ 0)
  set gminus := -min g (fun _ ↦ 0)
  have := (IntegrableOn.const 0 I).1
  observe hfplus_integ : IntegrableOn fplus I
  observe hgplus_integ : IntegrableOn gplus I
  have hfminus_integ : IntegrableOn fminus I := (hf.min this).neg.1
  have hgminus_integ : IntegrableOn gminus I := (hg.min this).neg.1
  have hfplus_nonneg : MajorizesOn fplus 0 I := by intro _; simp [fplus]
  have hfminus_nonneg : MajorizesOn fminus 0 I := by intro _; simp [fminus]
  have hgplus_nonneg : MajorizesOn gplus 0 I := by intro _; simp [gplus]
  have hgminus_nonneg : MajorizesOn gminus 0 I := by intro _; simp [gminus]
  have hfplusgplus := integ_of_mul_nonneg hfplus_integ hgplus_integ hfplus_nonneg hgplus_nonneg
  have hfplusgminus := integ_of_mul_nonneg hfplus_integ hgminus_integ hfplus_nonneg hgminus_nonneg
  have hfminusgplus := integ_of_mul_nonneg hfminus_integ hgplus_integ hfminus_nonneg hgplus_nonneg
  have hfminusgminus := integ_of_mul_nonneg hfminus_integ hgminus_integ hfminus_nonneg hgminus_nonneg
  rw [show f = fplus - fminus by ext; simp [fplus, fminus],
      show g = gplus - gminus by ext; simp [gplus, gminus]]
  ring_nf
  exact ((hfplusgplus.add (hfplusgminus.neg.1.sub hfminusgplus).1).1.add hfminusgminus).1
open BoundedInterval

open Classical in
/-- Exercise 11.4.2 -/
theorem IntegrableOn.split {I: BoundedInterval} {f: ℝ → ℝ} (hf: IntegrableOn f I) (P: Partition I) :
  integ f I = ∑ J ∈ P.intervals, integ f J := by
    -- `g J` is `f` cut down to the piece `J` (zero outside).
  set g : BoundedInterval → ℝ → ℝ := fun J x ↦ if x ∈ J then f x else 0 with hg
  have hgInt : ∀ J ∈ P.intervals, IntegrableOn (g J) I := fun J hJ ↦
    IntegrableOn.of_extend (P.contains J hJ) (hf.mono' (P.contains J hJ))
  have hgInteg : ∀ J ∈ P.intervals, integ (g J) I = integ f J := fun J hJ ↦
    IntegrableOn.of_extend' (P.contains J hJ) (hf.mono' (P.contains J hJ))
  -- The integral of a finite sum of pieces splits, by additivity.
  have key : ∀ s : Finset BoundedInterval, s ⊆ P.intervals →
      IntegrableOn (fun x ↦ ∑ J ∈ s, g J x) I ∧
      integ (fun x ↦ ∑ J ∈ s, g J x) I = ∑ J ∈ s, integ f J := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨(IntegrableOn.const 0 I).1, (IntegrableOn.const 0 I).2.trans (zero_mul _)⟩
    | insert J s hJs ih =>
      intro hsub
      have hJmem : J ∈ P.intervals := hsub (Finset.mem_insert_self J s)
      obtain ⟨ihInt, ihInteg⟩ := ih (fun x hx ↦ hsub (Finset.mem_insert_of_mem hx))
      have hsplit : (fun x ↦ ∑ J' ∈ insert J s, g J' x)
          = (g J) + (fun x ↦ ∑ J' ∈ s, g J' x) := by
        funext x; simp only [Pi.add_apply, Finset.sum_insert hJs]
      rw [hsplit]
      have hadd := (hgInt J hJmem).add ihInt
      refine ⟨hadd.1, ?_⟩
      rw [hadd.2, hgInteg J hJmem, ihInteg, Finset.sum_insert hJs]
  obtain ⟨_, hInteg⟩ := key P.intervals subset_rfl
  rw [← hInteg]
  apply integ_congr
  intro x hx
  -- For `x ∈ I`, exactly one piece `J₀` contains `x`, so the sum collapses to `f x`.
  obtain ⟨J₀, ⟨hJ₀mem, hxJ₀⟩, hUniq⟩ := P.exists_unique x hx
  show f x = ∑ J ∈ P.intervals, g J x
  rw [Finset.sum_eq_single J₀]
  · simp [hg, hxJ₀]
  · intro J' hJ'mem hne
    simp only [hg]
    rw [if_neg (fun h ↦ hne (hUniq J' ⟨hJ'mem, h⟩))]
  · exact fun hJ₀notin ↦ absurd hJ₀mem hJ₀notin

end Chapter11
