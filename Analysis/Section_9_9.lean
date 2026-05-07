import Mathlib.Tactic
import Analysis.Section_6_1
import Mathlib.Data.Nat.Nth
import Analysis.Section_9_6
/-!
# Analysis I, Section 9.9: Uniform continuity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`UniformContinuousOn`.
- Continuous functions on compact intervals are uniformly continuous.

-/

open Chapter6 Filter

namespace Chapter9

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  intro x hx
  simp only [Set.mem_Ioo] at hx
  have hxne : x ≠ 0 := ne_of_gt hx.1
  exact ((continuousAt_const (y := (1:ℝ))).div continuousAt_id hxne).continuousWithinAt

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  rw [BddOn]
  push_neg
  intro M
  use 1 / max (|M| + 1) 2
  simp
  constructor
  . have h2 : (2:ℝ) ≤ max (|M| + 1) 2 := le_max_right _ _
    calc (max (|M| + 1) 2)⁻¹ ≤ (2:ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
      _ < 2 := by norm_num
  . calc _ ≤ |M| := le_abs_self M
      _ < |M| + 1 := by linarith
      _ ≤ max (|M| + 1) 2 := le_max_left _ _
      _ ≤ |max (|M| + 1) 2| := le_abs_self _

/-- Example 9.9.1 -/
example (x : ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 1/11
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets f ε x₀ δ
  intro h
  unfold f x₀ ε
  unfold x₀ δ at h
  norm_num
  have hxpos : x > 0 := by rw [abs_le] at h; linarith [h.1]
  rw [show (x⁻¹ - 1 : ℝ) = (1 - x) / x by field_simp]
  rw [abs_div, abs_of_pos hxpos, abs_sub_comm]
  rw [div_le_iff₀ hxpos]
  nlinarith [abs_le.mp h]

example (x:ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 0.1
  let δ : ℝ := 1/1010
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets -merge f ε x₀ δ
  intro h
  unfold f x₀ ε
  unfold x₀ δ at h
  have hxpos : x > 0 := by rw [abs_le] at h; linarith [h.1]
  rw [show (1/x - 1/0.1 : ℝ) = (0.1 - x) / (0.1 * x) by field_simp]
  rw [abs_div, abs_of_pos (by positivity : (0.1 * x : ℝ) > 0), abs_sub_comm]
  rw [div_le_iff₀ (by positivity : (0.1 * x : ℝ) > 0)]
  nlinarith [abs_le.mp h]

example (x:ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε x₀ δ
  intro h
  unfold g ε x₀
  unfold x₀ δ at h
  rw [show (2*x - 2*1 : ℝ) = 2 * (x - 1) by ring, abs_mul]
  nlinarith [abs_nonneg (x - 1)]

example (x₀ x : ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε δ
  intro h
  unfold g ε
  unfold δ at h
  rw [show (2*x - 2*x₀ : ℝ) = 2 * (x - x₀) by ring, abs_mul]
  nlinarith [abs_nonneg (x - x₀)]

/-- Definition 9.9.2.  Here we use the Mathlib term {name}`UniformContinuousOn` -/
theorem UniformContinuousOn.iff (f: ℝ → ℝ) (X:Set ℝ) : UniformContinuousOn f X  ↔
  ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) := by
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.Close]
  grind

theorem ContinuousOn.ofUniformContinuousOn {X:Set ℝ} (f: ℝ → ℝ) (hf: UniformContinuousOn f X) :
  ContinuousOn f X := by
  intro x hx
  have hiff := (ContinuousWithinAt.tfae X f x).out 0 3
  rw [hiff]
  rw [UniformContinuousOn.iff] at hf
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := hf ε hε
  refine ⟨δ, hδ, fun x' hx' hd => ?_⟩
  specialize hf x hx x' hx'
  simp only [Real.Close, Real.dist_eq] at hf
  exact hf hd

example : ¬ UniformContinuousOn (fun x:ℝ ↦ 1/x) (Set.Icc 0 2) := by
  rw [UniformContinuousOn.iff]
  push_neg
  use 0.1
  norm_num
  intro δ hδ
  set x₀ : ℝ := min δ (1/10) with hx₀_def
  have hx₀_pos : x₀ > 0 := lt_min hδ (by norm_num)
  have hx₀_le : x₀ ≤ 1/10 := min_le_right _ _
  have hx₀_le_δ : x₀ ≤ δ := min_le_left _ _
  refine ⟨x₀, ⟨hx₀_pos.le, by linarith⟩, x₀/2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [Real.dist_eq]
    rw [show (x₀/2 - x₀ : ℝ) = -(x₀/2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  · rw [Real.dist_eq, show ((x₀/2)⁻¹ - x₀⁻¹ : ℝ) = x₀⁻¹ by field_simp; ring]
    rw [abs_of_pos (by positivity)]
    rw [lt_inv_comm₀ (by norm_num) hx₀_pos]
    linarith

end Chapter9

/-- Definition 9.9.5.  This is similar but not identical to `Real.close_seq` from Section 6.1. -/
abbrev Real.CloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  (a.m = b.m) ∧ ∀ n ≥ a.m, ε.Close (a n) (b n)

abbrev Real.EventuallyCloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeqs (a.from N) (b.from N)

abbrev Chapter6.Sequence.equiv (a b: Sequence) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyCloseSeqs a b

theorem EventuallyCloseSeqs.mono {ε₁ ε₂:ℝ} {a b: Sequence} (h: ε₁ ≤ ε₂) :
  ε₁.EventuallyCloseSeqs a b → ε₂.EventuallyCloseSeqs a b := by
  rintro ⟨N, hN, hm, hclose⟩
  exact ⟨N, hN, hm, λ n hn => le_trans (hclose n hn) h⟩

/-- Remark 9.9.6 -/
theorem Chapter6.Sequence.equiv_iff_rat (a b: Sequence) :
  a.equiv b ↔ ∀ ε > (0:ℚ), (ε:ℝ).EventuallyCloseSeqs a b := by
  constructor
  . intro h ε hε
    rw [equiv] at h
    have h' : ε > (0:ℝ) := by exact_mod_cast hε
    specialize h ε h'
    exact h
  . intro h
    rw [equiv]
    intro ε hε
    obtain ⟨ε', hε', hclose⟩ := exists_rat_btwn hε
    have hε'' : ε' > 0 := by exact_mod_cast hε'
    specialize h ε' hε''
    exact EventuallyCloseSeqs.mono hclose.le h

/-- Lemma 9.9.7 / Exercise 9.9.1 -/
theorem Chapter6.Sequence.equiv_iff (a b: Sequence) :
  a.equiv b ↔ atTop.Tendsto (fun n ↦ a n - b n) (nhds 0) := by
  constructor
  . intro h
    rw [equiv] at h
    rw [Metric.tendsto_nhds]
    intro ε hε
    specialize h (ε/2) (by linarith)
    rw [Real.EventuallyCloseSeqs] at h
    obtain ⟨N, hN, hclose⟩ := h
    rw [Filter.eventually_atTop]
    use N
    intro n hn
    rw [Real.CloseSeqs] at hclose
    obtain ⟨hm, hclose'⟩ := hclose
    specialize hclose' n
    have hmem : n ≥ (a.from N).m := by simp; omega
    specialize hclose' hmem
    rw [Real.Close, Real.dist_eq] at hclose'
    rw [Real.dist_eq]
    simp only [sub_zero]
    rw [Sequence.from_eval _ hn, Sequence.from_eval _ hn] at hclose'
    linarith
  . intro h
    rw [equiv]
    rw [Metric.tendsto_nhds] at h
    intro ε hε
    specialize h ε hε
    rw [Filter.eventually_atTop] at h
    rw [Real.EventuallyCloseSeqs]
    obtain ⟨N, hN⟩ := h
    use max (max N a.m) b.m
    constructor
    . simp
    . rw [Real.CloseSeqs]
      simp
      intro n hn hna hnb
      simp [hn, hna, hnb]
      specialize hN n hn
      rw [Real.dist_eq] at hN ⊢
      simp at hN
      exact hN.le

namespace Chapter9

theorem Real.dist_symm (x y: ℝ) : dist x y = dist y x := by
  rw [Real.dist_eq]
  rw [Real.dist_eq]
  rw [abs_sub_comm]

/-- Proposition 9.9.8 / Exercise 9.9.2 -/
theorem UniformContinuousOn.iff_preserves_equiv {X:Set ℝ} (f: ℝ → ℝ) :
  UniformContinuousOn f X ↔
  ∀ x y: ℕ → ℝ, (∀ n, x n ∈ X) → (∀ n, y n ∈ X) →
  (x:Sequence).equiv (y:Sequence) →
  (f ∘ x:Sequence).equiv (f ∘ y:Sequence) := by
  constructor
  . intro h x y hx hy h'
    rw [Chapter6.Sequence.equiv] at h' ⊢
    intro ε hε
    rw [UniformContinuousOn.iff] at h
    specialize h ε hε
    obtain ⟨δ, hδ, hf⟩ := h
    specialize h' δ hδ
    rw [Real.EventuallyCloseSeqs] at h' ⊢
    obtain ⟨N, hN, hclose⟩ := h'
    use N
    constructor
    . simp at hN
      linarith
    . rw [Real.CloseSeqs] at hclose ⊢
      simp at hclose ⊢
      intro n hn hN'
      specialize hclose n hn hN'
      simp [hn, hN'] at hclose ⊢
      specialize hf (x n.toNat) (hx n.toNat) (y n.toNat) (hy n.toNat)
      have : δ.Close (y n.toNat) (x n.toNat) := by
        rw [Real.Close, Real.dist_symm]
        exact hclose
      specialize hf this
      rw [Real.Close] at hf
      rw [Real.dist_symm] at hf
      exact hf
  . intro h
    rw [UniformContinuousOn.iff]
    intro ε hε
    by_contra h'
    push_neg at h'
    -- for every n, specialize h' at 1/(n+1) to find two points in X
    choose x₀ hx₀ x hx hclose hgap using
      (fun n : ℕ => h' (1/(n+1:ℝ)) (by positivity))
    -- x and x₀ are equiv as ℕ-sequences (using the def directly, no equiv_iff needed)
    have hequiv : (x:Sequence).equiv (x₀:Sequence) := by
      intro η hη
      obtain ⟨N, hN⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        |>.eventually_lt_const hη |> Filter.eventually_atTop.mp)
      refine ⟨N, by simp, ?_, ?_⟩
      · simp
      · intro n hn
        have hn_nat : n ≥ (N : ℤ) := by simp at hn; omega
        rw [Sequence.from_eval _ hn_nat, Sequence.from_eval _ hn_nat]
        obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = n := ⟨n.toNat, by omega⟩
        rw [Sequence.eval_coe, Sequence.eval_coe]
        have hk_ge : k ≥ N := by exact_mod_cast hn_nat
        have hk_lt : (1/((k:ℝ)+1)) < η := hN k hk_ge
        have := hclose k
        rw [Real.Close] at this ⊢
        linarith
    -- by h, f x and f x₀ are equiv
    specialize h x x₀ hx hx₀ hequiv
    rw [Chapter6.Sequence.equiv] at h
    obtain ⟨N, hN_ge, _, hfclose⟩ := h ε hε
    -- pick a large enough natural index k
    have hN_nonneg : N ≥ 0 := by
      have : ((↑(f ∘ x) : Sequence)).m = 0 := rfl
      omega
    set k := N.toNat with hk_def
    have hkN : (k : ℤ) ≥ N := by simp [hk_def, Int.toNat_of_nonneg hN_nonneg]
    have hk_in_from : (k : ℤ) ≥ ((↑(f ∘ x) : Sequence).from N).m := by
      have hm : ((↑(f ∘ x) : Sequence)).m = 0 := rfl
      simp only
      omega
    specialize hfclose k hk_in_from
    rw [Sequence.from_eval _ hkN, Sequence.from_eval _ hkN] at hfclose
    rw [Sequence.eval_coe, Sequence.eval_coe] at hfclose
    rw [Real.Close, Function.comp_apply, Function.comp_apply] at hfclose
    linarith [hgap k]

/-- Remark 9.9.9 -/
theorem Chapter6.Sequence.equiv_const (x₀: ℝ) (x:ℕ → ℝ) : atTop.Tendsto x (nhds x₀) ↔
  (x:Sequence).equiv (fun _:ℕ ↦ x₀:Sequence) := by
  rw [Sequence.equiv_iff]
  repeat rw [Metric.tendsto_nhds]
  simp
  constructor
  . intro h ε hε
    specialize h ε hε
    obtain ⟨N, hN⟩ := h
    use N
    intro n hn
    have : n ≥ 0 := by linarith
    lift n to ℕ using this
    specialize hN n (by exact_mod_cast hn)
    simp
    exact hN
  . intro h ε hε
    specialize h ε hε
    obtain ⟨N, hN⟩ := h
    use N.toNat
    intro b hb
    have hbZ : (N : ℤ) ≤ (b : ℤ) := by
      have : (N.toNat : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
      omega
    specialize hN b hbZ
    simp at hN
    rw [Real.dist_eq]
    exact hN

/-- Example 9.9.10 -/
noncomputable abbrev f_9_9_10 : ℝ → ℝ := fun x ↦ 1/x

theorem seqA_eq_seqB : (fun n:ℕ ↦ 1/(n+1:ℝ):Sequence).equiv (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    |>.eventually_lt_const hε |> Filter.eventually_atTop.mp)
  use N
  intro b hb
  have hb_nonneg : b ≥ 0 := le_trans (by simp) hb
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = b := ⟨b.toNat, by omega⟩
  rw [Sequence.eval_coe, Sequence.eval_coe]
  have hk_ge : k ≥ N := by exact_mod_cast hb
  have hk_lt : (1/((k:ℝ)+1)) < ε := hN k hk_ge
  have hkpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [Real.dist_eq, sub_zero,
    show (1/((k:ℝ)+1) - 1/(2*((k:ℝ)+1)) : ℝ) = 1/(2*((k:ℝ)+1)) by field_simp; ring]
  rw [abs_of_pos (by positivity)]
  have : 1/(2*((k:ℝ)+1)) ≤ 1/((k:ℝ)+1) := by
    apply one_div_le_one_div_of_le hkpos; linarith
  linarith

theorem seqA_in_ioo02 (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  simp only [one_div, Set.mem_Ioo, inv_pos]
  refine ⟨by positivity, ?_⟩
  rw [inv_lt_comm₀ (by positivity) (by norm_num)]
  have : (n:ℝ) ≥ 0 := by positivity
  linarith

theorem seqB_in_ioo02 (n:ℕ) : 1/(2*(n+1):ℝ) ∈ Set.Ioo 0 2 := by
  simp only [one_div, Set.mem_Ioo, inv_pos]
  refine ⟨by positivity, ?_⟩
  rw [inv_lt_comm₀ (by positivity) (by norm_num)]
  have : (n:ℝ) ≥ 0 := by positivity
  linarith

theorem fseqA_ne_fseqB : ¬ (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence).equiv
    (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) := by
  intro h
  obtain ⟨N, hN_ge, _, hclose⟩ := h 1 (by norm_num)
  -- pick a natural index k large enough that the gap > 1
  set k : ℤ := max N 1 with hk_def
  have hk_ge : k ≥ N := le_max_left _ _
  have hk_pos : k ≥ 1 := le_max_right _ _
  have hk_in : k ≥ ((↑(fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence).from N).m := by
    have hm : (((↑(fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence)).m : ℤ) = 0 := rfl
    simp only
    omega
  specialize hclose k hk_in
  rw [Sequence.from_eval _ hk_ge, Sequence.from_eval _ hk_ge] at hclose
  set m : ℕ := k.toNat with hm_def
  have hmk : (m : ℤ) = k := by simp [hm_def]; omega
  rw [show k = ((m:ℕ) : ℤ) from hmk.symm] at hclose
  rw [Sequence.eval_coe, Sequence.eval_coe] at hclose
  have hm_pos : m ≥ 1 := by have : (m:ℤ) ≥ 1 := by rw [hmk]; exact hk_pos
                            exact_mod_cast this
  unfold f_9_9_10 at hclose
  rw [Real.Close, Real.dist_eq] at hclose
  have hmpos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have h1 : 1 / (1/((m:ℝ)+1)) = (m:ℝ) + 1 := by field_simp
  have h2 : 1 / (1/(2*((m:ℝ)+1))) = 2*((m:ℝ) + 1) := by field_simp
  rw [h1, h2] at hclose
  have hmR : (m:ℝ) ≥ 1 := by exact_mod_cast hm_pos
  rw [show ((m:ℝ)+1 - 2*((m:ℝ)+1) : ℝ) = -((m:ℝ)+1) by ring, abs_neg,
    abs_of_pos hmpos] at hclose
  linarith

example : ¬ UniformContinuousOn f_9_9_10 (.Ioo 0 2) := by
  rw [UniformContinuousOn.iff_preserves_equiv]
  push_neg
  use (fun n:ℕ ↦ 1/(n+1:ℝ))
  use (fun n:ℕ ↦ 1/(2*(n+1):ℝ))
  refine ⟨fun n ↦ seqA_in_ioo02 n, fun n ↦ seqB_in_ioo02 n, seqA_eq_seqB, fseqA_ne_fseqB⟩

/-- Example 9.9.11 -/
abbrev f_9_9_11 : ℝ → ℝ := fun x ↦ x^2

theorem seqC_eq_seqD : ((fun n:ℕ ↦ (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    |>.eventually_lt_const hε |> Filter.eventually_atTop.mp)
  use N
  intro b hb
  have hb_nonneg : b ≥ 0 := le_trans (by simp) hb
  simp [hb_nonneg]
  specialize hN b.toNat (by grind only)
  simp at hN
  have : (b.toNat :ℝ) + 1 ≥ 0 := by positivity
  grind

theorem fseqC_neq_fseqD : ¬ ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ))):Sequence) := by
  intro h
  obtain ⟨N, hN_ge, _, hclose⟩ := h 1 (by norm_num)
  set k : ℤ := max N 0 with hk_def
  have hk_ge : k ≥ N := le_max_left _ _
  have hk_nonneg : k ≥ 0 := le_max_right _ _
  have hk_in : k ≥ ((↑(fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence).from N).m := by
    simp only
    omega
  specialize hclose k hk_in
  rw [Sequence.from_eval _ hk_ge, Sequence.from_eval _ hk_ge] at hclose
  set m : ℕ := k.toNat with hm_def
  have hmk : (m : ℤ) = k := by simp [hm_def]; omega
  rw [show k = ((m:ℕ) : ℤ) from hmk.symm] at hclose
  rw [Sequence.eval_coe, Sequence.eval_coe] at hclose
  unfold f_9_9_11 at hclose
  rw [Real.Close, Real.dist_eq] at hclose
  have hmpos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hexpand : ((m:ℝ)+1)^2 - ((m:ℝ)+1+1/((m:ℝ)+1))^2 = -(2 + 1/((m:ℝ)+1)^2) := by
    field_simp; ring
  rw [hexpand, abs_neg, abs_of_pos (by positivity)] at hclose
  have : (0:ℝ) < 1/((m:ℝ)+1)^2 := by positivity
  linarith

example : ¬ UniformContinuousOn f_9_9_11 .univ := by
  rw [UniformContinuousOn.iff_preserves_equiv]
  push_neg
  use (fun n:ℕ ↦ (n+1:ℝ))
  use (fun n:ℕ ↦ (n+1)+1/(n+1:ℝ))
  constructor
  . exact fun n ↦ Set.mem_univ _
  . constructor
    . exact fun n ↦ Set.mem_univ _
    . constructor
      . exact seqC_eq_seqD
      . exact fseqC_neq_fseqD

/-- Proposition 9.9.12 / Exercise 9.9.3  -/
theorem UniformContinuousOn.ofCauchy  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x: ℕ → ℝ} (hx: (x:Sequence).IsCauchy) (hmem : ∀ n, x n ∈ X) :
  (f ∘ x:Sequence).IsCauchy := by
  sorry

/-- Example 9.9.13 -/
example : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).IsCauchy := by
  sorry

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  sorry

example : ¬ ((fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence).IsCauchy := by
  sorry

example : ¬ UniformContinuousOn f_9_9_10 (Set.Ioo 0 2) := by
  sorry

/-- Corollary 9.9.14 / Exercise 9.9.4 -/
theorem UniformContinuousOn.limit_at_adherent  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x₀:ℝ} (hx₀: AdherentPt x₀ X) :
  ∃ L:ℝ, (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  sorry

/-- Proposition 9.9.15 / Exercise 9.9.5 -/
theorem UniformContinuousOn.of_bounded {E X:Set ℝ} {f: ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hEX: E ⊆ X) (hE: Bornology.IsBounded E) :
  Bornology.IsBounded (f '' E) := by
  sorry

/-- Theorem 9.9.16 -/
theorem UniformContinuousOn.of_continuousOn {a b:ℝ} {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) :
  UniformContinuousOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; rw [iff_preserves_equiv] at h
  simp [-Set.mem_Icc] at h
  choose x hx y hy hequiv ε hε h using h
  set E : Set ℕ := {n | ¬ ε.Close (f (x n)) (f (y n)) }
  have hE : Infinite E := by
    rw [←not_finite_iff_infinite]
    by_contra! this
    replace : ε.EventuallyCloseSeqs (fun n ↦ f (x n):Sequence) (fun n ↦ f (y n):Sequence) := by
      sorry
    sorry
  observe : Countable E
  set n : ℕ → ℕ := Nat.nth E
  rw [Set.infinite_coe_iff] at hE
  have hmono : StrictMono n := by apply_rules [Nat.nth_strictMono]
  have hmem (j:ℕ) : n j ∈ E := j.nth_mem_of_infinite hE
  have hsep (j:ℕ) : |f (x (n j)) - f (y (n j))| > ε := by
    specialize hmem j
    simpa [E, Real.Close, Real.dist_eq] using hmem
  observe hxmem : ∀ j, x (n j) ∈ Set.Icc a b
  observe hymem : ∀ j, y (n j) ∈ Set.Icc a b
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ j, hj, ⟨ L, hL, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨ hclosed, hbounded ⟩ _ hxmem
  replace hcont := ContinuousOn.continuousWithinAt hcont hL
  have hconv' := hconv.comp_of_continuous hcont (fun k ↦ hxmem (j k))
  rw [Sequence.equiv_iff] at hequiv
  replace hequiv : atTop.Tendsto (fun k ↦ x (n (j k)) - y (n (j k))) (nhds 0) := by
    observe hj' : atTop.Tendsto j .atTop
    observe hn' : atTop.Tendsto n .atTop
    observe hcoe : atTop.Tendsto (fun n:ℕ ↦ (n:ℤ)) .atTop
    exact hequiv.comp (hcoe.comp (hn'.comp hj'))
  have hyconv : atTop.Tendsto (fun k ↦ y (n (j k))) (nhds L) := by
    convert hconv.sub hequiv with k
    . abel
    simp
  replace hyconv := hyconv.comp_of_continuous hcont (fun k ↦ hymem (j k))
  have : atTop.Tendsto (fun k ↦ f (x (n (j k))) - f (y (n (j k)))) (nhds 0) := by
    convert hconv'.sub hyconv; simp
  sorry


/-- Exercise 9.9.6 -/
theorem UniformContinuousOn.comp {X Y: Set ℝ} {f g:ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hg: UniformContinuousOn g Y)
  (hrange: f '' X ⊆ Y) : UniformContinuousOn (g ∘ f) X := by
  sorry

end Chapter9
