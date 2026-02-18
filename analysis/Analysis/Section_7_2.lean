import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.Analysis.PSeries

/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = 1 + n := ⟨(N - 1).toNat, by omega⟩
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    show ∑ n ∈ Finset.Icc 1 1, example_7_2_4.seq n = 1 - (2:ℝ)^(-(1:ℤ))
    simp [Finset.Icc_self]; norm_num
  | succ k ih =>
    rw [show (1:ℤ) + ↑(k + 1) = (1 + ↑k) + 1 from by push_cast; ring]
    rw [partial_succ _ (show (1:ℤ) + ↑k ≥ 0 by omega), ih (by omega)]
    show 1 - (2:ℝ) ^ (-(1 + (↑k:ℤ))) + example_7_2_4.seq (1 + ↑k + 1) = _
    simp only [show (1:ℤ) + ↑k + 1 ≥ 1 from by omega, ↓reduceDIte]
    rw [show -(1 + (↑k : ℤ) + 1) = (-(1 + ↑k) : ℤ) + (-1 : ℤ) from by ring]
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; ring

private theorem zpow_two_neg_tendsto : Filter.Tendsto (fun N:ℤ => (2:ℝ)^(-N)) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 2⁻¹ by positivity) (by norm_num : (2:ℝ)⁻¹ < 1)
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε; obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by
    rw [show (2:ℝ)^(-n) = ((2:ℝ)⁻¹)^n.toNat from by
      rw [zpow_neg, ← zpow_natCast, Int.toNat_of_nonneg (le_trans (Nat.cast_nonneg N) hn), inv_zpow]]
    exact hN n.toNat (by omega)⟩

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by
  have key : Filter.Tendsto (fun N:ℤ => 1 - (2:ℝ)^(-N)) Filter.atTop (nhds 1) := by
    convert (tendsto_const_nhds (x := (1:ℝ))).sub zpow_two_neg_tendsto using 1; ring
  exact key.congr' (Filter.eventually_atTop.mpr ⟨1, fun N hN => (example_7_2_4a hN).symm⟩)

theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := sum_of_converges example_7_2_4b

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = 1 + n := ⟨(N - 1).toNat, by omega⟩
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    show ∑ n ∈ Finset.Icc 1 1, example_7_2_4'.seq n = (2:ℝ)^((1:ℤ)+1) - 2
    simp [Finset.Icc_self]; norm_num
  | succ k ih =>
    rw [show (1:ℤ) + ↑(k + 1) = (1 + ↑k) + 1 from by push_cast; ring]
    rw [partial_succ _ (show (1:ℤ) + ↑k ≥ 1 - 1 by omega), ih (by omega)]
    show (2:ℝ)^((1:ℤ) + ↑k + 1) - 2 + example_7_2_4'.seq (1 + ↑k + 1) = _
    simp only [show (1:ℤ) + ↑k + 1 ≥ 1 from by omega, ↓reduceDIte]
    have : (2:ℝ) ^ ((1:ℤ) + ↑k + 1 + 1) = 2 ^ ((1:ℤ) + ↑k + 1) * 2 :=
      zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0) _
    linarith

theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by
  intro ⟨L, hL⟩
  have hL := Metric.tendsto_atTop.mp hL
  obtain ⟨N, hN⟩ := hL 1 one_pos
  set M := max N 1
  have h1 := hN M (le_max_left _ _)
  have h2 := hN (M + 1) (by linarith [le_max_left N (1:ℤ)])
  rw [example_7_2_4'a (le_max_right N 1), Real.dist_eq] at h1
  rw [example_7_2_4'a (show M + 1 ≥ 1 by linarith [le_max_right N (1:ℤ)]), Real.dist_eq] at h2
  have habs1 := abs_lt.mp h1
  have habs2 := abs_lt.mp h2
  have zpow_double : (2:ℝ) ^ (M + 1 + 1) = 2 * 2 ^ (M + 1) := by
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]; ring
  have zpow_ge : (2:ℝ) ^ (M + 1) ≥ 4 := by
    have hM1 : (2:ℤ) ≤ M + 1 := by linarith [le_max_right N (1:ℤ)]
    have h := zpow_le_zpow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hM1
    linarith [show (2:ℝ) ^ (2:ℤ) = 4 from by norm_num]
  linarith

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  constructor
  · -- Forward: convergent ⟹ Cauchy ⟹ tails are small
    intro ⟨L, hL⟩ ε hε
    have hcauchy := hL.cauchySeq
    rw [Metric.cauchySeq_iff] at hcauchy
    obtain ⟨N₀, hN₀⟩ := hcauchy ε hε
    use max (N₀ + 1) s.m, le_max_right _ _
    intro p hp q hq
    by_cases hpq : p ≤ q
    · have hsub : Finset.Icc s.m (p-1) ⊆ Finset.Icc s.m q :=
        Finset.Icc_subset_Icc_right (by omega)
      have hsdiff := Finset.sum_sdiff hsub (f := s.seq)
      have hset : Finset.Icc s.m q \ Finset.Icc s.m (p-1) = Finset.Icc p q := by
        ext x; simp [Finset.mem_sdiff]; omega
      rw [hset] at hsdiff
      have key : ∑ n ∈ Finset.Icc p q, s.seq n = s.partial q - s.partial (p - 1) := by
        unfold Series.partial; linarith
      rw [key]
      have := hN₀ q (by linarith [le_max_left (N₀ + 1) s.m])
                    (p - 1) (by linarith [le_max_left (N₀ + 1) s.m])
      rw [Real.dist_eq] at this
      linarith [abs_sub_comm (s.partial q) (s.partial (p - 1))]
    · push_neg at hpq
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero]; linarith
  · -- Backward: Cauchy criterion ⟹ convergence (completeness of ℝ)
    intro h
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hNm, hN⟩ := h (ε / 2) (half_pos hε)
    refine ⟨N, fun p hp q hq => ?_⟩
    rw [Real.dist_eq]
    wlog hpq : p ≤ q with H
    · rw [abs_sub_comm]; exact H s h ε hε N hNm hN q hq p hp (by omega)
    have hsub : Finset.Icc s.m p ⊆ Finset.Icc s.m q := Finset.Icc_subset_Icc_right hpq
    have hsdiff := Finset.sum_sdiff hsub (f := s.seq)
    have hset : Finset.Icc s.m q \ Finset.Icc s.m p = Finset.Icc (p + 1) q := by
      ext x; simp [Finset.mem_sdiff]; omega
    rw [hset] at hsdiff
    rw [show s.partial p - s.partial q = -(∑ n ∈ Finset.Icc (p+1) q, s.seq n) from by
      unfold Series.partial; linarith]
    rw [abs_neg]
    linarith [hN (p + 1) (by omega) q hq]

/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  rw [converges_iff_tail_decay] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, -, hN⟩ := h (ε / 2) (half_pos hε)
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero]
  have := hN n hn n hn
  rw [Finset.Icc_self, Finset.sum_singleton] at this
  linarith

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  by_contra hcon
  have := decay_of_converges hcon
  contradiction

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _:ℕ ↦ (1:ℝ)):Series).diverges := by
  intro h
  have := Metric.tendsto_atTop.mp (decay_of_converges h) (1/2) (by norm_num)
  obtain ⟨N, hN⟩ := this
  have := hN (max N 0) (le_max_left _ _)
  simp only [show (max N 0 : ℤ) ≥ 0 from le_max_right _ _, ↓reduceIte, Real.dist_eq,
    sub_zero] at this
  norm_num at this

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  intro h
  have := Metric.tendsto_atTop.mp (decay_of_converges h) (1/2) (by norm_num)
  obtain ⟨N, hN⟩ := this
  have := hN (max N 0) (le_max_left _ _)
  simp only [show (max N 0 : ℤ) ≥ 0 from le_max_right _ _, ↓reduceIte, Real.dist_eq,
    sub_zero] at this
  rw [abs_pow, abs_neg, abs_one, one_pow] at this
  norm_num at this

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

theorem Series.abs_seq (s : Series) (n : ℤ) : s.abs.seq n = |s.seq n| := by
  unfold Series.abs mk'; simp only
  split
  · rfl
  · next h => rw [s.vanish n (by omega), abs_zero]

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (Absolute convergence test) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  rw [absConverges, converges_iff_tail_decay] at h
  rw [converges_iff_tail_decay]
  intro ε hε
  obtain ⟨N, hNm, hN⟩ := h ε hε
  refine ⟨N, by linarith, fun p hp q hq => ?_⟩
  calc |∑ n ∈ Finset.Icc p q, s.seq n|
      ≤ ∑ n ∈ Finset.Icc p q, |s.seq n| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Icc p q, s.abs.seq n := by congr 1; ext n; exact (s.abs_seq n).symm
    _ ≤ |∑ n ∈ Finset.Icc p q, s.abs.seq n| := le_abs_self _
    _ ≤ ε := hN p hp q hq

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  have hconv := converges_of_absConverges h
  rw [sum_of_converges (convergesTo_sum hconv), sum_of_converges (convergesTo_sum h)]
  exact le_of_tendsto_of_tendsto (convergesTo_sum hconv).abs (convergesTo_sum h)
    (Filter.eventually_atTop.mpr ⟨0, fun N _ =>
      calc |s.partial N|
          ≤ ∑ n ∈ Finset.Icc s.m N, |s.seq n| := Finset.abs_sum_le_sum_abs _ _
        _ = s.abs.partial N := by congr 1; ext n; exact (s.abs_seq n).symm⟩)

/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    convert h using 2 with _ n
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction k with
    | zero => simp
    | succ k ih =>
      have : N + 2 * ↑(k + 1) = (N + 2 * ↑k) + 2 := by push_cast; ring
      rw [this]
      calc S (N + 2 * ↑k + 2) ≤ S (N + 2 * ↑k) := claim3 (by linarith) (h'.add (even_two_mul _))
        _ ≤ S N := ih
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    induction k with
    | zero =>
      simp [claim0 hN, h'.add_one.neg_one_zpow]
    | succ k ih =>
      rw [show N + 2 * ↑(k + 1) + 1 = (N + 2 * ↑k + 1) + 2 from by push_cast; ring]
      linarith [claim2 (show N + 2 * ↑k + 1 ≥ m by linarith) ((h'.add (even_two_mul (↑k:ℤ))).add_one)]
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    rw [show N + 2*↑k + 1 = (N + 2*↑k) + 1 from by ring]
    simp [claim0 (show N + 2*↑k ≥ m by linarith),
          (h'.add (even_two_mul (↑k:ℤ))).add_one.neg_one_zpow, ha]
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    set j := (n - N).toNat
    have hjn : n = N + ↑j := by omega
    rcases j.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hSn : S n = S (N + 2 * ↑k) := by congr 1; omega
      exact ⟨by linarith [(claim4 hN h' k).1, (claim4 hN h' k).2.1, hSn],
             by linarith [why1 hN h' k, hSn]⟩
    · have hSn : S n = S (N + 2 * ↑k + 1) := by congr 1; omega
      exact ⟨by linarith [why2 hN h' k, hSn],
             by linarith [(claim4 hN h' k).2.1, (claim4 hN h' k).2.2, hSn]⟩
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by
    have : Nonempty { n // n ≥ m } := ⟨⟨m, le_refl _⟩⟩
    obtain ⟨⟨K, hKm⟩, hKε⟩ := Metric.tendsto_atTop.mp h ε hε
    obtain ⟨N, hNK, hNm, hNeven⟩ : ∃ N ≥ K, N ≥ m ∧ Even N := by
      rcases K.even_or_odd with hK | hK
      · exact ⟨K, le_refl _, hKm, hK⟩
      · exact ⟨K + 1, by omega, by omega, hK.add_one⟩
    have ha_small : a ⟨N + 1, by linarith⟩ ≤ ε := by
      have hsub : (⟨K, hKm⟩ : { n // n ≥ m }) ≤ ⟨N + 1, by linarith⟩ := by
        change K ≤ N + 1; omega
      have := hKε _ hsub
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha _)] at this; linarith
    refine ⟨N, fun n₁ hn₁ n₂ hn₂ => ?_⟩
    have ⟨h1_lo, h1_hi⟩ := why4 hNm hNeven hn₁
    have ⟨h2_lo, h2_hi⟩ := why4 hNm hNeven hn₂
    rw [_root_.abs_le]; constructor <;> linarith
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  set f : { n : ℤ // n ≥ 1 } → ℝ := fun n ↦ 1 / (↑n.val : ℝ)
  suffices h : (mk' (m := 1) (fun n ↦ (-1) ^ (↑n : ℤ) * f n)).converges by
    convert h using 2; ext n; exact (mul_one_div _ _).symm
  have hf_nn : ∀ n : { n : ℤ // n ≥ 1 }, f n ≥ 0 := fun ⟨n, hn⟩ => by
    simp only [f]; positivity
  have hf_anti : Antitone f := fun ⟨x, hx⟩ ⟨y, hy⟩ hxy => by
    simp only [f]
    exact one_div_le_one_div_of_le (by exact_mod_cast (show (0:ℤ) < x from by omega))
      (by exact_mod_cast hxy)
  apply (converges_of_alternating hf_nn hf_anti).mpr
  have : Nonempty { n : ℤ // n ≥ 1 } := ⟨⟨1, le_refl _⟩⟩
  have hg : Filter.Tendsto (fun (x : { n : ℤ // n ≥ 1 }) => x.val.toNat)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b =>
      ⟨⟨↑b + 1, by omega⟩, fun ⟨n, hn⟩ hle => by
        show n.toNat ≥ b; have : (↑b : ℤ) + 1 ≤ n := hle; omega⟩
  exact (tendsto_one_div_atTop_nhds_zero_nat.comp hg).congr fun ⟨n, hn⟩ => by
    simp only [Function.comp, f]; congr 1
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ n by omega)

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  have h_abs : ∀ k : ℤ, k ≥ 1 → example_7_2_13.abs.seq k = 1 / (↑k : ℝ) := by
    intro k hk; simp only [dif_pos hk, abs_div,
      abs_of_pos (show (0:ℝ) < k from by exact_mod_cast (show (0:ℤ) < k by omega))]
    rw [show k = (↑k.toNat : ℤ) from (Int.toNat_of_nonneg (by omega)).symm,
        zpow_natCast, abs_neg_one_pow]
  intro ⟨L, hL⟩
  have h_nn : ∀ k, 0 ≤ example_7_2_13.abs.seq k := by
    intro k; by_cases hk : k ≥ 1
    · rw [h_abs k hk]; positivity
    · exact le_of_eq (example_7_2_13.abs.vanish k (show k < 1 from by omega)).symm
  have h_mono : Monotone example_7_2_13.abs.partial :=
    fun _ _ hN => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hN) (fun k _ _ => h_nn k)
  have h_le := h_mono.ge_of_tendsto hL
  have h_eq : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1:ℝ)/((↑i:ℝ)+1) =
      example_7_2_13.abs.partial ↑n := by
    intro n; induction n with
    | zero => show (0:ℝ) = ∑ k ∈ Finset.Icc (1:ℤ) 0, _; simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih,
          show (↑(n+1) : ℤ) = ↑n + 1 from by push_cast; ring,
          partial_succ _ (by omega : (↑n : ℤ) ≥ 1 - 1)]
      congr 1; rw [h_abs (↑n + 1) (by omega)]; push_cast; ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.tendsto_atTop.mp Real.tendsto_sum_range_one_div_nat_succ_atTop (L + 1))
  linarith [h_eq N, h_le ↑N, hN N le_rfl]

theorem Series.example_7_2_13c :  example_7_2_13.condConverges :=
  ⟨example_7_2_13a, example_7_2_13b⟩

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  rw [convergesTo] at hs ht ⊢
  have key : (s + t).partial = s.partial + t.partial := by
    ext n; simp only [Pi.add_apply]; unfold Series.partial
    show ∑ i ∈ Finset.Icc (min s.m t.m) n, (s.seq i + t.seq i) =
         ∑ i ∈ Finset.Icc s.m n, s.seq i + ∑ i ∈ Finset.Icc t.m n, t.seq i
    rw [Finset.sum_add_distrib]; congr 1
    · exact (Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_left ..))
        (fun x hm hx => s.vanish x (by simp [Finset.mem_Icc] at hm hx; omega))).symm
    · exact (Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_right ..))
        (fun x hm hx => t.vanish x (by simp [Finset.mem_Icc] at hm hx; omega))).symm
  rw [key]; exact Filter.Tendsto.add hs ht

theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by
  have hs' := convergesTo_sum hs
  have ht' := convergesTo_sum ht
  have := convergesTo.add hs' ht'
  constructor
  . exact converges_of_convergesTo this
  . exact sum_of_converges this

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  rw [convergesTo] at hs ⊢
  have key : (c • s).partial = fun n => c * s.partial n := by
    ext n; unfold Series.partial
    show ∑ i ∈ Finset.Icc s.m n, (if i ≥ s.m then c * s.seq i else 0) =
         c * ∑ i ∈ Finset.Icc s.m n, s.seq i
    rw [Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_Icc.mp hi).1,
        Finset.mul_sum]
  rw [key]; exact hs.const_mul c

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by
  have hs' := convergesTo_sum hs
  have := convergesTo.smul (c := c) hs'
  exact ⟨converges_of_convergesTo this, sum_of_converges this⟩

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  rw [convergesTo] at hs ht ⊢
  have key : (s - t).partial = s.partial - t.partial := by
    ext n; simp only [Pi.sub_apply]; unfold Series.partial
    show ∑ i ∈ Finset.Icc (min s.m t.m) n, (s.seq i - t.seq i) =
         ∑ i ∈ Finset.Icc s.m n, s.seq i - ∑ i ∈ Finset.Icc t.m n, t.seq i
    rw [Finset.sum_sub_distrib]; congr 1
    · exact (Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_left ..))
        (fun x hm hx => s.vanish x (by simp [Finset.mem_Icc] at hm hx; omega))).symm
    · exact (Finset.sum_subset (Finset.Icc_subset_Icc_left (min_le_right ..))
        (fun x hm hx => t.vanish x (by simp [Finset.mem_Icc] at hm hx; omega))).symm
  rw [key]; exact Filter.Tendsto.sub hs ht

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by
  have hs' := convergesTo_sum hs
  have ht' := convergesTo_sum ht
  have := convergesTo.sub hs' ht'
  exact ⟨converges_of_convergesTo this, sum_of_converges this⟩

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  have h_m : (s.from (s.m + ↑k)).m = s.m + ↑k := show max s.m _ = _ by omega
  have h_sum : ∀ p q, p ≥ s.m + (k:ℤ) →
      ∑ i ∈ Finset.Icc p q, (s.from (s.m+↑k)).seq i = ∑ i ∈ Finset.Icc p q, s.seq i :=
    fun p q hp => Finset.sum_congr rfl fun i hi =>
      eval_mk' _ (show i ≥ max s.m (s.m + ↑k) by simp [Finset.mem_Icc] at hi; omega)
  rw [converges_iff_tail_decay, converges_iff_tail_decay]
  constructor
  · intro h ε hε
    obtain ⟨N, hNm, hN⟩ := h ε hε
    exact ⟨max N (s.m+↑k), by rw [h_m]; omega, fun p hp q hq => by
      rw [h_sum p q (by omega)]; exact hN p (by omega) q (by omega)⟩
  · intro h ε hε
    obtain ⟨N, hNm, hN⟩ := h ε hε
    exact ⟨N, by rw [h_m] at hNm; omega, fun p hp q hq => by
      rw [← h_sum p q (by rw [h_m] at hNm; omega)]; exact hN p (by omega) q (by omega)⟩

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  have hf := (converges_from s k).mp h
  have h_partial : ∀ N ≥ s.m + (k:ℤ),
      s.partial N = ∑ i ∈ Finset.Ico s.m (s.m+↑k), s.seq i + (s.from (s.m+↑k)).partial N := by
    intro N hN; unfold Series.partial
    rw [show (s.from (s.m+↑k)).m = s.m + ↑k from by show max s.m _ = _; omega]
    have h1 : ∑ i ∈ Finset.Icc (s.m+↑k) N, (s.from (s.m+↑k)).seq i =
        ∑ i ∈ Finset.Icc (s.m+↑k) N, s.seq i :=
      Finset.sum_congr rfl fun i hi => eval_mk' _
        (max_le (by have := (Finset.mem_Icc.mp hi).1; omega) (Finset.mem_Icc.mp hi).1)
    rw [h1, ← Finset.sum_union (Finset.disjoint_left.mpr fun x hx hx' => by
        simp at hx hx'; omega),
      show Finset.Ico s.m (s.m+↑k) ∪ Finset.Icc (s.m+↑k) N = Finset.Icc s.m N from by
        ext; simp; omega]
  exact tendsto_nhds_unique (convergesTo_sum h)
    (Filter.Tendsto.congr' (Filter.eventually_atTop.mpr ⟨s.m + ↑k, fun N hN => (h_partial N hN).symm⟩)
      (tendsto_const_nhds.add (convergesTo_sum hf)))

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  rw [convergesTo] at h ⊢
  suffices key : (mk' (m := s.m + L) (fun n ↦ s.seq (↑n - L))).partial =
      s.partial ∘ (· - L) by
    rw [key]
    exact h.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b + L, fun n hn => by omega⟩)
  ext N; unfold Series.partial; simp only [Function.comp]
  rw [Finset.sum_congr rfl fun i hi =>
    dif_pos (show i ≥ s.m + L from (Finset.mem_Icc.mp hi).1)]
  exact Finset.sum_nbij (· - L)
    (fun a ha => by simp [Finset.mem_Icc] at ha ⊢; omega)
    (fun a _ b _ h => by dsimp at h; omega)
    (fun j hj => ⟨j + L, by simp at hj ⊢; omega, by dsimp; omega⟩)
    (fun _ _ => rfl)

/-- Reindex a sum over `Finset.Icc (0:ℤ) n` to `Finset.range (n.toNat + 1)`. -/
private lemma sum_Icc_eq_sum_range (f : ℕ → ℝ) {n : ℤ} (hn : 0 ≤ n) :
    ∑ k ∈ Finset.Icc (0:ℤ) n, f k.toNat = ∑ k ∈ Finset.range (n.toNat + 1), f k := by
  have h_fwd : ∀ k ∈ Finset.Icc (0:ℤ) n, k.toNat ∈ Finset.range (n.toNat + 1) :=
    fun k hk => by simp [Finset.mem_Icc] at hk; simp [Finset.mem_range]; omega
  have h_inv : ∀ k ∈ Finset.range (n.toNat + 1), (k : ℤ) ∈ Finset.Icc (0:ℤ) n :=
    fun k hk => by simp [Finset.mem_range] at hk; simp [Finset.mem_Icc]; omega
  have h_left : ∀ k ∈ Finset.Icc (0:ℤ) n, ↑(k.toNat) = k :=
    fun k hk => Int.toNat_of_nonneg (Finset.mem_Icc.mp hk).1
  have h_right : ∀ k ∈ Finset.range (n.toNat + 1), (↑k : ℤ).toNat = k :=
    fun k _ => Int.toNat_natCast k
  exact Finset.sum_nbij' (·.toNat) (↑·) h_fwd h_inv h_left h_right (fun _ _ => rfl)

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a n - a (n+1)):Series).convergesTo (a 0) := by
  rw [convergesTo]
  rw [Metric.tendsto_atTop] at ha ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  rw [Real.dist_eq]
  have hn0 : (0:ℤ) ≤ n := by omega
  have h_tel : ((fun n:ℕ ↦ a n - a (n+1)):Series).partial n = a 0 - a (n.toNat + 1) := by
    unfold Series.partial; show ∑ k ∈ Finset.Icc 0 n, _ = _
    trans ∑ k ∈ Finset.Icc (0:ℤ) n, (a k.toNat - a (k.toNat + 1))
    · exact Finset.sum_congr rfl fun k hk => by simp [(Finset.mem_Icc.mp hk).1]
    exact (sum_Icc_eq_sum_range (fun m => a m - a (m + 1)) hn0).trans
      (Finset.sum_range_sub' a (n.toNat + 1))
  rw [h_tel, show a 0 - a (n.toNat + 1) - a 0 = -(a (n.toNat + 1)) from by ring, abs_neg]
  have := hN (n.toNat + 1) (by omega)
  rwa [Real.dist_eq, sub_zero] at this

/- Exercise 7.2.1  -/
def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  apply isFalse; intro hc
  have h := (converges_of_alternating (m := 1) (a := fun _ => (1:ℝ))
    (fun _ => zero_le_one) (fun _ _ _ => le_refl 1)).mp
  simp only [mul_one] at h
  haveI : Filter.NeBot (Filter.atTop : Filter { n : ℤ // n ≥ 1 }) :=
    Filter.atTop_neBot_iff.mpr ⟨⟨⟨1, le_refl _⟩⟩, ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      ⟨⟨max a b, by omega⟩, le_max_left a b, le_max_right a b⟩⟩⟩
  exact absurd (tendsto_nhds_unique tendsto_const_nhds (h hc)) one_ne_zero

end Chapter7
