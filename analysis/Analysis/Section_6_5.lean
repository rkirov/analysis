import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (_:ℕ) ↦ c):Sequence).TendsTo c := by
  rw [tendsTo_iff]; intro ε hε; use 0; intro n hn; simp [hn]; linarith

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

@[simp]
lemma Sequence.pow_eval {a:Sequence} {k: ℕ} {n: ℤ} (hn : n ≥ a.m): (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow, Pow.pow, inst_pow]
  grind

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ): a^(k+1) = a^k * a := by
  ext x
  . symm; exact Int.min_self a.m
  . simp only [mul_eval]
    by_cases h: x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha'; grind
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]; convert lim_harmonic.2; ext; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h <;> simp
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    convert Real.rpow_one _; field_simp
  simp [lim_eq, ha', pow_eq_zero hlim]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  rw [tendsTo_iff]; intro ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hx
  use (K : ℤ); intro n hn
  have hn' : n ≥ 0 := by omega
  simp [hn', abs_pow]
  calc |x| ^ n.toNat ≤ |x| ^ K :=
        pow_le_pow_of_le_one (abs_nonneg x) (le_of_lt hx) (by omega)
    _ ≤ ε := le_of_lt hK

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  subst hx; convert lim_of_const 1 using 2; simp

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
  intro ⟨L, hL⟩
  rcases hx with rfl | habs
  · -- x = -1: alternates between 1 and -1
    rw [tendsTo_iff] at hL
    obtain ⟨N, hN⟩ := hL (1/2) (by norm_num)
    set n_e := 2 * max 0 N with hn_e_def
    set n_o := 2 * max 0 N + 1 with hn_o_def
    have h1 := hN n_e (by omega)
    have h2 := hN n_o (by omega)
    have heval_e : (↑fun n ↦ (-1:ℝ) ^ n : Sequence) n_e = 1 := by
      show (if n_e ≥ 0 then (-1:ℝ)^n_e.toNat else 0) = 1
      rw [if_pos (by omega : n_e ≥ 0)]
      exact Even.neg_one_pow ⟨(max 0 N).toNat, by omega⟩
    have heval_o : (↑fun n ↦ (-1:ℝ) ^ n : Sequence) n_o = -1 := by
      show (if n_o ≥ 0 then (-1:ℝ)^n_o.toNat else 0) = -1
      rw [if_pos (by omega : n_o ≥ 0)]
      exact Odd.neg_one_pow ⟨(max 0 N).toNat, by omega⟩
    rw [heval_e] at h1; rw [heval_o] at h2
    have := (abs_le.mp h1).2; have := (abs_le.mp h2).1; linarith
  · -- |x| > 1: unbounded, contradicts convergent → bounded
    have ⟨M, _, hM⟩ := bounded_of_convergent ⟨L, hL⟩
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt M habs
    have := hM (K : ℤ)
    simp only [show (K:ℤ) ≥ 0 from by omega, ite_true, Int.toNat_natCast] at this
    rw [abs_pow] at this; linarith

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  rw [tendsTo_iff]; intro ε hε
  -- Preliminary (from hint): for M > 0, M^(1/(n+1)) ≤ 1 + ε for large n.
  -- Uses Lemma 6.5.2: (1+ε)^n is unbounded, so (1+ε)^K > M for some K,
  -- then taking K-th roots gives M^(1/K) ≤ 1+ε.
  have root_bound : ∀ M > 0, ∃ N : ℤ, ∀ n ≥ N, M ^ (1 / (↑n.toNat + 1:ℝ)) ≤ 1 + ε := by
    intro M hM
    rcases le_or_gt M 1 with hle | hgt
    · exact ⟨0, fun n _ ↦ (Real.rpow_le_one hM.le hle (by positivity)).trans (by linarith)⟩
    · obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt M (show (1:ℝ) < 1 + ε by linarith)
      have hK_pos : 0 < K := by
        by_contra h; push_neg at h; interval_cases K; simp at hK; linarith
      use (K - 1 : ℤ); intro n hn
      have hn_ge : (K:ℝ) ≤ ↑n.toNat + 1 := by exact_mod_cast show (K:ℤ) ≤ n.toNat + 1 by omega
      calc M ^ (1 / (↑n.toNat + 1:ℝ))
          ≤ M ^ (1 / (K:ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hgt.le
              (div_le_div_of_nonneg_left zero_le_one (by positivity) hn_ge)
        _ ≤ ((1 + ε) ^ K) ^ (1 / (K:ℝ)) :=
            Real.rpow_le_rpow hM.le hK.le (by positivity)
        _ = 1 + ε := by
            rw [← Real.rpow_natCast (1 + ε) K, ← Real.rpow_mul (by linarith)]
            simp [show (K:ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega)]
  rcases le_or_gt x 1 with hle | hgt
  · -- 0 < x ≤ 1: apply root_bound to x⁻¹
    obtain ⟨N, hN⟩ := root_bound x⁻¹ (inv_pos.mpr hx)
    use max 0 N; intro n hn
    have hn0 : n ≥ 0 := by omega
    specialize hN n (by omega : n ≥ N)
    simp only [hn0, ite_true]
    have hxp_le := Real.rpow_le_one hx.le hle (show 0 ≤ 1 / (↑n.toNat + 1:ℝ) by positivity)
    have hxp_pos := Real.rpow_pos_of_pos hx (1 / (↑n.toNat + 1:ℝ))
    rw [abs_of_nonpos (by linarith)]
    rw [Real.inv_rpow hx.le] at hN
    -- x^(1/(n+1)) ≥ (1+ε)⁻¹ ≥ 1 - ε
    have h1 : (1 + ε)⁻¹ ≤ x ^ (1 / (↑n.toNat + 1:ℝ)) :=
      (inv_le_comm₀ hxp_pos (by linarith)).mp hN
    have h2 : 1 - ε ≤ (1 + ε)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (by linarith : (0:ℝ) < 1 + ε)]
      nlinarith [sq_nonneg ε]
    linarith
  · -- x > 1: apply root_bound to x directly
    obtain ⟨N, hN⟩ := root_bound x hx
    use max 0 N; intro n hn
    have hn0 : n ≥ 0 := by omega
    simp only [hn0, ite_true]
    have h_ge := Real.one_le_rpow hgt.le (show 0 ≤ 1 / (↑n.toNat + 1:ℝ) by positivity)
    rw [abs_of_nonneg (by linarith)]
    linarith [hN n (by omega : n ≥ N)]

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
  rw [tendsTo_iff]; intro ε hε
  have hq' : (q:ℝ) > 0 := by exact_mod_cast hq
  set m := ⌈(q:ℝ)⁻¹⌉₊
  have hm_pos : 0 < m := Nat.ceil_pos.mpr (inv_pos.mpr hq')
  have hexp : 1 / (m:ℝ) ≤ (q:ℝ) := by
    rw [one_div]; exact (inv_le_comm₀ (by positivity : (0:ℝ) < m) hq').mpr (Nat.le_ceil _)
  have hpd : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(m:ℝ))):Sequence).TendsTo 0 := by
    have h := @lim_of_power_decay (m - 1)
    convert h using 3; congr 2
    have : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
    rw [← this]; push_cast; ring
  rw [tendsTo_iff] at hpd
  obtain ⟨N, hN⟩ := hpd ε hε
  use max 0 N; intro n hn
  have hn0 : n ≥ 0 := by omega
  have hnN : n ≥ N := by omega
  specialize hN n hnN
  simp only [show n ≥ 0 from by omega, ite_true] at hN ⊢
  rw [sub_zero] at hN ⊢
  have hbase_pos : (0:ℝ) < ↑n.toNat + 1 := by positivity
  rw [abs_of_nonneg (by positivity)] at hN ⊢
  calc 1 / (↑n.toNat + 1) ^ (q:ℝ)
      ≤ 1 / (↑n.toNat + 1) ^ (1 / (m:ℝ)) := by
        apply div_le_div_of_nonneg_left zero_le_one
          (Real.rpow_pos_of_pos hbase_pos _)
          (Real.rpow_le_rpow_of_exponent_le (by linarith [n.toNat.cast_nonneg (α := ℝ)]) hexp)
    _ ≤ ε := hN

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
  intro ⟨L, hL⟩
  have hq' : (q:ℝ) > 0 := by exact_mod_cast hq
  obtain ⟨M, hM_nn, hM⟩ := bounded_of_convergent ⟨L, hL⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((M + 1) ^ (q:ℝ)⁻¹)
  have h := hM (N : ℤ)
  simp only [show (N:ℤ) ≥ 0 from by omega, ite_true, Int.toNat_natCast] at h
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h
  have : (↑N + 1:ℝ) ^ (q:ℝ) > M := by
    have hM1 : (0:ℝ) < M + 1 := by linarith
    calc (↑N + 1:ℝ) ^ (q:ℝ)
        > ((M + 1) ^ (q:ℝ)⁻¹) ^ (q:ℝ) := by
          apply Real.rpow_lt_rpow (Real.rpow_nonneg (le_of_lt hM1) _)
          · linarith
          · exact hq'
      _ = M + 1 := by
          rw [← Real.rpow_mul (le_of_lt hM1), inv_mul_cancel₀ (ne_of_gt hq'), Real.rpow_one]
      _ > M := by linarith
  linarith

end Chapter6
