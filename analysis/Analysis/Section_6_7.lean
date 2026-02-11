import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real

/-- Lemma 6.7.1 (Continuity of exponentiation) -/
lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  -- This proof is rearranged slightly from the original text.
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  obtain h | rfl | h := lt_trichotomy x 1
  . have h' : x ≤ 1 := le_of_lt h
    rw [←Cauchy_iff_convergent]
    intro ε hε
    choose K hK hclose using lim_of_roots hx (ε*x^M) (by positivity)
    choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
    simp [CloseSeq, dist_eq] at hclose hK hN
    lift N to ℕ using hN
    lift K to ℕ using hK
    specialize hclose K (by simp) (by simp); simp at hclose
    use N, by simp
    intro n hn m hm; simp at hn hm
    specialize hq n (by simp [hn]) m (by simp [hm])
    simp [Close, hn, hm, dist_eq] at hq ⊢
    have : 0 ≤ (N:ℤ) := by simp
    lift n to ℕ using by linarith
    lift m to ℕ using by linarith
    simp at hn hm hq ⊢
    obtain hqq | hqq := le_or_gt (q m) (q n)
    . replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by
        exact rpow_le_rpow_of_exponent_ge hx h' (by exact_mod_cast hqq)
      rw [abs_of_nonpos (by linarith)]
      have hqub := (abs_le.mp hq).2
      have hclose' : 1 - x ^ ((K:ℝ) + 1)⁻¹ ≤ ε * x ^ M := by linarith [(abs_le.mp hclose).1]
      calc
        _ = x^(q m:ℝ) * (1 - x^(q n - q m:ℝ)) := by ring_nf; rw [←rpow_add (by linarith)]; ring_nf
        _ ≤ x^(-M) * (1 - x^((K:ℝ) + 1)⁻¹) := by
          apply mul_le_mul
          · exact rpow_le_rpow_of_exponent_ge hx h' (by specialize hbound m; simp_all [abs_le']; linarith)
          · linarith [rpow_le_rpow_of_exponent_ge hx h' (by exact hqub)]
          · linarith [rpow_le_one hx.le h' (show (0:ℝ) ≤ (q n - q m:ℝ) from by exact_mod_cast sub_nonneg.mpr hqq)]
          · positivity
        _ ≤ x^(-M) * (ε * x^M) := by gcongr
        _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; linarith
    . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by
        exact rpow_le_rpow_of_exponent_ge hx h' (by exact_mod_cast hqq.le)
      rw [abs_of_nonneg (by linarith)]
      have hqub : ↑(q m) - ↑(q n) ≤ ((K:ℝ) + 1)⁻¹ := by
        have := (abs_le.mp hq).1; linarith
      have hclose' : 1 - x ^ ((K:ℝ) + 1)⁻¹ ≤ ε * x ^ M := by linarith [(abs_le.mp hclose).1]
      calc
        _ = x^(q n:ℝ) * (1 - x^(q m - q n:ℝ)) := by ring_nf; rw [←rpow_add]; ring_nf; positivity
        _ ≤ x^(-M) * (1 - x^((K:ℝ) + 1)⁻¹) := by
          apply mul_le_mul
          · exact rpow_le_rpow_of_exponent_ge hx h' (by specialize hbound n; simp_all [abs_le']; linarith)
          · linarith [rpow_le_rpow_of_exponent_ge hx h' (by exact hqub)]
          · linarith [rpow_le_one hx.le h' (show (0:ℝ) ≤ (q m - q n:ℝ) from by exact_mod_cast sub_nonneg.mpr hqq.le)]
          · positivity
        _ ≤ x^(-M) * (ε * x^M) := by gcongr
        _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; positivity
  . simp; exact ⟨ 1, lim_of_const 1 ⟩
  have h': 1 ≤ x := by linarith
  rw [←Cauchy_iff_convergent]
  intro ε hε
  choose K hK hclose using lim_of_roots hx (ε*x^(-M)) (by positivity)
  choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
  simp [CloseSeq, dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose
  use N, by simp
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm])
  simp [Close, hn, hm, dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [rpow_le_rpow_left_iff h]; norm_cast
    rw [abs_of_nonneg (by linarith)]
    calc
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; linarith
  replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [rpow_le_rpow_left_iff h]; norm_cast; linarith
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←rpow_add]; ring_nf; positivity
    _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
      gcongr <;> try exact h'
      . rw [sub_nonneg]; apply one_le_rpow h'; norm_cast; linarith
      . specialize hbound n; simp_all [abs_le']
      grind [abs_le']
    _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
    _ = ε := by rw [mul_comm, mul_assoc, ←rpow_add]; simp; positivity


lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))]
    rw [lim_eq] at this
    convert (lim_mul (b := (fun n ↦ x^(r n:ℝ):Sequence)) (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe]
      rcongr _ n
      rw [←rpow_add (by linarith)]
      simp [r]
    grind
  intro ε hε
  have h1 := lim_of_roots hx
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε
  choose K2 hK2 h4 using h2 ε hε
  simp [Inv.inv] at hK1 hK2
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2
  have hr := tendsTo_sub hq hq'
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity)
  refine ⟨ N, by simp_all, ?_ ⟩
  intro n hn; simp at hn
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])
  simp [hn, dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢
  specialize hr n (by simp [hn])
  simp [Close, hn, abs_le'] at hr
  obtain h | rfl | h := lt_trichotomy x 1
  . have h' : x ≤ 1 := le_of_lt h
    have h5 : x^(K + 1:ℝ)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
      exact rpow_le_rpow_of_exponent_ge hx h' (by simp_all [r])
    have h6 : x ^ (r n.toNat:ℝ) ≤ (x^(K + 1:ℝ)⁻¹)⁻¹ := by
      rw [←rpow_neg (by linarith)]
      exact rpow_le_rpow_of_exponent_ge hx h' (by simp [r]; linarith)
    split_ands <;> linarith
  . simp; linarith
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  split_ands <;> linarith

theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q
  apply lim_eq_LIM at hcauchy
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy
  convert hcauchy; aesop

/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim ((fun n ↦ x^((eq_lim_of_rat α).choose n:ℝ)):Sequence)

lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq

lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩

lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  exact (lim_eq.mp (lim_of_const _)).2.symm

/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  choose q' hq' using eq_lim_of_rat q
  rw [rpow_eq_lim_ratPow hx hq']
  -- since x > 0, then x ^ y > 0 for all y, so the limit is ≥ 0
  by_contra hlt
  push_neg at hlt
  have htends := ratPow_tendsto_rpow hx hq'
  rw [rpow_eq_lim_ratPow hx hq'] at htends
  rw [Sequence.tendsTo_iff] at htends
  obtain ⟨N, hN⟩ := htends _ (neg_pos.mpr hlt)
  have hN' := hN (max N 0) (le_max_left _ _)
  simp only [show (0:ℤ) ≤ max N 0 from le_max_right _ _, ↓reduceIte] at hN'
  linarith [(abs_le.mp hN').2, show x ^ (q' (max N 0).toNat : ℝ) > 0 from by positivity]


/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  convert_to ((fun n ↦ ((q' n + r' n:ℚ):ℝ)):Sequence).TendsTo (q + r) at hq'r'
  . aesop
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←rpow_add]; simp; linarith


private lemma Real.pow_tendsto_of_tendsto_one {f : ℕ → ℝ} (hf : (↑f : Sequence).TendsTo 1) :
    ∀ M : ℕ, ((fun n ↦ f n ^ M) : Sequence).TendsTo 1 := by
  intro M; induction M with
  | zero => simpa using lim_of_const 1
  | succ k ih =>
    have h := tendsTo_mul ih hf; rw [one_mul] at h
    have : ((fun n ↦ f n ^ (k + 1)) : Sequence) =
        ((fun n ↦ f n ^ k) : Sequence) * ((f) : Sequence) := by
      rw [mul_coe]; rcongr n
    rw [this]; exact h

/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by
  set L := rpow x q with hL_def
  have hL : L > 0 := by
    rw [hL_def]; by_contra hle; push_neg at hle
    have h0 : rpow x q = 0 := le_antisymm hle (ratPow_nonneg hx q)
    have hone : rpow x 0 = 1 := by
      rw [show (0:ℝ) = ((0:ℚ):ℝ) from by norm_cast, rpow_of_rat_eq_ratPow hx]; simp [rpow_zero]
    have := ratPow_add hx q (-q); rw [add_neg_cancel, hone, h0, zero_mul] at this; linarith
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  -- q'_n * r'_n → q*r
  have hprod := tendsTo_mul hq' hr'; rw [mul_coe] at hprod
  convert_to ((fun n ↦ ((q' n * r' n : ℚ) : ℝ)) : Sequence).TendsTo (q * r) at hprod
  · aesop
  -- (x^q'_n)^r'_n → rpow x (q*r), via rpow_mul at rational exponents
  have hA : ((fun n ↦ (x ^ (q' n : ℝ)) ^ (r' n : ℝ)) : Sequence).TendsTo (rpow x (q * r)) := by
    have rpow_eq : (fun n : ℕ ↦ x ^ ((q' n * r' n : ℚ) : ℝ)) =
        fun n ↦ (x ^ (q' n : ℝ)) ^ (r' n : ℝ) := by
      ext n; push_cast; exact rpow_mul hx.le _ _
    rw [← rpow_eq]; exact ratPow_tendsto_rpow hx hprod
  -- L^r'_n → rpow L r
  have hB := ratPow_tendsto_rpow hL hr'
  -- Factor: (x^q'_n)^r'_n = (x^q'_n/L)^r'_n * L^r'_n; show the ratio → 1
  suffices hC : ((fun n ↦ (x ^ (q' n : ℝ) / L) ^ (r' n : ℝ)) : Sequence).TendsTo 1 by
    have hD := tendsTo_mul hC hB; rw [mul_coe, one_mul] at hD
    -- Transfer to the same sequence as hA via pointwise div-mul cancellation
    have factor_eq : (fun n : ℕ ↦ (x ^ (q' n : ℝ) / L) ^ (r' n : ℝ) * L ^ (r' n : ℝ)) =
        fun n ↦ (x ^ (q' n : ℝ)) ^ (r' n : ℝ) := by
      ext n; rw [div_rpow (rpow_nonneg hx.le _) hL.le, div_mul_cancel₀]
      exact ne_of_gt (rpow_pos_of_pos hL _)
    rw [factor_eq] at hD
    exact (lim_eq.mp hD).2.symm.trans (lim_eq.mp hA).2
  -- Squeeze: u_n := x^q'_n / L → 1, need u_n^r'_n → 1
  have hu : ((fun n ↦ x ^ (q' n : ℝ) / L) : Sequence).TendsTo 1 := by
    have div_eq : (fun n : ℕ ↦ x ^ (q' n : ℝ) * (1 / L)) = fun n ↦ x ^ (q' n : ℝ) / L := by
      ext n; rw [mul_one_div]
    have := tendsTo_mul (ratPow_tendsto_rpow hx hq') (lim_of_const (1/L))
    rw [mul_coe, ← hL_def, mul_one_div_cancel (ne_of_gt hL), div_eq] at this; exact this
  obtain ⟨Mb, _, hMb⟩ := bounded_of_convergent ⟨r, hr'⟩
  rw [Sequence.boundedBy_def] at hMb
  set M := ⌈Mb⌉₊ + 1
  have hM_le : ∀ n, |(r' n : ℝ)| ≤ (M : ℝ) := fun n ↦
    le_trans (hMb n) (le_trans (Nat.le_ceil Mb) (by exact_mod_cast Nat.le_succ _))
  have hu_pow := pow_tendsto_of_tendsto_one hu M
  rw [Sequence.tendsTo_iff]; intro ε hε
  rw [Sequence.tendsTo_iff] at hu_pow
  obtain ⟨N, hN⟩ := hu_pow (min (ε/2) (1/2)) (by positivity)
  use max N 0; intro n hn
  have hn0 : (0:ℤ) ≤ n := le_trans (le_max_right _ _) hn
  simp only [hn0, ↓reduceIte]
  have hNn := hN n (le_trans (le_max_left _ _) hn)
  simp only [hn0, ↓reduceIte] at hNn
  set u := x ^ (q' n.toNat : ℝ) / L with hu_def
  have hu_pos : u > 0 := div_pos (rpow_pos_of_pos hx _) hL
  have hbd := abs_le.mp hNn
  have hge : u ^ M ≥ 1/2 := by linarith [min_le_right (ε/2) (1/2 : ℝ)]
  have hclose := abs_le.mp (le_trans hNn (min_le_left _ _))
  have hr_le : (r' n.toNat : ℝ) ≤ M := le_of_abs_le (hM_le n.toNat)
  have hr_ge : -(M:ℝ) ≤ (r' n.toNat : ℝ) := neg_le_of_abs_le (hM_le n.toNat)
  rw [abs_le]
  by_cases hu1 : 1 ≤ u
  · have h_up : u ^ (r' n.toNat : ℝ) ≤ u ^ (M : ℝ) :=
      rpow_le_rpow_of_exponent_le hu1 hr_le
    have h_lo : u ^ (-(M:ℝ)) ≤ u ^ (r' n.toNat : ℝ) :=
      rpow_le_rpow_of_exponent_le hu1 hr_ge
    rw [rpow_natCast] at h_up; rw [rpow_neg hu_pos.le, rpow_natCast] at h_lo
    have hpM : u ^ M ≥ 1 := one_le_pow₀ hu1
    have hinv_ge : 1 - (u ^ M)⁻¹ ≤ ε / 2 := by
      have : 1 - (u ^ M)⁻¹ = (u ^ M - 1) / u ^ M := by field_simp
      calc 1 - (u ^ M)⁻¹ = (u ^ M - 1) / u ^ M := this
        _ ≤ u ^ M - 1 := div_le_self (by linarith) hpM
        _ ≤ ε / 2 := hclose.2
    exact ⟨by linarith, by linarith⟩
  · push_neg at hu1
    have h_lo : u ^ (M : ℝ) ≤ u ^ (r' n.toNat : ℝ) :=
      rpow_le_rpow_of_exponent_ge hu_pos hu1.le hr_le
    have h_up : u ^ (r' n.toNat : ℝ) ≤ u ^ (-(M:ℝ)) :=
      rpow_le_rpow_of_exponent_ge hu_pos hu1.le hr_ge
    rw [rpow_natCast] at h_lo; rw [rpow_neg hu_pos.le, rpow_natCast] at h_up
    have hinv_le : (u ^ M)⁻¹ - 1 ≤ ε := by
      have : (u ^ M)⁻¹ - 1 = (1 - u ^ M) / u ^ M := by field_simp
      have huM_pos : (0:ℝ) < u ^ M := by positivity
      rw [this, div_le_iff₀ huM_pos]
      calc (1 - u ^ M) ≤ ε / 2 := by linarith [hclose.1]
        _ ≤ ε * u ^ M := by nlinarith [hge]
    exact ⟨by linarith, by linarith⟩

/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  have h0 : rpow x 0 = 1 := by
    rw [show (0:ℝ) = ((0:ℚ):ℝ) from by norm_cast, rpow_of_rat_eq_ratPow hx]
    simp [rpow_zero]
  have h1 := ratPow_add hx q (-q)
  rw [add_neg_cancel, h0] at h1
  rw [one_div]
  exact eq_inv_of_mul_eq_one_right h1.symm

/-- Proposition 6.7.3(d) / Exercise 6.7.1 -/
theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  -- Helper: x^q'_n - y^q'_n → rpow x q - rpow y q, and for large n with q'_n > 0
  -- we can compare terms using Mathlib's rational-exponent monotonicity.
  have aux : ∀ a b : ℝ, a > 0 → b > 0 → a > b → rpow a q > rpow b q := by
    intro a b ha hb hab
    by_contra hle; push_neg at hle
    choose q' hq' using eq_lim_of_rat q
    have hdiff := tendsTo_sub (ratPow_tendsto_rpow ha hq') (ratPow_tendsto_rpow hb hq')
    rw [sub_coe] at hdiff; rw [Sequence.tendsTo_iff] at hdiff hq'
    set L := rpow a q - rpow b q
    obtain hlt | heq := lt_or_eq_of_le hle
    · -- L < 0: pick ε = -L, sequence terms ≤ 0 but > 0 from rational monotonicity
      obtain ⟨N, hN⟩ := hdiff (-L) (by linarith)
      obtain ⟨N', hN'⟩ := hq' (q/2) (by linarith)
      set n := max (max N N') 0
      have hn0 : (0:ℤ) ≤ n := le_max_right _ _
      have hN1 := hN n (le_trans (le_max_left _ _) (le_max_left _ _))
      have hN2 := hN' n (le_trans (le_max_right _ _) (le_max_left _ _))
      simp only [hn0, ↓reduceIte] at hN1 hN2
      have hqn : (q' n.toNat : ℝ) > 0 := by linarith [(abs_le.mp hN2).1]
      linarith [(abs_le.mp hN1).2, rpow_lt_rpow hb.le hab hqn]
    · -- rpow a q = rpow b q: take q-th root to get a = b, contradiction
      have rpow_one : ∀ z > 0, rpow z 1 = z := fun z hz => by
        rw [show (1:ℝ) = ((1:ℚ):ℝ) from by norm_cast, rpow_of_rat_eq_ratPow hz]; simp
      have h1 := ratPow_ratPow ha q (1/q)
      have h2 := ratPow_ratPow hb q (1/q)
      rw [mul_one_div_cancel (ne_of_gt h), rpow_one a ha] at h1
      rw [mul_one_div_cancel (ne_of_gt h), rpow_one b hb] at h2
      linarith [h1.symm.trans (heq ▸ h2)]
  constructor
  · exact aux x y hx hy
  · intro hrpow
    rcases lt_trichotomy x y with hlt | heq | hgt
    · linarith [aux y x hy hx hlt]
    · subst heq; linarith
    · exact hgt

private lemma Real.rpow_one_base (α : ℝ) : rpow 1 α = 1 := by
  choose s hs using eq_lim_of_rat α
  have h1 := ratPow_tendsto_rpow (show (1:ℝ) > 0 by norm_num) hs
  simp_rw [one_rpow] at h1
  exact (lim_eq.mp h1).2.symm.trans (lim_eq.mp (lim_of_const 1)).2

private lemma Real.rpow_zero' {x : ℝ} (hx : x > 0) : rpow x 0 = 1 := by
  rw [show (0:ℝ) = ((0:ℚ):ℝ) from by norm_cast, rpow_of_rat_eq_ratPow hx]; simp

private lemma Real.rpow_pos' {x : ℝ} (hx : x > 0) (α : ℝ) : rpow x α > 0 := by
  by_contra hle; push_neg at hle
  have h0 : rpow x α = 0 := le_antisymm hle (ratPow_nonneg hx α)
  have h1 : rpow x (-α) = 0 := by rw [ratPow_neg hx, h0]; simp
  have h2 := ratPow_add hx α (-α); rw [add_neg_cancel, h0, h1, mul_zero] at h2
  linarith [rpow_zero' hx]

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  have hx0 : x > 0 := by linarith
  -- Reduce to: rpow x α > 1 ↔ α > 0
  suffices key : ∀ α, rpow x α > 1 ↔ α > 0 by
    have h1 := ratPow_add hx0 (q - r) r; rw [sub_add_cancel] at h1
    constructor
    · intro h; rw [h1] at h
      have : rpow x (q - r) > 1 := by
        by_contra hle; push_neg at hle
        linarith [mul_le_of_le_one_left (rpow_pos' hx0 r).le hle]
      exact sub_pos.mp ((key _).mp this)
    · intro h
      have h2 := (key _).mpr (sub_pos.mpr h)
      linarith [mul_lt_mul_of_pos_right h2 (rpow_pos' hx0 r)]
  intro α; constructor
  · intro h
    rcases lt_trichotomy α 0 with hlt | heq | hgt
    · have hmα := ((ratPow_mono hx0 (by norm_num : (1:ℝ) > 0) (neg_pos.mpr hlt)).mp hx)
      rw [rpow_one_base] at hmα
      rw [show α = -(-α) from by ring, ratPow_neg hx0] at h
      linarith [(div_lt_one (rpow_pos' hx0 (-α))).mpr hmα]
    · rw [heq, rpow_zero' hx0] at h; linarith
    · exact hgt
  · intro h
    have := ((ratPow_mono hx0 (by norm_num : (1:ℝ) > 0) h).mp hx)
    rwa [rpow_one_base] at this

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q > rpow x r ↔ q < r := by
  suffices key : ∀ α, rpow x α < 1 ↔ α > 0 by
    have h1 := ratPow_add hx0.gt (r - q) q; rw [sub_add_cancel] at h1
    constructor
    · intro h; rw [h1] at h
      have : rpow x (r - q) < 1 := by
        by_contra hle; push_neg at hle
        linarith [le_mul_of_one_le_left (rpow_pos' hx0.gt q).le hle]
      exact sub_pos.mp ((key _).mp this)
    · intro h
      have h2 := (key _).mpr (sub_pos.mpr h)
      linarith [mul_lt_of_lt_one_left (rpow_pos' hx0.gt q) h2]
  intro α; constructor
  · intro h
    rcases lt_trichotomy α 0 with hlt | heq | hgt
    · have h_neg : rpow x (-α) < 1 := by
        have := (ratPow_mono (by norm_num : (1:ℝ) > 0) hx0.gt (neg_pos.mpr hlt)).mp (by linarith)
        rwa [rpow_one_base] at this
      rw [show α = -(-α) from by ring, ratPow_neg hx0.gt] at h
      linarith [(one_lt_div (rpow_pos' hx0.gt (-α))).mpr h_neg]
    · rw [heq, rpow_zero' hx0.gt] at h; linarith
    · exact hgt
  · intro h
    have := (ratPow_mono (by norm_num : (1:ℝ) > 0) hx0.gt h).mp (by linarith : (1:ℝ) > x)
    rwa [rpow_one_base] at this

/-- Proposition 6.7.3(f) / Exercise 6.7.1 -/
theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  choose q' hq' using eq_lim_of_rat q
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hy hq'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hy hq', rpow_eq_lim_ratPow (mul_pos hx hy) hq',
    ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; exact mul_rpow hx.le hy.le

end Chapter6
