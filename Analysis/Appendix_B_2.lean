import Mathlib.Tactic
import Analysis.Appendix_B_1

/-!
# Analysis I, Appendix B.2: The decimal representation of real numbers

An implementation of the decimal representation of Mathlib's real numbers {lean}`ℝ`.

This is separate from the way decimal numerals are already represented in Mathlib.  We also represent the integer part of the natural numbers just by {lean}`ℕ`, avoiding using the decimal representation from the
previous section, although we still retain the {name}`AppendixB.Digit` class.
-/

namespace AppendixB

structure NNRealDecimal where
  intPart : ℕ
  fracPart : ℕ → Digit

open NNReal NNRealDecimal

#check mk

@[coe]
noncomputable def NNRealDecimal.toNNReal (d:NNRealDecimal) : NNReal :=
  d.intPart + ∑' i, (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ)

noncomputable instance NNRealDecimal.instCoeNNReal : Coe NNRealDecimal NNReal where
  coe := toNNReal

/-- Exercise B.2.1 -/
theorem NNRealDecimal.toNNReal_conv (d:NNRealDecimal) :
  Summable fun i ↦ (d.fracPart i) * (10:NNReal) ^ (-i-1:ℝ) := by
  refine NNReal.summable_of_le ?_ (NNReal.summable_geometric (r := 1/10) (by norm_num))
  intro i
  calc (d.fracPart i) * (10:NNReal)^(-i-1:ℝ)
      ≤ 10 * (10:NNReal)^(-i-1:ℝ) := by
        gcongr
        exact_mod_cast (d.fracPart i).lt.le
    _ = (10:NNReal)^(-i:ℝ) := by
        nth_rewrite 1 [show (10:NNReal) = (10:NNReal)^(1:ℝ) from (rpow_one 10).symm]
        rw [← rpow_add (by norm_num)]; congr 1; ring
    _ = (1/10:NNReal)^i := by
        rw [rpow_neg, rpow_natCast, one_div]; exact (inv_pow 10 i).symm

theorem NNRealDecimal.surj (x:NNReal) : ∃ d:NNRealDecimal, x = d := by
  -- This proof is written to follow the structure of the original text.
  by_cases h : x = 0
  . use mk 0 fun _ ↦ 0; simp [h, toNNReal]
  let s : ℕ → ℕ := fun n ↦ ⌊ x * 10^n ⌋₊
  have hs (n:ℕ) : s n ≤ x * 10^n := Nat.floor_le (by positivity)
  have hs' (n:ℕ) : x * 10^n < s n + 1 := Nat.lt_floor_add_one _
  have hdigit (n:ℕ) : ∃ a:Digit, s (n+1) = 10 * s n + (a:ℕ) := by
    have hl : (10:NNReal) * s n < s (n+1) + 1 := calc
      _ ≤ 10 * (x * 10^n) := by gcongr; grind
      _ = x * 10^(n+1) := by ring_nf
      _ < _ := hs' _
    have hu : s (n+1) < (10:NNReal) * s n + 10 := calc
      _ ≤ x * 10^(n+1) := hs (n+1)
      _ = 10 * (x * 10^n) := by ring_nf
      _ < 10 * (s n + 1) := by gcongr; grind
      _ = _ := by ring
    norm_cast at hl hu
    set d := s (n+1) - 10 * s n
    have hd : d < 10 := by omega
    have : s (n+1) = 10 * s n + d := by omega
    use Digit.mk hd
  choose a ha using hdigit
  set d := mk (s 0) a; use d
  have hsum (n:ℕ) : s n * (10:NNReal)^(-n:ℝ) = s 0 + ∑ i ∈ .range n, a i * (10:NNReal)^(-i-1:ℝ) := by
    induction' n with n hn; simp
    rw [ha n]; calc
      _ = s n * (10:NNReal)^(-n:ℝ) + a n * 10^(-n-1:ℝ) := by
        simp [add_mul]; ring_nf; congr 1
        rw [mul_assoc, ←rpow_add_one]; ring_nf; norm_num
      _ = s 0 + (∑ i ∈ .range n, a i * (10:NNReal)^(-i-1:ℝ) + a n * 10^(-n-1:ℝ)) := by grind
      _ = _ := by congr; symm; apply Finset.sum_range_succ
  have := (d.toNNReal_conv.tendsto_sum_tsum_nat).const_add (s 0:NNReal)
  convert_to Filter.atTop.Tendsto (fun n ↦ s n * (10:NNReal)^(-n:ℝ)) (nhds (d:NNReal)) at this
  . ext n; rw [hsum n]
  apply tendsto_nhds_unique _ this
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ x - (10:NNReal)^(-n:ℝ)) (h := fun _ ↦ x)
  . convert Filter.Tendsto.const_sub (c := 0) x _
    . simp
    convert tendsto_pow_atTop_nhds_zero_of_lt_one (?_:(1/10:NNReal) < 1) with n
    . rw [←rpow_natCast, one_div, inv_rpow, rpow_neg]
    apply div_lt_one_of_lt; bound
  . exact tendsto_const_nhds
  . intro n; simp; calc
    _ = (x * 10^n) * (10:NNReal)^(-n:ℝ) := by
      rw [mul_assoc, ←rpow_natCast, ←rpow_add]; simp; norm_num
    _ ≤ ((s n:NNReal) + 1)*(10:NNReal)^(-n:ℝ) := by gcongr; grind [le_of_lt]
    _ = _ := by ring
  intro n; simp; calc
    _ ≤ (x * 10^n) * (10:NNReal)^(-n:ℝ) := by gcongr; grind
    _ = x := by rw [mul_assoc, ←rpow_natCast, ←rpow_add]; simp; norm_num

/-- Proposition B.2.2 -/
theorem NNRealDecimal.not_inj : (1:NNReal) = (mk 1 fun _ ↦ 0) ∧ (1:NNReal) = (mk 0 fun _ ↦ 9) := by
  -- This proof is written to follow the structure of the original text.
  simp [toNNReal]
  have := (mk 0 fun _ ↦ 9).toNNReal_conv.tendsto_sum_tsum_nat
  simp at this
  apply tendsto_nhds_unique _ this
  convert_to Filter.atTop.Tendsto (fun n:ℕ ↦ 1 - (10:NNReal)^(-n:ℝ)) (nhds 1) using 2 with n
  . induction' n with n hn
    . simp
    rw [Finset.sum_range_succ, hn, Nat.cast_add, Nat.cast_one, neg_add']
    have : (10:NNReal)^(-n:ℝ) = 10^(-n-1:ℝ) * 10 := by
      rw [←rpow_add_one]; simp; norm_num
    simp [this, ←coe_inj]
    rw [NNReal.coe_sub, NNReal.coe_sub]
    . suffices h : ∀ c a : ℝ, c = 9 → 1 - a * 10 + c * a = 1 - a by apply h; norm_cast
      grind
    . apply rpow_le_one_of_one_le_of_nonpos; norm_num; linarith
    rw [←rpow_add_one]
    apply rpow_le_one_of_one_le_of_nonpos; norm_num; linarith; norm_num
  convert Filter.Tendsto.const_sub (f := fun n:ℕ ↦ (10:NNReal)^(-n:ℝ)) (c := 0) 1 _; simp
  convert tendsto_pow_atTop_nhds_zero_of_lt_one (show (1/10:NNReal) < 1 by bound) with n
  rw [←rpow_natCast, one_div, inv_rpow, rpow_neg]

inductive RealDecimal where
  | pos : NNRealDecimal → RealDecimal
  | neg : NNRealDecimal → RealDecimal

noncomputable instance RealDecimal.instCoeReal : Coe RealDecimal ℝ where
  coe := fun d ↦ match d with
    | RealDecimal.pos d => d.toNNReal
    | RealDecimal.neg d => -(d.toNNReal:ℝ)

theorem RealDecimal.surj (x:ℝ) : ∃ d:RealDecimal, x = d := by
  obtain h | h := le_or_gt 0 x
  . choose d hd using NNRealDecimal.surj (x.toNNReal); use pos d; simp [←hd, h]
  . choose d hd using NNRealDecimal.surj ((-x).toNNReal); use neg d; simp [←hd, show 0 ≤ -x by linarith]

/-- Exercise B.2.2 -/
theorem RealDecimal.not_inj_one (d: RealDecimal) : (d:ℝ) = 1 ↔ (d = pos (mk 1 fun _ ↦ 0) ∨ d = pos (mk 0 fun _ ↦ 9)) := by
  have hcoe9 : ((9:Digit):NNReal) = (9:NNReal) := by
    rw [show ((9:Digit):NNReal) = (((9:Digit):ℕ):NNReal) from rfl, show ((9:Digit):ℕ) = 9 from rfl,
      Nat.cast_ofNat]
  have T9 : ∑' (i:ℕ), (9:NNReal) * (10:NNReal)^(-i-1:ℝ) = 1 := by
    have h := not_inj.2
    simp only [toNNReal, hcoe9, Nat.cast_zero, zero_add] at h
    exact h.symm
  have h9sum : Summable (fun (i:ℕ) ↦ (9:NNReal) * (10:NNReal)^(-i-1:ℝ)) := by
    have h := (mk 0 fun _ ↦ 9).toNNReal_conv
    simpa only [hcoe9] using h
  constructor
  · intro hd
    cases d with
    | neg e =>
      exfalso
      have heq : (↑(RealDecimal.neg e) : ℝ) = -(↑e.toNNReal : ℝ) := rfl
      rw [heq] at hd
      have hnn : (0:ℝ) ≤ ↑e.toNNReal := e.toNNReal.coe_nonneg
      linarith
    | pos e =>
      have hf : (e.intPart:NNReal) + ∑' (i:ℕ), ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ) = 1 := by
        have heq : (↑(RealDecimal.pos e) : ℝ) = (↑e.toNNReal : ℝ) := rfl
        rw [heq] at hd
        have hf : e.toNNReal = 1 := by exact_mod_cast hd
        rwa [toNNReal] at hf
      have hFsum : Summable (fun (i:ℕ) ↦ ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ)) :=
        e.toNNReal_conv
      have hbound : ∀ (i:ℕ), ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ) ≤ (9:NNReal) * (10:NNReal)^(-i-1:ℝ) := by
        intro i
        gcongr
        have h10 := (e.fracPart i).lt
        have : (e.fracPart i:ℕ) ≤ 9 := by omega
        exact_mod_cast this
      have hip : e.intPart ≤ 1 := by
        have hle : (e.intPart:NNReal) ≤ 1 := by rw [← hf]; exact self_le_add_right _ _
        exact_mod_cast hle
      have hcase : e.intPart = 0 ∨ e.intPart = 1 := by omega
      rcases hcase with h | h
      · right
        have hF1 : (∑' (i:ℕ), ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ)) = 1 := by
          rw [h, Nat.cast_zero, zero_add] at hf; exact hf
        have hdig : ∀ i, e.fracPart i = 9 := by
          intro k
          by_contra hk
          have hlt9 : (e.fracPart k:ℕ) < 9 := by
            have h10 := (e.fracPart k).lt
            have hne := mt (Digit.inj (e.fracPart k) 9).mpr hk
            rw [show ((9:Digit):ℕ) = 9 from rfl] at hne
            omega
          have hpos : (0:NNReal) < (10:NNReal)^(-k-1:ℝ) := by positivity
          have hlt : ((e.fracPart k):NNReal) * (10:NNReal)^(-k-1:ℝ) < (9:NNReal) * (10:NNReal)^(-k-1:ℝ) :=
            mul_lt_mul_of_pos_right (by exact_mod_cast hlt9) hpos
          have hcontra := NNReal.tsum_lt_tsum hbound hlt h9sum
          rw [hF1, T9] at hcontra
          exact lt_irrefl 1 hcontra
        obtain ⟨ip, fp⟩ := e
        rw [show ip = 0 from h, show fp = (fun _ ↦ (9:Digit)) from funext hdig]
      · left
        have hF0 : (∑' (i:ℕ), ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ)) = 0 := by
          rw [h, Nat.cast_one] at hf; simpa using hf
        have hdig : ∀ i, e.fracPart i = 0 := by
          intro k
          have hz := (hFsum.tsum_eq_zero_iff).mp hF0 k
          have hzero : ((e.fracPart k):NNReal) = 0 := by
            rcases mul_eq_zero.mp hz with h' | h'
            · exact h'
            · have hpos : (0:NNReal) < (10:NNReal)^(-k-1:ℝ) := by positivity
              exact absurd h' hpos.ne'
          have : (e.fracPart k:ℕ) = 0 := by exact_mod_cast hzero
          rw [Digit.inj, show ((0:Digit):ℕ) = 0 from rfl]; exact this
        obtain ⟨ip, fp⟩ := e
        rw [show ip = 1 from h, show fp = (fun _ ↦ (0:Digit)) from funext hdig]
  · rintro (rfl | rfl)
    · show (↑(mk 1 fun _ ↦ 0).toNNReal : ℝ) = 1
      rw [← not_inj.1]; norm_num
    · show (↑(mk 0 fun _ ↦ 9).toNNReal : ℝ) = 1
      rw [← not_inj.2]; norm_num

theorem coe_digit_nine : ((9:Digit):NNReal) = 9 := by
  rw [show ((9:Digit):NNReal) = (((9:Digit):ℕ):NNReal) from rfl, show ((9:Digit):ℕ) = 9 from rfl,
    Nat.cast_ofNat]

theorem coe_digit_le_nine (a : Digit) : (a:NNReal) ≤ 9 := by
  have h : (a:ℕ) ≤ 9 := by have := a.lt; omega
  exact_mod_cast h

theorem coe_digit_lt_nine_of_ne {a : Digit} (h : a ≠ 9) : (a:NNReal) < 9 := by
  have hne := mt (Digit.inj a 9).mpr h
  rw [show ((9:Digit):ℕ) = 9 from rfl] at hne
  have h9 : (a:ℕ) < 9 := by have := a.lt; omega
  exact_mod_cast h9

theorem coe_digit_eq_zero_iff (a : Digit) : (a:NNReal) = 0 ↔ a = 0 := by
  rw [Nat.cast_eq_zero, show (0:ℕ) = ((0:Digit):ℕ) from rfl, ← Digit.inj]

/-- The all-nines fractional tail sums to one: the engine behind `0.999… = 1`. -/
theorem sum_nines : ∑' (i:ℕ), (9:NNReal) * (10:NNReal)^(-i-1:ℝ) = 1 := by
  have h := not_inj.2
  simp only [toNNReal, coe_digit_nine, Nat.cast_zero, zero_add] at h
  exact h.symm

theorem nines_summable : Summable (fun (i:ℕ) ↦ (9:NNReal) * (10:NNReal)^(-i-1:ℝ)) := by
  have h := (mk 0 fun _ ↦ 9).toNNReal_conv
  simpa only [coe_digit_nine] using h

/-- The value 0.dₖdₖ₊₁dₖ₊₂… of the digit tail of e starting at position k. -/
noncomputable def NNRealDecimal.tailFrom (e : NNRealDecimal) (k : ℕ) : NNReal :=
  (mk 0 (fun i ↦ e.fracPart (i + k))).toNNReal

theorem NNRealDecimal.tailFrom_summable (e : NNRealDecimal) (k : ℕ) :
    Summable (fun i ↦ ((e.fracPart (i + k)):NNReal) * (10:NNReal)^(-i-1:ℝ)) :=
  (mk 0 (fun i ↦ e.fracPart (i + k))).toNNReal_conv

theorem NNRealDecimal.tailFrom_eq (e : NNRealDecimal) (k : ℕ) :
    e.tailFrom k = ∑' i, ((e.fracPart (i + k)):NNReal) * (10:NNReal)^(-i-1:ℝ) := by
  rw [tailFrom, toNNReal]; simp

/-- Split a decimal's value into its length-k prefix and the (scaled) tail from position k. -/
theorem NNRealDecimal.toNNReal_eq_prefix_add_tail (e : NNRealDecimal) (k : ℕ) :
    e.toNNReal = ((e.intPart:NNReal)
        + ∑ i ∈ Finset.range k, ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ))
        + (10:NNReal)^(-k:ℝ) * e.tailFrom k := by
  rw [toNNReal, NNReal.sum_add_tsum_nat_add k e.toNNReal_conv, ← add_assoc]
  congr 1
  rw [tailFrom_eq, ← tsum_mul_left]
  congr 1; funext i
  rw [show (-(↑(i+k):ℝ)-1) = -(k:ℝ) + (-(i:ℝ)-1) by push_cast; ring, rpow_add (by norm_num)]
  ring

theorem NNRealDecimal.tailFrom_le_one (e : NNRealDecimal) (k : ℕ) : e.tailFrom k ≤ 1 := by
  rw [tailFrom_eq]
  calc ∑' (i:ℕ), ((e.fracPart (i+k)):NNReal) * (10:NNReal)^(-i-1:ℝ)
      ≤ ∑' (i:ℕ), (9:NNReal) * (10:NNReal)^(-i-1:ℝ) :=
        Summable.tsum_le_tsum (fun i ↦ by gcongr; exact coe_digit_le_nine _)
          (e.tailFrom_summable k) nines_summable
    _ = 1 := sum_nines

theorem NNRealDecimal.tailFrom_eq_zero_iff (e : NNRealDecimal) (k : ℕ) :
    e.tailFrom k = 0 ↔ ∀ i, e.fracPart (i + k) = 0 := by
  rw [tailFrom_eq, (e.tailFrom_summable k).tsum_eq_zero_iff]
  refine forall_congr' (fun i ↦ ?_)
  rw [mul_eq_zero, or_iff_left (by positivity : (0:NNReal) < (10:NNReal)^(-i-1:ℝ)).ne',
    coe_digit_eq_zero_iff]

theorem NNRealDecimal.tailFrom_eq_one_iff (e : NNRealDecimal) (k : ℕ) :
    e.tailFrom k = 1 ↔ ∀ i, e.fracPart (i + k) = 9 := by
  constructor
  · intro h1
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, hj⟩ := hcon
    have hpos : (0:NNReal) < (10:NNReal)^(-j-1:ℝ) := by positivity
    have hb : ∀ (i:ℕ), ((e.fracPart (i+k)):NNReal) * (10:NNReal)^(-i-1:ℝ)
        ≤ (9:NNReal) * (10:NNReal)^(-i-1:ℝ) := fun i ↦ by gcongr; exact coe_digit_le_nine _
    have hlt : ((e.fracPart (j+k)):NNReal) * (10:NNReal)^(-j-1:ℝ) < (9:NNReal) * (10:NNReal)^(-j-1:ℝ) :=
      mul_lt_mul_of_pos_right (coe_digit_lt_nine_of_ne hj) hpos
    have hcontra := NNReal.tsum_lt_tsum hb hlt nines_summable
    rw [← tailFrom_eq, h1, sum_nines] at hcontra
    exact lt_irrefl 1 hcontra
  · intro h9
    rw [tailFrom_eq]
    calc ∑' (i:ℕ), ((e.fracPart (i+k)):NNReal) * (10:NNReal)^(-i-1:ℝ)
        = ∑' (i:ℕ), (9:NNReal) * (10:NNReal)^(-i-1:ℝ) := by
          congr 1; funext i; rw [h9 i, coe_digit_nine]
      _ = 1 := sum_nines

/-- Peel one digit off a tail: 0.dₖdₖ₊₁… = 10⁻¹·(dₖ + 0.dₖ₊₁dₖ₊₂…). -/
theorem NNRealDecimal.tailFrom_succ (e : NNRealDecimal) (k : ℕ) :
    e.tailFrom k = (10:NNReal)^(-1:ℝ) * (((e.fracPart k):NNReal) + e.tailFrom (k+1)) := by
  have hfun : (fun j ↦ e.fracPart (j + 1 + k)) = (fun j ↦ e.fracPart (j + (k+1))) := by
    funext j; congr 1; omega
  have htl : (mk 0 (fun i ↦ e.fracPart (i + k))).tailFrom 1 = e.tailFrom (k+1) := by
    show (mk 0 (fun j ↦ e.fracPart (j + 1 + k))).toNNReal
       = (mk 0 (fun j ↦ e.fracPart (j + (k+1)))).toNNReal
    rw [hfun]
  have key := (mk 0 (fun i ↦ e.fracPart (i + k))).toNNReal_eq_prefix_add_tail 1
  rw [htl] at key
  rw [show e.tailFrom k = (mk 0 (fun i ↦ e.fracPart (i + k))).toNNReal from rfl, key]
  simp only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one, zero_add, neg_zero, zero_sub]
  ring

/-- If two decimals have the same value and agree on the integer part and the first k digits,
their tails from position k are equal. -/
theorem NNRealDecimal.tailFrom_eq_of_prefix_eq {e e' : NNRealDecimal} (k : ℕ)
    (hval : e.toNNReal = e'.toNNReal) (hint : e.intPart = e'.intPart)
    (hpre : ∀ i, i < k → e.fracPart i = e'.fracPart i) :
    e.tailFrom k = e'.tailFrom k := by
  have hpref : (e.intPart:NNReal)
        + ∑ i ∈ Finset.range k, ((e.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ)
      = (e'.intPart:NNReal)
        + ∑ i ∈ Finset.range k, ((e'.fracPart i):NNReal) * (10:NNReal)^(-i-1:ℝ) := by
    rw [hint]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpre i (Finset.mem_range.mp hi)]
  rw [e.toNNReal_eq_prefix_add_tail k, e'.toNNReal_eq_prefix_add_tail k, hpref] at hval
  exact mul_left_cancel₀ (by positivity : (0:NNReal) < (10:NNReal)^(-k:ℝ)).ne'
    (add_left_cancel hval)

/-- Comparing two equal tails at position k: either they share digit k and the next tails are
equal too, or they form a `…a000…` vs `…(a+1)999…` split (one tail all-nines, the other all-zeros). -/
theorem NNRealDecimal.digit_step {e e' : NNRealDecimal} (k : ℕ)
    (h : e.tailFrom k = e'.tailFrom k) :
    (e.fracPart k = e'.fracPart k ∧ e.tailFrom (k+1) = e'.tailFrom (k+1))
    ∨ ((e.fracPart k : ℕ) + 1 = (e'.fracPart k : ℕ) ∧ e.tailFrom (k+1) = 1 ∧ e'.tailFrom (k+1) = 0)
    ∨ ((e'.fracPart k : ℕ) + 1 = (e.fracPart k : ℕ) ∧ e'.tailFrom (k+1) = 1 ∧ e.tailFrom (k+1) = 0) := by
  rw [tailFrom_succ e k, tailFrom_succ e' k] at h
  have hcancel := mul_left_cancel₀ (by positivity : (0:NNReal) < (10:NNReal)^(-1:ℝ)).ne' h
  have key : ((e.fracPart k:ℕ):ℝ) + (e.tailFrom (k+1):ℝ)
           = ((e'.fracPart k:ℕ):ℝ) + (e'.tailFrom (k+1):ℝ) := by
    have h2 := congrArg NNReal.toReal hcancel
    push_cast at h2
    exact_mod_cast h2
  have hTe0 : (0:ℝ) ≤ (e.tailFrom (k+1):ℝ) := (e.tailFrom (k+1)).coe_nonneg
  have hTe1 : (e.tailFrom (k+1):ℝ) ≤ 1 := by exact_mod_cast e.tailFrom_le_one (k+1)
  have hTe'0 : (0:ℝ) ≤ (e'.tailFrom (k+1):ℝ) := (e'.tailFrom (k+1)).coe_nonneg
  have hTe'1 : (e'.tailFrom (k+1):ℝ) ≤ 1 := by exact_mod_cast e'.tailFrom_le_one (k+1)
  have hab1 : (e.fracPart k:ℕ) ≤ (e'.fracPart k:ℕ) + 1 := by
    have : ((e.fracPart k:ℕ):ℝ) ≤ ((e'.fracPart k:ℕ):ℝ) + 1 := by linarith
    exact_mod_cast this
  have hab2 : (e'.fracPart k:ℕ) ≤ (e.fracPart k:ℕ) + 1 := by
    have : ((e'.fracPart k:ℕ):ℝ) ≤ ((e.fracPart k:ℕ):ℝ) + 1 := by linarith
    exact_mod_cast this
  rcases Nat.lt_trichotomy (e.fracPart k:ℕ) (e'.fracPart k:ℕ) with hlt | heq | hgt
  · right; left
    have hd1 : (e.fracPart k:ℕ) + 1 = (e'.fracPart k:ℕ) := by omega
    have hcast : ((e'.fracPart k:ℕ):ℝ) = ((e.fracPart k:ℕ):ℝ) + 1 := by exact_mod_cast hd1.symm
    refine ⟨hd1, ?_, ?_⟩
    · have : (e.tailFrom (k+1):ℝ) = 1 := by linarith
      exact_mod_cast this
    · have : (e'.tailFrom (k+1):ℝ) = 0 := by linarith
      exact_mod_cast this
  · left
    refine ⟨by rw [Digit.inj]; exact heq, ?_⟩
    have hcast : ((e.fracPart k:ℕ):ℝ) = ((e'.fracPart k:ℕ):ℝ) := by exact_mod_cast heq
    have : (e.tailFrom (k+1):ℝ) = (e'.tailFrom (k+1):ℝ) := by linarith
    exact_mod_cast this
  · right; right
    have hd1 : (e'.fracPart k:ℕ) + 1 = (e.fracPart k:ℕ) := by omega
    have hcast : ((e.fracPart k:ℕ):ℝ) = ((e'.fracPart k:ℕ):ℝ) + 1 := by exact_mod_cast hd1.symm
    refine ⟨hd1, ?_, ?_⟩
    · have : (e'.tailFrom (k+1):ℝ) = 1 := by linarith
      exact_mod_cast this
    · have : (e.tailFrom (k+1):ℝ) = 0 := by linarith
      exact_mod_cast this

theorem NNRealDecimal.toNNReal_eq_intPart_add_tail (e : NNRealDecimal) :
    e.toNNReal = (e.intPart:NNReal) + e.tailFrom 0 := by
  have h := e.toNNReal_eq_prefix_add_tail 0
  simpa using h

/-- The integer-part analog of the digit step at the integer boundary. -/
theorem NNRealDecimal.intPart_step {e e' : NNRealDecimal} (h : e.toNNReal = e'.toNNReal) :
    (e.intPart = e'.intPart ∧ e.tailFrom 0 = e'.tailFrom 0)
    ∨ (e.intPart + 1 = e'.intPart ∧ e.tailFrom 0 = 1 ∧ e'.tailFrom 0 = 0)
    ∨ (e'.intPart + 1 = e.intPart ∧ e'.tailFrom 0 = 1 ∧ e.tailFrom 0 = 0) := by
  rw [toNNReal_eq_intPart_add_tail e, toNNReal_eq_intPart_add_tail e'] at h
  have key : ((e.intPart:ℕ):ℝ) + (e.tailFrom 0:ℝ) = ((e'.intPart:ℕ):ℝ) + (e'.tailFrom 0:ℝ) := by
    have h2 := congrArg NNReal.toReal h
    push_cast at h2
    exact_mod_cast h2
  have hTe0 : (0:ℝ) ≤ (e.tailFrom 0:ℝ) := (e.tailFrom 0).coe_nonneg
  have hTe1 : (e.tailFrom 0:ℝ) ≤ 1 := by exact_mod_cast e.tailFrom_le_one 0
  have hTe'0 : (0:ℝ) ≤ (e'.tailFrom 0:ℝ) := (e'.tailFrom 0).coe_nonneg
  have hTe'1 : (e'.tailFrom 0:ℝ) ≤ 1 := by exact_mod_cast e'.tailFrom_le_one 0
  have hab1 : e.intPart ≤ e'.intPart + 1 := by
    have : ((e.intPart:ℕ):ℝ) ≤ ((e'.intPart:ℕ):ℝ) + 1 := by linarith
    exact_mod_cast this
  have hab2 : e'.intPart ≤ e.intPart + 1 := by
    have : ((e'.intPart:ℕ):ℝ) ≤ ((e.intPart:ℕ):ℝ) + 1 := by linarith
    exact_mod_cast this
  rcases Nat.lt_trichotomy e.intPart e'.intPart with hlt | heq | hgt
  · right; left
    have hd1 : e.intPart + 1 = e'.intPart := by omega
    have hcast : ((e'.intPart:ℕ):ℝ) = ((e.intPart:ℕ):ℝ) + 1 := by exact_mod_cast hd1.symm
    refine ⟨hd1, ?_, ?_⟩
    · have : (e.tailFrom 0:ℝ) = 1 := by linarith
      exact_mod_cast this
    · have : (e'.tailFrom 0:ℝ) = 0 := by linarith
      exact_mod_cast this
  · left
    refine ⟨heq, ?_⟩
    have hcast : ((e.intPart:ℕ):ℝ) = ((e'.intPart:ℕ):ℝ) := by exact_mod_cast heq
    have : (e.tailFrom 0:ℝ) = (e'.tailFrom 0:ℝ) := by linarith
    exact_mod_cast this
  · right; right
    have hd1 : e'.intPart + 1 = e.intPart := by omega
    have hcast : ((e.intPart:ℕ):ℝ) = ((e'.intPart:ℕ):ℝ) + 1 := by exact_mod_cast hd1.symm
    refine ⟨hd1, ?_, ?_⟩
    · have : (e'.tailFrom 0:ℝ) = 1 := by linarith
      exact_mod_cast this
    · have : (e.tailFrom 0:ℝ) = 0 := by linarith
      exact_mod_cast this

/-- The low base-ten digits of a natural number, weighted by their place value. -/
theorem sum_base_ten (p m : ℕ) : ∑ j ∈ Finset.range m, (p / 10^j % 10) * 10^j = p % 10^m := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ring

/-- The k-th fractional digit of the trailing-zeros expansion of p / 10^m. -/
def termDigit (p m k : ℕ) : Digit :=
  if k < m then Digit.mk (Nat.mod_lt (p / 10^(m-1-k)) (by norm_num : (0:ℕ) < 10)) else 0

/-- The trailing-zeros decimal representation of p / 10^m. -/
def termRep (p m : ℕ) : NNRealDecimal := mk (p / 10^m) (termDigit p m)

theorem termDigit_eq_zero {p m k : ℕ} (h : m ≤ k) : termDigit p m k = 0 := by
  rw [termDigit, if_neg (by omega)]

theorem termDigit_toNat {p m k : ℕ} (h : k < m) : (termDigit p m k : ℕ) = p / 10^(m-1-k) % 10 := by
  rw [termDigit, if_pos h]

theorem termRep_toNNReal (p m : ℕ) : (termRep p m).toNNReal = (p:NNReal) / (10:NNReal)^m := by
  have htail : (termRep p m).tailFrom m = 0 := by
    rw [tailFrom_eq_zero_iff]; intro i; exact termDigit_eq_zero le_add_self
  rw [toNNReal_eq_prefix_add_tail (termRep p m) m, htail, mul_zero, add_zero]
  simp only [termRep]
  rw [eq_div_iff (pow_ne_zero m (by norm_num : (10:NNReal) ≠ 0)), add_mul, Finset.sum_mul]
  have hterm : ∀ k ∈ Finset.range m,
      ((termDigit p m k : NNReal) * (10:NNReal)^(-k-1:ℝ)) * (10:NNReal)^m
      = (((termDigit p m k:ℕ) * 10^(m-1-k) : ℕ):NNReal) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hpow : (10:NNReal)^(-(k:ℝ)-1) * (10:NNReal)^m = (10:NNReal)^(m-1-k) := by
      rw [← rpow_natCast (10:NNReal) m, ← rpow_add (by norm_num),
        ← rpow_natCast (10:NNReal) (m-1-k), show m-1-k = m-(k+1) from by omega,
        Nat.cast_sub (by omega : k+1 ≤ m)]
      congr 1; push_cast; ring
    rw [mul_assoc, hpow]
    push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  have hsum : ∑ k ∈ Finset.range m, (termDigit p m k:ℕ) * 10^(m-1-k) = p % 10^m := by
    have hre : ∀ k ∈ Finset.range m,
        (termDigit p m k:ℕ) * 10^(m-1-k) = (p / 10^(m-1-k) % 10) * 10^(m-1-k) := by
      intro k hk; rw [termDigit_toNat (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl hre, Finset.sum_range_reflect (fun j => (p/10^j % 10) * 10^j) m,
      sum_base_ten]
  have hnat : (p / 10^m) * 10^m + ∑ k ∈ Finset.range m, (termDigit p m k:ℕ) * 10^(m-1-k) = p := by
    rw [hsum, Nat.mul_comm]; exact Nat.div_add_mod p (10^m)
  have hcast := congrArg (Nat.cast (R := NNReal)) hnat
  push_cast at hcast ⊢
  exact hcast

/-- Any trailing-zeros fraction can be written with numerator zero, exponent zero, or numerator
not divisible by ten. -/
theorem exists_reduced : ∀ (m p : ℕ), ∃ (p' m' : ℕ),
    (p:NNReal)/(10:NNReal)^m = (p':NNReal)/(10:NNReal)^m'
    ∧ (p' = 0 ∨ m' = 0 ∨ ¬ (10 ∣ p')) := by
  intro m
  induction m with
  | zero => intro p; exact ⟨p, 0, rfl, Or.inr (Or.inl rfl)⟩
  | succ m ih =>
    intro p
    by_cases h : 10 ∣ p
    · obtain ⟨q, rfl⟩ := h
      obtain ⟨p', m', heq, hcond⟩ := ih q
      refine ⟨p', m', ?_, hcond⟩
      rw [← heq, pow_succ, show ((10*q:ℕ):NNReal) = 10 * (q:NNReal) by push_cast; ring]
      field_simp
      ring
    · exact ⟨p, m+1, rfl, Or.inr (Or.inr h)⟩

/-- The nines-partner digit function: agree below the last place, decrement there, nines after. -/
def termDigit9 (p m k : ℕ) : Digit :=
  if k < m - 1 then termDigit p m k
  else if k = m - 1 then Digit.mk (show p % 10 - 1 < 10 from by omega)
  else 9

/-- The trailing-nines representation partnering the trailing-zeros one. -/
def termRep9 (p m : ℕ) : NNRealDecimal := mk (p / 10^m) (termDigit9 p m)

theorem termRep9_toNNReal {p m : ℕ} (hm : 1 ≤ m) (hp : ¬ 10 ∣ p) :
    (termRep9 p m).toNNReal = (p:NNReal)/(10:NNReal)^m := by
  have hp10 : 1 ≤ p % 10 := by
    rcases Nat.eq_zero_or_pos (p % 10) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hp
    · exact h
  have hd9 : (termDigit9 p m (m-1):ℕ) = p % 10 - 1 := by
    rw [termDigit9, if_neg (by omega), if_pos rfl]
  have htail : (termRep p m).tailFrom (m-1) = (10:NNReal)^(-1:ℝ) * ((p%10:ℕ):NNReal) := by
    rw [tailFrom_succ]
    have ht0 : (termRep p m).tailFrom (m-1+1) = 0 := by
      rw [show m-1+1 = m from by omega, tailFrom_eq_zero_iff]; intro i
      exact termDigit_eq_zero le_add_self
    rw [ht0, add_zero]
    congr 1
    show ((termDigit p m (m-1):ℕ):NNReal) = ((p%10:ℕ):NNReal)
    congr 1
    rw [termDigit_toNat (by omega), show m-1-(m-1)=0 from by omega, pow_zero, Nat.div_one]
  have htail9 : (termRep9 p m).tailFrom (m-1) = (10:NNReal)^(-1:ℝ) * ((p%10:ℕ):NNReal) := by
    rw [tailFrom_succ]
    have ht9 : (termRep9 p m).tailFrom (m-1+1) = 1 := by
      rw [show m-1+1 = m from by omega, tailFrom_eq_one_iff]; intro i
      show termDigit9 p m (i+m) = 9
      rw [termDigit9, if_neg (by omega), if_neg (by omega)]
    rw [ht9]
    congr 1
    show ((termDigit9 p m (m-1):ℕ):NNReal) + 1 = ((p%10:ℕ):NNReal)
    rw [hd9, show ((p%10-1:ℕ):NNReal) + 1 = ((p%10:ℕ):NNReal) from by
      rw [← Nat.cast_one (R := NNReal), ← Nat.cast_add, Nat.cast_inj]; omega]
  rw [← termRep_toNNReal p m, toNNReal_eq_prefix_add_tail (termRep9 p m) (m-1),
    toNNReal_eq_prefix_add_tail (termRep p m) (m-1), htail, htail9]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  show ((termDigit9 p m i:NNReal)) * (10:NNReal)^(-i-1:ℝ)
     = ((termDigit p m i:NNReal)) * (10:NNReal)^(-i-1:ℝ)
  rw [show termDigit9 p m i = termDigit p m i from by rw [termDigit9, if_pos hi]]

theorem intRep9_toNNReal {K : ℕ} (hK : 1 ≤ K) :
    (mk (K-1) (fun _ ↦ (9:Digit))).toNNReal = (K:NNReal) := by
  rw [toNNReal_eq_intPart_add_tail]
  have htail : (mk (K-1) (fun _ ↦ (9:Digit))).tailFrom 0 = 1 := by
    rw [tailFrom_eq_one_iff]; intro i; rfl
  rw [htail]
  show ((K-1:ℕ):NNReal) + 1 = (K:NNReal)
  rw [← Nat.cast_one (R := NNReal), ← Nat.cast_add, Nat.cast_inj]; omega

/-- Two distinct decimals with equal value and equal integer parts agree up to a first position,
where the digits differ by one and the two tails become all-nines and all-zeros. -/
theorem NNRealDecimal.digits_split {e e' : NNRealDecimal}
    (hv : e.toNNReal = e'.toNNReal) (hint : e.intPart = e'.intPart) (hne : e ≠ e') :
    ∃ p, (∀ i < p, e.fracPart i = e'.fracPart i) ∧
      (((e.fracPart p:ℕ) + 1 = (e'.fracPart p:ℕ) ∧ (∀ j, e.fracPart (p+1+j) = 9)
          ∧ (∀ j, e'.fracPart (p+1+j) = 0))
       ∨ ((e'.fracPart p:ℕ) + 1 = (e.fracPart p:ℕ) ∧ (∀ j, e'.fracPart (p+1+j) = 9)
          ∧ (∀ j, e.fracPart (p+1+j) = 0))) := by
  classical
  have hdiff : ∃ k, e.fracPart k ≠ e'.fracPart k := by
    by_contra h
    push_neg at h
    apply hne
    obtain ⟨ip, fp⟩ := e
    obtain ⟨ip', fp'⟩ := e'
    have hii : ip = ip' := hint
    subst hii
    congr 1
    funext k
    exact h k
  have hp_spec : e.fracPart (Nat.find hdiff) ≠ e'.fracPart (Nat.find hdiff) := Nat.find_spec hdiff
  have hp_min : ∀ i < Nat.find hdiff, e.fracPart i = e'.fracPart i := fun i hi =>
    not_not.mp (Nat.find_min hdiff hi)
  refine ⟨Nat.find hdiff, hp_min, ?_⟩
  have htp : e.tailFrom (Nat.find hdiff) = e'.tailFrom (Nat.find hdiff) :=
    tailFrom_eq_of_prefix_eq _ hv hint hp_min
  rcases digit_step (Nat.find hdiff) htp with ⟨heq, _⟩ | ⟨hd, h1, h0⟩ | ⟨hd, h1, h0⟩
  · exact absurd heq hp_spec
  · left
    refine ⟨hd, fun j => ?_, fun j => ?_⟩
    · rw [show Nat.find hdiff+1+j = j+(Nat.find hdiff+1) from by ring]
      exact (tailFrom_eq_one_iff e _).mp h1 j
    · rw [show Nat.find hdiff+1+j = j+(Nat.find hdiff+1) from by ring]
      exact (tailFrom_eq_zero_iff e' _).mp h0 j
  · right
    refine ⟨hd, fun j => ?_, fun j => ?_⟩
    · rw [show Nat.find hdiff+1+j = j+(Nat.find hdiff+1) from by ring]
      exact (tailFrom_eq_one_iff e' _).mp h1 j
    · rw [show Nat.find hdiff+1+j = j+(Nat.find hdiff+1) from by ring]
      exact (tailFrom_eq_zero_iff e _).mp h0 j

theorem NNRealDecimal.ext' {e e' : NNRealDecimal} (hI : e.intPart = e'.intPart)
    (hd : ∀ k, e.fracPart k = e'.fracPart k) : e = e' := by
  obtain ⟨ip, fp⟩ := e; obtain ⟨ip', fp'⟩ := e'
  have hii : ip = ip' := hI
  subst hii; congr 1; funext k; exact hd k

theorem intRep0_toNNReal (K : ℕ) : (mk K (fun _ ↦ (0:Digit))).toNNReal = (K:NNReal) := by
  rw [toNNReal_eq_intPart_add_tail]
  have htail : (mk K (fun _ ↦ (0:Digit))).tailFrom 0 = 0 := by
    rw [tailFrom_eq_zero_iff]; intro i; rfl
  rw [htail, add_zero]

/-- A positive integer has exactly the trailing-zeros and trailing-nines representations. -/
theorem rep_int_unique {K : ℕ} (hK : 1 ≤ K) {e : NNRealDecimal} (he : e.toNNReal = (K:NNReal)) :
    e = mk K (fun _ ↦ 0) ∨ e = mk (K-1) (fun _ ↦ 9) := by
  have hvv : e.toNNReal = (mk K (fun _ ↦ (0:Digit))).toNNReal := by rw [he, intRep0_toNNReal]
  have he1tail : (mk K (fun _ ↦ (0:Digit))).tailFrom 0 = 0 := by
    rw [tailFrom_eq_zero_iff]; intro i; rfl
  rcases intPart_step hvv with ⟨hi, ht⟩ | ⟨hi, ht1, ht0⟩ | ⟨hi, ht1, ht0⟩
  · left
    apply NNRealDecimal.ext' hi
    intro k
    have : e.tailFrom 0 = 0 := by rw [ht, he1tail]
    exact (tailFrom_eq_zero_iff e 0).mp this k
  · right
    have hiK : (mk K (fun _ ↦ (0:Digit))).intPart = K := rfl
    have hint : e.intPart = K - 1 := by omega
    apply NNRealDecimal.ext' (by simpa using hint)
    intro k
    exact (tailFrom_eq_one_iff e 0).mp ht1 k
  · exact absurd (ht1.symm.trans he1tail) (by norm_num)

/-- A non-integer trailing fraction has exactly the trailing-zeros and trailing-nines reps. -/
theorem rep_nonint_unique {p m : ℕ} (hm : 1 ≤ m) (hp : ¬ 10 ∣ p) {e : NNRealDecimal}
    (he : e.toNNReal = (p:NNReal)/(10:NNReal)^m) :
    e = termRep p m ∨ e = termRep9 p m := by
  have hp10 : 1 ≤ p % 10 := by
    rcases Nat.eq_zero_or_pos (p % 10) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hp
    · exact h
  have hd9 : (termDigit9 p m (m-1):ℕ) = p % 10 - 1 := by
    rw [termDigit9, if_neg (by omega), if_pos rfl]
  have hlast : termDigit p m (m-1) ≠ 0 := by
    have hz : (termDigit p m (m-1):ℕ) = p % 10 := by
      rw [termDigit_toNat (by omega), show m-1-(m-1)=0 from by omega, pow_zero, Nat.div_one]
    intro hc
    rw [hc] at hz
    change (0:ℕ) = p % 10 at hz
    omega
  have hII : (termRep p m).intPart = (termRep9 p m).intPart := rfl
  by_cases hcase : e = termRep p m
  · exact Or.inl hcase
  · right
    have hvv : e.toNNReal = (termRep p m).toNNReal := by rw [he, termRep_toNNReal]
    have hne0 : (termRep p m).tailFrom 0 ≠ 0 := fun h0 =>
      hlast ((tailFrom_eq_zero_iff (termRep p m) 0).mp h0 (m-1))
    have hne1 : (termRep p m).tailFrom 0 ≠ 1 := by
      intro h1
      have h := (tailFrom_eq_one_iff (termRep p m) 0).mp h1 m
      rw [show (termRep p m).fracPart (m+0) = termDigit p m m from rfl,
        termDigit_eq_zero (le_refl m)] at h
      exact absurd h (by decide)
    have hint : e.intPart = (termRep p m).intPart := by
      rcases intPart_step hvv with ⟨hi, _⟩ | ⟨_, _, ht0⟩ | ⟨_, ht1, _⟩
      · exact hi
      · exact absurd ht0 hne0
      · exact absurd ht1 hne1
    rcases digits_split hvv hint hcase with ⟨q, hbelow, hsplit⟩
    rcases hsplit with ⟨hdq, h9e, h0r⟩ | ⟨hdq, h9r, h0e⟩
    · -- e is the nines side; termRep is zeros side. Pin q = m-1.
      have hqlt : q < m := by
        by_contra hc
        push_neg at hc
        rw [show (termRep p m).fracPart q = termDigit p m q from rfl, termDigit_eq_zero hc,
          show ((0:Digit):ℕ) = 0 from rfl] at hdq
        omega
      have hqge : m - 1 ≤ q := by
        by_contra hc
        push_neg at hc
        have h0 := h0r (m-1-(q+1))
        rw [show q+1+(m-1-(q+1)) = m-1 from by omega] at h0
        exact hlast h0
      have hqm : q = m - 1 := by omega
      subst hqm
      apply NNRealDecimal.ext' (hint.trans hII)
      intro k
      rcases lt_trichotomy k (m-1) with hk | hk | hk
      · rw [hbelow k hk]
        show termDigit p m k = termDigit9 p m k
        rw [termDigit9, if_pos hk]
      · subst hk
        show e.fracPart (m-1) = termDigit9 p m (m-1)
        rw [Digit.inj, hd9]
        have hd : ((termRep p m).fracPart (m-1) : ℕ) = p % 10 := by
          show (termDigit p m (m-1) : ℕ) = p % 10
          rw [termDigit_toNat (by omega), show m-1-(m-1)=0 from by omega, pow_zero, Nat.div_one]
        omega
      · have he9 : e.fracPart k = 9 := by
          have h := h9e (k - m)
          rwa [show (m-1)+1+(k-m) = k from by omega] at h
        rw [he9]
        show (9:Digit) = termDigit9 p m k
        rw [termDigit9, if_neg (by omega), if_neg (by omega)]
    · -- termRep would be the nines side, impossible since it terminates in zeros
      exfalso
      have h := h9r m
      rw [show (termRep p m).fracPart (q+1+m) = termDigit p m (q+1+m) from rfl,
        termDigit_eq_zero (by omega)] at h
      exact absurd h (by decide)

/-- A positive trailing-decimal value has exactly two representations. -/
theorem nnreal_two_reps {y : NNReal} (p m : ℕ) (hpm : y = (p:NNReal)/(10:NNReal)^m) (hy0 : y ≠ 0) :
    ∃ e₁ e₂ : NNRealDecimal, e₁ ≠ e₂ ∧ e₁.toNNReal = y ∧ e₂.toNNReal = y
      ∧ ∀ e, e.toNNReal = y → e = e₁ ∨ e = e₂ := by
  obtain ⟨p', m', hpm', hcond⟩ := exists_reduced m p
  rw [hpm'] at hpm
  subst hpm
  have hp'0 : p' ≠ 0 := by rintro rfl; apply hy0; simp
  by_cases hm0 : m' = 0
  · subst hm0
    have hyp' : (p':NNReal)/(10:NNReal)^0 = (p':NNReal) := by rw [pow_zero]; exact div_one _
    refine ⟨mk p' (fun _ ↦ 0), mk (p'-1) (fun _ ↦ 9), ?_, ?_, ?_, ?_⟩
    · intro hc
      have hcc : p' = p' - 1 := congrArg NNRealDecimal.intPart hc
      omega
    · rw [intRep0_toNNReal, hyp']
    · rw [intRep9_toNNReal (by omega), hyp']
    · intro e he
      rw [hyp'] at he
      exact rep_int_unique (by omega) he
  · have hm1 : 1 ≤ m' := by omega
    have hp' : ¬ 10 ∣ p' := by rcases hcond with h|h|h; exacts [absurd h hp'0, absurd h hm0, h]
    have hp10' : 1 ≤ p' % 10 := by
      rcases Nat.eq_zero_or_pos (p' % 10) with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) hp'
      · exact h
    refine ⟨termRep p' m', termRep9 p' m', ?_, termRep_toNNReal p' m',
      termRep9_toNNReal hm1 hp', ?_⟩
    · intro hc
      have h1 : ((termRep p' m').fracPart (m'-1):ℕ) = p'%10 := by
        show (termDigit p' m' (m'-1):ℕ) = p'%10
        rw [termDigit_toNat (by omega), show m'-1-(m'-1)=0 from by omega, pow_zero, Nat.div_one]
      have h2 : ((termRep9 p' m').fracPart (m'-1):ℕ) = p'%10 - 1 := by
        show (termDigit9 p' m' (m'-1):ℕ) = p'%10 - 1
        rw [termDigit9, if_neg (by omega), if_pos rfl]
      have hcc : ((termRep p' m').fracPart (m'-1):ℕ) = ((termRep9 p' m').fracPart (m'-1):ℕ) :=
        congrArg (fun d => (NNRealDecimal.fracPart d (m'-1):ℕ)) hc
      rw [h1, h2] at hcc
      omega
    · intro e he
      exact rep_nonint_unique hm1 hp' he

theorem rep_zero_unique {e : NNRealDecimal} (he : e.toNNReal = 0) : e = mk 0 (fun _ ↦ 0) := by
  rw [toNNReal_eq_intPart_add_tail, add_eq_zero] at he
  apply NNRealDecimal.ext'
  · show e.intPart = 0
    exact_mod_cast he.1
  · intro k
    exact (tailFrom_eq_zero_iff e 0).mp he.2 k

/-- Exercise B.2.3 -/
abbrev TerminatingDecimal (x:ℝ) : Prop := ∃ (n:ℤ) (m:ℕ), x = n / (10:ℝ)^m

theorem RealDecimal.not_inj_terminating {x:ℝ} (hx: TerminatingDecimal x) :
    ∃ d₁ d₂:RealDecimal, d₁ ≠ d₂ ∧ ∀ d: RealDecimal, d = x ↔ d = d₁ ∨ d = d₂ := by
  obtain ⟨n, m, hnm⟩ := hx
  have h10 : (0:ℝ) < (10:ℝ)^m := by positivity
  rcases lt_trichotomy x 0 with hxlt | hx0 | hxpos
  · -- x < 0
    have hpos : (0:ℝ) < -x := by linarith
    have hn : n < 0 := by
      rw [hnm] at hxlt
      have hcancel : (n:ℝ)/(10:ℝ)^m * (10:ℝ)^m = n := by field_simp
      have : (n:ℝ) < 0 := by nlinarith [mul_neg_of_neg_of_pos hxlt h10]
      exact_mod_cast this
    have hcoe : (((-n).toNat:ℝ)) = -(n:ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ -n)]; push_cast; ring
    have hy : (-x).toNNReal = ((-n).toNat:NNReal)/(10:NNReal)^m := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal (-x) (le_of_lt hpos), hnm]
      push_cast
      rw [hcoe]; ring
    obtain ⟨e₁, e₂, hne, hv1, hv2, huniq⟩ :=
      nnreal_two_reps ((-n).toNat) m hy (ne_of_gt (Real.toNNReal_pos.mpr hpos))
    refine ⟨neg e₁, neg e₂, ?_, ?_⟩
    · intro hc; exact hne (RealDecimal.neg.inj hc)
    intro d
    constructor
    · intro hd
      cases d with
      | neg e =>
        have hee : e.toNNReal = (-x).toNNReal := by
          have h1 : (↑e.toNNReal:ℝ) = -x := by have h0 : -(↑e.toNNReal:ℝ) = x := hd; linarith
          rw [← Real.coe_toNNReal (-x) (le_of_lt hpos)] at h1
          exact_mod_cast h1
        rcases huniq e hee with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      | pos e =>
        exfalso
        have h0 : (↑e.toNNReal:ℝ) = x := hd
        have := e.toNNReal.coe_nonneg
        linarith
    · rintro (rfl | rfl)
      · show -(↑e₁.toNNReal:ℝ) = x
        rw [hv1, Real.coe_toNNReal (-x) (le_of_lt hpos)]; ring
      · show -(↑e₂.toNNReal:ℝ) = x
        rw [hv2, Real.coe_toNNReal (-x) (le_of_lt hpos)]; ring
  · -- x = 0
    subst hx0
    refine ⟨pos (mk 0 (fun _ ↦ 0)), neg (mk 0 (fun _ ↦ 0)), by simp, ?_⟩
    intro d
    constructor
    · intro hd
      cases d with
      | pos e =>
        refine Or.inl ?_
        have hee : e.toNNReal = 0 := by have h0 : (↑e.toNNReal:ℝ) = 0 := hd; exact_mod_cast h0
        rw [rep_zero_unique hee]
      | neg e =>
        refine Or.inr ?_
        have hee : e.toNNReal = 0 := by
          have h0 : -(↑e.toNNReal:ℝ) = 0 := hd
          rw [neg_eq_zero] at h0; exact_mod_cast h0
        rw [rep_zero_unique hee]
    · rintro (rfl | rfl)
      · show (↑(mk 0 (fun _ ↦ (0:Digit))).toNNReal:ℝ) = 0
        rw [intRep0_toNNReal]; simp
      · show -(↑(mk 0 (fun _ ↦ (0:Digit))).toNNReal:ℝ) = 0
        rw [intRep0_toNNReal]; simp
  · -- x > 0
    have hxle : 0 ≤ x := le_of_lt hxpos
    have hn : 0 < n := by
      rw [hnm] at hxpos
      have hcancel : (n:ℝ)/(10:ℝ)^m * (10:ℝ)^m = n := by field_simp
      have : 0 < (n:ℝ) := by nlinarith [mul_pos hxpos h10]
      exact_mod_cast this
    have hcoe : ((n.toNat:ℝ)) = (n:ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (le_of_lt hn)]
    have hy : x.toNNReal = (n.toNat:NNReal)/(10:NNReal)^m := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal x hxle, hnm]
      push_cast
      rw [hcoe]
    obtain ⟨e₁, e₂, hne, hv1, hv2, huniq⟩ :=
      nnreal_two_reps (n.toNat) m hy (ne_of_gt (Real.toNNReal_pos.mpr hxpos))
    refine ⟨pos e₁, pos e₂, ?_, ?_⟩
    · intro hc; exact hne (RealDecimal.pos.inj hc)
    intro d
    constructor
    · intro hd
      cases d with
      | pos e =>
        have hee : e.toNNReal = x.toNNReal := by
          have h0 : (↑e.toNNReal:ℝ) = x := hd
          rw [← Real.coe_toNNReal x hxle] at h0
          exact_mod_cast h0
        rcases huniq e hee with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h])
      | neg e =>
        exfalso
        have h0 : -(↑e.toNNReal:ℝ) = x := hd
        have := e.toNNReal.coe_nonneg
        linarith
    · rintro (rfl | rfl)
      · show (↑e₁.toNNReal:ℝ) = x
        rw [hv1]; exact Real.coe_toNNReal x hxle
      · show (↑e₂.toNNReal:ℝ) = x
        rw [hv2]; exact Real.coe_toNNReal x hxle

/-- A decimal whose tail from some position vanishes is a terminating fraction. -/
theorem NNRealDecimal.terminating_of_tailFrom_zero {e : NNRealDecimal} {k : ℕ}
    (h : e.tailFrom k = 0) : ∃ N : ℕ, e.toNNReal = (N:NNReal)/(10:NNReal)^k := by
  refine ⟨e.intPart * 10^k + ∑ i ∈ Finset.range k, (e.fracPart i:ℕ) * 10^(k-1-i), ?_⟩
  rw [toNNReal_eq_prefix_add_tail e k, h, mul_zero, add_zero,
    eq_div_iff (pow_ne_zero k (by norm_num : (10:NNReal) ≠ 0)), add_mul, Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range k,
      ((e.fracPart i:NNReal) * (10:NNReal)^(-i-1:ℝ)) * (10:NNReal)^k
      = (((e.fracPart i:ℕ) * 10^(k-1-i) : ℕ):NNReal) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hpow : (10:NNReal)^(-(i:ℝ)-1) * (10:NNReal)^k = (10:NNReal)^(k-1-i) := by
      rw [← rpow_natCast (10:NNReal) k, ← rpow_add (by norm_num),
        ← rpow_natCast (10:NNReal) (k-1-i), show k-1-i = k-(i+1) from by omega,
        Nat.cast_sub (by omega : i+1 ≤ k)]
      congr 1; push_cast; ring
    rw [mul_assoc, hpow]; push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  push_cast
  rfl

/-- Two distinct representations of the same value force the value to be a terminating decimal. -/
theorem NNRealDecimal.terminating_of_ne {e e' : NNRealDecimal} (hv : e.toNNReal = e'.toNNReal)
    (hne : e ≠ e') : ∃ (N k : ℕ), e.toNNReal = (N:NNReal)/(10:NNReal)^k := by
  rcases intPart_step hv with ⟨hi, _⟩ | ⟨_, _, ht0⟩ | ⟨_, _, ht0⟩
  · rcases digits_split hv hi hne with ⟨p, _, hsplit⟩
    rcases hsplit with ⟨_, _, h0r⟩ | ⟨_, _, h0e⟩
    · have h0 : e'.tailFrom (p+1) = 0 := (tailFrom_eq_zero_iff e' (p+1)).mpr
        (fun i => by rw [show i+(p+1) = p+1+i from by ring]; exact h0r i)
      obtain ⟨N, hN⟩ := terminating_of_tailFrom_zero h0
      exact ⟨N, p+1, hv.trans hN⟩
    · have h0 : e.tailFrom (p+1) = 0 := (tailFrom_eq_zero_iff e (p+1)).mpr
        (fun i => by rw [show i+(p+1) = p+1+i from by ring]; exact h0e i)
      obtain ⟨N, hN⟩ := terminating_of_tailFrom_zero h0
      exact ⟨N, p+1, hN⟩
  · obtain ⟨N, hN⟩ := terminating_of_tailFrom_zero ht0
    exact ⟨N, 0, hv.trans hN⟩
  · obtain ⟨N, hN⟩ := terminating_of_tailFrom_zero ht0
    exact ⟨N, 0, hN⟩

theorem RealDecimal.inj_nonterminating {x:ℝ} (hx: ¬TerminatingDecimal x) : ∃! d:RealDecimal, d = x := by
  obtain ⟨d, hd⟩ := RealDecimal.surj x
  refine ⟨d, hd.symm, ?_⟩
  intro d' hd'
  by_contra hne
  apply hx
  have hval : (d':ℝ) = (d:ℝ) := by rw [hd', hd]
  cases d' with
  | pos e' =>
    cases d with
    | pos e =>
      have hee : e'.toNNReal = e.toNNReal := by
        have h1 : (↑e'.toNNReal:ℝ) = ↑e.toNNReal := hval
        exact_mod_cast h1
      obtain ⟨N, k, hNk⟩ := NNRealDecimal.terminating_of_ne hee (fun h => hne (by rw [h]))
      refine ⟨N, k, ?_⟩
      rw [← hd']
      show (↑e'.toNNReal:ℝ) = (N:ℝ)/(10:ℝ)^k
      rw [hNk]; push_cast; ring
    | neg e =>
      have h1 : (↑e'.toNNReal:ℝ) = -↑e.toNNReal := hval
      have hx0 : x = 0 := by
        rw [← hd']
        show (↑e'.toNNReal:ℝ) = 0
        have h2 := e'.toNNReal.coe_nonneg
        have h3 := e.toNNReal.coe_nonneg
        linarith
      exact ⟨0, 0, by rw [hx0]; simp⟩
  | neg e' =>
    cases d with
    | pos e =>
      have h1 : -(↑e'.toNNReal:ℝ) = ↑e.toNNReal := hval
      have hx0 : x = 0 := by
        rw [← hd']
        show -(↑e'.toNNReal:ℝ) = 0
        have h2 := e'.toNNReal.coe_nonneg
        have h3 := e.toNNReal.coe_nonneg
        linarith
      exact ⟨0, 0, by rw [hx0]; simp⟩
    | neg e =>
      have hee : e'.toNNReal = e.toNNReal := by
        have : -(↑e'.toNNReal:ℝ) = -↑e.toNNReal := hval
        have h2 : (↑e'.toNNReal:ℝ) = ↑e.toNNReal := by linarith
        exact_mod_cast h2
      obtain ⟨N, k, hNk⟩ := NNRealDecimal.terminating_of_ne hee (fun h => hne (by rw [h]))
      refine ⟨-(N:ℤ), k, ?_⟩
      rw [← hd', show ((RealDecimal.neg e':ℝ)) = -(↑e'.toNNReal:ℝ) from rfl, hNk]
      push_cast; ring

/-- The i-th fractional digit of a real decimal (ignoring its sign). -/
def RealDecimal.digit : RealDecimal → ℕ → Digit
  | pos e, i => e.fracPart i
  | neg e, i => e.fracPart i

/-- A decimal whose every tail avoids the all-zeros and all-nines extremes is the unique
representation of its value. -/
theorem NNRealDecimal.eq_of_toNNReal_eq_of_no_extreme {E e' : NNRealDecimal}
    (hv : E.toNNReal = e'.toNNReal) (hext : ∀ k, E.tailFrom k ≠ 0 ∧ E.tailFrom k ≠ 1) : E = e' := by
  by_contra hne
  rcases intPart_step hv with ⟨hi, _⟩ | ⟨_, ht1, _⟩ | ⟨_, _, ht0⟩
  · rcases digits_split hv hi hne with ⟨p, _, hsplit⟩
    rcases hsplit with ⟨_, h9e, _⟩ | ⟨_, _, h0e⟩
    · exact (hext (p+1)).2 ((tailFrom_eq_one_iff E (p+1)).mpr
        (fun i => by rw [show i+(p+1)=p+1+i from by ring]; exact h9e i))
    · exact (hext (p+1)).1 ((tailFrom_eq_zero_iff E (p+1)).mpr
        (fun i => by rw [show i+(p+1)=p+1+i from by ring]; exact h0e i))
  · exact (hext 0).2 ht1
  · exact (hext 0).1 ht0

/-- Exercise B.2.4.  This is Corollary 8.3.4, but the intent is to rewrite the proof using the decimal system. -/
example : Uncountable ℝ := by
  rw [uncountable_iff_not_countable]
  intro hc
  rw [countable_iff_exists_surjective] at hc
  obtain ⟨f, hf⟩ := hc
  choose g hg using fun i => RealDecimal.surj (f i)
  set E : NNRealDecimal := mk 0 (fun i => if RealDecimal.digit (g i) i = 1 then 2 else 1) with hE
  have hdiag_ne : ∀ i, E.fracPart i ≠ RealDecimal.digit (g i) i := by
    intro i
    show (if RealDecimal.digit (g i) i = 1 then (2:Digit) else 1) ≠ RealDecimal.digit (g i) i
    by_cases h : RealDecimal.digit (g i) i = 1
    · rw [if_pos h, h]; decide
    · rw [if_neg h]; exact fun hc => h hc.symm
  have hext : ∀ k, E.tailFrom k ≠ 0 ∧ E.tailFrom k ≠ 1 := by
    intro k
    refine ⟨fun h0 => absurd ((tailFrom_eq_zero_iff E k).mp h0 0) ?_,
      fun h1 => absurd ((tailFrom_eq_one_iff E k).mp h1 0) ?_⟩
    · show (if RealDecimal.digit (g (0+k)) (0+k) = 1 then (2:Digit) else 1) ≠ 0
      split <;> decide
    · show (if RealDecimal.digit (g (0+k)) (0+k) = 1 then (2:Digit) else 1) ≠ 9
      split <;> decide
  have hne : E.toNNReal ≠ 0 := by
    rw [toNNReal_eq_intPart_add_tail]
    show ((0:ℕ):NNReal) + E.tailFrom 0 ≠ 0
    rw [Nat.cast_zero, zero_add]
    exact (hext 0).1
  have hEpos : (0:ℝ) < ↑E.toNNReal := by
    have : 0 < E.toNNReal := zero_lt_iff.mpr hne
    exact_mod_cast this
  obtain ⟨i, hi⟩ := hf (RealDecimal.pos E : ℝ)
  rw [hg i] at hi
  cases hgi : g i with
  | neg e =>
    rw [hgi] at hi
    have heq : -(↑e.toNNReal:ℝ) = ↑E.toNNReal := hi
    have := e.toNNReal.coe_nonneg
    linarith
  | pos e =>
    rw [hgi] at hi
    have hee : e.toNNReal = E.toNNReal := by
      have h : (↑e.toNNReal:ℝ) = ↑E.toNNReal := hi
      exact_mod_cast h
    have hEe : E = e := NNRealDecimal.eq_of_toNNReal_eq_of_no_extreme hee.symm hext
    have hdg : RealDecimal.digit (g i) i = e.fracPart i := by rw [hgi]; rfl
    apply hdiag_ne i
    rw [hEe, hdg]


end AppendixB
