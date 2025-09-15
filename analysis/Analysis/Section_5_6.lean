import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' n with n ih
  . rw [pow_zero]
    rw [one_mul]
    rw [_root_.zero_add]
  . rw [pow_succ]
    rw [mul_comm _ x]
    rw [mul_assoc]
    rw [ih]
    rw [mul_comm x]
    rw [← pow_succ]
    rw [_root_.add_assoc]
    rw [add_comm _ 1]
    rw [← _root_.add_assoc]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m ih
  . rw [pow_zero]
    rw [mul_zero]
    rw [pow_zero]
  . rw [pow_succ]
    rw [ih]
    rw [pow_add]
    rw [mul_add]
    rw [mul_one]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n ih
  . repeat rw [pow_zero]
    rw [mul_one]
  . rw [pow_succ]
    rw [ih]
    have : x ^ n * y ^ n * (x * y) = x ^ n * x ^ 1 * y ^ n * y ^ 1 := by
      repeat rw [pow_one]
      ring
    rw [this]
    rw [pow_add]
    rw [mul_assoc]
    rw [pow_add]

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  . intro h
    induction' n with n ih
    . contradiction
    . rw [pow_succ] at h
      by_cases hz : n = 0
      . rw [hz] at h
        rw [pow_zero] at h
        rw [one_mul] at h
        exact h
      . have : 0 < n := by exact Nat.zero_lt_of_ne_zero hz
        specialize ih this
        have h' : x ^ n = 0 ∨ x = 0 := by exact mul_eq_zero.mp h
        cases' h' with h h
        . exact ih h
        . exact h
  . intro h
    rw [h]
    induction' n with n ih
    . contradiction
    . rw [pow_succ]
      by_cases hz: n = 0
      . rw [hz]
        ring
      . have : 0 < n := by exact Nat.zero_lt_of_ne_zero hz
        specialize ih this
        rw [ih]
        rw [mul_zero]

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  . rw [pow_zero]
    norm_num
  . rw [pow_succ]
    exact mul_nonneg ih hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  have hx': x ≥ 0 := by exact le_of_lt hx
  have := pow_nonneg n hx'
  rw [ge_iff_le] at this
  rw [gt_iff_lt]
  rw [le_iff_lt_or_eq] at this
  cases' this with h h
  . exact h
  . by_cases hn : n = 0
    . subst n
      rw [pow_zero] at h
      linarith
    . have hn' : 0 < n := by exact Nat.zero_lt_of_ne_zero hn
      have := (pow_eq_zero x _ hn').mp h.symm
      subst x
      linarith

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  . rw [pow_zero]
    rw [pow_zero]
  . rw [pow_succ]
    rw [pow_succ]
    apply mul_le_mul ih hxy hy
    have hx : x ≥ 0 := by exact le_trans hy hxy
    exact pow_nonneg n hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction' n with n ih
  . contradiction
  . rw [pow_succ]
    rw [pow_succ]
    by_cases hz: n = 0
    . subst n
      simp only [pow_zero, one_mul, gt_iff_lt]
      exact hxy
    . have hn' : 0 < n := by exact Nat.zero_lt_of_ne_zero hz
      specialize ih hn'
      have hx' : x ^ n > 0 := by
        apply pow_pos
        exact lt_of_le_of_lt hy hxy
      by_cases hy': y = 0
      . subst y
        simp
        exact Left.mul_pos hx' hxy
      simp at hy
      rw [le_iff_lt_or_eq] at hy
      have : 0 ≠ y := by simp only [ne_eq]; contrapose! hy'; exact hy'.symm
      simp [this] at hy
      have hy' : y ^ n > 0 := by exact pow_pos n hy
      exact mul_lt_mul_of_pos' ih hxy hy hx'

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero]
    rw [pow_zero]
    have : 0 < (1: Real) := by exact zero_lt_one' Real
    rw [_root_.abs_of_nonneg (le_of_lt this)]
  . rw [pow_succ]
    rw [pow_succ]
    rw [ih]
    rw [abs_mul]

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

lemma Real.div_eq_mul_inv (x y: Real) : x / y = x * (1 / y) := by field_simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0)(hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  wlog hnm : n ≥ m
  . simp only [ge_iff_le, not_le] at hnm
    have := this x m n hx (by exact Int.le_of_lt hnm)
    rwa [mul_comm, add_comm]
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  obtain ⟨m', hm'⟩ := Int.eq_nat_or_neg m
  rcases hn' with ⟨rfl | rfl⟩
  . rcases hm' with ⟨rfl | rfl⟩
    . have : (n':ℤ) + (m':ℤ) = (((n' + m'):ℕ): ℤ) := by rfl
      rw [this]
      norm_cast
      exact pow_add _ _ _
    . subst m -- why didn't rfl do it
      rw [zpow_neg]
      field_simp
      by_cases h2: n' ≥ m'
      . have : (n': ℤ) + -(m':ℤ) = n' - m' := by rfl
        rw [this]
        norm_cast
        rw [pow_add]
        congr
        omega
      . have : (n': ℤ) + -(m':ℤ) = -(m' - n') := by omega
        rw [this]
        simp at h2
        have : (m': ℤ) - (n':ℤ) = (((m' - n'): ℕ): ℤ) := by rw [Int.natCast_sub h2.le]
        rw [this]
        rw [zpow_neg]
        field_simp
        rw [pow_add]
        congr
        omega
  . subst n -- why didn't rfl do it
    rw [zpow_neg]
    rcases hm' with ⟨rfl | rfl⟩
    . field_simp
      by_cases h2: n' ≥ m'
      . have : -(n': ℤ) + (m':ℤ) = -(n' - m') := by omega
        rw [this]
        norm_cast
        rw [zpow_neg]
        field_simp
        rw [pow_add]
        congr
        omega
      . have : -(n': ℤ) + (m':ℤ) = m' - n' := by omega
        rw [this]
        simp at h2
        have : (m': ℤ) - (n':ℤ) = (((m' - n'): ℕ): ℤ) := by rw [Int.natCast_sub h2.le]
        rw [this]
        rw [pow_eq_pow]
        rw [pow_add]
        congr
        omega
    . subst m
      rw [zpow_neg]
      field_simp
      have : -(n': ℤ) + (-(m':ℤ)) = -(n' + m') := by omega
      rw [this]
      norm_cast
      rw [zpow_neg]
      field_simp
      rw [pow_add]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  obtain ⟨m', hm'⟩ := Int.eq_nat_or_neg m
  rcases hm' with ⟨rfl | rfl⟩
  . norm_cast
    obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
    rcases hn' with ⟨rfl | rfl⟩
    . norm_cast
      exact pow_mul _ _ _
    . subst n
      rw [zpow_neg]
      field_simp
      norm_cast
      rw [pow_mul]
  . subst m
    obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
    rcases hn' with ⟨rfl | rfl⟩
    . norm_cast
      rw [zpow_neg]
      field_simp
      norm_cast
      rw [pow_mul]
    . subst n
      rw [zpow_neg, zpow_neg]
      field_simp
      norm_cast
      exact pow_mul _ _ _

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . norm_cast
    rw [mul_pow]
  . subst n
    repeat rw [zpow_neg]
    field_simp
    rw [mul_pow]

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . norm_cast
    exact pow_pos n' hx
  . subst n
    rw [zpow_neg]
    field_simp

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . apply pow_ge_pow _ _ _ hxy
    exact le_of_lt hy
  . exfalso
    linarith

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . exfalso
    linarith
  . subst n
    repeat rw [zpow_neg]
    have := pow_ge_pow _ _ n' hxy (le_of_lt hy)
    simp only [Int.neg_neg_iff_pos, Int.natCast_pos] at hn
    have hyp : y ^ n' > 0 := by exact pow_pos n' hy
    exact one_div_le_one_div_of_le hyp this

theorem pow_nat_inj {x y:Real} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rw [pow_left_inj₀ hx.le hy.le hn] at hxy
  exact hxy

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . norm_cast at hn
    exact pow_nat_inj hx hy hn hxy
  . subst n
    rw [zpow_neg, zpow_neg] at hxy
    norm_cast at hn
    simp only [and_true] at hn
    apply pow_nat_inj hx hy hn
    simp only [one_div, inv_inj] at hxy
    exact hxy

theorem pow_nat_abs (x:Real) (n:ℕ): |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero, pow_zero]
    norm_num
  . rw [pow_add, pow_add]
    rw [abs_mul]
    rw [ih]
    rw [pow_one, pow_one]

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . exact pow_nat_abs x n'
  . subst n
    rw [zpow_neg, zpow_neg]
    rw [pow_nat_abs]
    rw [abs_one_div]

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  simp
  rw [zero_pow (by linarith)]
  exact hx

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      rw [show (1:Real) = 1^n by simp]
      rw [pow_lt_pow_iff_left₀ (by norm_num) (by linarith) (by linarith)]
      exact hy'
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    by_cases hnone: n = 1
    . subst n
      simpa
    replace hn : n > 1 := by
      simp at hn
      rw [le_iff_lt_or_eq] at hn
      have :1 ≠ n := by exact fun a ↦ hnone (id (Eq.symm a))
      simp [this] at hn
      exact hn
    have : y > 1 := by linarith
    suffices h: y < y ^ n by
      exact lt_trans hy' h
    have hyeq: y = y ^ 1 := by simp
    conv_lhs => rw [hyeq]
    exact pow_lt_pow_right₀ this hn
  linarith

theorem pow_sub_pow {a b: Real} (hb: a < b) {n: ℕ}:
    b ^ n - a ^ n = (b - a) * ∑ i ∈ (Finset.range n), b ^ i * a ^ (n - 1 - i) := by
  have := Commute.geom_sum₂ (Commute.all b a) (by linarith) n
  symm at this
  have hneq: b - a ≠ 0 := by linarith
  have := congrArg (. * (b - a)) this
  field_simp at this
  rw [mul_comm] at this
  exact this

-- taken from baby Rudin page 10
theorem pow_sub_pow_lt {a b: Real} {n: ℕ} (hn: 1 < n) (ha: 0 ≤ a) (hb: a < b) :
  b ^ n - a ^ n < (b - a) * n * (b ^ (n - 1)) := by
  rw [pow_sub_pow hb]
  have claim1 {i:ℕ} (h: i ∈ Finset.range n) : b ^ i * a ^ (n - 1 - i) ≤ b ^ (n - 1) := by
    have hi: i < n := by exact Finset.mem_range.mp h
    have : a ^ (n - 1 - i) ≤ b ^ (n - 1 - i) := Real.pow_ge_pow _ _ _ hb.le ha
    calc
      _ ≤ b ^ i * b ^ (n - 1 - i) := by
        gcongr
        have : 0 < b := by linarith
        left
        exact Real.pow_pos i this
      _ = b ^ (n - 1) := by
        rw [← pow_add]
        congr
        omega

  have claim1': a ^ (n - 1) < b ^ (n - 1) := Real.pow_gt_pow _ _ _ hb ha (by omega)

  have claim2 : ∑ i ∈ (Finset.range n), b ^ i * a ^ (n - 1 - i) < n * (b ^ (n - 1)) := by
    have zero_in_range : 0 ∈ Finset.range n := by
      rw [Finset.mem_range]
      omega
    rw [← Finset.sum_erase_add _ _ zero_in_range]
    simp
    calc
      _ < ∑ i ∈ (Finset.range n).erase 0, b ^ i * a ^ (n - 1 - i) + b ^ (n - 1) := by
        gcongr
      _ ≤ ∑ i ∈ (Finset.range n).erase 0, b ^ (n - 1) + b ^ (n - 1) := by
        gcongr with i hi
        simp at hi
        specialize claim1 (i:=i) (by
          rw [Finset.mem_range]
          exact hi.2
        )
        exact claim1
      _ = (n - 1) * (b ^ (n - 1)) + b ^ (n - 1) := by
        rw [Finset.sum_const]
        simp [zero_in_range]
        left
        have : 1 ≤ n := by omega -- norm_cast needs some help
        norm_cast

      _ = n * (b ^ (n - 1)) := by ring
  rw [mul_assoc]
  exact mul_lt_mul_of_pos_of_nonneg (by linarith) claim2 (by linarith) (by
    apply mul_nonneg
    . exact Nat.cast_nonneg' n
    . apply pow_nonneg (lt_of_le_of_lt ha hb).le
  )

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
  unfold root
  have hlub := ExtendedReal.sSup_of_bounded (Real.rootset_nonempty hx n hn)
    (Real.rootset_bddAbove n hn)
  rw [isLUB_def] at hlub
  -- have to deal with x = 0 case separately
  -- todo: see if this can be avioded
  by_cases hn0: x = 0
  . subst x
    set S : Set Real := {y | y ≥ 0 ∧ y ^ n ≤ 0}
    have h_eq(x: Real): S = ({0} : Set Real) := by
      ext x
      simp
      constructor
      . intro hx
        simp at hx
        obtain ⟨hx1, hx2⟩ := hx
        have : x ^ n ≥ 0 := by exact pow_nonneg n hx1
        have : x ^ n = 0 := by exact (le_antisymm hx2 this)
        exact (pow_eq_zero x n hn).mp this
      . intro h
        subst x
        unfold S
        simp
        right
        exact zero_pow (by linarith)
    simp_all
    intro h
    exact Nat.ne_zero_of_lt hn
  replace hx: 0 < x := by
    simp at hx
    rw [le_iff_lt_or_eq] at hx
    have : 0 ≠ x := by exact fun a ↦ hn0 (id (Eq.symm a))
    simp [this] at hx
    exact hx
  -- have to deal with n = 1 case separately
  -- todo: see if this can be avioded
  by_cases hnone: n = 1
  . subst n
    simp_all
    set S : Real := sSup {y | y ≥ 0 ∧ y ≤ x}
    suffices h_eq: S = x by simp [h_eq]
    obtain ⟨h1, h2⟩ := hlub
    rw [Real.upperBound_def] at h1
    specialize h1 x (by simp; linarith)
    specialize h2 x (by rw [Real.upperBound_def]; simp)
    linarith
  replace hn: 1 < n := by
    simp at hn
    rw [le_iff_lt_or_eq] at hn
    have : 1 ≠ n := by exact fun a ↦ hnone (id (Eq.symm a))
    simp [this] at hn
    exact hn
  constructor
  . intro h
    rw [← h] at hlub
    replace ⟨h1, h2⟩ := hlub
    rw [Real.upperBound_def] at h1
    rcases trichotomous' (y ^ n) x with (h | h | h)
    . exfalso
      let ε := (y ^ n - x) / (n * y ^ (n - 1))
      have hy: 0 < y := by
        simp at h
        have := hx.trans h
        simp at hy
        rw [le_iff_lt_or_eq] at hy
        cases' hy with hy hy
        . exact hy
        . exfalso
          rw [← hy] at this
          rw [zero_pow (by linarith)] at this
          linarith
      have hε : 0 < ε := by
        unfold ε
        apply div_pos
        . linarith
        . apply mul_pos
          . positivity
          . positivity
      have hε' : ε < y := by
        unfold ε
        calc
          _ = y ^ n / (n * y ^ (n - 1)) - x / (n * y ^ (n - 1)) := by
            ring
          _ < y ^ n / (n * y ^ (n - 1)) := by
            simp
            positivity
          _ = y / n := by
            field_simp
            ring_nf
            have : y * y ^ (n - 1) = y ^ n := by
              conv_lhs =>
                arg 1
                rw [show y = y ^ 1 by simp]
              rw [pow_add y (n - 1) 1]
              congr
              omega
            rw [this]
          _ ≤ y := by
            exact div_nat_le_self_of_nonnneg hy.le n
      specialize h2 (y - ε) (by
        rw [Real.upperBound_def]
        simp
        intro t ht ht'
        by_contra ht''
        simp at ht''
        have h: y ^ n - t ^ n < y ^ n - x :=
          calc
            _ ≤ y ^ n - (y - ε) ^ n := by
              gcongr
              linarith
            _ < _ := by exact pow_sub_pow_lt (a:=y - ε) (b:=y) hn (by linarith) (by linarith)
            _ = ε * n * y ^ (n - 1) := by simp
            _ = (y ^ n - x) / (n * y ^ (n - 1)) *  n * y ^ (n - 1) := by
              unfold ε
              rfl
            _ = y ^ n - x := by
              field_simp
              ring_nf
        simp at h
        linarith
      )
      linarith
    . exfalso
      -- magic choice taken from baby Rudin page 10
      let ε := min (1/2) ((x - y^n) / (2 * n * (y + 1)^(n - 1)))
      have hε : 0 < ε := by
        unfold ε
        apply lt_min (by norm_num)
        apply div_pos
        . linarith
        . positivity
      have hε' : ε < 1 := by
        unfold ε
        calc
          _ ≤ (1:Real)/2 := min_le_left _ _
          _ < (1:Real) := by norm_num
      have hε'' : ε < (x - y^n) / (n * (y + 1)^(n - 1)) := by
        unfold ε
        calc
          _ ≤ (x - y^n) / (2 * n * (y + 1)^(n - 1)) := min_le_right _ _
          _ < (x - y^n) / (n * (y + 1)^(n - 1)) := by
            gcongr
            . linarith
            . norm_cast
              exact lt_two_mul_self (by linarith)
      specialize h1 (y + ε) (by
        simp
        constructor
        . linarith
        . have :=
            calc
              (y + ε) ^ n - y ^ n < _ := pow_sub_pow_lt (a:=y) (b:= y + ε) hn (by linarith) (by linarith)
              _ ≤ ε * n * (y + 1)^(n - 1) := by simp; gcongr
              _ < (x - y^n) / (n * (y + 1)^(n - 1)) *  n * (y + 1)^(n - 1) := by gcongr
              _ = x - y^n := by field_simp; ring
          simp at this
          exact this.le
      )
      linarith
    . exact h
  . intro h
    subst x
    simp_all
    set X := sSup {y_1 | 0 ≤ y_1 ∧ y_1 ^ n ≤ y ^ n}
    obtain ⟨h1, h2⟩ := hlub
    rw [Real.upperBound_def] at h1
    specialize h1 y (by simp; exact hy)
    specialize h2 y (by
      rw [Real.upperBound_def]
      intro x hx
      simp at hx
      obtain ⟨hx1, hx2⟩ := hx
      exact le_of_pow_le_pow_left₀ (by linarith) hy hx2
    )
    linarith

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  unfold root
  have := ExtendedReal.sSup_of_bounded (Real.rootset_nonempty hx n hn)
    (Real.rootset_bddAbove n hn)
  rw [isLUB_def] at this
  replace ⟨h1, h2⟩ := this
  rw [Real.upperBound_def] at h1
  set y := sSup {y | y ≥ 0 ∧ y ^ n ≤ x}
  specialize h1 0 (by simp; rw [zero_pow (by linarith)]; exact hx)
  exact h1

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have := Real.eq_root_iff_pow_eq hx (Real.root_nonneg hx hn) hn
  simp at this
  have hy := (Real.root_nonneg hx hn)
  set y := x.root n
  rw [← this]
  constructor
  . intro h
    exact pow_pos n h
  . intro h
    have hn' : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
    have : 0 = (0:Real)^n := by exact Eq.symm ((fun x n hn ↦ (pow_eq_zero x n hn).mpr) 0 n hn rfl)
    rw [this] at h
    exact lt_of_pow_lt_pow_left₀ n hy h

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  have := Real.eq_root_iff_pow_eq hx (Real.root_nonneg hx hn) hn
  simp at this
  exact this

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  have hx' : x ^ n ≥ 0 := by exact pow_nonneg n hx
  have hn' : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have := Real.eq_root_iff_pow_eq hx' (Real.root_nonneg hx' hn) hn
  simp at this
  rw [pow_left_inj₀ (root_nonneg hx' hn) hx hn'] at this
  exact this

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  have h1 := Real.eq_root_iff_pow_eq hx (Real.root_nonneg hx hn) hn
  simp at h1
  have hxr := (Real.root_nonneg hx hn)
  set xr := x.root n
  rw [← h1]
  have h2 := Real.eq_root_iff_pow_eq hy (Real.root_nonneg hy hn) hn
  simp at h2
  have hyr := (Real.root_nonneg hy hn)
  set yr := y.root n
  rw [← h2]
  constructor
  . intro h
    exact lt_of_pow_lt_pow_left₀ n hxr h
  . intro h
    exact pow_gt_pow xr yr n h hyr hn

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  have h1 := Real.eq_root_iff_pow_eq (x:=x) (n:=l) (by linarith) (Real.root_nonneg (by linarith) (by linarith)) (by linarith)
  simp at h1
  set xl := x.root l
  have h2 := Real.eq_root_iff_pow_eq (x:=x) (n:=k) (by linarith) (Real.root_nonneg (x:=x) (n:=k) (by linarith) (by linarith)) (by linarith)
  simp at h2
  set xk := x.root k
  rw [← h1] at h2
  have hxl: xl > 1 := by
    have hxrl: xl ^ l > 1 := by
      rw [h1]
      exact hx
    rw [show (1:Real) = 1^l by simp] at hxrl
    exact lt_of_pow_lt_pow_left₀ l (Real.root_nonneg (by linarith) (by linarith)) hxrl
  have hxk: xk > 1 := by
    have hxrk: xk ^ k > 1 := by
      rw [h2]
      exact lt_of_lt_of_eq hx (id (Eq.symm h1))
    rw [show (1:Real) = 1^k by simp] at hxrk
    exact lt_of_pow_lt_pow_left₀ k (Real.root_nonneg (by linarith) (by linarith)) hxrk
  rcases trichotomous' xl xk with (h | h | h)
  . exact h
  . exfalso
    have :=
      calc
        xl ^ k < xk ^ k := by exact pow_gt_pow xk xl k h (by linarith) (by linarith)
        _ = xl ^ l := by rw [h2]
    have : xl ^ l < xl ^ k := by exact pow_lt_pow_right₀ hxl hkl
    linarith
  . exfalso
    rw [h] at h2
    have : k = l := by exact (pow_right_inj₀ (by linarith) (by linarith)).mp h2
    linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  have h1 := Real.eq_root_iff_pow_eq (x:=x) (n:=l) (by linarith) (Real.root_nonneg (by linarith) (by linarith)) (by linarith)
  simp at h1
  set xl := x.root l
  have h2 := Real.eq_root_iff_pow_eq (x:=x) (n:=k) (by linarith) (Real.root_nonneg (x:=x) (n:=k) (by linarith) (by linarith)) (by linarith)
  simp at h2
  set xk := x.root k
  rw [← h1] at h2
  have hxl: xl < 1 := by
    have hxrl: xl ^ l < 1 := by
      rw [h1]
      exact hx
    rw [show (1:Real) = 1^l by simp] at hxrl
    exact lt_of_pow_lt_pow_left₀ l (by norm_num) hxrl
  have hxk: xk < 1 := by
    have hxrk: xk ^ k < 1 := by
      rw [h2]
      exact lt_of_eq_of_lt h1 hx
    rw [show (1:Real) = 1^k by simp] at hxrk
    exact lt_of_pow_lt_pow_left₀ k (by norm_num) hxrk
  have hxl': 0 < xl := by
    unfold xl
    exact (Real.root_pos (by linarith) (by linarith)).mpr hx0
  have hxk': 0 < xk := by
    unfold xk
    exact (Real.root_pos (by linarith) (by linarith)).mpr hx0
  rcases trichotomous' xl xk with (h | h | h)
  . exfalso
    have :=
      calc
        xl ^ k > xk ^ k := by exact pow_gt_pow xl xk k h (by linarith) (by linarith)
        _ = xl ^ l := by rw [h2]
    have : xl ^ l > xl ^ k := by exact pow_lt_pow_right_of_lt_one₀ hxl' hxl hkl
    linarith
  . exact h
  . exfalso
    rw [h] at h2
    have : k = l := by exact (pow_right_inj₀ (by linarith) (by linarith)).mp h2
    linarith

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1) (hk: k ≥ 1): (1:Real).root k = 1 := by
  have h1 := Real.eq_root_iff_pow_eq (x:=1) (y:=1) (n:=k) (by norm_num) (by norm_num) hk
  simp at h1
  rw [← h1]

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  have hx': x.root n ≥ 0 := by exact Real.root_nonneg hx hn
  have hy': y.root n ≥ 0 := by exact Real.root_nonneg hy hn
  have h1 := Real.eq_root_iff_pow_eq (x:=x*y) (y:= (x.root n) * (y.root n)) (n:=n)
    (by exact Left.mul_nonneg hx hy) (by exact Left.mul_nonneg hx' hy') hn
  simp at h1
  symm
  rw [h1]
  rw [Real.mul_pow]
  rw [Real.pow_of_root hx hn]
  rw [Real.pow_of_root hy hn]

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  have hmn : n * m ≥ 1 := by exact Right.one_le_mul hn hm
  have hmn': x.root (n * m) ≥ 0 := by exact Real.root_nonneg hx hmn
  have h1 := Real.eq_root_iff_pow_eq hx (hmn') hmn
  simp at h1
  rw [mul_comm] at h1
  rw [← pow_mul] at h1
  conv_lhs => rw [← h1]
  rw [Real.root_of_pow (by
    apply pow_nonneg
    . rw [mul_comm] at hmn
      exact Real.root_nonneg hx hmn
    ) hn]
  rw [Real.root_of_pow (by
    rw [mul_comm] at hmn'
    exact hmn'
  ) hm]
  rw [mul_comm]

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  have hn := Real.root_nonneg (x:=x) (n:=1) (by linarith) (by norm_num)
  have h1 := Real.eq_root_iff_pow_eq (x:=x) (n:=1) (by linarith) hn (by norm_num)
  simp at h1
  exact h1

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  have := congrArg (root . n) h
  simp at this
  rw [Real.root_of_pow (by linarith) hn] at this
  rw [Real.root_of_pow (by linarith) hn] at this
  exact this

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by
      subst a
      simp at hq
      symm at hq
      rw [div_eq_zero_iff] at hq
      norm_cast at hq
      cases' hq with hq hq
      . exact hq
      . linarith
    simp_all
  have : a' > 0 := by
    rw [div_eq_div_iff] at hq
    . norm_cast at hq
      have : 0 < a * b' := by positivity
      rw [hq] at this
      apply Int.pos_of_mul_pos_left this
      positivity
    . positivity
    . positivity
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, mul_comm, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  have := ratPow_def hx 1 (b:=n) (by linarith)
  simp only [Int.cast_one, one_div, zpow_one] at this
  simp only [one_div] at ⊢
  exact this

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  have := ratPow_def hx n (b:=1) (by linarith)
  simp at this
  rwa [root_one hx] at this

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_nonneg {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_def hx a hb]
  exact Real.zpow_pos a ((Real.root_pos hx.le hb).mpr hx)

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  have hbd: b * d > 0 := by positivity
  have h1 : (a/b:ℚ) + (c/d:ℚ) = ((a*d + b*c):ℤ)/((b*d):ℕ) := by
    field_simp; ring
  rw [h1]
  rw [ratPow_def hx _ hb]
  rw [ratPow_def hx _ hd]
  rw [ratPow_def hx _ hbd]

  have hrb: x.root b > 0 := by exact (Real.root_pos hx.le hb).mpr hx
  rw [← ratPow_eq_pow hrb a]
  conv_rhs => rw [show (a:ℚ) = ((a * d):ℤ) / d by field_simp]
  rw [ratPow_def hrb _ hd]

  have hrd: x.root d > 0 := by exact (Real.root_pos hx.le hd).mpr hx
  rw [← ratPow_eq_pow hrd c]
  conv_rhs => rw [show (c:ℚ) = ((c * b):ℤ) / b by field_simp]
  rw [ratPow_def hrd _ hb]
  rw [root_root hx.le (by linarith) (by linarith)]
  rw [root_root hx.le (by linarith) (by linarith)]
  rw [mul_comm b d]
  have hbdr : x.root (d * b) > 0 := by
    rw [mul_comm d b]
    exact (Real.root_pos hx.le hbd).mpr hx
  rw [zpow_add _ _ _ (by linarith)]
  rw [mul_comm _ c]

theorem Real.root_pos' {x: Real} (hx: x > 0) {a: ℕ} (ha: a ≥ 1) : x.root a > 0 := by
  exact (Real.root_pos hx.le ha).mpr hx

theorem Real.root_pow_swap {x: Real} (a: ℤ) (b: ℕ) (hb: b > 0) (hx: x > 0) :
  (x.root b)^a = (x^a).root b := by
  rw [eq_root_iff_pow_eq (by positivity) (by
    apply zpow_nonneg
    exact (root_pos' hx (by linarith)).le
  ) (by linarith)]
  rw [← pow_eq_pow]
  rw [zpow_mul]
  rw [mul_comm]
  rw [← zpow_mul]
  simp only [zpow_natCast]
  rw [pow_of_root (Or.inl hx) hb]

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  have hbd: b * d > 0 := by positivity
  have h1 : (a/b:ℚ) * (c/d:ℚ) = ((a*c):ℤ)/((b*d):ℕ) := by
    field_simp
  rw [h1]
  rw [ratPow_def hx _ hb]
  rw [ratPow_def (by
    apply zpow_pos
    exact root_pos' hx hb
  ) _ hd]
  rw [ratPow_def hx _ hbd]
  rw [← root_pow_swap a d hd (by exact root_pos' hx hb)]
  rw [root_root hx.le (by linarith) (by linarith)]
  rw [zpow_mul]

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  have : x^q > 0 := by exact Real.ratPow_nonneg hx q
  field_simp [this]
  rw [<- ratPow_add hx]
  simp
  rfl

-- missing theorems, upstream
theorem Real.pow_gt_pow' (x y:Real) (n:ℕ) (hxy: x^n > y^n) (hx: x > 0) (hn: n ≠ 0) : x > y := by
  by_cases h: x = y
  . subst x
    linarith
  have := Real.trichotomous' x y
  by_contra h'
  have hxy' : y > x := by tauto
  have hn': n > 0 := by omega
  have := Real.pow_gt_pow y x n hxy' hx.le hn'
  linarith

theorem Real.zpow_gt_zpow' (x y:Real) (n:ℤ) (hxy: x^n > y^n) (hx: x > 0) (hn: n > 0) : x > y := by
  by_cases h: x = y
  . subst x
    linarith
  have := Real.trichotomous' x y
  by_contra h'
  have hxy' : y > x := by tauto
  have := Real.zpow_ge_zpow hxy'.le hx hn
  linarith

theorem Real.zpow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {z:ℤ} (h: z > 0) : x > y ↔ x^z > y^z := by
  simp
  constructor
  . intro h'
    have := zpow_ge_zpow h'.le hy h
    by_cases h'' : x = y
    . linarith
    . simp at h''
      have hnot: ¬ y ^ z = x ^ z := by
        contrapose! h''
        symm at h''
        exact zpow_inj hx hy (by linarith) h''
      simp at this
      rw [le_iff_lt_or_eq] at this
      simp [hnot] at this
      exact this
  . intro h
    by_cases h' : x = y
    . subst y
      linarith
    . have hy': y ^ z > 0 := by exact zpow_pos _ hy
      exact zpow_gt_zpow' _ _ _ h hx (by linarith)

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_def hx _ hb]
  rw [ratPow_def hy _ hb]
  have : 0 < a := by
    simp at h
    rw [div_pos_iff] at h
    norm_cast at h
    tauto
  rw [Real.root_mono hx.le hy.le hb]
  rw [Real.zpow_mono (root_pos' hx hb) (root_pos' hy hb) this]

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  sorry

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  sorry

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  sorry

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  sorry

theorem Real.root_zero (n:ℕ) (h: n > 0) : (0:Real).root n = 0 := by
  symm
  rw [eq_root_iff_pow_eq (by norm_num) (by norm_num) h]
  simp only [pow_eq_zero_iff', ne_eq, true_and]
  linarith

/-- Exercise 5.6.4 -/
theorem Real.abs_eq_pow_sqrt (x:Real) : |x| = (x^2).root 2 := by
  rcases trichotomous' x 0 with (h | h | h)
  . rw [abs_of_nonneg h.le]
    have hx2 : x^2 ≥ 0 := by positivity
    rw [eq_root_iff_pow_eq hx2 h.le (by norm_num)]
  . rw [_root_.abs_of_neg h]
    have hx2 : x^2 ≥ 0 := by positivity
    rw [eq_root_iff_pow_eq hx2 (by linarith) (by norm_num)]
    ring
  . subst x
    simp
    symm
    exact Real.root_zero 2 (by norm_num)

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  sorry

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  sorry

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
