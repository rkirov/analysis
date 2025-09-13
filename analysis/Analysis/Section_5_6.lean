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

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by sorry

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by sorry

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by sorry

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by sorry

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by sorry

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by sorry

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by sorry

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by sorry

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by sorry

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by sorry

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by sorry

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
    have : a' = 0 := by sorry
    simp_all
  have : a' > 0 := by sorry
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

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by sorry

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by sorry

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  sorry

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  sorry

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  sorry

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  sorry

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  sorry

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
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by sorry

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
