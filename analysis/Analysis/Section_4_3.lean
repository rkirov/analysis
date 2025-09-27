import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  by_cases h1: x > 0
  . rw [abs_of_pos h1]
    exact Eq.symm (_root_.abs_of_pos h1)
  . by_cases h2: x = 0
    . rw [h2]
      rfl
    . simp only [gt_iff_lt, not_lt] at h1
      rw [le_iff_lt_or_eq] at h1
      simp only [h2, or_false] at h1
      rw [abs_of_neg h1]
      exact Eq.symm (_root_.abs_of_neg h1)

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  by_cases h1: x > 0
  . rw [_root_.abs_of_pos h1]
    exact le_of_lt h1
  . by_cases h2: x = 0
    . rw [h2]
      rfl
    . simp only [ge_iff_le, _root_.abs_nonneg]

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  constructor
  . intro h
    by_cases h1: x > 0
    . rw [_root_.abs_of_pos h1] at h
      tauto
    . simp only [gt_iff_lt, not_lt] at h1
      by_cases h2: x = 0
      . exact h2
      . rw [le_iff_lt_or_eq] at h1
        simp only [h2, or_false] at h1
        rw [_root_.abs_of_neg h1] at h
        exact neg_eq_zero.mp h
  . intro h
    rw [h]
    rfl

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  wlog h: x ≥ y
  . specialize this y x
    simp at h
    have hxy :y ≥ x := by exact le_of_lt h
    have := this hxy
    rw [add_comm]
    conv_rhs => rw [add_comm]
    exact this
  . by_cases hy: y ≥ 0
    . rw [abs_of_nonneg hy]
      have hx : x ≥ 0 := by trans y; exact h; exact hy
      rw [abs_of_nonneg hx]
      have hxy : x + y ≥ 0 := by exact Rat.add_nonneg hx hy
      rw [abs_of_nonneg hxy]
    . simp at hy
      by_cases hxy: x + y ≥ 0
      . rw [abs_of_nonneg hxy]
        rw [_root_.abs_of_neg hy]
        have hx : x ≥ 0 := by linarith
        rw [abs_of_nonneg hx]
        linarith
      . simp at hxy
        rw [_root_.abs_of_neg hxy]
        rw [_root_.abs_of_neg hy]
        simp only [neg_add_rev, le_add_neg_iff_add_le, neg_add_cancel_comm]
        by_cases hx: x ≥ 0
        . rw [abs_of_nonneg hx]
          have hnx : -x ≤ 0 := by
            simp only [Left.neg_nonpos_iff]
            exact hx
          trans 0
          exact hnx
          exact hx
        . simp only [ge_iff_le, not_le] at hx
          rw [_root_.abs_of_neg hx]

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  constructor
  . rintro ⟨h1, h2⟩
    by_cases hx: x ≥ 0
    . rw [abs_of_nonneg hx]
      exact h2
    . simp only [ge_iff_le, not_le] at hx
      rw [_root_.abs_of_neg hx]
      exact neg_le.mp h1
  . intro h
    by_cases hy: y ≥ 0
    . by_cases hx: x ≥ 0
      . rw [abs_of_nonneg hx] at h
        constructor
        . linarith
        . exact h
      . simp only [ge_iff_le, not_le] at hx
        rw [_root_.abs_of_neg hx] at h
        constructor
        . linarith
        . linarith
    . simp only [ge_iff_le, not_le] at hy
      have := abs_nonneg x
      exfalso
      linarith

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  rw [abs_le_iff x |x|]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  wlog hs: x ≥ y
  . specialize this y x
    simp at hs
    have h: y ≥ x := by exact le_of_lt hs
    have := this h
    rw [mul_comm]
    conv_rhs => rw [mul_comm]
    exact this
  by_cases hx: x ≥ 0
  . rw [abs_of_nonneg hx]
    by_cases hy: y ≥ 0
    . rw [abs_of_nonneg hy]
      have hxy : x * y ≥ 0 := by exact Rat.mul_nonneg hx hy
      rw [abs_of_nonneg hxy]
    . simp at hy
      rw [_root_.abs_of_neg hy]
      have hxy : x * y ≤ 0 := by
        -- why can't linarith solve this?
        simp at hx hy ⊢
        rw [le_iff_lt_or_eq] at hx ⊢
        cases' hx with h h
        . left
          exact mul_neg_of_pos_of_neg h hy
        . right
          rw [← h]
          simp only [zero_mul]
      rw [_root_.abs_of_nonpos hxy]
      simp only [mul_neg]
  . simp at hx
    have hy: y < 0 := by linarith
    rw [_root_.abs_of_neg hx]
    rw [_root_.abs_of_neg hy]
    have hxy : x * y > 0 := by exact mul_pos_of_neg_of_neg hx hy
    rw [_root_.abs_of_pos hxy]
    simp only [mul_neg, neg_mul, neg_neg]

theorem abs_div (x y:ℚ) : |x / y| = |x| / |y| := by
  by_cases hy: y = 0
  . subst y
    simp only [div_zero, abs_zero]
  . have hy': |y| ≠ 0 := by
      contrapose hy
      simp only [Decidable.not_not]
      simp only [ne_eq, Decidable.not_not] at hy
      exact (abs_eq_zero_iff y).mp hy
    field_simp
    rw [← abs_mul]
    field_simp

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  have := abs_mul x (-1)
  have hone:|(-1)| = (1:ℚ) := by rfl
  rw [hone] at this
  rw [mul_one] at this
  have h2: x * -1 = -x := by exact mul_neg_one x
  rw [h2] at this
  exact this

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by
  rw [dist]
  exact abs_nonneg _

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [dist]
  rw [abs_eq_zero_iff]
  exact sub_eq_zero

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  repeat rw [dist]
  have : x - y = - (y - x) := by exact Eq.symm (neg_sub y x)
  rw [this]
  exact abs_neg _

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  repeat rw [dist]
  have : x - z = (x - y) + (y - z) := by simp only [sub_add_sub_cancel]
  rw [this]
  exact abs_add _ _

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]
  have : (0.99:ℚ) - 1.01 = -0.02 := by linarith
  rw [this]
  have : |-(0.02:ℚ)| = 0.02 := by
    have h: (-(0.02):ℚ) < 0 := by linarith
    rw [_root_.abs_of_neg h]
    simp only [neg_neg]
  rw [this]
  linarith

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]
  simp
  have : (0.99:ℚ) - 1.01 = -0.02 := by linarith
  rw [this]
  have : |-(0.02:ℚ)| = 0.02 := by
    have h: (-(0.02):ℚ) < 0 := by linarith
    rw [_root_.abs_of_neg h]
    simp only [neg_neg]
  rw [this]
  linarith

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff]
  simp only [sub_self, abs_zero]
  exact le_of_lt hε

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [close_iff]
  simp only [sub_self]
  rfl

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor
  . intro h
    rw [h]
    intro e he
    rw [close_iff]
    simp only [sub_self]
    exact le_of_lt he
  . intro h
    by_contra hxy
    have : |x - y| > 0 := by
      have hnn := abs_nonneg (x - y)
      change 0 ≤ |x - y| at hnn
      rw [le_iff_lt_or_eq] at hnn
      cases' hnn with h h
      . exact h
      . symm at h
        apply (abs_eq_zero_iff _).mp at h
        exfalso
        have : x = y := by linarith
        contradiction
    . specialize h (|x - y| / 2)
      have : |x - y| / 2 > 0 := by linarith
      have := h this
      rw [close_iff] at this
      linarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  repeat rw [close_iff]
  have : x - y = - (y - x) := by exact Eq.symm (neg_sub y x)
  rw [this]
  rw [abs_neg]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
  rw [close_iff] at hxy hyz ⊢
  have : x - z = (x - y) + (y - z) := by exact Eq.symm (sub_add_sub_cancel x y z)
  rw [this]
  have := abs_add (x - y) (y - z)
  trans
  . exact this
  . linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
  rw [close_iff] at hxy hzw ⊢
  have : x + z - (y + w) = x - y + (z - w) := by ring
  rw [this]
  trans
  . exact abs_add (x - y) (z - w)
  . linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
  rw [close_iff] at hxy hzw ⊢
  have : x - z - (y - w) = x - y + (- (z - w)) := by ring
  rw [this]
  trans
  . exact abs_add (x - y) (- (z - w))
  . have : |(- (z - w))| ≤ δ := by
      rw [abs_neg]
      exact hzw
    linarith

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥ ε) :
    ε'.Close x y := by
  rw [close_iff] at hxy ⊢
  trans
  . exact hxy
  . exact hε

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  wlog h: y ≤ w ∧ w ≤ z
  . have hb2 := Or.symm hbetween
    simp [h] at hbetween
    exact this hxz hxy hb2 hbetween
  have ⟨hyw, hwz⟩ := h
  rw [close_iff] at hxy hxz ⊢
  have hε: ε ≥ 0 := by
    by_contra he
    simp at he
    have := abs_nonneg (x - y)
    linarith
  by_cases hn: z = y
  . have : w = y := by linarith
    subst w
    exact hxy
  set t := (w - y) / (z - y)
  have hyz : y ≤ z := by exact Rat.le_trans hyw hwz
  have ht: 0 ≤ t := by
    unfold t
    apply Rat.div_nonneg
    . linarith
    . linarith
  have ht' : 0 ≤ 1 - t := by
    unfold t
    field_simp
    rw [div_le_one₀]
    linarith
    rw [sub_pos]
    rw [le_iff_lt_or_eq] at hyz
    cases' hyz with h h
    . exact h
    . symm at h
      contradiction
  have ht'': (1 - t) * y + t * z = w := by
    unfold t
    -- help field_simp
    have hn': z - y ≠ 0 := by exact sub_ne_zero_of_ne hn
    field_simp [hn']
    ring
  rw [← ht'']
  have : x = (1 - t) * x + t * x := by ring
  rw [this]
  calc |(1 - t) * x + t * x - ((1 - t) * y + t * z)| = |(1 - t) * (x - y) + t * (x - z)| := by ring_nf
    _ ≤ |(1 - t) * (x - y)| + |t * (x - z)| := abs_add _ _
    _ ≤ |(1 - t)| * |x - y| + |t| * |x - z| := by repeat rw [abs_mul]
    _ ≤ |(1 - t)| * ε + |t| * |x - z| := by
      simp only [add_le_add_iff_right]
      apply mul_le_mul_of_nonneg_left hxy (by exact (abs_nonneg _))
    _ ≤ |(1 - t)| * ε + |t| * ε := by
      simp only [add_le_add_iff_left]
      apply mul_le_mul_of_nonneg_left hxz (by exact (abs_nonneg _))
    _ ≤ |(1 - t)| * ε + t * ε := by
      simp only [add_le_add_iff_left]
      apply mul_le_mul_of_nonneg_right
      . rw [abs_of_nonneg ht]
      . linarith
     _ ≤ (1 - t) * ε + t * ε := by
      simp only [add_le_add_iff_right]
      apply mul_le_mul_of_nonneg_right
      . rw [abs_of_nonneg ht']
      . linarith
    _ = ε := by ring

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
  rw [close_iff] at hxy ⊢
  have : x * z - y * z = (x - y) * z := by exact Eq.symm (sub_mul x y z)
  rw [this]
  rw [abs_mul]
  have hz: |z| ≥ 0 := by exact abs_nonneg z
  exact mul_le_mul_of_nonneg_right hxy hz

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
  set a := y-x
  have ha : y = x + a := by simp only [add_sub_cancel, a]
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by simp only [add_sub_cancel, b]
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by rw [ha, hb]; ring
  rw [close_symm, close_iff]
  rw [this]
  calc
    _ = |a * z + b * (x + a)| := by ring_nf
    _ ≤ |a * z + b * y| := by rw [ha]
    _ ≤ |a * z| + |b * y| := by exact abs_add _ _
    _ ≤ |a| * |z| + |b| * |y| := by simp only [abs_mul, le_refl]
    _ ≤ ε * |z| + |b| * |y| := by
      simp only [add_le_add_iff_right]
      exact mul_le_mul_of_nonneg_right haε (abs_nonneg z)
    _ ≤ _ := by
      simp only [add_le_add_iff_left]
      exact mul_le_mul_of_nonneg_right hbδ (abs_nonneg y)

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

lemma pow_one (x:ℚ) : x^1 = x := by
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' n with n ih
  . rw [pow_zero]
    rw [one_mul]
    rw [zero_add]
  . rw [pow_succ]
    rw [mul_comm _ x]
    rw [mul_assoc]
    rw [ih]
    rw [mul_comm x]
    rw [← pow_succ]
    rw [add_assoc]
    rw [add_comm _ 1]
    rw [← add_assoc]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m ih
  . rw [pow_zero]
    rw [mul_zero]
    rw [pow_zero]
  . rw [pow_succ]
    rw [ih]
    rw [pow_add]
    rw [mul_add]
    rw [mul_one]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
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

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
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

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  . rw [pow_zero]
    rfl
  . rw [pow_succ]
    exact mul_nonneg ih hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
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
      contradiction
    . have hn' : 0 < n := by exact Nat.zero_lt_of_ne_zero hn
      have := (pow_eq_zero x _ hn').mp h.symm
      subst x
      contradiction

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  . rw [pow_zero]
    rw [pow_zero]
  . rw [pow_succ]
    rw [pow_succ]
    apply mul_le_mul ih hxy hy
    have hx : x ≥ 0 := by exact Rat.le_trans hy hxy
    exact pow_nonneg n hx

theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y > 0) (hn: n ≠ 0) : x^n > y^n := by
  induction' n with n ih
  . contradiction
  . rw [pow_succ]
    rw [pow_succ]
    by_cases hz: n = 0
    . subst n
      simp only [pow_zero, one_mul, gt_iff_lt]
      exact hxy
    . specialize ih hz
      have hx' : x ^ n > 0 := by
        apply pow_pos
        exact lt_trans hy hxy
      have hy' : y ^ n > 0 := by exact pow_pos n hy
      exact mul_lt_mul_of_pos' ih hxy hy hx'

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero]
    rw [pow_zero]
    rfl
  . rw [pow_succ]
    rw [pow_succ]
    rw [ih]
    rw [abs_mul]

theorem eq_zero_of_pow_eq_zero (x: ℚ) (n: ℕ) (h: x ^ n = 0): x = 0 ∧ n > 0 := by
  have hn : n > 0 := by
    by_contra hz
    simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hz
    subst n
    rw [pow_zero] at h
    contradiction
  constructor
  . exact (pow_eq_zero x n hn).mp h
  . exact hn

theorem zero_pow (m: ℕ) (h: m > 0) : (0:ℚ) ^ m = 0 := by
  have h' := pow_eq_zero 0 m h
  exact h'.mpr rfl

theorem pow_sub (x:ℚ) (m n:ℕ) (h: n ≥ m) (hx: x ≠ 0): x ^ n / x ^ m = x ^ (n - m) := by
  by_cases hm : x ^ m = 0
  . apply eq_zero_of_pow_eq_zero at hm
    tauto
  . field_simp [hm]
    rw [pow_add]
    rw [Nat.sub_add_cancel h]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

lemma cast_add (a b:ℕ): (a + b: ℕ) = (a: ℤ) + (b: ℤ) := by rfl
lemma cast_mul (a b:ℕ): (a * b: ℕ) = (a: ℤ) * (b: ℤ) := by rfl
lemma cast_sub (a b:ℕ) (h: b ≤ a): (a - b: ℕ) = (a: ℤ) - (b: ℤ) := by exact Int.ofNat_sub h

example : ¬ ∀ x:ℚ, ∀ n m:ℤ, x^n * x^m = x^(n+m) := by
  push_neg
  use 0, 1, -1
  simp

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0) : x^n * x^m = x^(n+m) := by
  wlog hnm : n ≥ m
  . simp only [ge_iff_le, not_le] at hnm
    have := this x m n hx (by exact Int.le_of_lt hnm)
    rwa [mul_comm, add_comm]
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  obtain ⟨m', hm'⟩ := Int.eq_nat_or_neg m
  rcases hn' with ⟨rfl | rfl⟩
  . rcases hm' with ⟨rfl | rfl⟩
    . repeat rw [pow_eq_zpow]
      have : (n':ℤ) + (m':ℤ) = (((n' + m'):ℕ): ℤ) := by rfl
      rw [this]
      rw [pow_eq_zpow]
      exact pow_add _ _ _
    . subst m -- why didn't rfl do it
      rw [zpow_neg, pow_eq_zpow]
      field_simp
      by_cases h2: n' ≥ m'
      . have : (n': ℤ) + -(m':ℤ) = n' - m' := by rfl
        rw [this]
        rw [← cast_sub n' m' h2]
        rw [pow_eq_zpow]
        rw [pow_add]
        congr
        omega
      . have : (n': ℤ) + -(m':ℤ) = -(m' - n') := by omega
        rw [this]
        rw [← cast_sub m' n' _]
        rw [zpow_neg]
        field_simp
        rw [pow_add]
        congr
        omega
        linarith
  . subst n -- why didn't rfl do it
    rw [zpow_neg]
    rcases hm' with ⟨rfl | rfl⟩
    . field_simp
      by_cases h2: n' ≥ m'
      . have : -(n': ℤ) + (m':ℤ) = m' - n' := by omega
        rw [this]
        rw [← cast_sub]
        rw [pow_eq_zpow]
        rw [pow_add]
        congr
        omega
        linarith
      . have : -(n': ℤ) + (m':ℤ) = -(n' - m') := by omega
        rw [this]
        rw [← cast_sub]
        rw [zpow_neg]
        field_simp
        rw [pow_add]
        congr
        omega
        linarith
    . subst m
      rw [zpow_neg]
      field_simp
      have : -(n': ℤ) + (-(m':ℤ)) = -(n' + m') := by omega
      rw [this]
      rw [← cast_add]
      rw [zpow_neg]
      field_simp
      rw [pow_add]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
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

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . repeat rw [pow_eq_zpow]
    rw [mul_pow]
  . subst n
    repeat rw [zpow_neg]
    field_simp
    rw [mul_pow]

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . rw [pow_eq_zpow]
    exact pow_pos n' hx
  . subst n
    rw [zpow_neg]
    field_simp

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . repeat rw [pow_eq_zpow]
    apply pow_ge_pow _ _ _ hxy
    exact le_of_lt hy
  . exfalso
    linarith

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
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

theorem pow_nat_inj {x y:ℚ} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  wlog h: x ≤ y
  . have hxy' : y ≤ x := by exact le_of_not_ge h
    exact (this hy hx hn hxy.symm hxy').symm
  . by_contra hneq
    have h': x < y := by exact lt_of_le_of_ne h hneq
    have := pow_gt_pow _ _ n h' hx hn
    linarith

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . repeat rw [pow_eq_zpow] at hxy
    norm_cast at hn
    exact pow_nat_inj hx hy hn hxy
  . subst n
    rw [zpow_neg, zpow_neg] at hxy
    norm_cast at hn
    simp only [and_true] at hn
    apply pow_nat_inj hx hy hn
    simp only [one_div, inv_inj] at hxy
    exact hxy

theorem pow_nat_abs (x:ℚ) (n:ℕ): |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero, pow_zero]
    rfl
  . rw [← pow_add, ← pow_add]
    rw [abs_mul]
    rw [ih]
    rw [pow_one, pow_one]

theorem abs_one_div(x:ℚ): 1 / |x| = |1 / x| := by
  have : (1:ℚ) = |1| := by rfl
  conv_lhs => rw [this]
  exact Eq.symm (abs_div 1 x)

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ): |x|^n = |x^n| := by
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . repeat rw [pow_eq_zpow]
    exact pow_nat_abs x n'
  . subst n
    rw [zpow_neg, zpow_neg]
    rw [pow_nat_abs]
    rw [abs_one_div]

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  induction' N with N ih
  . qify
    rw [pow_zero]
    rfl
  . by_cases hz: N = 0
    . subst hz
      rw [zero_add]
      decide
    have hz' : 0 < N := by exact Nat.zero_lt_of_ne_zero hz
    qify
    rw [pow_succ]
    suffices h: ↑N * 1 < 2 ^ N * 2 by
      rw [mul_one] at h
      norm_cast
    rw [mul_comm _ 1, mul_comm _ 2]
    apply mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
    . decide
    . exact ih
    . exact hz'
    . decide
