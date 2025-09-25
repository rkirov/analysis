import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
     intro a
     rfl
    symm := by
      intro a b h
      exact h.symm
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by exact ofNat_inj n 0

/-- natCast is a homomorphism of monoids -/
theorem Int.natCast_add (a b:ℕ) : ((a + b) : Int) = (a : Int) + (b : Int) := by rfl

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ h; simp at h ⊢
    dsimp [Setoid.r]
    calc _ = c + b := by rw [add_comm]
      _ = a + d := by rw [h]
      _ = _ := by rw [add_comm]
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩
    apply Quot.sound
    simp [Setoid.r]
    abel
  ) (by
    rintro ⟨a1, a2⟩
    apply Quot.sound
    simp [Setoid.r]
  ) (by
    rintro ⟨a1, a2⟩
    apply Quot.sound
    simp [Setoid.r]
    rw [add_comm]
  )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    apply Quot.sound
    simp [Setoid.r]
    abel

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    apply Quot.sound
    simp [Setoid.r]
    -- abel needs some help
    repeat rw [mul_comm a1, mul_comm a2]
    abel
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    rintro ⟨a1, a2⟩
    apply Quot.sound
    simp [Setoid.r]
  mul_one := by
    rintro ⟨a1, a2⟩
    apply Quot.sound
    simp [Setoid.r]

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩
    apply Quot.sound
    simp [Setoid.r]
    -- abel needs some help
    repeat rw [mul_add]
    abel
  right_distrib := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩
    apply Quot.sound
    simp [Setoid.r]
    -- abel needs some help
    repeat rw [add_mul]
    abel
  zero_mul := by
    rintro ⟨a1, a2⟩
    apply Quot.sound
    simp [Setoid.r]
  mul_zero := by
    rintro ⟨a1, a2⟩
    apply Quot.sound
    simp [Setoid.r]

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  rw [sub_eq]
  repeat rw [natCast_eq]
  rw [neg_eq]
  rw [add_eq]
  rw [eq]
  simp only [add_zero, zero_add, Nat.add_left_cancel_iff]

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  rw [mul_eq] at h
  rw [ofNat_eq] at h
  rw [eq] at h
  simp at h
  rw [ofNat_eq]
  repeat rw [eq]
  simp only [add_zero, zero_add]
  wlog ha: a1 < a2
  . simp at ha
    have : a2 = a1 ∨ a2 < a1 := by exact Nat.eq_or_lt_of_le ha
    cases' this with he hb
    . left
      exact he.symm
    . specialize this a2 a1 b1 b2
      have := this (by omega) hb
      omega
  . wlog hb: b1 < b2
    . simp at hb
      have : b2 = b1 ∨ b2 < b1 := by exact Nat.eq_or_lt_of_le hb
      cases' this with he hb
      . right
        exact he.symm
      . specialize this a1 a2 b2 b1
        have := this (by omega) ha hb
        omega
    . have h: (a2 - a1) * b2 = (a2 - a1) * b1 := by
        repeat rw [Nat.mul_sub_right_distrib]
        omega
      have h': (a2 - a1) * (b2 - b1) = 0 := by
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [Nat.mul_eq_zero] at h'
      omega

theorem Int.neg_mul (a b: Int) : (-a) * b = -(a * b) := by
  -- exact Lean.Grind.CommRing.neg_mul a b -- but this might be cheating?
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  rw [neg_eq]
  repeat rw [mul_eq]
  rw [neg_eq]
  rw [eq]
  omega

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have h1: a * c - b * c = 0 := by exact Lean.Grind.CommRing.sub_eq_zero_iff.mpr h -- is this cheating?
  have h2: (a - b) * c = 0 := by
    rw [Int.sub_eq]
    rw [right_distrib]
    rw [Int.neg_mul]
    rwa [← Int.sub_eq]
  apply mul_eq_zero at h2
  cases' h2 with h3 h4
  . rwa [sub_eq_zero] at h3
  . contradiction

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor
  . intro h
    obtain ⟨⟨n, hn⟩ , he⟩ := h
    use n
    constructor
    . contrapose! he
      rw [he] at hn
      simp only [Nat.cast_zero, add_zero] at hn
      exact hn.symm
    . exact hn
  . intro h
    obtain ⟨n, hn, he⟩ := h
    rw [lt_iff]
    constructor
    . use n
    . contrapose! hn
      rw [hn] at he
      simp only [left_eq_add] at he
      exact (cast_eq_0_iff_eq_0 n).mp he

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff] at h ⊢
  obtain ⟨⟨t, ht⟩, hn⟩ := h
  constructor
  . use t
    rw [ht]
    abel
  . contrapose! hn
    simp only [add_left_inj] at hn
    exact hn

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff] at hab hc ⊢
  obtain ⟨⟨t, ht⟩, hnt⟩ := hab
  obtain ⟨⟨u, hu⟩, hnu⟩ := hc
  constructor
  . use t * u
    rw [ht, hu]
    simp only [zero_add, Nat.cast_mul]
    exact right_distrib a ↑t ↑u
  . contrapose! hnt
    exact mul_right_cancel₀ a b c hnt (id (Ne.symm hnu))

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff] at h ⊢
  obtain ⟨⟨t, ht⟩, hn⟩ := h
  constructor
  . use t
    rw [ht]
    simp only [neg_add_rev, neg_add_cancel_comm]
  . contrapose! hn
    have : a = -(-b) := by exact neg_eq_iff_eq_neg.mp hn
    rw [this]
    simp only [neg_neg]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rw [le_iff] at h ⊢
  obtain ⟨t, ht⟩ := h
  use t
  rw [ht]
  simp only [neg_add_rev, neg_add_cancel_comm]

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff] at hab hbc ⊢
  obtain ⟨⟨t, ht⟩, hn⟩ := hab
  obtain ⟨⟨u, hu⟩, hnu⟩ := hbc
  constructor
  . use t + u
    rw [hu, ht]
    simp only [Nat.cast_add]
    ring
  . contrapose! hn
    subst a
    rw [hu] at ht
    have : (u: Int) + (t: Int) = 0 := by
      conv_lhs at ht => rw [← add_zero b]
      rw [add_assoc] at ht
      apply add_left_cancel at ht
      exact ht.symm
    rw [← natCast_add] at this
    sorry

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  have := Int.trichotomous (a - b)
  rcases this with h1 | h2 | h3
  . right; right; rwa [sub_eq_zero] at h1;
  . obtain ⟨n, hn, hab⟩ := h2
    left
    simp only [gt_iff_lt]
    rw [lt_iff]
    constructor
    . use n
      exact Eq.symm (add_eq_of_eq_sub' (Eq.symm hab))
    . have hn': n ≠ 0 := by exact Nat.ne_zero_of_lt hn
      contrapose! hn
      rw [hn] at hab
      simp at hab
      symm at hab
      rw [cast_eq_0_iff_eq_0] at hab
      contradiction
  . right; left;
    obtain ⟨n, hn, hab⟩ := h3
    rw [lt_iff]
    constructor
    . use n
      have := add_eq_of_eq_sub' (Eq.symm hab)
      change b - ↑n = a at this
      apply eq_add_of_sub_eq' at this
      rw [add_comm]
      exact this
    . have hn': n ≠ 0 := by exact Nat.ne_zero_of_lt hn
      contrapose! hn
      rw [hn] at hab
      simp at hab
      rw [cast_eq_0_iff_eq_0] at hab
      contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  by_contra! h
  obtain ⟨h1, h2⟩ := h
  rw [h2] at h1
  rw [gt_iff_lt] at h1
  rw [lt_iff] at h1
  tauto

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  by_contra! h
  obtain ⟨h1, h2⟩ := h
  rw [h2] at h1
  rw [lt_iff] at h1
  tauto

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        sorry
      | isFalse h =>
        apply isFalse
        sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by sorry

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by sorry

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by sorry

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by sorry

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by sorry

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by sorry

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    sorry)
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

end Section_4_1
