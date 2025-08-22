import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of ℕ and ℤ.

- Equivalence with the Mathlib rationals `_root_.Rat` (or `ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers `ℕ` and integers `ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

instance : ToString PreRat where
  toString q := toString q.numerator ++ " // " ++ toString q.denominator

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by
      intro a
      rfl
    symm := by
      intro a b h
      omega
    trans := by
      intro a b c hab hbc
      have ha := a.nonzero
      have hb := b.nonzero
      have hc := c.nonzero
      have hab' := hab -- stash for later
      apply_fun (· * c.numerator) at hab
      rw [mul_assoc] at hab
      rw [mul_comm _ c.numerator] at hab
      rw [← hbc] at hab
      rw [← mul_assoc] at hab
      rw [mul_comm _ b.numerator] at hab
      repeat rw [mul_assoc] at hab
      rw [mul_comm a.denominator] at hab
      rw [mul_eq_mul_left_iff] at hab
      cases' hab with h1 h2
      . exact h1
      . rw [h2] at hbc
        simp only [zero_mul, zero_eq_mul] at hbc
        cases' hbc with h3 h4
        . rw [h2] at hab'
          simp only [zero_mul, mul_eq_zero] at hab'
          cases' hab' with h5 h6
          . rw [h3, h5]
            omega
          . contradiction
        . contradiction
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩
    -- why rw doesn't work here but simp does?
    simp [eq a c h1 h2]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    have : a * c * (b' * d') = (a * b') * (c * d') := by ring
    rw [this, h3, h4]
    ring
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨a, b, h1⟩ ⟨c, d, h2⟩ h
    simp_all [Setoid.r]
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

theorem Rat.of_Nat_eq' (n:ℕ) : (ofNat(n):Rat) = n // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by sorry

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  repeat rw [Rat.coe_Int_eq]
  rw [add_eq]
  rw [eq] <;> omega
  exact Int.one_ne_zero
  exact Int.one_ne_zero

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  repeat rw [Rat.coe_Int_eq]
  rw [mul_eq]
  rw [eq] <;> omega
  exact Int.one_ne_zero
  exact Int.one_ne_zero

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b h
  simp only at h
  repeat rw [Rat.coe_Int_eq] at h
  rw [eq] at h
  simp only [mul_one] at h
  exact h
  exact Int.one_ne_zero
  exact Int.one_ne_zero

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ h
    simp_all [Setoid.r]
    by_cases ha : a = 0
    . simp_all [ha]
    . by_cases hc : c = 0
      . simp_all [ha, hc]
      . simp_all [ha, hc]
        symm at h
        rw [mul_comm c, mul_comm a] at h
        exact h
  )

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
  intro a
  obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
  rw [of_Nat_eq']
  rw [add_eq]
  rw [eq]
  . simp only [CharP.cast_eq_zero, zero_mul, one_mul, zero_add]
  . omega
  . exact hc
  . exact Int.one_ne_zero
  . exact hc
 ) (by
  intro a
  obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
  rw [of_Nat_eq']
  rw [neg_eq]
  rw [add_eq]
  rw [eq]
  simp only [neg_mul, mul_one, CharP.cast_eq_zero, zero_mul]
  rw [mul_comm]
  . omega
  . contrapose hc
    simp only [ne_eq, Decidable.not_not]
    simp only [ne_eq, mul_eq_zero, or_self, Decidable.not_not] at hc
    exact hc
  . exact Int.one_ne_zero
  . exact hc
  . exact hc
  . exact hc
 )

theorem Rat.sub_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) - (c // d) = (a*d - b*c) // (b*d) := by
  change a // b + (-c // d) = _
  rw [neg_eq]
  rw [add_eq]
  rw [eq]
  . ring
  . exact Int.mul_ne_zero hb hd
  . exact Int.mul_ne_zero hb hd
  . exact hb
  . exact hd
  . exact hd

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro a b
    obtain ⟨ a1, b1, h1, rfl ⟩ := eq_diff a
    obtain ⟨ a2, b2, h2, rfl ⟩ := eq_diff b
    rw [add_eq _ _ h1 h2, add_eq _ _ h2 h1]
    rw [eq]
    . ring
    . exact Int.mul_ne_zero h1 h2
    . exact Int.mul_ne_zero h2 h1

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by
    intro a b
    obtain ⟨ a1, b1, h1, rfl ⟩ := eq_diff a
    obtain ⟨ a2, b2, h2, rfl ⟩ := eq_diff b
    rw [mul_eq _ _ h1 h2, mul_eq _ _ h2 h1]
    rw [eq]
    . ring
    . exact Int.mul_ne_zero h1 h2
    . exact Int.mul_ne_zero h2 h1
  mul_assoc := by
    intro a b c
    obtain ⟨ a1, b1, h1, rfl ⟩ := eq_diff a
    obtain ⟨ a2, b2, h2, rfl ⟩ := eq_diff b
    obtain ⟨ a3, b3, h3, rfl ⟩ := eq_diff c
    repeat rw [mul_eq]
    rw [eq]
    . ring
    . exact Int.mul_ne_zero (Int.mul_ne_zero h1 h2) h3
    . exact Int.mul_ne_zero h1 (Int.mul_ne_zero h2 h3)
    . exact h1
    . exact Int.mul_ne_zero h2 h3
    . exact h2
    . exact h3
    . exact Int.mul_ne_zero h1 h2
    . exact h3
    . exact h1
    . exact h2
  one_mul := by
    intro a
    obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
    rw [of_Nat_eq']
    rw [mul_eq]
    rw [eq]
    . simp only [Nat.cast_one, one_mul]
    . omega
    . exact hc
    . exact Int.one_ne_zero
    . exact hc
  mul_one := by
    intro a
    obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
    rw [of_Nat_eq']
    rw [mul_eq]
    rw [eq]
    . simp only [Nat.cast_one, mul_one]
    . omega
    . exact hc
    . exact hc
    . exact Int.one_ne_zero

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by
    intro a b c
    obtain ⟨ a1, b1, h1, rfl ⟩ := eq_diff a
    obtain ⟨ a2, b2, h2, rfl ⟩ := eq_diff b
    obtain ⟨ a3, b3, h3, rfl ⟩ := eq_diff c
    repeat rw [mul_eq]
    rw [add_eq, mul_eq, add_eq]
    rw [eq]
    . ring
    . exact Int.mul_ne_zero h1 (Int.mul_ne_zero h2 h3)
    . apply Int.mul_ne_zero
      . exact Int.mul_ne_zero h1 h2
      . exact Int.mul_ne_zero h1 h3
    . exact Int.mul_ne_zero h1 h2
    . exact Int.mul_ne_zero h1 h3
    . exact h1
    . exact Int.mul_ne_zero h2 h3
    . exact h2
    . exact h3
    . exact h1
    . exact h3
    . exact h1
    . exact h2
  right_distrib := by
    intro a b c
    obtain ⟨ a1, b1, h1, rfl ⟩ := eq_diff a
    obtain ⟨ a2, b2, h2, rfl ⟩ := eq_diff b
    obtain ⟨ a3, b3, h3, rfl ⟩ := eq_diff c
    repeat rw [mul_eq]
    rw [add_eq, mul_eq, add_eq]
    rw [eq]
    . ring
    . exact Int.mul_ne_zero (Int.mul_ne_zero h1 h2) h3
    . apply Int.mul_ne_zero
      . exact Int.mul_ne_zero h1 h3
      . exact Int.mul_ne_zero h2 h3
    . exact Int.mul_ne_zero h1 h3
    . exact Int.mul_ne_zero h2 h3
    . exact Int.mul_ne_zero h1 h2
    . exact h3
    . exact h1
    . exact h2
    . exact h2
    . exact h3
    . exact h1
    . exact h3
  zero_mul := by
    intro a
    obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
    repeat rw [of_Nat_eq']
    rw [mul_eq]
    rw [eq]
    . simp only [CharP.cast_eq_zero, zero_mul, mul_one, one_mul]
    . omega
    . exact Int.one_ne_zero
    . exact Int.one_ne_zero
    . exact hc
  mul_zero := by
    intro a
    obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
    repeat rw [of_Nat_eq']
    rw [mul_eq]
    rw [eq]
    . simp only [CharP.cast_eq_zero, mul_zero, mul_one, zero_mul]
    . omega
    . exact Int.one_ne_zero
    . exact hc
    . exact Int.one_ne_zero
  mul_assoc := by
    intro a b c
    obtain ⟨ a1, b1, h1, rfl ⟩ := eq_diff a
    obtain ⟨ a2, b2, h2, rfl ⟩ := eq_diff b
    obtain ⟨ a3, b3, h3, rfl ⟩ := eq_diff c
    repeat rw [mul_eq]
    rw [eq]
    . ring
    . apply Int.mul_ne_zero
      . exact Int.mul_ne_zero h1 h2
      . exact h3
    . exact Int.mul_ne_zero h1 (Int.mul_ne_zero h2 h3)
    . exact h1
    . exact Int.mul_ne_zero h2 h3
    . exact h2
    . exact h3
    . exact Int.mul_ne_zero h1 h2
    . exact h3
    . exact h1
    . exact h2

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by sorry

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

theorem Rat.coe_Rat_eq' (a:ℤ) {b:ℕ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  change ((a : ℚ) / ↑b).num // ((a:ℚ) / ↑b).den = _
  rw [eq]
  . qify
    have := Rat.num_div_den ((a:ℚ) / b)
    rwa [div_eq_div_iff] at this
    . simp only [ne_eq, Rat.natCast_eq_zero, Rat.den_ne_zero, not_false_eq_true]
    . exact Nat.cast_ne_zero.mpr hb
  . simp only [ne_eq, Int.natCast_eq_zero, Rat.den_ne_zero, not_false_eq_true]
  . exact Int.ofNat_ne_zero.mpr hb

theorem Rat.coe_Rat_inj : Function.Injective (fun (n:ℚ) ↦ (n:Rat)) := by
  intro p q h
  simp only at h
  rw [← Rat.num_div_den p] at h
  rw [← Rat.num_div_den q] at h
  repeat rw [coe_Rat_eq'] at h
  rw [eq] at h
  exact Rat.eq_iff_mul_eq_mul.mpr h
  . have := p.den_nz
    exact Int.ofNat_ne_zero.mpr this
  . have := q.den_nz
    exact Int.ofNat_ne_zero.mpr this
  . exact q.den_nz
  . exact p.den_nz

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl


/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    use 0
    use 1
    apply coe_Int_inj.ne_iff.mpr
    exact Int.zero_ne_one

  mul_inv_cancel := by
    intro a ha
    obtain ⟨ b, c, hc, rfl ⟩ := eq_diff a
    have hb: b ≠ 0 := by
      contrapose ha
      simp only [ne_eq, Decidable.not_not] at ha ⊢
      rw [ha]
      rw [of_Nat_eq]
      rw [eq]
      . omega
      . exact hc
      . exact Int.one_ne_zero
    rw [inv_eq]
    rw [mul_eq]
    rw [of_Nat_eq]
    rw [eq]
    . simp only [mul_one, Nat.cast_one, one_mul]
      rw [mul_comm]
    . exact Int.mul_ne_zero hc hb
    . exact Int.one_ne_zero
    . exact hc
    . exact hb
    . exact hc

  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
  rw [Rat.div_eq]
  rw [Rat.inv_eq]
  rw [Rat.mul_eq]
  rw [Rat.eq] <;> omega
  . omega
  . omega
  . omega

-- also
example : (3//4) / (5//6) = 18 // 20 := by
  rw [Rat.div_eq]
  rw [Rat.inv_eq]
  rw [Rat.mul_eq]
  rw [Rat.eq] <;> omega
  . omega
  . omega
  . omega

-- in built in Q
example : (3/4) / (5/6) = 9 / 10 := by omega
example : (3/4) / (5/6) = 18 / 20 := by omega

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by
    intro a b
    repeat rw [Rat.coe_Int_eq]
    rw [add_eq _ _ Int.one_ne_zero Int.one_ne_zero]
    simp only [mul_one, one_mul]
  map_mul' := by
    intro a b
    repeat rw [Rat.coe_Int_eq]
    rw [mul_eq _ _ Int.one_ne_zero Int.one_ne_zero]
    simp only [mul_one]

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  have hat := lt_trichotomy a 0
  have hbt := lt_trichotomy b 0
  have hbt': b > 0 ∨ b < 0 := by aesop
  rcases hat with haneg | ha0 | hapos
  . cases' hbt' with hbpos hbneg
    . right; right
      use -a // b
      constructor
      . use -a, b
        constructor
        . linarith
        . constructor
          . exact hbpos
          . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq, neg_eq]
            rw [eq]
            . simp only [one_mul, neg_mul, mul_one]
            . exact hb
            . aesop
            . exact hb
            . exact Int.one_ne_zero
            . exact hb
            . exact Int.one_ne_zero
      . simp only [neg_neg]
    . right; left
      use -a, -b
      constructor
      . omega
      . constructor
        . omega
        . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq]
          rw [eq]
          . simp only [mul_neg, one_mul, mul_one, neg_mul]
          . exact hb
          . omega
          . exact Int.one_ne_zero
          . omega
          . exact Int.one_ne_zero
  . rw [ha0]
    left
    rw [of_Nat_eq]
    rw [eq]
    . simp only [mul_one, CharP.cast_eq_zero, zero_mul]
    . exact hb
    . exact Int.one_ne_zero
  . cases' hbt' with hbpos hbneg
    . right; left
      use a, b
      constructor
      . exact hapos
      . constructor
        . exact hbpos
        . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq]
          rw [eq]
          . simp only [one_mul, mul_one]
          . linarith
          . simp only [one_mul, ne_eq]
            omega
          . exact Int.one_ne_zero
          . exact hb
          . exact Int.one_ne_zero
    . right; right
      use a // (-b)
      constructor
      . use a, -b
        constructor
        . exact hapos
        . constructor
          . omega
          . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq]
            rw [eq]
            . simp only [mul_neg, one_mul, mul_one]
            . omega
            . omega
            . exact Int.one_ne_zero
            . omega
            . exact Int.one_ne_zero
      . rw [neg_eq]
        rw [eq]
        . simp only [mul_neg, neg_mul]
        . omega
        . omega
        . omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  rintro ⟨ h1, h2 ⟩
  rw [h1] at h2
  rw [isPos] at h2
  obtain ⟨ a, b, ha, hb, h2' ⟩ := h2
  rw [coe_Int_eq, of_Nat_eq] at h2'
  rw [coe_Int_eq, div_eq, inv_eq, mul_eq] at h2'
  rw [eq] at h2'
  simp at h2'
  . linarith
  . exact Int.one_ne_zero
  . simp only [one_mul, ne_eq]
    omega
  . exact Int.one_ne_zero
  . omega
  . exact Int.one_ne_zero

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  rintro ⟨h1, h2⟩
  rw [isNeg] at h2
  obtain ⟨ r, hr1, hr2 ⟩ := h2
  rw [isPos] at hr1
  obtain ⟨ a, b, ha, hb, hr1' ⟩ := hr1
  rw [h1] at hr2
  simp only [zero_eq_neg] at hr2
  subst r
  rw [coe_Int_eq, coe_Int_eq, of_Nat_eq, div_eq, inv_eq, mul_eq] at hr2
  rw [eq] at hr2
  simp at hr2
  . linarith
  . simp only [one_mul, ne_eq]
    exact Int.ne_of_gt hb
  . exact Int.one_ne_zero
  . exact Int.one_ne_zero
  . omega
  . exact Int.one_ne_zero

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  rintro ⟨ h1, h2 ⟩
  rw [isNeg] at h2
  obtain ⟨ r, hr1, hr2 ⟩ := h2
  rw [isPos] at h1 hr1
  obtain ⟨ a, b, ha, hb, h1' ⟩ := h1
  obtain ⟨ c, d, hc, hd, hr1' ⟩ := hr1
  subst x
  subst r
  repeat rw [coe_Int_eq] at h1'
  rw [div_eq, inv_eq, mul_eq, neg_eq, div_eq, inv_eq, mul_eq] at h1'
  rw [eq] at h1'
  . simp only [mul_one, one_mul, neg_mul] at h1'
    have : a * d > 0 := by exact Int.mul_pos ha hd
    have : c * b > 0 := by exact Int.mul_pos hc hb
    linarith
  . omega
  . omega
  . exact Int.one_ne_zero
  . exact Ne.symm (Int.ne_of_lt hb)
  . exact Int.one_ne_zero
  . omega
  . exact Int.one_ne_zero
  . exact Ne.symm (Int.ne_of_lt hd)
  . exact Int.one_ne_zero

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  constructor
  . intro h
    simp only [gt_iff_lt] at h
    rw [lt_iff] at h
    rw [isNeg] at h
    obtain ⟨ r, hr1, hr2 ⟩ := h
    have : (x - y) = r := by
      have := by exact congrArg ((-1) * .) hr2
      simp only [neg_mul, one_mul, neg_sub, mul_neg, neg_neg] at this
      exact this
    rw [this]
    exact hr1
  . intro h
    simp only [gt_iff_lt]
    rw [lt_iff]
    rw [isNeg]
    use (x - y)
    constructor
    . exact h
    . ring

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  constructor
  . intro h
    simp only [ge_iff_le, gt_iff_lt] at h ⊢
    rw [le_iff] at h
    cases' h with h1 h2
    . left; exact h1
    . right; exact h2.symm
  . intro h
    simp only [gt_iff_lt, ge_iff_le] at h ⊢
    rw [le_iff]
    cases' h with h1 h2
    . left; exact h1
    . right; exact h2.symm

-- z is needed otherwise x < y gets stuck?
-- todo: ask on Zulip why
/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  have := Rat.trichotomous (x - y)
  rcases this with hzero | hpos | hneg
  . right; right
    have : x - y + y = 0 + y := by exact congrArg (. + y) hzero
    simp only [sub_add_cancel, zero_add] at this
    exact this
  . left
    rw [gt_iff]
    exact hpos
  . right; left
    rw [lt_iff]
    exact hneg

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  rintro ⟨ h1, h2 ⟩
  rw [gt_iff] at h1
  rw [lt_iff] at h2
  exact Rat.not_pos_and_neg (x - y) ⟨ h1, h2 ⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rintro ⟨ h1, h2 ⟩
  rw [gt_iff] at h1
  have : (x - y) = 0 := by rw [h2]; ring
  exact Rat.not_zero_and_pos (x - y) ⟨this, h1⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rintro ⟨ h1, h2 ⟩
  rw [lt_iff] at h1
  have : (x - y) = 0 := by rw [h2]; ring
  exact Rat.not_zero_and_neg (x - y) ⟨this, h1⟩

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ (y - x).isPos := by exact gt_iff y x

-- why not? because rfl solves it? I guess definition of `>` differs from book
theorem Rat.antisymm' (x y:Rat) : x < y ↔ y > x := by rfl

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  -- working with isPos is easier
  rw [← gt_iff_lt] at hxy hyz ⊢
  rw [gt_iff] at hxy hyz ⊢
  rw [isPos] at hxy hyz ⊢
  obtain ⟨ a, b, ha, hb, hxy' ⟩ := hxy
  obtain ⟨ c, d, hc, hd, hyz' ⟩ := hyz
  use a * d + b * c, b * d
  constructor
  -- why can't linarith do this automatically?
  . have : a * d > 0 := by exact Int.mul_pos ha hd
    have : b * c > 0 := by exact Int.mul_pos hb hc
    linarith
  . constructor
    . exact Int.mul_pos hb hd
    . have : z - x = (z - y) + (y - x) := by ring
      rw [this]
      rw [hxy', hyz']
      simp only [Int.cast_add, Int.cast_mul]
      repeat rw [coe_Int_eq]
      repeat rw [div_eq, inv_eq, mul_eq]
      repeat rw [add_eq]
      rw [div_eq, mul_eq, mul_eq, mul_eq, inv_eq]
      rw [add_eq, mul_eq]
      rw [eq]
      . ring
      -- is there a better way to use omega and friends on all possible goals
      . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
        omega
      . simp only [mul_one, one_mul, ne_eq, mul_eq_zero, not_or]
        omega
      . omega
      . have bneq : b ≠ 0 := by exact Ne.symm (Int.ne_of_lt hb)
        have dneq : d ≠ 0 := by exact Ne.symm (Int.ne_of_lt hd)
        exact Int.mul_ne_zero bneq dneq
      repeat omega

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  rw [← gt_iff_lt] at hxy ⊢
  rw [gt_iff] at hxy ⊢
  simp only [add_sub_add_right_eq_sub]
  exact hxy

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  rw [← gt_iff_lt] at hxy ⊢
  rw [gt_iff] at hxy ⊢
  have : (y * z - x * z) = (y - x) * z := by ring
  rw [this]
  rw [isPos] at hz hxy ⊢
  obtain ⟨ a, b, ha, hb, hxy' ⟩ := hxy
  obtain ⟨ c, d, hc, hd, hz' ⟩ := hz
  use a * c, b * d
  constructor
  . exact Int.mul_pos ha hc
  . constructor
    . exact Int.mul_pos hb hd
    . rw [hxy']
      rw [hz']
      repeat rw [coe_Int_eq]
      repeat rw [div_eq, inv_eq, mul_eq]
      rw [mul_eq]
      rw [eq]
      . ring
      . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
        omega
      . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
        omega
      . omega
      . have bneq : b ≠ 0 := by exact Ne.symm (Int.ne_of_lt hb)
        have dneq : d ≠ 0 := by exact Ne.symm (Int.ne_of_lt hd)
        exact Int.mul_ne_zero bneq dneq
      repeat omega

theorem Rat.gt_of_neq_le (a b: Rat): (¬ a ≤ b) ↔ a > b := by
  constructor
  . intro h
    rw [le_iff] at h
    push_neg at h
    have := Rat.trichotomous' a b a
    tauto
  . intro h
    rw [le_iff]
    push_neg
    constructor
    . by_contra h2
      exact Rat.not_gt_and_lt _ _ ⟨h, h2⟩
    . by_contra h2
      have := And.intro h h2
      exact Rat.not_gt_and_eq _ _ this

theorem Rat.formalDiv_eq (a b: ℤ) (hb: b ≠ 0): ⟦{ numerator := a, denominator := b, nonzero := hb }⟧ = a // b := by
  rw [formalDiv]
  simp [hb]

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            rw [le_iff_eq_or_lt] at h
            rw [← ge_iff_le] at ⊢
            rw [ge_iff]
            rw [gt_iff]
            cases' h with hlt heq
            . right
              simp only [Quotient.eq]
              rw [mul_comm b] at hlt
              symm
              exact hlt
            . left
              rw [isPos]
              use c * b - a * d, b * d
              constructor
              . rw [mul_comm c]
                exact Int.sub_pos_of_lt heq
              . constructor
                . simp only [gt_iff_lt]
                  have : b * d ≠ 0 := by exact Int.mul_ne_zero hb hd
                  exact lt_of_le_of_ne hbd (id (Ne.symm this))
                . simp [Rat.formalDiv_eq]
                  rw [sub_eq]
                  repeat rw [coe_Int_eq]
                  rw [div_eq, mul_eq, mul_eq, mul_eq, inv_eq]
                  simp only [mul_one]
                  rw [sub_eq, mul_eq, eq]
                  . ring
                  . exact Int.mul_ne_zero hd hb
                  . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
                    omega
                  . exact Int.one_ne_zero
                  . exact Int.mul_ne_zero hb hd
                  repeat omega
          | isFalse h =>
            apply isFalse
            simp only [not_le] at h
            rw [gt_of_neq_le]
            rw [gt_iff]
            use a * d - b * c, b * d
            constructor
            . exact Int.sub_pos_of_lt h
            . constructor
              . have : b * d ≠ 0 := by exact Int.mul_ne_zero hb hd
                exact lt_of_le_of_ne hbd (id (Ne.symm this))
              . simp [formalDiv_eq]
                rw [sub_eq]
                repeat rw [coe_Int_eq]
                rw [div_eq, mul_eq, mul_eq, mul_eq, inv_eq, sub_eq, mul_eq]
                rw [eq]
                . ring
                . exact Int.mul_ne_zero hb hd
                . simp only [mul_one, one_mul, ne_eq, mul_eq_zero, not_or]
                  omega
                . omega
                . exact Int.mul_ne_zero hb hd
                repeat omega
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            simp only [not_le] at hbd
            rw [le_iff_eq_or_lt] at h
            rw [← ge_iff_le] at ⊢
            rw [ge_iff]
            rw [gt_iff]
            cases' h with hlt heq
            . right
              simp only [Quotient.eq]
              rw [mul_comm b] at hlt
              exact hlt
            . left
              use a * d - b * c, (-b) * d
              constructor
              . omega
              . constructor
                . simp only [neg_mul, Int.neg_pos]
                  exact hbd
                . repeat rw [formalDiv_eq]
                  rw [sub_eq, coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq]
                  rw [eq]
                  . ring
                  . exact Int.mul_ne_zero hd hb
                  . simp only [neg_mul, mul_neg, one_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
                    omega
                  . omega
                  . simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
                    omega
                  repeat omega
          | isFalse h =>
            apply isFalse
            simp only [not_le] at hbd
            simp only [not_le] at h
            rw [gt_of_neq_le]
            rw [gt_iff]
            use b * c - a * d, (-b) * d
            constructor
            . omega
            . constructor
              simp only [neg_mul, Int.neg_pos]
              exact hbd
              . repeat rw [formalDiv_eq]
                rw [sub_eq, coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq]
                rw [eq]
                . ring
                . exact Int.mul_ne_zero hb hd
                . simp only [neg_mul, mul_neg, one_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
                  omega
                . omega
                . simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
                  omega
                repeat omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := by
    intro a
    rw [le_iff]
    right
    rfl
  le_trans := by
    intro a b c ha hb
    rw [le_iff] at ha hb ⊢
    cases' ha with h1 h2
    . cases' hb with h3 h4
      . left
        exact lt_trans h1 h3
      . left
        rwa [h4] at h1
    . cases' hb with h3 h4
      . rw [← h2] at h3
        left
        exact h3
      . rw [← h2] at h4
        right
        exact h4
  lt_iff_le_not_ge := by
    intro a b
    repeat rw [le_iff]
    push_neg
    constructor
    . intro h
      constructor
      . left; exact h
      . constructor
        . have := Rat.not_gt_and_lt a b
          tauto
        . have := Rat.not_lt_and_eq a b
          tauto
    . rintro ⟨h1, h2⟩
      tauto
  le_antisymm := by
    intro a b h1 h2
    rw [le_iff] at h1 h2
    by_contra heq
    have := Rat.not_gt_and_lt a b
    tauto
  le_total := by
    intro a b
    by_cases h: a = b
    . rw [h]
      tauto
    . repeat rw [le_iff]
      simp [h]
      have : b ≠ a := by tauto
      simp [this]
      have := Rat.trichotomous' a b a
      simp [h] at this
      tauto
  toDecidableLE := decidableRel

theorem Rat.add_le_add_left : ∀ (a b : Rat), a ≤ b → ∀ (c : Rat), c + a ≤ c + b := by
  intro p q h c
  rw [le_iff] at h ⊢
  cases' h with h1 h2
  . left
    rw [← gt_iff_lt] at h1 ⊢
    rw [gt_iff] at h1 ⊢
    rw [isPos] at h1 ⊢
    obtain ⟨a, b, ha, hb, hab⟩ := h1
    use a, b
    constructor
    . exact ha
    . constructor
      . exact hb
      . simp only [add_sub_add_left_eq_sub]
        exact hab
  . right
    rw [h2]

/-- If I don't extract them I get a non-termination error -/
theorem Rat.mul_lt_mul_of_pos_left :  ∀ (a b c : Rat), a < b → 0 < c → c * a < c * b := by
  intro p q r h hr
  rw [← gt_iff_lt] at h ⊢
  rw [gt_iff] at h ⊢
  rw [isPos] at h ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := h
  rw [lt_iff] at hr
  simp only [zero_sub] at hr
  rw [isNeg] at hr
  simp only [neg_inj, exists_eq_right'] at hr
  rw [isPos] at hr
  obtain ⟨c, d, hc, hd, hcd⟩ := hr
  use a * c, b * d
  constructor
  . exact Int.mul_pos ha hc
  . constructor
    . exact Int.mul_pos hb hd
    . have : r * q - r * p = r * (q - p) := by exact Eq.symm (mul_sub_left_distrib r q p)
      rw [this]
      rw [hab, hcd]
      repeat rw [div_eq]
      repeat rw [coe_Int_eq]
      repeat rw [inv_eq]
      repeat rw [mul_eq]
      rw [eq]
      . ring
      . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
        omega
      . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
        omega
      . omega
      . have bne : b ≠ 0 := by exact Ne.symm (Int.ne_of_lt hb)
        have dne : d ≠ 0 := by exact Ne.symm (Int.ne_of_lt hd)
        exact Int.mul_ne_zero bne dne
      . omega
      repeat omega

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := Rat.add_le_add_left

  add_le_add_right := by
    intro p q h c
    have := Rat.add_le_add_left p q h c
    rw [add_comm p, add_comm q]
    exact this
  mul_lt_mul_of_pos_left := Rat.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by
    intro p q r h hr
    rw [mul_comm p, mul_comm q]
    exact Rat.mul_lt_mul_of_pos_left p q r h hr
  le_of_add_le_add_left := by
    intro p q r h
    rw [le_iff] at h ⊢
    rcases h with h1 | h2
    . left
      rw [← gt_iff_lt] at h1 ⊢
      rw [gt_iff] at h1 ⊢
      rw [isPos] at h1 ⊢
      obtain ⟨a, b, ha, hb, hab⟩ := h1
      use a, b
      simp_all
    . simp only [add_right_inj] at h2
      right
      exact h2
  zero_le_one := by
    rw [le_iff]
    simp only [zero_ne_one, or_false]
    rw [← gt_iff_lt]
    rw [gt_iff]
    rw [isPos]
    use 1, 1
    simp_all

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  rw [isNeg] at hz
  obtain ⟨r, hr, hqr⟩ := hz
  subst z
  simp only [mul_neg, gt_iff_lt, neg_lt_neg_iff]
  exact mul_lt_mul_right hxy hr

/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    intro a b h
    simp only
    rw [PreRat.eq] at h
    suffices h: (a.numerator : ℚ) * ↑b.denominator = ↑b.numerator * ↑a.denominator by
      have ha' := a.nonzero
      have hb' := b.nonzero
      -- field tactic?
      sorry
    have := congrArg (@Int.cast ℚ _root_.Rat.instIntCast .) h
    simp at this
    exact this
    )
  invFun := fun n ↦ (n: Rat)
  left_inv n := by
    simp only
    obtain ⟨a, b, hb, hab⟩ := eq_diff n
    subst n
    simp [hb]
    repeat rw [coe_Int_eq]
    rw [div_eq, inv_eq, mul_eq]
    rw [eq]
    . ring
    repeat omega

  right_inv n := by
    simp only
    obtain ⟨a, b, hb, hab⟩ := eq_diff n
    rw [hab]
    simp [hb]
    rw [← coe_Rat_eq] at hab
    apply coe_Rat_inj at hab
    . exact hab.symm
    . exact hb

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by
    intro p q
    obtain ⟨a, b, hb, rfl⟩ := eq_diff p
    obtain ⟨c, d, hd, rfl⟩ := eq_diff q
    simp [hb, hd]
    rw [le_iff_lt_or_eq]
    rw [← ge_iff_le]
    rw [ge_iff]
    rw [gt_iff]
    constructor
    . intro h
      cases' h with h1 h2
      . left
        rw [isPos]
        by_cases hbd : b * d > 0
        . use b * c - a * d, b * d
          constructor
          . sorry -- need a field tactic to get Z equality form h
          . constructor
            . exact hbd
            . repeat rw [coe_Int_eq]
              rw [div_eq, inv_eq, mul_eq]
              rw [sub_eq]
              rw [eq]
              . ring
              . exact Int.mul_ne_zero hd hb
              . simp only [one_mul, ne_eq, mul_eq_zero, not_or]
                omega
              repeat omega
        . have hbdneq : b * d ≠ 0 := by exact Int.mul_ne_zero hb hd
          simp only [gt_iff_lt, not_lt] at hbd
          rw [le_iff_lt_or_eq] at hbd
          simp [hbdneq] at hbd
          use (-b) * c + a * d, -b * d
          constructor
          . sorry
          . constructor
            . linarith
            . repeat rw [coe_Int_eq]
              rw [div_eq, inv_eq, mul_eq]
              rw [sub_eq]
              rw [eq]
              . ring
              . exact Int.mul_ne_zero hd hb
              . simp only [neg_mul, mul_neg, one_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
                omega
              . omega
              . omega
              . omega
              . simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero, not_or]
                omega
              repeat omega
      . right
        rw [eq]
        . sorry
        . exact hd
        . exact hb
    . intro h
      cases' h with h1 h2
      . rw [isPos] at h1
        obtain ⟨x, y, hx, hy, hxy⟩ := h1
        left
        rw [sub_eq] at hxy
        rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq, mul_eq] at hxy
        rw [eq] at hxy
        simp at hxy
        -- cases b * d > 0 and otherwise
        . sorry
        . exact Int.mul_ne_zero hd hb
        repeat omega
      . right
        rw [eq] at h2
        . sorry
        . exact hd
        . exact hb

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by
    intro p q
    obtain ⟨a, b, hb, rfl⟩ := eq_diff p
    obtain ⟨c, d, hd, rfl⟩ := eq_diff q
    simp [hb, hd]
    rw [add_eq _ _ hb hd]
    have : ¬b = 0 ∧ ¬d = 0 := by exact And.intro hb hd
    simp [this]
    -- field
    . sorry
  map_mul' := by
    intro p q
    obtain ⟨a, b, hb, rfl⟩ := eq_diff p
    obtain ⟨c, d, hd, rfl⟩ := eq_diff q
    simp [hb, hd]
    rw [mul_eq _ _ hb hd]
    have : ¬b = 0 ∧ ¬d = 0 := by exact And.intro hb hd
    simp [this]
    -- field
    sorry


/--
  Moved from earlier in original text.

  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equiv_rat : ℚ ≃+* Rat := Rat.equivRat_ring.symm

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
