import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, `Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.2.1. (Addition of natural numbers).
    Compare with Mathlib's `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- This instance allows for the `+` notation to be used for natural number addition. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Compare with Mathlib's `Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Compare with Mathlib's `Nat.succ_add`. -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Compare with Mathlib's `Nat.one_add`. -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- The sum of two natural numbers is again a natural number.
#check (fun (n m:Nat) ↦ n + m)

/-- Lemma 2.2.2 (n + 0 = n). Compare with Mathlib's `Nat.add_zero`. -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- This proof is written to follow the structure of the original text.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Lemma 2.2.3 (n+(m++) = (n+m)++). Compare with Mathlib's `Nat.add_succ`. -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Why?). Compare with Mathlib's `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  revert n; apply induction
  . rfl
  . intro i ih
    rw [succ_add]
    rw [← ih]

/-- Proposition 2.2.4 (Addition is commutative). Compare with Mathlib's `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- this proof is written to follow the structure of the original text.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Proposition 2.2.5 (Addition is associative) / Exercise 2.2.1
    Compare with Mathlib's `Nat.add_assoc`. -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  revert c; apply induction
  . rw [add_zero, add_zero]
  . intro c habc
    rw [add_succ]
    rw [habc]
    rw [add_succ]
    rw [add_succ]


/-- Proposition 2.2.6 (Cancellation law).
    Compare with Mathlib's `Nat.add_left_cancel`. -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Not from textbook) Nat can be given the structure of a commutative additive monoid.
This permits tactics such as `abel` to apply to the Chapter 2 natural numbers. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- This illustration of the `abel` tactic is not from the
    textbook. -/
example (a b c d:Nat) : (a+b)+(c+0+d) = (b+c)+(d+a) := by abel

/-- Definition 2.2.7 (Positive natural numbers).-/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.IsPos ↔ n ≠ 0 := by rfl

/-- Proposition 2.2.8 (positive plus natural number is positive).
    Compare with Mathlib's `Nat.add_pos_left`. -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.IsPos) : (a + b).IsPos := by
  -- This proof is written to follow the structure of the original text.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Compare with Mathlib's `Nat.add_pos_right`.

This theorem is a consequence of the previous theorem and `add_comm`, and `grind` can automatically discover such proofs.
-/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.IsPos) : (b + a).IsPos := by
  grind [add_comm, add_pos_left]

/-- Corollary 2.2.9 (if sum vanishes, then summands vanish).
    Compare with Mathlib's `Nat.add_eq_zero`. -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  obtain ha | hb := h
  . rw [← isPos_iff] at ha
    observe : (a + b).IsPos
    contradiction
  rw [← isPos_iff] at hb
  observe : (a + b).IsPos
  contradiction

/-
The API in `Tools/ExistsUnique.Lean`, and the method `existsUnique_of_exists_of_unique` in
particular, may be useful for the next problem.  Also, the `obtain` tactic is
useful for extracting witnesses from existential statements; for instance, `obtain ⟨ x, hx ⟩ := h`
extracts a witness `x` and a proof `hx : P x` of the property from a hypothesis `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique

/-- Lemma 2.2.10 (unique predecessor) / Exercise 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.IsPos) : ∃! b, b++ = a := by
  apply existsUnique_of_exists_of_unique
  . revert a
    apply induction
    . intro h
      contradiction
    . intro a ih pos
      use a
  . intro b₁ b₂ h₁ h₂
    rw [← h₁] at h₂
    rw [succ.injEq] at h₂
    exact h₂.symm

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `≤` notation on the natural numbers. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Definition 2.2.11 (Ordering of the natural numbers).
    This defines the `<` notation on the natural numbers. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

/-- Compare with Mathlib's `le_iff_exists_add`. -/
lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Compare with Mathlib's `ge_iff_le`. -/
@[symm]
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Compare with Mathlib's `gt_iff_lt`. -/
@[symm]
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Compare with Mathlib's `Nat.le_of_lt`. -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Compare with Mathlib's `Nat.le_iff_lt_or_eq`. -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . use 3
    decide
  decide

/-- Compare with Mathlib's `Nat.lt_succ_self`. -/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  rw [succ_eq_add_one]
  constructor
  . use 1
  . by_contra h
    conv_lhs at h => rw [← add_zero n]
    apply Nat.add_cancel_left at h
    contradiction

/-- Proposition 2.2.12 (Basic properties of order for natural numbers) / Exercise 2.2.3

(a) (Order is reflexive). Compare with Mathlib's `Nat.le_refl`.-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  use 0
  rw [add_zero]

@[refl]
theorem Nat.le_refl (a:Nat) : a ≤ a := a.ge_refl

/-- The refl tag allows for the `rfl` tactic to work for inequalities. -/
example (a b:Nat): a+b ≥ a+b := by rfl

/-- (b) (Order is transitive).  The `obtain` tactic will be useful here.
    Compare with Mathlib's `Nat.le_trans`. -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hbc
  use d + e
  rw [hd, he]
  rw [add_assoc]
  rw [add_comm d _]

theorem Nat.le_trans {a b c:Nat} (hab: a ≤ b) (hbc: b ≤ c) : a ≤ c := Nat.ge_trans hbc hab

/-- (c) (Order is anti-symmetric). Compare with Mathlib's `Nat.le_antisymm`. -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  obtain ⟨d, hd⟩ := hab
  obtain ⟨e, he⟩ := hba
  rw [hd] at he
  rw [add_assoc] at he
  conv_lhs at he => rw [← add_zero b]
  apply Nat.add_cancel_left at he
  have edz := Nat.add_eq_zero _ _ he.symm
  obtain ⟨dz, ez⟩ := edz
  rw [dz] at hd
  rw [add_zero] at hd
  exact hd

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`. -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  . intro hab
    obtain ⟨d, hd⟩ := hab
    use d
    rw [hd]
    rw [add_assoc]
    rw [add_comm d _]
    rw [add_assoc]
  . intro habc
    obtain ⟨d, hd⟩ := habc
    use d
    apply Nat.add_cancel_left c
    rw [add_comm]
    rw [hd]
    rw [add_comm b c]
    rw [add_assoc]

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_right`.  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Addition preserves order).  Compare with Mathlib's `Nat.add_le_add_left`.  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Compare with Mathlib's `Nat.succ_le_iff`. -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  constructor
  . intro h
    obtain ⟨d, hd⟩ := h.1
    cases d with
    | zero =>
      have zz : zero = 0 := by rfl
      rw [zz] at hd
      rw [add_zero] at hd
      symm at hd
      have nab := h.2
      exfalso
      contradiction
    | succ d =>
      rw [hd]
      rw [succ_eq_add_one]
      rw [succ_eq_add_one]
      rw [← Nat.add_le_add_left]
      use d
      rw [add_comm]
  . intro h
    obtain ⟨d, hd⟩ := h
    constructor
    . use d + 1
      rw [hd]
      rw [succ_eq_add_one]
      rw [add_assoc]
      rw [add_comm d 1]
    . have h : a++ ≤ b
      use d
      by_contra he
      rw [he] at h
      obtain ⟨ e, he' ⟩ := h
      conv_lhs at he' => rw [← add_zero b]
      rw [succ_eq_add_one] at he'
      rw [add_assoc] at he'
      apply add_cancel_left at he'
      symm at he'
      apply Nat.add_eq_zero _ _ at he'
      cases he'
      contradiction


/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.IsPos ∧ b = a + d := by
  rw [Nat.lt_iff_succ_le]
  constructor
  . intro h
    obtain ⟨d, hd⟩ := h
    use d + 1
    constructor
    . rw [Nat.isPos_iff]
      by_contra he
      apply Nat.add_eq_zero _ _ at he
      cases he
      contradiction
    . rw [hd]
      rw [succ_eq_add_one]
      rw [add_assoc]
      rw [add_comm d 1]
  . intro h
    obtain ⟨d, hdpos, hd⟩ := h
    rw [hd]
    cases d with
    | zero =>
      contradiction
    | succ e =>
      use e
      rw [succ_eq_add_one]
      rw [succ_eq_add_one]
      rw [add_assoc]
      rw [add_comm e 1]

/-- If a < b then a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- if a > b then a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- If a > b and a < b then contradiction -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (le_of_lt h.1) (le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction

theorem Nat.not_lt_self {a: Nat} (h : a < a) : False := by
  apply not_lt_of_gt a a
  simp [h]

theorem Nat.lt_of_le_of_lt {a b c : Nat} (hab: a ≤ b) (hbc: b < c) : a < c := by
  rw [lt_iff_add_pos] at *
  choose d hd using hab
  choose e he1 he2 using hbc
  use d + e; split_ands
  . exact add_pos_right d he1
  . rw [he2, hd, add_assoc]

/-- This lemma was a `why?` statement from Proposition 2.2.13,
but is more broadly useful, so is extracted here. -/
theorem Nat.zero_le (a:Nat) : 0 ≤ a := by
  sorry

/-- Proposition 2.2.13 (Trichotomy of order for natural numbers) / Exercise 2.2.4
    Compare with Mathlib's `trichotomous`.  Parts of this theorem have been placed
    in the preceding Lean theorems. -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- This proof is written to follow the structure of the original text.
  revert a; apply induction
  . observe why : 0 ≤ b
    rw [le_iff_lt_or_eq] at why
    tauto
  intro a ih
  obtain case1 | case2 | case3 := ih
  . rw [lt_iff_succ_le] at case1
    rw [le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by
      rw [case2]
      exact succ_gt b
    tauto
  have why : a++ > b := by
    obtain ⟨ d, hd ⟩ := case3
    obtain ⟨ e, he ⟩ := d
    constructor
    . use e + 1
      rw [succ_eq_add_one]
      rw [he]
      rw [add_assoc]
    . by_contra h
      rw [h] at he
      rw [succ_eq_add_one] at he
      conv_lhs at he => rw [← add_zero a]
      rw [add_assoc] at he
      apply add_cancel_left at he
      have := Nat.add_eq_zero _ _ he.symm
      cases this
      contradiction
  tauto

/--
  (Not from textbook) Establish the decidability of this order computably.  The portion of the
  proof involving decidability has been provided; the remaining sorries involve claims about the
  natural numbers.  One could also have established this result by the `classical` tactic
  followed by `exact Classical.decRel _`, but this would make this definition (as well as some
  instances below) noncomputable.

  Compare with Mathlib's `Nat.decLe`.
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    use b
    rw [zero_add]
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        rw [h]
        by_contra h2
        rw [← lt_iff_succ_le] at h2
        obtain ⟨ d, hd ⟩ := h2
        contradiction
      | isFalse h2 =>
        apply isTrue
        have : a < b := ⟨ h , h2 ⟩
        rw [lt_iff_succ_le] at this
        exact this
    | isFalse h2 =>
      apply isFalse
      by_contra h
      rw [← lt_iff_succ_le] at h
      apply le_of_lt at h
      contradiction

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe

/-- (Not from textbook) Nat has the structure of a linear ordering. This allows for tactics
such as `order` and `calc` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_ge a b := by
    constructor
    . intro h; refine ⟨ le_of_lt h, ?_ ⟩
      by_contra h'
      exact not_lt_self (lt_of_le_of_lt h' h)
    rintro ⟨ h1, h2 ⟩
    rw [lt_iff, ←le_iff]; refine ⟨ h1, ?_ ⟩
    by_contra h
    subst h
    contradiction
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total a b := by
    obtain h | rfl | h := trichotomous a b
    . left; exact le_of_lt h
    . simp [ge_refl]
    . right; exact le_of_lt h
  toDecidableLE := decidableRel

/-- This illustration of the `order` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) (hbc: b ≤ c) (hcd: c ≤ d)
        (hda: d ≤ a) : a = c := by order

/-- An illustration of the `calc` tactic with `≤/<`. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hcd: c ≤ d)
        (hde: d ≤ e) : a + 0 < e := by
  calc
    a + 0 = a := by simp
        _ ≤ b := hab
        _ < c := hbc
        _ ≤ d := hcd
        _ ≤ e := hde

/-- (Not from textbook) Nat has the structure of an ordered monoid. This allows for tactics
such as `gcongr` to be applicable to the Chapter 2 natural numbers. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left a b hab c := (add_le_add_left a b c).mp hab

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d e:Nat) (hab: a ≤ b) (hbc: b < c) (hde: d < e) :
  a + d ≤ c + e := by
  gcongr
  order

theorem add_lt_false (a b : Nat) (h: a + b < a) : False := by
  obtain ⟨ d, hd ⟩ := h
  obtain ⟨ e, he ⟩ := d
  rw [add_assoc] at he
  conv_lhs at he => rw [← add_zero a]
  apply Nat.add_cancel_left at he
  have := Nat.add_eq_zero _ _ he.symm
  obtain ⟨ dz, ez ⟩ := this
  rw [dz] at hd
  rw [add_zero] at hd
  contradiction

theorem lt_zero_false (a: Nat) (h: a < 0) : False := by
  obtain ⟨ d, hd ⟩ := h
  obtain ⟨ e, he ⟩ := d
  symm at he
  apply Nat.add_eq_zero at he
  obtain ⟨ az, ez ⟩ := he
  contradiction

theorem le_lt_to_le (a b c: Nat) (h: a ≤ b) (h2: b < c) : a < c := by
  -- this proof is written to follow the structure of the original text.
  obtain ⟨ d, hd ⟩ := h
  obtain ⟨ e, he ⟩ := h2
  obtain ⟨ f, hf ⟩ := e
  constructor
  . use f + d
    rw [hf, hd]
    rw [add_assoc]
    rw [add_comm f d]
  . contrapose! he
    rw [hf, hd] at he
    rw [add_assoc] at he
    conv_lhs at he => rw [← add_zero a]
    apply Nat.add_cancel_left at he
    have := Nat.add_eq_zero _ _ he.symm
    obtain ⟨ dz, ez ⟩ := this
    rw [ez] at hf
    rw [add_zero] at hf
    symm at hf
    exact hf

theorem lt_le_to_le (a b c: Nat) (h: a < b) (h2: b ≤ c) : a < c := by
  -- this proof is written to follow the structure of the original text.
  obtain ⟨ d, hd ⟩ := h
  obtain ⟨ e, he ⟩ := h2
  obtain ⟨ f, hf ⟩ := d
  constructor
  . use f + e
    rw [he, hf]
    rw [add_assoc]
  . contrapose! hd
    rw [he, hf] at hd
    rw [add_assoc] at hd
    conv_lhs at hd => rw [← add_zero a]
    apply Nat.add_cancel_left at hd
    have := Nat.add_eq_zero _ _ hd.symm
    obtain ⟨ dz, ez ⟩ := this
    rw [dz] at hf
    rw [add_zero] at hf
    symm at hf
    exact hf


/-- Proposition 2.2.14 (Strong principle of induction) / Exercise 2.2.5
    Compare with Mathlib's `Nat.strong_induction_on`.
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
    -- can this be done with induction + generalize?
    have q : ∀ m, ∀ m', m₀ ≤ m' ∧ m' < m → P m' := by
      intro m
      induction m with
      | zero =>
        intro m' hm'
        obtain ⟨ h₀, h₁ ⟩ := hm'
        exfalso
        apply lt_zero_false at h₁
        contradiction
      | succ m ih =>
        intro m'' hm''
        obtain ⟨ h₀'', h₁'' ⟩ := hm''
        apply hind m'' h₀''
        intro m' hm'
        apply ih
        constructor
        . exact hm'.1
        apply lt_le_to_le m' m'' m
        . exact hm'.2
        . rw [lt_iff_succ_le] at h₁''
          rw [succ_eq_add_one] at h₁''
          rw [succ_eq_add_one] at h₁''
          rw [← add_le_add_right] at h₁''
          exact h₁''
    intro m hm
    apply q (m++)
    constructor
    . exact hm
    rw [lt_iff_succ_le]

/-- Exercise 2.2.6 (backwards induction)
    Compare with Mathlib's `Nat.decreasingInduction`. -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  induction n with
  | zero =>
    intro m hm
    obtain ⟨ h₀, h₁ ⟩ := hm
    have z: zero = 0 := by rfl
    rw [z] at h₁
    symm at h₁
    apply Nat.add_eq_zero at h₁
    obtain ⟨ mz, hz ⟩ := h₁
    rw [mz]
    exact hn
  | succ n ih =>
    intro m hm
    have hnn := hind _ hn
    by_cases hnp : m = (n++)
    . rw [hnp]
      exact hn
    . have hmm : m < n++ := ⟨ hm, hnp⟩
      rw [lt_iff_succ_le] at hmm
      rw [succ_eq_add_one] at hmm
      rw [succ_eq_add_one] at hmm
      rw [← add_le_add_right] at hmm
      apply ih
      . exact hnn
      . exact hmm

/-- Exercise 2.2.7 (induction from a starting point)
    Compare with Mathlib's `Nat.le_induction`. -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  intro hn
  intro m hm
  obtain ⟨ d, hd ⟩ := hm
  induction d generalizing m with
  | zero =>
    have z : zero = 0 := by rfl
    rw [z] at hd
    rw [add_zero] at hd
    rw [hd]
    exact hn
  | succ d ih =>
    cases m with
    | zero =>
      exfalso
      rw [succ_eq_add_one] at hd
      have z : zero = 0 := by rfl
      rw [z] at hd
      symm at hd
      apply add_eq_zero at hd
      obtain ⟨ mz, hz ⟩ := hd
      apply add_eq_zero at hz
      obtain ⟨ mz2, hz2 ⟩ := hz
      contradiction
    | succ m =>
      apply hind
      apply ih
      rw [succ_eq_add_one] at hd
      rw [succ_eq_add_one] at hd
      rw [← add_assoc] at hd
      rw [add_comm _ 1] at hd
      rw [add_comm _ 1] at hd
      apply add_cancel_left at hd
      exact hd

end Chapter2
