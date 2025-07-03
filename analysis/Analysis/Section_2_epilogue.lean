import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers `Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers `ℕ`.

After this epilogue, `Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers `ℕ` throughout.  In particular, one should use the full Mathlib API for `ℕ` for
all subsequent chapters, in lieu of the `Chapter2.Nat` API.

Filling the sorries here requires both the Chapter2.Nat API and the Mathlib API for the standard
natural numbers `ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction `Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  . rw [Chapter2.Nat.succ_add]
    repeat rw [Chapter2.Nat.succ_toNat]
    rw [hn]
    rw [_root_.add_assoc, _root_.add_assoc, _root_.add_comm 1 _]

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction n with
  | zero => simp
  | succ n' ih =>
    rw [succ_mul]
    rw [succ_toNat]
    rw [right_distrib]
    rw [← ih]
    simp
    apply map_add

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
    intro n m
    constructor
    . intro h
      obtain ⟨k, hk⟩ := Nat.le.dest h
      use k
      apply_fun equivNat
      simp
      rw [← hk]
      rw [map_add]
      -- need to create a hypothesis to simplify before rw.
      have inv := equivNat.right_inv k
      simp at inv
      rw [inv]
    . rintro ⟨k, hk⟩
      apply_fun equivNat at hk
      simp at hk
      rw [hk]
      rw [map_add]
      rw [le_add_iff_nonneg_right]
      apply zero_le

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction m with
  | zero =>
    change n.toNat ^ 0 = n ^ 0
    simp [pow_zero]
  | succ m ih =>
    simp [pow_succ]
    rw [← ih]
    rw [pow_add]
    simp
    congr
    apply equivNat.left_inv

/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2.Nat : PeanoAxioms where
  Nat := _root_.Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with `unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  intro a b h
  induction a generalizing b with
  | zero =>
    induction b with
    | zero => rfl
    | succ b ih =>
      simp [natCast] at h
      symm at h
      exfalso
      exact P.succ_ne _ h
  | succ a ih =>
    induction b with
    | zero =>
      simp [natCast] at h
      exfalso
      exact P.succ_ne _ h
    | succ b ih2 =>
      repeat rw [natCast] at h
      apply P.succ_cancel at h
      have a_eq_b := ih h
      rw [a_eq_b]

/-- One can start the proof here with `unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  apply P.induction
  . use 0
  . intro n ih
    obtain ⟨m, hm⟩ := ih
    use Nat.succ m
    simp [natCast]
    rw [hm]

theorem natCast_bijective (P: PeanoAxioms) : Function.Bijective P.natCast :=
 ⟨natCast_injective P, natCast_surjective P⟩

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol `≃` is an alias for Mathlib's `Equiv` class; for instance `P.Nat ≃ Q.Nat` is
    an alias for `_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    apply_fun equiv.equiv
    simp
    rw [equiv.equiv_zero]
  equiv_succ n := by
    apply_fun equiv.equiv
    simp
    rw [equiv.equiv_succ]
    simp

/-- This exercise will require application of Mathlib's API for the `Equiv` class.
    Some of this API can be invoked automatically via the `simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by simp [equiv1.equiv_zero, equiv2.equiv_zero]
  equiv_succ n := by simp [equiv1.equiv_succ, equiv2.equiv_succ]

theorem zero_or_succ (P : PeanoAxioms) (x : P.Nat): x = P.zero ∨ ∃ n, x = P.succ n := by
  revert x
  apply P.induction
  . left
    rfl
  . intro n ih
    right
    use n

/-- Useful Mathlib tools for inverting bijections include `Function.surjInv` and `Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := Equiv.ofBijective P.natCast (natCast_bijective P)
  equiv_zero := by rfl;
  equiv_succ n := by rfl;

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by
  exact Equiv.trans (Equiv.symm (Equiv.fromNat P)) (Equiv.fromNat Q)


/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  revert n
  apply P.induction
  . rw [equiv_zero1, equiv_zero2]
  . intro n ih
    rw [equiv_succ1, equiv_succ2]
    apply congrArg
    exact ih

noncomputable abbrev Equiv.fromCh2Nat (P : PeanoAxioms) := Equiv.mk' Chapter2.Nat P

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  -- basic idea, we already proved this in chapter 2 for Chapter2.Nat
  -- so we just need to use the equivalence between Chapter2.Nat and P.Nat
  -- to transfer the result.
  apply existsUnique_of_exists_of_unique
  let e := Equiv.fromCh2Nat P
  let f_lift := fun a b ↦ e.equiv.symm (f (e.equiv a) (e.equiv b))
  let c_lift := e.equiv.symm c
  let r := Chapter2.Nat.recurse f_lift c_lift
  use fun n ↦ e.equiv (r (e.equiv.symm n))
  constructor
  . simp [r]
    -- some tricky things to note, there are inverse versions of
    -- equiv_zero and equiv_succ that need extra proofs.
    have hz : e.equiv.symm P.zero = _root_.Chapter2.Nat.zero := by
      apply_fun e.equiv
      simp
      -- equiv_zero needs an extra simp before it can be applied
      -- to fully expand Equiv.Nat to the underlying Chapter2.Nat
      have h2 := e.equiv_zero
      simp at h2
      exact h2.symm
    rw [hz]
    simp [Chapter2.Nat.recurse, c_lift]
  . intro a
    simp [r, Chapter2.Nat.recurse]
    have hz : ∀ n, e.equiv.symm (P.succ n) = Chapter2.Nat.succ (e.equiv.symm n) := by
      intro n
      apply_fun e.equiv
      simp
      have h2 := e.equiv_succ
      simp at h2
      have h3 := h2 (e.equiv.symm n)
      simp at h3
      exact h3.symm
    rw [hz]
    simp [Chapter2.Nat.recurse, f_lift]
  -- uniqueness easy enough to prove from scratch, instead of lifting
  intro a b h1 h2
  ext n
  revert n
  apply P.induction
  . rw [h1.1, h2.1]
  . intro n ih
    rw [h1.2 n, h2.2 n]
    apply congrArg
    exact ih
