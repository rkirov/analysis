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
  simp [equivNat]
  induction n with
  | zero => simp
  | succ n' ih =>
    rw [succ_mul]
    rw [succ_toNat]
    rw [right_distrib]
    rw [← ih]
    simp
    apply map_add'


/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  . intro h
    simp at h
    have h2 := Nat.le.dest h
    obtain ⟨k, hk⟩ := h2
    use k
    apply_fun equivNat.toFun
    simp
    rw [← hk]
    rw [map_add']
    -- odd dance, I can't do simply
    -- rw [equivNat.right_inv k]
    have h := equivNat.right_inv k
    simp at h -- why is this needed?
    rw [h]
  . intro h
    obtain ⟨k, hk⟩ := h
    apply_fun equivNat.toFun at hk
    rw [hk]
    simp
    rw [map_add']
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
    rw [toNat_eq]

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
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
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

noncomputable def f (P: PeanoAxioms) (x : P.Nat) : ℕ :=
  Classical.indefiniteDescription (fun _ => True) ((zero_or_succ P x).elim
    (fun h_zero => ⟨0, trivial⟩)
    (fun h_succ => ⟨1 + f P (Classical.choose h_succ), trivial⟩))

/-- Useful Mathlib tools for inverting bijections include `Function.surjInv` and `Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := f P
    left_inv := by sorry
    right_inv := by sorry
  }
  equiv_zero := by sorry
  equiv_succ n := by sorry

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


/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  -- basic idea, we already proved this in chapter 2 for Chapter2.Nat
  -- so we just need to use the equivalence between Chapter2.Nat and P.Nat
  -- to transfer the result.
  have e := Equiv.fromCh2Nat P
  have r := Chapter2.Nat.recurse_uniq (fun a => fun b => e.equiv.invFun (f (e.equiv a) (e.equiv b))) (e.equiv.invFun c)
  apply existsUnique_of_exists_of_unique
  have re := ExistsUnique.exists r
  obtain ⟨a, ha1, ha2⟩ := re
  use fun n => e.equiv.toFun (a (e.equiv.invFun n))
  constructor
  . have h1 : e.equiv.invFun zero = Chapter2.Nat.zero := by
      rw [← e.equiv_zero]
      -- rw [e.equiv.left_inv] -- feels like this should work ??
      sorry
    rw [h1]
    have h2 : 0 = Chapter2.Nat.zero := by rfl
    rw [h2] at ha1
    rw [ha1]
    rw [e.equiv.right_inv c]
  . intro n
    have h3 : e.equiv.invFun (P.succ n) = Chapter2.Nat.succ (e.equiv.invFun n) := by
      apply_fun e.equiv.toFun -- why does replacing with e.equiv make the next line fail?
      rw [e.equiv.right_inv]
      -- simp [Chapter2.Nat.succ]
      rw [Chapter2.Nat.succ_eq_add_one]
      rw [e.equiv_succ] -- why does this not work?
      sorry
    rw [h3, ha2 (e.equiv.invFun n)]
    simp
  . intro h1 h2 ih1 ih2
    let h1' := fun n ↦ e.equiv.invFun (h1 (e.equiv.toFun n))
    let h2' := fun n ↦ e.equiv.invFun (h2 (e.equiv.toFun n))
    have hi1' : h1' (0: _root_.Chapter2.Nat) = e.equiv.invFun c ∧
    ∀ (n : _root_.Chapter2.Nat),
      h1' (n++) = e.equiv.invFun (f (e.equiv n) (e.equiv (h1' n))) := by
      constructor
      . simp [h1']
        change h1 (e.equiv _root_.Chapter2.Nat.zero) = c
        -- rw [e.equiv_zero] -- why does this not work?
        sorry
      . intro n
        dsimp [h1']
        apply congrArg
        -- rw [e.equiv_succ] -- why does this not work?
        sorry
    have hi2' : h2' (0: _root_.Chapter2.Nat) = e.equiv.invFun c ∧
    ∀ (n : _root_.Chapter2.Nat),
      h2' (n++) = e.equiv.invFun (f (e.equiv n) (e.equiv (h2' n))) := by sorry
    have eq' := ExistsUnique.unique r hi1' hi2'
    ext n
    have eq'n : h1' (e.equiv.invFun n) = h2' (e.equiv.invFun n) := by rw [eq']
    unfold h1' h2' at eq'n
    apply_fun e.equiv.toFun at eq'n
    repeat rw [e.equiv.right_inv] at eq'n
    exact eq'n

end PeanoAxioms
