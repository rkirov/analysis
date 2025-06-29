import Mathlib.Tactic

namespace Chapter2

/--
  Assumption 2.6 (Existence of natural numbers).  Here we use an explicit construction of the
  natural numbers (using an inductive type).  For a more axiomatic approach, see the epilogue to
  this chapter.
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- this allows `decide` to work on `Nat`

/-- Axiom 2.1 (0 is a natural number) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩
#check (0:Nat)

/-- Axiom 2.2 (Successor of a natural number is a natural number) -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)

/--
  Recursion. Analogous to the inbuilt Mathlib method `Nat.rec` associated to
  the Mathlib natural numbers
-/
abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (recurse f c n)

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := sorry

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's `Nat.rec_add_one`. -/
theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) :
    recurse f c (n++) = f n (recurse f c n) := by rfl

end Chapter2

namespace repro
/-- The Peano axioms for an abstract type `Nat` -/
@[ext]
class PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

/-- The notion of an equivalence between two structures obeying the Peano axioms -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2NatP : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := sorry
  succ_cancel := sorry
  induction := sorry

noncomputable abbrev Equiv.fromCh2Nat (P : PeanoAxioms) : Equiv Chapter2NatP P := sorry



/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
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
  -- have h1 := Chapter2.Nat.eq_recurse f_lift c_lift r
  constructor
  . simp [r]
    have hz : e.equiv.symm P.zero = Chapter2NatP.zero := by
      apply_fun e.equiv
      simp
      rw [e.equiv_zero]
    rw [hz]
    simp [Chapter2NatP, c_lift]
  . intro a
    simp [r, Chapter2NatP, Chapter2.Nat.recurse, ← Chapter2.Nat.recurse_succ]

  -- uniqueness easy enough to prove from scratch, insteadf of lifting
  intro a b h1 h2
  ext n
  revert n
  apply P.induction
  . rw [h1.1, h2.1]
  . intro n ih
    rw [h1.2 n, h2.2 n]
    apply congrArg
    exact ih


end repro
