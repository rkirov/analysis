import Mathlib.Tactic

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

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib.Nat : PeanoAxioms where
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

theorem zero_or_succ (P : PeanoAxioms) (x : P.Nat): x = P.zero ∨ ∃ n, x = P.succ n := by
  revert x
  apply P.induction
  . left
    rfl
  . intro n ih
    right
    use n

/--
The general idea is use Classical logic to and the `zero_or_succ` lemma to define a function
that can do non-computable match on x - it is either zero or a successor - and then recurse.

Using Claude I got to something that almost work using `Classical.indefiniteDescription
but it is:
1) feels too complicated? why can't I just use `match`?
2) still doesn't work because of non-terminating recursion.
--/
noncomputable def f (P: PeanoAxioms) (x : P.Nat) : ℕ :=
  Classical.indefiniteDescription (fun _ => True) ((zero_or_succ P x).elim
    (fun h_zero => ⟨0, trivial⟩)
    (fun h_succ => ⟨1 + f P (Classical.choose h_succ), trivial⟩))

/-- Note: I suspect that this construction is non-computable and requires classical logic. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib.Nat P where
  equiv := {
    toFun := natCast P
    invFun := f P
    left_inv := by sorry
    right_inv := by sorry
  }
  equiv_zero := by sorry
  equiv_succ n := by sorry
end repro
