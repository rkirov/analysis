import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.4: The axiom of choice

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib's dependent product type `∀ α, X α`.
- The axiom of choice in various equivalent forms, as well as the countable axiom of choice.

As the Chapter 3 set theory has been deprecated for many chapters at this point, we will not insert the axiom of choice directly into that theory in this text; but this could be accomplished if desired
(e.g., by extending the `Chapter3.SetTheory` class to a `Chapter3.SetTheoryWithChoice` class), and
students are welcome to attempt this separately.  Instead, we will use Mathlib's native
{name}`Classical.choice` axiom.  Technically, this axiom has already been used quite frequently in the
text already, in large part because Mathlib uses {name}`Classical.choice` to derive many weaker statements,
such as the law of the excluded middle.  So the distinctions made in the original text regarding
whether a given statement or not uses the axiom of choice are somewhat blurred in this formalization.
It is theoretically possible to restore this distinction by removing the reliance on Mathlib and
working throughout with custom structures such as `Chapter3.SetTheory` and
`Chapter3.SetTheoryWithChoice`, but this would be extremely tedious and not attempted here.
-/

namespace Chapter8

/-- Definition 8.4.1 (Infinite Cartesian products).  We will avoid using this definition in favor
of the Mathlib form {lean}`∀ α, X α` which we will shortly show is equivalent to (or more precisely,
generalizes) this one.

{given -show}`α : I`
Because Lean does not allow unrestricted unions of types, we cheat slightly here by assuming all the
{lean}`X α` are sets in a common universe {name}`U`.  Note that the Mathlib definition does not have this
restriction. -/
abbrev CartesianProduct {I U: Type} (X : I → Set U) := { x : I → ⋃ α, X α // ∀ α, ↑(x α) ∈ X α }

/-- Equivalence with Mathlib's product -/
def CartesianProduct.equiv {I U: Type} (X : I → Set U) :
  CartesianProduct X ≃ ∀ α, X α := {
  toFun x α := ⟨ x.val α, by aesop ⟩
  invFun x := ⟨ fun α ↦ ⟨ x α, by simp; use α; aesop ⟩, by aesop ⟩
  left_inv x := by aesop
  right_inv x := by aesop
  }

/-- Example 8.4.2. -/
def Function.equiv {I X:Type} : (∀ _:I, X) ≃ (I → X) := {
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
}

def product_zero_equiv {X: Fin 0 → Type} : (∀ i:Fin 0, X i) ≃ PUnit := {
  toFun f := PUnit.unit
  invFun x i := nomatch i
  left_inv f := by aesop
  right_inv f := rfl
}

def product_one_equiv {X: Fin 1 → Type} : (∀ i:Fin 1, X i) ≃ X 0 := {
  toFun f := f 0
  invFun x i := by rwa [←Fin.fin_one_eq_zero i] at x
  left_inv f := by ext i; rw [Fin.fin_one_eq_zero i]; simp
  right_inv f := rfl
}

def product_two_equiv {X: Fin 2 → Type} : (∀ i:Fin 2, X i) ≃ (X 0 × X 1) := {
  toFun f := (f 0, f 1)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2
  left_inv f := by aesop
  right_inv f := rfl
}

def product_three_equiv {X: Fin 3 → Type} : (∀ i:Fin 3, X i) ≃ (X 0 × X 1 × X 2) := {
  toFun f := (f 0, f 1, f 2)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2.1
    | 2 => f.2.2
  left_inv f := by aesop
  right_inv f := rfl
}

/-- Axiom 8.1 (Choice) -/
theorem axiom_of_choice {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by use fun i ↦ (h i).some

theorem axiom_of_countable_choice {I: Type} {X: I → Type} [Countable I] (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := axiom_of_choice h

/-- Lemma 8.4.5 -/
theorem exist_tendsTo_sup {E: Set ℝ} (hnon: E.Nonempty) (hbound: BddAbove E) :
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  -- This proof is written to follow the structure of the original text.
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1:ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1:ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1:ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, le_csSup hbound hs.1 ⟩
  have ⟨ a ⟩ := axiom_of_countable_choice hX
  use fun n ↦ ↑(a n); constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ sSup E - 1/(n+1:ℝ)) (h := fun _:ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro n; have := (a n).property; simp_all [X]

/-- Remark 8.4.6.  This special case of Lemma 8.4.5 avoids (countable) choice. -/
theorem exist_tendsTo_sup_of_closed {E: Set ℝ} (hnon: E.Nonempty) (hbound: BddAbove E) (hclosed: IsClosed E) :
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1:ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1:ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1:ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, le_csSup hbound hs.1 ⟩
  set a : ℕ → ℝ := fun n ↦ sInf (X n)
  have ha (n:ℕ) : a n ∈ X n := by
    apply IsClosed.csInf_mem _ Set.Nonempty.of_subtype
    . rw [bddBelow_def]; use sSup E - 1 / (n+1:ℝ); aesop
    . rw [show X n = E ∩ .Icc (sSup E - 1 / (n+1:ℝ)) (sSup E) by ext; aesop]
      exact hclosed.inter isClosed_Icc
  use a; constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ sSup E - 1/(n+1:ℝ)) (h := fun _:ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro _; simp_all [X]

/-- Proposition 8.4.7 / Exercise 8.4.1 -/
theorem exists_function {X Y : Type} {P : X → Y → Prop} (h: ∀ x, ∃ y, P x y) :
  ∃ f : X → Y, ∀ x, P x (f x) := by
  let I := X
  let X' : I → Type := fun i ↦ { y : Y // P i y }
  have hX' : ∀ i, Nonempty (X' i) := by
    intro i
    have : ∃ y, P i y := h i
    choose y hy using this
    use y
  obtain ⟨f⟩ := axiom_of_choice hX'
  use fun x ↦ (f x).val
  intro x
  have := (f x).property
  simp only [X'] at this
  exact this

/-- Exercise 8.4.1.  The spirit of the question here is to establish this result directly
from {name}`exists_function`, avoiding previous results that relied more explicitly
on the axiom of choice. -/
theorem axiom_of_choice_from_exists_function {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by
  set Y := (i : I) × X i
  have h' : ∀ i, ∃ y : Y, y.1 = i := fun i ↦ ⟨⟨i, (h i).some⟩, rfl⟩
  obtain ⟨f, hf⟩ := exists_function h'
  exact ⟨fun i ↦ (hf i) ▸ (f i).2⟩

/-- Exercise 8.4.2 -/
theorem exists_set_singleton_intersect {I U:Type} {X: I → Set U} (h: Set.PairwiseDisjoint .univ X)
  (hnon: ∀ α, Nonempty (X α)) :
  ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  obtain ⟨f⟩ := axiom_of_choice (fun α ↦ hnon α)
  use { f i | i : I }
  intro α
  have hsing : {x | ∃ i, ↑(f i) = x} ∩ X α = {↑(f α)} := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, rfl⟩, hxα⟩
      have hfi := (f i).property
      by_contra hne
      have hneq : i ≠ α := fun heq ↦ hne (by subst heq; rfl)
      exact Set.disjoint_left.mp (h (Set.mem_univ i) (Set.mem_univ α) hneq) hfi hxα
    · rintro rfl; exact ⟨⟨α, rfl⟩, (f α).property⟩
  rw [hsing, Nat.card_eq_one_iff_exists]
  exact ⟨⟨↑(f α), Set.mem_singleton _⟩, fun ⟨y, hy⟩ ↦ by simp [Set.mem_singleton_iff.mp hy]⟩

/-- Exercise 8.4.2.  The spirit of the question here is to establish this result directly
from {name}`exists_set_singleton_intersect`, avoiding previous results that relied more explicitly
on the axiom of choice. -/
theorem axiom_of_choice_from_exists_set_singleton_intersect {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by
  let U := (i : I) × X i
  let X' : I → Set U := fun i ↦ {s | s.1 = i}
  have hdisj : Set.PairwiseDisjoint .univ X' := by
    intro i _ j _ hij
    exact Set.disjoint_left.mpr fun s (hi : s.1 = i) (hj : s.1 = j) ↦ by subst i j; contradiction
  have hne : ∀ i, Nonempty (X' i) := fun i ↦ ⟨⟨⟨i, (h i).some⟩, rfl⟩⟩
  obtain ⟨Y, hY⟩ := exists_set_singleton_intersect hdisj hne
  exact ⟨fun i ↦
    let y := Nat.card_eq_one_iff_exists.mp (hY i) |>.choose.val
    have : y ∈ Y ∩ X' i := (Nat.card_eq_one_iff_exists.mp (hY i)).choose.property
    have : y.1 = i := this.2
    this ▸ y.2⟩

/-- Exercise 8.4.3 -/
theorem Function.Injective.inv_surjective {A B:Type} {g: B → A} (hg: Function.Surjective g) :
  ∃ f : A → B, Function.Injective f ∧ Function.RightInverse f g := by
  -- the preimages of a given a
  let X : A → Set B := fun a ↦ { b | g b = a }
  have hX : ∀ a, Nonempty (X a) := fun a ↦ by
    have : ∃ b, g b = a := hg a
    choose b hb using this
    use b
    simp [X, hb]
  obtain ⟨f⟩ := axiom_of_choice hX
  use fun a ↦ (f a).val
  constructor
  · intro a b h
    simp only [] at h
    have ha : g (f a).val = a := (f a).property
    have hb : g (f b).val = b := (f b).property
    rw [h] at ha
    exact ha.symm.trans hb
  · exact fun a ↦ (f a).property

/-- Exercise 8.4.3.  The spirit of the question here is to establish this result directly
from {name}`Function.Injective.inv_surjective`, avoiding previous results that relied more explicitly
on the axiom of choice. -/
theorem axiom_of_choice_from_function_injective_inv_surjective {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by
  let A := I
  let B := (i : I) × X i
  let g : B → A := fun s ↦ s.1
  have hg : Function.Surjective g := fun i ↦ ⟨⟨i, (h i).some⟩, rfl⟩
  have ⟨f, hf_inj, hf_right_inv⟩ := Function.Injective.inv_surjective hg
  exact ⟨fun i ↦ (hf_right_inv i) ▸ (f i).2⟩

end Chapter8
