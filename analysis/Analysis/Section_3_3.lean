import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.3

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A notion of function `Function X Y` between two sets `X`, `Y` in the set theory of Section 3.1
- Various relations with the Mathlib notion of a function `X → Y` between two types `X`, `Y`.
  (Note from Section 3.1 that every `Set` `X` can also be viewed as a subtype
  `{ x:Object // x ∈ X }` of `Object`.)
- Basic function properties and operations, such as composition, one-to-one and onto functions,
  and inverses.

In the rest of the book we will deprecate the Chapter 3 version of a function, and work with the
Mathlib notion of a function instead.  Even within this section, we will switch to the Mathlib
formalism for some of the examples involving number systems such as `ℤ` or `ℝ` that have not been
implemented in the Chapter 3 framework.
-/

namespace Chapter3

/-
We will work here with the version `nat` of the natural numbers internal to the Chapter 3 set
theory, though usually we will use coercions to then immediately translate to the Mathlib
natural numbers `ℕ`.
-/
export SetTheory (Set Object nat)

variable [SetTheory]

/--
  Definition 3.3.1. `Function X Y` is the structure of functions from `X` to `Y`.
  Analogous to the Mathlib type `X → Y`.
-/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

#check Function.mk

/--
  Converting a Chapter 3 function `f: Function X Y` to a Mathlib function `f: X → Y`.
  The Chapter 3 definition of a function was nonconstructive, so we have to use the
  axiom of choice here.
-/
noncomputable instance Function.inst_coefn (X Y: Set)  : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := fun f x ↦ Classical.choose (f.unique x)

noncomputable abbrev Function.to_fn {X Y: Set} (f: Function X Y) (x:X) : Y := f x

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Converting a Mathlib function to a Chapter 3 function -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by
    intro x
    apply ExistsUnique.intro (f x)
    . rfl
    intro y h
    assumption)


/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  constructor
  . intro h
    subst h
    exact (Classical.choose_spec (f.unique x)).1
  intro h
  apply (Classical.choose_spec (f.unique x)).2
  assumption

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]


/-- Example 3.3.2.   -/
abbrev P_3_3_2a : nat → nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_2a_existsUnique (x: nat) : ∃! y: nat, P_3_3_2a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):nat)
  . simp [P_3_3_2a]
  intro y h
  simp only [P_3_3_2a, Equiv.symm_apply_eq] at h
  assumption

abbrev SetTheory.Set.f_3_3_2a : Function nat nat := Function.mk P_3_3_2a P_3_3_2a_existsUnique

theorem SetTheory.Set.f_3_3_2a_eval (x y: nat) : y = f_3_3_2a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval _ _ _


theorem SetTheory.Set.f_3_3_2a_eval' (n: ℕ) : f_3_3_2a (n:nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_2a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_2a_eval'' : f_3_3_2a 4 = 5 :=  f_3_3_2a_eval' 4

theorem SetTheory.Set.f_3_3_2a_eval''' (n:ℕ) : f_3_3_2a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_2a_eval' _

abbrev SetTheory.Set.P_3_3_2b : nat → nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_2b_existsUnique : ¬ ∀ x, ∃! y: nat, P_3_3_2b x y := by
  by_contra h
  replace h := ExistsUnique.exists (h (0:nat))
  obtain ⟨ n, hn ⟩ := h
  have : ((0:nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_2b, this] at hn

abbrev SetTheory.Set.P_3_3_2c : (nat \ {(0:Object)}: Set) → nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_2c_existsUnique (x: (nat \ {(0:Object)}: Set)) :
    ∃! y: nat, P_3_3_2c x y := by
  -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
  -- sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x
  simp at hx
  obtain ⟨ hx1, hx2⟩ := hx
  set n := ((⟨ x, hx1 ⟩:nat):ℕ)
  have : x = (n:nat) := by simp [n]
  simp [P_3_3_2c, this, SetTheory.Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):nat)
  . simp [←hx2]
  intro y hy
  set m := (y:ℕ)
  simp [←hy, m]

abbrev SetTheory.Set.f_3_3_2c : Function (nat \ {(0:Object)}: Set) nat :=
  Function.mk P_3_3_2c P_3_3_2c_existsUnique

theorem SetTheory.Set.f_3_3_2c_eval (x: (nat \ {(0:Object)}: Set)) (y: nat) :
    y = f_3_3_2c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _

/-- Create a version of a non-zero `n` inside `nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [SetTheory.Object.ofnat_eq',h]
    rw [←SetTheory.Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_2c_eval' (n: ℕ) : f_3_3_2c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; rw [f_3_3_2c_eval]; simp

theorem SetTheory.Set.f_3_3_2c_eval'' : f_3_3_2c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_2c_eval' 3

theorem SetTheory.Set.f_3_3_2c_eval''' (n:ℕ) :
    f_3_3_2c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_2c_eval' (2*n+2)

/--
  Example 3.3.3 is a little tricky to replicate with the current formalism as the real numbers
  have not been constructed yet.  Instead, I offer some Mathlib counterparts.  Of course, filling
  in these sorries will require using some Mathlib API, for instance for the nonnegative real
  class `NNReal`, and how this class interacts with `ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra!
  obtain ⟨f, hf⟩ := this
  have h1 := hf 1 1
  have h2 := hf 1 (-1)
  simp at h1 h2
  linarith

example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra!
  obtain ⟨f, hf⟩ := this
  have h1 := hf 1 1
  have h2 := hf 1 (-1)
  simp at h1 h2
  linarith

example : ∃ f: NNReal → NNReal, ∀ x y, y = f x ↔ y^2 = x := by
  use NNReal.sqrt
  intro x y
  constructor
  . intro h
    rw [h]
    simp
  . intro h
    rw [← h]
    simp

/-- Example 3.3.4. The unused variable `_x` is underscored to avoid triggering a linter. -/
abbrev SetTheory.Set.P_3_3_4 : nat → nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_4_existsUnique (x: nat) : ∃! y: nat, P_3_3_4 x y := by
  apply ExistsUnique.intro 7
  all_goals simp [P_3_3_4]

abbrev SetTheory.Set.f_3_3_4 : Function nat nat := Function.mk P_3_3_4 P_3_3_4_existsUnique

theorem SetTheory.Set.f_3_3_4_eval (x: nat) : f_3_3_4 x = 7 := by
  symm; rw [Function.eval]

/-- Definition 3.3.7 (Equality of functions) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor
  . intro h; simp [h]
  intro h
  ext x y
  constructor
  . intro hf
    rwa [←Function.eval _ _ _, ←h x, Function.eval _ _ _]
  intro hg
  rwa [←Function.eval _ _ _, h x, Function.eval _ _ _]

/--
  Example 3.3.8 (simplified).  The second part of the example is tricky to replicate in this
  formalism, so a Mathlib substitute is offered instead.
-/
abbrev SetTheory.Set.f_3_3_8a : Function nat nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))

abbrev SetTheory.Set.f_3_3_8b : Function nat nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))

theorem SetTheory.Set.f_3_3_8_eq : f_3_3_8a = f_3_3_8b := by
  rw [Function.eq_iff]
  intro x
  rw [Function.eval_of, Function.eval_of]
  set n := (x:ℕ)
  simp; ring

example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  ext x
  simp

example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  intro h
  have h2 := congrFun h (-1)
  simp at h2
  linarith

/-- Example 3.3.9 -/
abbrev SetTheory.Set.f_3_3_9 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x,hx ⟩; simp at hx)

theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by
  ext x y
  obtain ⟨ x1, h ⟩ := x
  have c : x1 ∉ ∅ := not_mem_empty x1
  contradiction

/-- Definition 3.3.10 (Composition) -/
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` is already taken in Mathlib for the composition of Mathlib functions,
-- so we use `○` here instead to avoid ambiguity.
infix:90 "○" => Function.comp

theorem Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x) := Function.eval_of _ _

/--
  Compatibility with Mathlib's composition operation.
  You may find the `ext` and `simp` tactics to be useful.
-/
theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  -- why can't simply unwrapping comp work, but I have to pass an element first
  -- rw [Function.comp, comp]
  ext x
  rw [to_fn_eval]
  rw [Function.comp_apply, comp_eval]

/-- Example 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 : Function nat nat := Function.mk_fn (fun x ↦ (2*x:ℕ))

abbrev SetTheory.Set.g_3_3_11 : Function nat nat := Function.mk_fn (fun x ↦ (x+3:ℕ))

theorem SetTheory.Set.g_circ_f_3_3_11 :
    g_3_3_11 ○ f_3_3_11 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):nat)) := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of, Function.eval_of, Function.eval_of]
  simp

theorem SetTheory.Set.f_circ_g_3_3_11 :
    f_3_3_11 ○ g_3_3_11 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):nat)) := by
  rw [Function.eq_iff]
  intro x
  rw [Function.comp_eval, Function.eval_of, Function.eval_of, Function.eval_of]
  simp; ring

/-- Lemma 3.3.12 (Composition is associative) -/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f := by
  rw [Function.eq_iff]
  intro x
  simp_rw [Function.comp_eval]

abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  apply forall_congr'; intro x
  apply forall_congr'; intro x'
  tauto

/--
  Compatibility with Mathlib's `Function.Injective`.  You may wish to use the `unfold` tactic to
  understand Mathlib concepts such as `Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  unfold Function.Injective
  rw [one_to_one]
  simp [to_fn_eval]
  -- why can't I complete here with simp?
  constructor
  . intro h a ah b bh h'
    specialize h a ah b bh
    by_contra hn
    have h' := h hn
    contradiction
  . intro h a ah b bh h'
    specialize h a ah b bh
    contrapose! h'
    exact h h'

/--
  Example 3.3.15.  One half of the example requires the integers, and so is expressed using
  Mathlib functions instead of Chapter 3 functions.
-/
theorem SetTheory.Set.f_3_3_15_one_to_one :
    (Function.mk_fn (fun (n:nat) ↦ ((n^2:ℕ):nat))).one_to_one := by
  rw [Function.one_to_one]
  intro x y ne
  repeat rw [Function.eval_of]
  simp
  exact ne

example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  rw [Function.Injective] at h
  specialize h ((by simp): 1 ^2 = (-1) ^2)
  linarith

example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  rw [Function.Injective]
  intro x y ih
  simp at ih -- which theorem simpifies it?
  exact ih


/-- Remark 3.3.16 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h
  push_neg at h
  exact h

/-- Definition 3.3.17 (Onto functions) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y

/-- Compatibility with Mathlib's Function.Surjective-/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by
  rw [Function.Surjective]

/-- Example 3.3.18 (using Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  rw [Function.Surjective]
  push_neg
  use 2
  intro a
  by_contra h
  have h2 : |a| ≤ 2 := by
    by_contra hn
    push_neg at hn
    have two_abs : |(2:ℤ)| = 2 := by simp
    rw [← two_abs] at hn
    rw [← sq_lt_sq] at hn
    rw [h] at hn
    contradiction
  have h_le : a ≤ 2 := le_of_abs_le h2
  have h_ge : -2 ≤ a := neg_le_of_abs_le h2
  interval_cases a <;> norm_num at h

abbrev A_3_3_18 := { m:ℤ // ∃ n:ℤ, m = n^2 }

example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_18) := by
  rw [Function.Surjective]
  simp

/-- Definition 3.3.20 (Bijective functions) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto

/-- Compatibility with Mathlib's Function.Bijective-/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.Bijective]
  rw [← Function.onto_iff, ← Function.one_to_one_iff']

/-- Example 3.3.21 (using Mathlib) -/
abbrev f_3_3_21 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩

lemma ex1 : ¬ Function.Injective f_3_3_21 := by
  rw [Function.Injective]
  intro h
  have hn : f_3_3_21 0 = f_3_3_21 1 := by rfl;
  specialize h hn
  contradiction

example : ¬ Function.Bijective f_3_3_21 := by
  rw [Function.Bijective]
  push_neg
  intro i
  exfalso
  exact ex1 i

abbrev g_3_3_21 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩

theorem ex2 : ¬ Function.Surjective g_3_3_21 := by
  rw [Function.Surjective]
  push_neg
  use ⟨4 , by norm_num ⟩
  intro a
  match a with
  | 0 => rw [g_3_3_21]; simp
  | 1 => rw [g_3_3_21]; simp

example : ¬ Function.Bijective g_3_3_21 := by
  rw [Function.Bijective]
  push_neg
  intro _
  exact ex2

abbrev h_3_3_21 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩

example : Function.Bijective h_3_3_21 := by
  constructor
  . rw [Function.Injective]
    intro x y h
    match x, y with
    | 0, 0 => rw [h_3_3_21] at h;
    | 1, 1 => rw [h_3_3_21] at h;
    | 2, 2 => rw [h_3_3_21] at h;
    | 0, 1 => rw [h_3_3_21] at h; contradiction;
    | 0, 2 => rw [h_3_3_21] at h; contradiction;
    | 1, 0 => rw [h_3_3_21] at h; contradiction;
    | 1, 2 => rw [h_3_3_21] at h; contradiction;
    | 2, 0 => rw [h_3_3_21] at h; contradiction;
    | 2, 1 => rw [h_3_3_21] at h; contradiction;
  . rw [Function.Surjective]
    intro b
    fin_cases b
    . use 0;
    . use 1; rfl;
    . use 2; rfl;

/--
  Example 3.3.22 is formulated using Mathlib rather than the set theory framework here to avoid
  some tedious technical issues (cf. Exercise 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  constructor
  . intro x y h
    simp at h
    exact h
  . intro y
    obtain ⟨ y', hy'⟩ := y
    simp
    exact Nat.zero_lt_of_ne_zero hy'

example : ¬ Function.Bijective (fun n ↦ n+1) := by
  rw [Function.Bijective]
  push_neg
  intro h
  rw [Function.Surjective]
  push_neg
  use 0
  intro a
  symm
  exact Nat.zero_ne_add_one a

/-- Remark 3.3.24 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  use Nat
  use Nat
  use Function.mk_fn (fun n ↦ 0)
  constructor
  . intro x
    simp
  . rw [Function.bijective]
    push_neg
    intro _
    rw [Function.onto]
    intro h
    specialize h 1
    obtain ⟨ x, hx ⟩ := h
    -- why can't this be applied 3 lines above
    rw [eval_of] at hx
    simp at hx

/--
  We cannot use the notation `f⁻¹` for the inverse because in Mathlib's `Inv` class, the inverse
  of `f` must be exactly of the same type of `f`, and `Function Y X` is a different type from
  `Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intro y
    apply existsUnique_of_exists_of_unique
    . obtain ⟨ x, hx ⟩ := h.2 y
      use x
    intro x x' hx hx'
    simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1 _ _
    simp [hx]
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

/-- Compatibility with Mathlib's notion of inverse -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext x
  congr
  symm
  rw [inverse_eval]
  -- not needing injective hypothesis?
  obtain ⟨ _, hs ⟩ := (Function.bijective_iff f).mp h
  -- undo some unfortunate expansion
  rw [← to_fn_eval]
  have hli := Function.rightInverse_invFun hs
  rw [hli]

/-- Exercise 3.3.1 -/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by sorry

theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by sorry

theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by sorry

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by sorry

/-- Exercise 3.3.2 -/
theorem Function.comp_of_inj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.one_to_one)
  (hg: g.one_to_one) : (g ○ f).one_to_one := by sorry

theorem Function.comp_of_surj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.onto)
  (hg: g.onto) : (g ○ f).onto := by sorry

/--
  Exercise 3.3.3 - fill in the sorrys in the statements in  a reasonable fashion.
-/
example (X: Set) : (SetTheory.Set.f_3_3_9 X).one_to_one ↔ sorry := by sorry

example (X: Set) : (SetTheory.Set.f_3_3_9 X).onto ↔ sorry := by sorry

example (X: Set) : (SetTheory.Set.f_3_3_9 X).bijective ↔ sorry := by sorry

/--
  Exercise 3.3.4.  State and prove theorems or counterexamples in the case that `hg` or `hf` is
  omitted as a hypothesis.
-/
theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
  (heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by sorry

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
  (heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' := by sorry

/--
  Exercise 3.3.5.  State or prove theorems or counterexamples in the case that `f` is replaced
  with `g` or vice versa in the conclusion.
-/
theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hinj :
    (g ○ f).one_to_one) : f.one_to_one := by sorry

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hinj : (g ○ f).onto) : g.onto := by sorry

/-- Exercise 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by sorry

theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by sorry

theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by sorry

theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by sorry

theorem Function.comp_bijective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.bijective)
  (hg: g.bijective) : (g ○ f).bijective := by sorry

/-- Exercise 3.3.7 -/
theorem Function.inv_of_comp {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hf: f.bijective) (hg: g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by sorry

/-- Exercise 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by sorry

theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by sorry

theorem Function.comp_id {A B:Set} (f: Function A B) : f ○ Function.id A = f := by sorry

theorem Function.id_comp {A B:Set} (f: Function A B) : Function.id B ○ f = f := by sorry

theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by sorry

theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by sorry

theorem Function.glue {X Y Z:Set} (hXY: Disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry



end Chapter3
