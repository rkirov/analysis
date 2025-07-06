import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Tools.ExistsUnique

/-!
# Analysis I, Section 3.3: Functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A notion of function `Function X Y` between two sets `X`, `Y` in the set theory of Section 3.1
- Various relations with the Mathlib notion of a function `X → Y` between two types `X`, `Y`.
  (Note from Section 3.1 that every `Set` `X` can also be viewed as a subtype
  `{x : Object // x ∈ X }` of `Object`.)
- Basic function properties and operations, such as composition, one-to-one and onto functions,
  and inverses.

In the rest of the book we will deprecate the Chapter 3 version of a function, and work with the
Mathlib notion of a function instead.  Even within this section, we will switch to the Mathlib
formalism for some of the examples involving number systems such as `ℤ` or `ℝ` that have not been
implemented in the Chapter 3 framework.

We will work here with the version `Nat` of the natural numbers internal to the Chapter 3 set
theory, though usually we will use coercions to then immediately translate to the Mathlib
natural numbers `ℕ`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter3

export SetTheory (Set Object)

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
noncomputable def Function.to_fn {X Y: Set} (f: Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose

noncomputable instance Function.inst_coefn (X Y: Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Converting a Mathlib function to a Chapter 3 `Function` -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp)

/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  convert ((f.unique x).choose_iff y).symm

theorem Function.fn_ext {X Y: Set} {f g: Function X Y} : (∀ x : X, f x = g x) ↔ f = g := by
  constructor
  . intro h
    ext x y
    specialize h x
    repeat rw [← eval]
    rw [h]
  . intro h
    rw [h]
    simp

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]

theorem Function.to_fn_eq {X Y: Set} (f g: Function X Y): f.to_fn = g.to_fn ↔ f = g := by
  constructor
  . intro h
    ext x y
    have : f.to_fn x = g.to_fn x := by rw [h]
    repeat rw [to_fn_eval] at this
    repeat rw [← eval]
    -- magic simps, why can't one immediately do rw [this]
    simp
    simp at this
    rw [this]
  . intro h
    rw [h]

theorem Function.mk_to_fn {X Y: Set} (f: X → Y) : (mk_fn f).to_fn = f := by
  ext x
  rw [to_fn_eval]
  rw [eval_of]

/-- Example 3.3.3.   -/
abbrev P_3_3_3a : Nat → Nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_3a_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_3a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):Nat)
  . simp [P_3_3_3a]
  intro y h
  simpa [P_3_3_3a, Equiv.symm_apply_eq] using h

abbrev SetTheory.Set.f_3_3_3a : Function Nat Nat := Function.mk P_3_3_3a P_3_3_3a_existsUnique

theorem SetTheory.Set.f_3_3_3a_eval (x y: Nat) : y = f_3_3_3a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval _ _ _


theorem SetTheory.Set.f_3_3_3a_eval' (n: ℕ) : f_3_3_3a (n:Nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_3a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5 :=  f_3_3_3a_eval' 4

theorem SetTheory.Set.f_3_3_3a_eval''' (n:ℕ) : f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_3a_eval' _

abbrev SetTheory.Set.P_3_3_3b : Nat → Nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y: Nat, P_3_3_3b x y := by
  by_contra h
  choose n hn _ using h (0:Nat)
  have : ((0:Nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_3b, this] at hn

abbrev SetTheory.Set.P_3_3_3c : (Nat \ {(0:Object)}: Set) → Nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_3c_existsUnique (x: (Nat \ {(0:Object)}: Set)) :
    ∃! y: Nat, P_3_3_3c x y := by
  -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
  -- sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x; simp at hx; obtain ⟨ hx1, hx2 ⟩ := hx
  set n := ((⟨ x, hx1 ⟩:Nat):ℕ)
  have : x = (n:Nat) := by simp [n]
  simp [P_3_3_3c, this, Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):Nat)
  . simp [←hx2]
  intro y hy; simp [←hy]

abbrev SetTheory.Set.f_3_3_3c : Function (Nat \ {(0:Object)}: Set) Nat :=
  Function.mk P_3_3_3c P_3_3_3c_existsUnique

theorem SetTheory.Set.f_3_3_3c_eval (x: (Nat \ {(0:Object)}: Set)) (y: Nat) :
    y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _

/-- Create a version of a non-zero `n` inside `Nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (Nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [Object.ofnat_eq',h]
    rw [←Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_3c_eval' (n: ℕ) : f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; simp [f_3_3_3c_eval]

theorem SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_3c_eval' 3

theorem SetTheory.Set.f_3_3_3c_eval''' (n:ℕ) :
    f_3_3_3c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_3c_eval' (2*n+2)

/--
  Example 3.3.4 is a little tricky to replicate with the current formalism as the real numbers
  have not been constructed yet.  Instead, I offer some Mathlib counterparts, using the
  Mathlib API for `NNReal` and `ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; set y := f (-1)
  have h1 := (hf _ y).mp (by rfl)
  have h2 := sq_nonneg y
  linarith

example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; specialize hf 4; set y := f 4
  have hy := (hf y).mp (by rfl)
  have h1 : 2 = y := (hf 2).mpr (by norm_num)
  have h2 : -2 = y := (hf (-2)).mpr (by norm_num)
  linarith

example : ∃ f: NNReal → NNReal, ∀ x y, y = f x ↔ y^2 = x := by
  use NNReal.sqrt; intro x y
  constructor <;> intro h
  · rw [h, NNReal.sq_sqrt]
  · rw [←h, NNReal.sqrt_sq]

/-- Example 3.3.5. The unused variable `_x` is underscored to avoid triggering a linter. -/
abbrev SetTheory.Set.P_3_3_5 : Nat → Nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_5_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_5 x y := by
  apply ExistsUnique.intro 7 <;> simp [P_3_3_5]

abbrev SetTheory.Set.f_3_3_5 : Function Nat Nat := Function.mk P_3_3_5 P_3_3_5_existsUnique

theorem SetTheory.Set.f_3_3_5_eval (x: Nat) : f_3_3_5 x = 7 := by
  symm; rw [Function.eval]

/-- Definition 3.3.8 (Equality of functions) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor <;> intro h
  . simp [h]
  ext x y; constructor <;> intros
  . rwa [←Function.eval, ←h x, Function.eval]
  rwa [←Function.eval, h x, Function.eval]

/--
  Example 3.3.10 (simplified).  The second part of the example is tricky to replicate in this
  formalism, so a Mathlib substitute is offered instead.
-/
abbrev SetTheory.Set.f_3_3_10a : Function Nat Nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))

abbrev SetTheory.Set.f_3_3_10b : Function Nat Nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))

theorem SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b := by
  simp_rw [Function.eq_iff, Function.eval_of]
  intros; simp; ring

example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  simp_rw [NNReal.abs_eq]

example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  intro h
  let a := (fun (x:ℝ) ↦ x) (-1)
  let b := (fun x:ℝ ↦ |(x:ℝ)|) (-1)
  have hab : a = b := by unfold a; rw [h]
  norm_num [a, b] at hab

/-- Example 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x,hx ⟩; simp at hx)

theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by
  ext x y
  obtain ⟨ x1, h ⟩ := x
  have c : x1 ∉ ∅ := not_mem_empty x1
  contradiction

/-- Definition 3.3.13 (Composition) -/
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
-/
theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  ext; simp only [Function.comp_eval, Function.comp_apply]

/-- Example 3.3.14 -/
abbrev SetTheory.Set.f_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (2*x:ℕ))

abbrev SetTheory.Set.g_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (x+3:ℕ))

theorem SetTheory.Set.g_circ_f_3_3_14 :
    g_3_3_14 ○ f_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):Nat)) := by
  simp [Function.eq_iff, Function.eval_of]

theorem SetTheory.Set.f_circ_g_3_3_14 :
    f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):Nat)) := by
  simp [Function.eq_iff, Function.eval_of]
  intros; ring

/-- Lemma 3.3.15 (Composition is associative) -/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f := by
  simp [Function.eq_iff]

abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  peel with x hx; tauto

/--
  Compatibility with Mathlib's `Function.Injective`.  You may wish to use the `unfold` tactic to
  understand Mathlib concepts such as `Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  rw [one_to_one_iff, Function.Injective]

/--
  Example 3.3.18.  One half of the example requires the integers, and so is expressed using
  Mathlib functions instead of Chapter 3 functions.
-/
theorem SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n:Nat) ↦ ((n^2:ℕ):Nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro _ _ h
  simpa [Function.eval, Function.eval_of] using h

example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  have h1 : (fun n ↦ n ^ 2) 1 = (1:ℤ) := by norm_num
  have h2 : (fun n ↦ n ^ 2) (-1) = (1:ℤ) := by norm_num
  nth_rewrite 2 [←h1] at h2
  specialize h h2
  contradiction

example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  intro _ _ _; rwa [← pow_left_inj₀ (by norm_num) (by norm_num) (show 2 ≠ 0 by norm_num)]

/-- Remark 3.3.19 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h; aesop

/-- Definition 3.3.20 (Onto functions) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y

/-- Compatibility with Mathlib's Function.Surjective-/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by rfl

/-- Example 3.3.21 (using Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  unfold Function.Surjective; push_neg
  use (-1); intro a
  linarith [sq_nonneg a]

abbrev A_3_3_21 := { m:ℤ // ∃ n:ℤ, m = n^2 }

example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_21) := by
  rintro ⟨b, ⟨a, ha⟩⟩; use a
  simp only [ha]

/-- Definition 3.3.23 (Bijective functions) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto

/-- Compatibility with Mathlib's Function.Bijective-/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.bijective, Function.Bijective, one_to_one_iff', onto_iff]

/-- Example 3.3.24 (using Mathlib) -/
abbrev f_3_3_24 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩

example : ¬ Function.Injective f_3_3_24 := by decide
example : ¬ Function.Bijective f_3_3_24 := by decide

abbrev g_3_3_24 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩

example : ¬ Function.Surjective g_3_3_24 := by decide
example : ¬ Function.Bijective g_3_3_24 := by decide

abbrev h_3_3_24 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩

example : Function.Bijective h_3_3_24 := by decide

/--
  Example 3.3.25 is formulated using Mathlib rather than the set theory framework here to avoid
  some tedious technical issues (cf. Exercise 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  constructor
  · intro _ _
    simp only [Subtype.mk.injEq]; omega
  intro ⟨x, hx⟩; use x-1
  simp only [Subtype.mk.injEq]; omega

example : ¬ Function.Bijective (fun n ↦ n+1) := by
  suffices h : ¬ Function.Surjective (fun n ↦ n+1) by unfold Function.Bijective; tauto
  unfold Function.Surjective; push_neg
  use 0; intros
  symm; apply Nat.zero_ne_add_one

-- set_option pp.proofs true
/-- Remark 3.3.27 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  use Nat, Nat
  set f := mk_fn fun x ↦ (0: Nat); use f
  constructor
  · intros
    apply existsUnique_of_exists_of_unique
    · use 0; rw [Function.eval]
    intros; rw [Function.eval] at *; aesop
  rw [Function.bijective]
  suffices h : ¬ f.one_to_one by tauto
  rw [Function.one_to_one_iff]
  push_neg; use 0, 1; simp [f]

/--
  We cannot use the notation `f⁻¹` for the inverse because in Mathlib's `Inv` class, the inverse
  of `f` must be exactly of the same type of `f`, and `Function Y X` is a different type from
  `Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intros
    apply existsUnique_of_exists_of_unique
    . aesop
    intro _ _ hx hx'; simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1
    simp [hx]
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

/-- Compatibility with Mathlib's notion of inverse -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext y; congr; symm
  rw [inverse_eval]
  apply Function.rightInverse_invFun (f.bijective_iff.mp h).2

/--
  Exercise 3.3.1.  Although a proof operating directly on functions would be shorter,
  the spirit of the exercise is to show these using the `Function.eq_iff` definition.
-/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by rfl

theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by
  constructor <;>
  . intro h
    symm
    exact h

theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by
  rw [hfg, hgh]

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by
  rw [hff', hgg']

/-- Exercise 3.3.2 -/
theorem Function.comp_of_inj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.one_to_one)
  (hg: g.one_to_one) : (g ○ f).one_to_one := by
  rw [one_to_one_iff]
  intro x y
  repeat rw [eval_of]
  intro h
  rw [one_to_one_iff] at hf
  rw [one_to_one_iff] at hg
  apply hf _ _
  apply hg _ _
  exact h

theorem Function.comp_of_surj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.onto)
  (hg: g.onto) : (g ○ f).onto := by
  rw [onto_iff]
  rw [onto_iff] at hg
  rw [onto_iff] at hf
  rw [Function.Surjective]
  rw [Function.Surjective] at hf
  rw [Function.Surjective] at hg
  intro b
  specialize hg b
  obtain ⟨ a, ha ⟩ := hg
  specialize hf a
  obtain ⟨ c, hc ⟩ := hf
  use c
  rw [comp_eq_comp]
  simp [hc, ha]


/--
  Exercise 3.3.3 - fill in the sorrys in the statements in a reasonable fashion.
-/
theorem empty_function_one_to_one_iff (X: Set) (f: Function ∅ X) : f.one_to_one ↔ True := by
  simp

theorem empty_function_onto_iff (X: Set) (f: Function ∅ X) : f.onto ↔ X = ∅ := by
  simp
  symm
  exact SetTheory.Set.eq_empty_iff_forall_notMem

theorem empty_function_bijective_iff (X: Set) (f: Function ∅ X) : f.bijective ↔ X = ∅:= by
  rw [Function.bijective]
  simp
  symm
  exact SetTheory.Set.eq_empty_iff_forall_notMem

/--
  Exercise 3.3.4.
-/
theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
  (heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by
  -- move problem to mathlib defs because it is easier to work there
  -- without worrying about messy expansions.
  -- not using mathlib theorems which will make this miss the point.
  apply_fun to_fn at heq
  repeat rw [comp_eq_comp] at heq
  rw [← to_fn_eq]
  rw [one_to_one_iff'] at hg
  -- work in mathlib's fn here. ext produces clearer result not showing P
  ext x
  rw [SetTheory.Set.coe_inj]
  apply hg
  -- why doesn't this work
  -- rw [← Function.comp_apply]
  change (g.to_fn ∘ f.to_fn) x = (g.to_fn ∘ f'.to_fn) x
  rw [heq]

example : ∃ X Y Z:Set, ∃ f f': Function X Y, ∃ g : Function Y Z, g ○ f = g ○ f' ∧ f ≠ f' := by
  use Nat
  use Nat
  use Nat
  use Function.mk_fn (fun n ↦ n)
  use Function.mk_fn (fun n ↦ 0)
  use Function.mk_fn (fun n ↦ 0)
  constructor
  . simp
  . simp
    intro h
    -- why can't congrFun h 1 1
    have h1 := congrFun h 1
    have h2 := congrFun h1 1
    simp at h2

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
  (heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' := by
  -- move problem to mathlib defs because it is easier to work there
  -- without worrying about messy expansions.
  -- not using mathlib theorems which will make miss the point.
  apply_fun to_fn at heq
  repeat rw [comp_eq_comp] at heq
  rw [onto_iff] at hf
  rw [← to_fn_eq]
  -- work in mathlib fn from here on
  ext x
  rw [SetTheory.Set.coe_inj]
  rw [Function.Surjective] at hf
  specialize hf x
  obtain ⟨ y, hy ⟩ := hf
  have h := congrFun heq y
  repeat rw [Function.comp_apply] at h
  repeat rw [hy] at h
  exact h

example : ∃ X Y Z:Set, ∃ f: Function X Y, ∃ g g': Function Y Z, g ○ f = g' ○ f ∧ g ≠ g' := by
  use Nat
  use Nat
  use Nat
  use Function.mk_fn (fun n ↦ 0)
  use Function.mk_fn (fun n ↦ 0)
  use Function.mk_fn (fun n ↦ n)
  constructor
  . ext x
    repeat rw [← Function.eval]
  . intro h
    simp at h
    have h1 := congrFun h 1
    have h2 := congrFun h1 1
    simp at h2


def Function.comp_cancel_left_without_hg : Decidable (∀ (X Y Z:Set) (f f': Function X Y) (g : Function Y Z) (heq : g ○ f = g ○ f'), f = f') := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Function.comp_cancel_right_without_hg : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g g': Function Y Z) (heq : g ○ f = g' ○ f), g = g') := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/--
  Exercise 3.3.5.
-/
theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hinj :
    (g ○ f).one_to_one) : f.one_to_one := by
  -- move problem to mathlib defs because it is easier to work there
  -- without worrying about messy expansions.
  -- not using mathlib theorems which will make miss the point.
  rw [one_to_one_iff'] at hinj
  rw [one_to_one_iff']
  rw [comp_eq_comp] at hinj
  -- work in mathlib fn from here on
  rw [Function.Injective]
  rw [Function.Injective] at hinj
  intro a b h
  apply_fun g.to_fn at h
  exact hinj h

example : ∃ X Y Z:Set, ∃ f : Function X Y, ∃ g : Function Y Z, (g ○ f).one_to_one ∧ ¬ g.one_to_one := by
  use {0}
  use Nat
  use {0}
  use Function.mk_fn (fun n ↦ 0)
  use Function.mk_fn (fun n ↦ ⟨0, (by simp)⟩)
  constructor
  . simp
  . simp
    use 0
    constructor
    . exact (SetTheory.nat_equiv 0).2
    . use 1
      constructor
      . exact (SetTheory.nat_equiv 1).2
      intro h
      have neO : (0:Object) ≠ 1 := by simp
      exact neO h

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hinj : (g ○ f).onto) : g.onto := by
  -- move problem to mathlib defs because it is easier to work there
  -- without worrying about messy expansions.
  -- not using mathlib theorems which will make miss the point.
  rw [onto_iff] at hinj
  rw [onto_iff]
  rw [comp_eq_comp] at hinj
  -- work in mathlib fn from here on
  rw [Function.Surjective]
  rw [Function.Surjective] at hinj
  intro b
  specialize hinj b
  obtain ⟨ a, ha ⟩ := hinj
  use (f.to_fn a)
  exact ha

example : ∃ X Y Z:Set, ∃ f : Function X Y, ∃ g : Function Y Z, (g ○ f).onto ∧ ¬ f.onto := by
  use Nat
  use Nat
  use {0}
  use Function.mk_fn (fun n ↦ 0)
  use Function.mk_fn (fun n ↦ ⟨0, (by simp)⟩)
  constructor
  . rw [Function.onto]
    intro y
    have : (y:Object) = (0:Object) := by
      exact (SetTheory.singleton_axiom _ _).mp y.property
    use 0
    rw [Function.eval_of]
    rw [Function.eval_of]
    symm
    ext -- why does this work?
    exact this
  . rw [Function.onto]
    intro h
    specialize h 1
    obtain ⟨ x, hx ⟩ := h
    rw [Function.eval_of] at hx
    have neO : (0:Nat) ≠ 1 := by simp
    contradiction

def Function.comp_injective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).one_to_one), g.one_to_one) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Function.comp_surjective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).onto), f.onto) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Function.comp_injective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).one_to_one), g.one_to_one) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

def Function.comp_surjective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hsurj :
    (g ○ f).onto), f.onto) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by
  symm
  rw [inverse_eval]

theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by
    rw [← inverse_eval]

theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by
  have h1 :((f.inverse h) ○ f).onto := by
    rw [Function.onto]
    intro y
    use y
    rw [comp_eval]
    rw [inverse_comp_self]
  have ho := comp_surjective h1
  have h2 :(f ○ (f.inverse h)).one_to_one := by
    rw [one_to_one_iff]
    intro x y h
    repeat rw [comp_eval] at h
    repeat rw [self_comp_inverse] at h
    rw [h]
  have hi := comp_injective h2
  exact ⟨hi, ho⟩

theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by
  ext x
  repeat rw [← eval]
  rw [inverse_eval]
  constructor
  . intro h
    rw [← h]
    symm
    rw [← inverse_eval]
  . intro h
    rw [h]
    symm
    rw [inverse_eval]

/-- Exercise 3.3.7 -/
theorem Function.comp_bijective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.bijective)
  (hg: g.bijective) : (g ○ f).bijective := by
  constructor
  . exact comp_of_inj hf.1 hg.1
  . exact comp_of_surj hf.2 hg.2

theorem Function.inv_of_comp {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hf: f.bijective) (hg: g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by
  ext x
  repeat rw [← eval]
  symm
  rw [inverse_eval]
  repeat rw [comp_eval]
  repeat rw [inverse_eval]

/-- Exercise 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

theorem Function.inclusion_eval (X Y: Set) (x: X) (h: X ⊆ Y) : ((inclusion h) x).val = x.val := by rw [eval_of]

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.id_eval (X: Set) (x: X) : (id X) x = x := by rw [eval_of]

theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by
  ext x
  rw [← eval]

set_option pp.proofs true

theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by
  rw [← to_fn_eq]
  rw [comp_eq_comp]
  repeat rw [inclusion]
  repeat rw [mk_to_fn]
  ext
  simp only [Function.comp_apply]

theorem Function.comp_id {A B:Set} (f: Function A B) : f ○ Function.id A = f := by
  ext x
  repeat rw [← eval]
  repeat rw [id_eval]

theorem Function.id_comp {A B:Set} (f: Function A B) : Function.id B ○ f = f := by
  ext x
  repeat rw [← eval]
  rw [comp_eval]
  repeat rw [id_eval]

theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by
  ext x
  repeat rw [← eval]
  rw [comp_eval]
  rw [id_eval]
  rw [self_comp_inverse]

theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by
  ext x
  repeat rw [← eval]
  rw [comp_eval]
  rw [id_eval]
  rw [inverse_comp_self]

open Classical in
theorem Function.glue {X Y Z:Set} (hXY: Disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by
  apply existsUnique_of_exists_of_unique
  .
    set F : Function (X ∪ Y) Z := Function.mk_fn (fun z ↦
      if h : (z.val ∈ X) then f ⟨z.val, h⟩
      else g ⟨z.val, (by
        have h2 := z.property
        rw [SetTheory.Set.mem_union] at h2;
        tauto
      )⟩) with hF

    use F
    constructor
    . ext x
      repeat rw [← eval]
      have hsub := (SetTheory.Set.subset_union_left X Y)
      have hunion : x.val ∈ (X ∪ Y) := hsub x x.property
      have F_at_x : F ⟨x.val, hunion⟩ = f x := by
        rw [hF, Function.eval_of, dif_pos x.property]
      rw [comp_eval]
      have inc_eval : (fun x ↦ choose ((inclusion (SetTheory.Set.subset_union_left X Y)).unique x)) x =
         ⟨x, ((SetTheory.Set.subset_union_left X Y) x) x.property⟩  := by
        rw [eval_of]
      rw [inc_eval, F_at_x]
    . ext x
      repeat rw [← eval]
      have hsub := (SetTheory.Set.subset_union_right X Y)
      have hunion : x.val ∈ (X ∪ Y) := hsub x x.property
      have F_at_x : F ⟨x.val, hunion⟩ = g x := by
        have hneqx : (x:Object) ∉ X := by
          rw [SetTheory.Set.disjoint_iff] at hXY
          by_contra hx
          have hy := x.property
          have hxintery := (SetTheory.Set.mem_inter x _ _).mpr ⟨ hx, hy ⟩
          rw [hXY] at hxintery
          have ne := SetTheory.Set.not_mem_empty x
          contradiction
        rw [hF, Function.eval_of, dif_neg hneqx]
      rw [comp_eval]
      have inc_eval : (fun x ↦ choose ((inclusion (SetTheory.Set.subset_union_right X Y)).unique x)) x =
         ⟨x, ((SetTheory.Set.subset_union_right X Y) x) x.property⟩  := by
        rw [eval_of]
      rw [inc_eval, F_at_x]
  . intro F G hF hG
    ext x
    have hx : x.val ∈ (X ∪ Y) := x.property
    rw [SetTheory.Set.mem_union] at hx
    cases' hx with hX hY
    . have he : ∃ x': X, (inclusion (SetTheory.Set.subset_union_left X Y)) x' = x := by
        use ⟨x.val, hX⟩
        rw [inclusion]
        rw [eval_of]
      obtain ⟨ x' , hx' ⟩ := he
      rw [← hx']
      repeat rw [← eval]
      repeat rw [← comp_eval]
      rw [hF.1, hG.1]
    . have he : ∃ x': Y, (inclusion (SetTheory.Set.subset_union_right X Y)) x' = x := by
        use ⟨x.val, hY⟩
        rw [inclusion]
        rw [eval_of]
      obtain ⟨ x' , hx' ⟩ := he
      rw [← hx']
      repeat rw [← eval]
      repeat rw [← comp_eval]
      rw [hF.2, hG.2]

end Chapter3
