import Mathlib.Tactic

/-!
# Analysis I, Section 3.1

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with
  their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a set

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set`, which is not compatible with the notion
  `Chapter3.Set` defined here, though we will try to make the notations match as much as
  possible.  This causes some notational conflict: for instance, one may need to explicitly
  specify `(∅:Chapter3.Set)` instead of just `∅` to indicate that one is using the `Chapter3.Set`
  version of the empty set, rather than the Mathlib version of the empty set, and similarly for
  other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `(X: Chapter3.Object)` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is
  mostly needed when manipulating sets of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create a full equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)
-/



namespace Chapter3

/- The ability to work in multiple universe is not relevant immediately, but
becomes relevant when constructing models of set theory in the Chapter 3 epilogue. -/
universe u v

/-- The axioms of Zermelo-Frankel theory with atoms  -/
class SetTheory where
  Set : Type u -- Axiom 3.1
  Object : Type v -- Axiom 3.1
  set_to_object : Set ↪ Object -- Axiom 3.1
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2
  emptyset: Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3
  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5
  specify A (P: Subtype (mem . A) → Prop) : Set -- Axiom 3.6
  specification_axiom A (P: Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6
  replace A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Axiom 3.7
  replacement_axiom A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Axiom 3.7
  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  power_set_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

export SetTheory (Set Object)

-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]

/-- Definition 3.1.1 (objects can be elements of sets) -/
instance objects_mem_sets : Membership Object Set where
  mem X x := SetTheory.mem x X

-- Now we can use the `∈` notation between our `Object` and `Set`.
example (X: Set) (x: Object) : Prop := x ∈ X

/-- Axiom 3.1 (Sets are objects)-/
instance sets_are_objects : Coe Set Object where
  coe X := SetTheory.set_to_object X

-- Now we can treat a `Set` as an `Object` when needed.
example (X Y: Set) : Prop := (X: Object) ∈ Y

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: (X: Object) = (Y: Object)) : X = Y :=
  SetTheory.set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : (X: Object) = (Y: Object) ↔  X = Y := by
  constructor
  . exact coe_eq
  intro h; subst h; rfl

/-- Axiom 3.2 (Equality of sets)-/
abbrev SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := SetTheory.extensionality _ _ h

/-- Axiom 3.2 (Equality of sets)-/
theorem SetTheory.Set.ext_iff (X Y: Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  . intro h; subst h; simp
  . intro h; apply ext; exact h

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := SetTheory.emptyset

-- Now we can use the `∅` notation to refer to `SetTheory.emptyset`.
example : ∅ = SetTheory.emptyset := by rfl

-- Make everything we define in `SetTheory.Set.*` accessible directly.
open SetTheory.Set

/--
  Axiom 3.3 (empty set).
  Note: in some applications one may have to explicitly cast ∅ to Set due to
  Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := SetTheory.emptyset_mem

/-- Empty set has no elements -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  constructor
  . intro h
    intro x
    rw [h]
    exact emptyset_mem x
  . intro h
    apply ext
    intro y
    constructor
    . intro hy
      exfalso
      have hy := (h y)
      contradiction
    . intro hy
      exfalso
      have nhy := SetTheory.emptyset_mem y
      contradiction

/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  apply existsUnique_of_exists_of_unique
  . use SetTheory.emptyset
    exact SetTheory.emptyset_mem
  . intro x y hx hy
    have hxz := eq_empty_iff_forall_notMem.mpr hx
    have hyz := eq_empty_iff_forall_notMem.mpr hy
    simp [hxz, hyz]

/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by
    simp [this, not_mem_empty]
  replace claim := ext claim
  contradiction

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := SetTheory.singleton

-- Now we can use the `{x}` notation for a single element `Set`.
example (x: Object) : Set := {x}

/--
  Axiom 3.3(a) (singleton).
  Note: in some applications one may have to explicitly cast {a} to Set due to Mathlib's
  existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := by
  exact SetTheory.singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := SetTheory.union_pair

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
example (X Y: Set) : Set := X ∪ Y

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  SetTheory.union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b c:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_quad (x a b c d:Object) : x ∈ ({a,b,c,d}:Set) ↔ (x = a ∨ x = b ∨ x = c ∨ x = d) := by
  simp [Insert.insert, Insert.insert, mem_union, mem_singleton]

/-- Remark 3.1.8 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  apply existsUnique_of_exists_of_unique
  . use {a}
    intro x
    exact mem_singleton x a
  . intro X Y hX hY
    apply ext
    intro x
    have hxa := hX x
    have hya := hY x
    rw [hxa, hya]

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  apply existsUnique_of_exists_of_unique
  . use {a,b}
    intro x
    exact mem_pair x a b
  . intro X Y hX hY
    apply ext
    intro x
    have hxa := hX x
    have hya := hY x
    rw [hxa, hya]

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by
  apply ext
  intro x
  constructor <;>
  . intro hx
    rw [mem_pair] at hx
    rw [mem_pair]
    exact hx.symm

/-- Remark 3.1.8 -/
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_pair] at hx
    rw [mem_singleton]
    cases hx with
    | inl h => exact h
    | inr h => exact h
  . intro hx
    rw [mem_pair]
    rw [mem_singleton] at hx
    left
    exact hx

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) :
    a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [ext_iff] at h
  simp [mem_pair] at h
  have h1 := h a
  have h2 := h b
  have h3 := h c
  have h4 := h d
  simp at h1 h2 h3 h4
  cases h1 with
  | inl h1a =>
    left
    constructor
    . exact h1a
    . by_cases bd : b = d
      . exact bd
      . simp [bd] at h2
        have ndb: ¬d = b := by contrapose! bd; exact bd.symm;
        simp [ndb] at h4
        simp [h2, h4]
        exact h1a.symm
  | inr h1b =>
    right
    constructor
    . exact h1b
    . by_cases bc : c = b
      . exact bc.symm
      . simp [bc] at h3
        have nca: ¬b = c := by contrapose! bc; exact bc.symm;
        simp [nca] at h2
        simp [h2, h3]
        exact h1b.symm

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty: Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty: Object), (singleton_empty: Object)}

/-- Exercise 3.1.2-/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  dsimp [empty, singleton_empty]
  rw [ext_iff]
  intro h
  have h1 := h empty
  simp at h1

/-- Exercise 3.1.2-/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  dsimp [empty, pair_empty]
  rw [ext_iff]
  intro h
  have h1 := h empty
  simp at h1

/-- Exercise 3.1.2-/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  dsimp [singleton_empty, pair_empty]
  rw [ext_iff]
  intro h
  have h1 := h singleton_empty
  simp at h1
  exact emptyset_neq_singleton h1.symm

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by
  apply ext
  intro x
  rw [h]

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by
  apply ext
  intro x
  rw [h]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) :
    ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  apply ext
  intro x
  simp

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by
  apply ext
  intro x
  rw [mem_union, mem_union]
  exact Or.comm

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- this proof is written to follow the structure of the original text.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . rw [mem_union] at case1
      rcases case1 with case1a | case1b
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . have : x ∈ A ∪ B := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    . rw [mem_union] at case2
      rcases case2 with case2a | case2b
      . rw [mem_union, mem_union]
        tauto
      have : x ∈ A ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto

/-- Proposition 3.1.27(c) -/
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  apply ext
  intro x
  rw [mem_union]
  tauto

/-- Proposition 3.1.27(a) -/
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  apply ext
  intro x
  rw [mem_union]
  have e := emptyset_mem x
  tauto

/-- Proposition 3.1.27(a) -/
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  apply ext
  intro x
  rw [mem_union]
  have e := emptyset_mem x
  tauto

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c} := by
  apply ext
  intro x
  simp only [mem_union, mem_pair, mem_triple]
  tauto

/-- Definition 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

-- Now we can use `⊆` for a subset relationship between two `Set`s.
example (X Y: Set) : Prop := X ⊆ Y

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

-- Now we can use `⊂` for a strict subset relationship between two `Set`s.
example (X Y: Set) : Prop := X ⊂ Y

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by
  rw [← hAA']
  exact hAB

/-- Examples 3.1.16 -/
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := by
  intro x
  tauto

/-- Examples 3.1.16 -/
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := by
  intro x
  have e := emptyset_mem x
  tauto

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- this proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  replace hx := hAB x hx
  replace hx := hBC x hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  apply ext
  intro x
  constructor
  . exact hAB x
  . exact hBA x

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  rw [ssubset_def] at hAB hBC
  rw [ssubset_def]
  constructor
  . exact subset_trans hAB.1 hBC.1
  . contrapose! hAB
    intro h
    rw [← hAB] at hBC
    exact subset_antisymm _ _ h hBC.1


/--
  This defines the subtype `A.toSubtype` for any `A:Set`.
  Note that `A.toSubtype` gives you a type, similar to how `Object` or `Set` are types.
  A value `x'` of type `A.toSubtype` combines some `x: Object` with a proof that `hx: x ∈ A`.

  To produce an element `x'` of this subtype, use `⟨ x, hx ⟩`, where `x: Object` and `hx: x ∈ A`.
  The object `x` associated to a subtype element `x'` is recovered as `x'.val`, and
  the property `hx` that `x` belongs to `A` is recovered as `x'.property`.
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

example (A: Set) (x: Object) (hx: x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A: Set) (x': A.toSubtype) : Object := x'.val
example (A: Set) (x': A.toSubtype) : x'.val ∈ A := x'.property

-- In practice, a subtype lets us carry an object with a membership proof as a single value.
-- Compare these two proofs. They are equivalent, but the latter packs `x` and `hx` into `x'`.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

-- Now instead of writing `x': A.toSubtype`, we can just write `x': A`.
-- Compare these three proofs. They are equivalent, but the last one reads most concisely.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property
example (A B: Set) (x': A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

/--
  Elements of a set (implicitly coerced to a subtype) are also elements of the set
  (with respect to the membership operation of the set theory).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj

/--
  If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A`
  (viewed as a subtype) corresponding to `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl


abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A.toSubtype) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

/-- Axiom 3.6 (axiom of specification) -/
theorem SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
  constructor
  . intro h
    have h' := specification_axiom h
    use h'
    rw [←specification_axiom' P ⟨ x, h' ⟩ ]
    simp [h]
  intro h
  obtain ⟨ h, hP ⟩ := h
  rw [←specification_axiom' P ⟨ x,h ⟩ ] at hP
  simp at hP; assumption

theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by
  intro x h
  exact specification_axiom h

/-- This exercise may require some understanding of how  subtypes are implemented in Lean. -/
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop}
  (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) :
    A.specify P = A'.specify P' := by
    apply ext
    intro x
    have h' := hPP' x
    repeat rw [specification_axiom'' ]
    constructor
    . intro h
      obtain ⟨ hx, hP ⟩ := h
      have hx' : x ∈ A' := by rw [hAA'] at hx; exact hx
      have f := (h' hx hx').mp hP
      use hx'
    . intro h
      obtain ⟨ hx', hP' ⟩ := h
      have hx : x ∈ A := by rw [← hAA'] at hx'; exact hx'
      have f := (h' hx hx').mpr hP'
      use hx


instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

-- Now we can use the `X ∩ Y` notation for an intersection of two `Set`s.
example (X Y: Set) : Set := X ∩ Y

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

-- Now we can use the `X \ Y` notation for a difference of two `Set`s.
example (X Y: Set) : Set := X \ Y

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by
  apply ext
  intro x
  repeat rw [mem_inter]
  tauto

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by
  apply ext
  intro x
  repeat rw [mem_union]
  tauto

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by
  apply ext
  intro x
  repeat rw [mem_union]
  tauto

/-- Proposition 3.1.27(c) -/
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  apply ext
  intro x
  repeat rw [mem_inter]
  tauto

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply ext
  intro x
  repeat rw [mem_inter]
  tauto

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply ext
  intro x
  repeat rw [mem_union]
  repeat rw [mem_inter]
  repeat rw [mem_union]
  tauto

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply ext
  intro x
  repeat rw [mem_union]
  repeat rw [mem_inter]
  repeat rw [mem_union]
  tauto

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by
  apply ext
  intro x
  repeat rw [mem_union]
  repeat rw [mem_sdiff]
  tauto


/-- Proposition 3.1.27(f) -/
-- appears that extra assumption hAX is not needed. True for any A X.
theorem SetTheory.Set.inter_compl {A X:Set} (hAX: A ⊆ X) : A ∩ (X \ A) = ∅ := by
  apply ext
  intro x
  repeat rw [mem_inter]
  repeat rw [mem_sdiff]
  have ne := emptyset_mem x
  tauto

/-- Proposition 3.1.27(g) -/
-- appears that extra assumption hAX hBX is not needed. True for any A B X.
theorem SetTheory.Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
    X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  apply ext
  intro x
  repeat rw [mem_inter]
  repeat rw [mem_sdiff]
  repeat rw [mem_union]
  tauto

/-- Proposition 3.1.27(g) -/
-- appears that extra assumption hAX hBX is not needed. True for any A B X.
theorem SetTheory.Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
    X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  apply ext
  intro x
  repeat rw [mem_sdiff]
  repeat rw [mem_union]
  repeat rw [mem_sdiff]
  repeat rw [mem_inter]
  tauto

/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by
    intro a b x ih
    rw [mem_union]
    left
    exact ih
  le_sup_right := by
    intro a b x ib
    rw [mem_union]
    right
    exact ib
  sup_le := by
    intro a b c
    intro h1 h2 x ih
    rw [mem_union] at ih
    cases ih with
    | inl y => exact h1 _ y
    | inr y => exact h2 _ y
  inf_le_left := by
    intro a b x ih
    rw [mem_inter] at ih
    exact ih.1
  inf_le_right := by
    intro a b x ih
    rw [mem_inter] at ih
    exact ih.2
  le_inf := by
    intro a b c ab ac
    intro x
    rw [mem_inter]
    intro xa
    constructor
    . exact ab _ xa
    . exact ac _ xa
  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]
    exact subset_self _

/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

-- Now we've defined `A ≤ B` to mean `A ⊆ B`, and set `⊥` to `∅`.
-- This makes the `Disjoint` definition from Mathlib work with our `Set`.
example (A B: Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅: Set) := by rfl
example (A B: Set) : Prop := Disjoint A B

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

-- Going forward, we'll use `Nat` as a type.
-- However, notice we've set `Nat` to `SetTheory.nat` which is a `Set` and not a type.
-- The only reason we can write `x: Nat` is because we've previously defined a `CoeSort`
-- coercion that lets us write `x: A` (when `A` is a `Set`) as a shortcut for `x: A.toSubtype`.
-- This is why, whenever you see `x: Nat`, you're really looking at `x: Nat.toSubtype`.
example (x: Nat) : Nat.toSubtype := x
example (x: Nat) : Object := x.val
example (x: Nat) : (x.val ∈ Nat) := x.property
example (o: Object) (ho: o ∈ Nat) : Nat := ⟨o, ho⟩

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.

instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n: ℕ) : Object := n
example (n: ℕ) : Set := {(n: Object)}

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5:Nat) ≠ (3:Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (5:Object) ≠ (3:Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n := by exact ofNat_inj' m n

example (n: ℕ) : (n: Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n


/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  simp only [subset_def, mem_pair, mem_triple]
  intro x hx
  tauto


/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) = ({5}:Set) := by
  apply ext
  intro x
  simp only [mem_singleton, specification_axiom'']
  constructor
  · rintro ⟨h1, h2⟩
    simp only [mem_pair] at h1
    tauto
  rintro ⟨rfl⟩
  norm_num

/-- Example 3.1.24 -/

example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by
  apply ext
  -- Instead of unfolding repetitive branches by hand like earlier,
  -- you can use the `aesop` tactic which does this automatically.
  aesop

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  aesop

example : ¬ Disjoint ({1, 2, 3}:Set) {2,3,4} := by
  rw [disjoint_iff]
  intro h
  change {1, 2, 3} ∩ {2, 3, 4} = ∅ at h
  rw [eq_empty_iff_forall_notMem] at h
  aesop

example : Disjoint (∅:Set) ∅ := by
  rw [SetTheory.Set.disjoint_iff]
  apply SetTheory.Set.ext
  intro x
  rw [SetTheory.Set.mem_inter]
  simp

/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by
  apply ext
  simp only [mem_sdiff, instInsert]
  aesop

/-- Example 3.1.30 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ))
 (by aesop)
   = {4,6,10} := by
  apply SetTheory.Set.ext
  intro x
  rw [SetTheory.Set.replacement_axiom _ x]
  simp
  constructor
  . intro h
    rcases h with h3 | h5 | h9
    . obtain ⟨n, h1, h2⟩ := h3
      left
      rw [h2]
      have hn_eq : n = 3 := by
        rw [← SetTheory.Object.natCast_inj]
        exact h1.symm
      rw [hn_eq]
      norm_num
    . obtain ⟨n, h1, h2⟩ := h5
      right
      left
      rw [h2]
      have hn_eq : n = 5 := by
        rw [← SetTheory.Object.natCast_inj]
        exact h1.symm
      rw [hn_eq]
      norm_num
    . obtain ⟨n, h1, h2⟩ := h9
      right
      right
      rw [h2]
      have hn_eq : n = 9 := by
        rw [← SetTheory.Object.natCast_inj]
        exact h1.symm
      rw [hn_eq]
      norm_num
  . intro h
    rcases h with h4 | h6 | h10
    . rw [h4]
      left
      use 3
      simp
    . rw [h6]
      right
      left
      use 5
      simp
    . rw [h10]
      right
      right
      use 9
      simp

/-- Example 3.1.31 -/

example : ({3,5,9}:Set).replace (P := fun _ y ↦ y=1) (by aesop) = {1} := by
  apply ext
  simp only [replacement_axiom]
  aesop

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
theorem SetTheory.Set.subset_tfae (A B:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
  tfae_have 1 → 2 := by exact subset_union
  tfae_have 2 → 1 := by
    intro h x
    rw [← h]
    rw [mem_union]
    tauto
  tfae_have 1 → 3 := by
    intro h
    apply ext
    intro x
    simp
    intro ha
    exact h x ha
  tfae_have 3 → 1 := by
    intro h
    rw [← h]
    intro x
    rw [mem_inter]
    simp
  tfae_finish

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A := by
  intro x
  rw [mem_inter]
  tauto

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B := by
  intro x
  rw [mem_inter]
  tauto

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  constructor
  . intro h
    constructor
    . intro c ac
      have h2 := h c ac
      rw [mem_inter] at h2
      tauto
    . intro c bc
      have h2 := h c bc
      apply inter_subset_right
      rw [mem_inter] at h2
      tauto
  . intro h
    obtain ⟨ h1, h2 ⟩ := h
    intro c hc
    rw [mem_inter]
    exact ⟨ h1 c hc, h2 c hc⟩

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B := by
  intro x
  rw [mem_union]
  tauto

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B := by
  intro x
  rw [mem_union]
  tauto

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  constructor
  . intro h
    constructor
    . exact subset_trans (subset_union_left _ _) h
    . exact subset_trans (subset_union_right _ _) h
  . intro ⟨ h1 , h2⟩
    intro x xab
    rw [mem_union] at xab
    cases xab with
    | inl h => exact h1 x h
    | inr h => exact h2 x h

/-- Exercise 3.1.8 -/
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by
  have h := (subset_tfae A (A ∪ B))
  have sub := (subset_union_left A B)
  apply (h.out 0 2).mp
  exact sub

/-- Exercise 3.1.8 -/
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by
  have h := (subset_tfae (A ∩ B) A)
  have h1 := (h.out 0 1).mp (inter_subset_left A B)
  rw [union_comm]
  exact h1

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    A = X \ B := by
  apply ext
  intro x
  constructor
  . intro xa
    rw [mem_sdiff]
    constructor
    . rw [← h_union]
      rw [mem_union]
      left
      exact xa
    . have hn := not_mem_empty
      contrapose! hn
      rw [← h_inter]
      use x
      rw [mem_inter]
      exact ⟨xa, hn⟩
  intro h
  rw [mem_sdiff] at h
  rw [← h_union] at h
  rw [mem_union] at h
  obtain ⟨hab, hn⟩ := h
  cases hab with
  | inl h => exact h
  | inr h => contradiction

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    B = X \ A := by
  have h_union': B ∪ A = X := by
    rw [← h_union]
    exact union_comm _ _
  have h_inter': B ∩ A = ∅ := by
    rw [← h_inter]
    exact inter_comm _ _
  exact partition_left h_union' h_inter'

theorem SetTheory.Set.inter_compl' {A X:Set} : A ∩ (X \ A) = ∅ := by
  apply ext
  intro x
  repeat rw [mem_inter]
  repeat rw [mem_sdiff]
  have ne := emptyset_mem x
  tauto

theorem SetTheory.Set.inter_empty {A: Set} : A ∩ ∅ = ∅ := by
  apply ext
  intro x
  rw [mem_inter]
  have e := emptyset_mem
  tauto

/--
  Exercise 3.1.10.
  You may find `Function.onFun_apply` and the `fin_cases` tactic useful.
-/
theorem SetTheory.Set.pairwise_disjoint (A B:Set) :
    Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by
    rw [pairwise_fin_succ_iff]
    constructor
    . intro i
      fin_cases i
      . simp [Function.onFun]
        rw [SetTheory.Set.disjoint_iff]
        rw [inter_assoc _ _ _]
        rw [inter_compl']
        exact inter_empty
      . simp [Function.onFun]
        rw [SetTheory.Set.disjoint_iff]
        apply ext
        intro x
        rw [mem_inter]
        repeat rw [mem_sdiff]
        have e := emptyset_mem
        tauto
    constructor
    . intro j
      fin_cases j
      . simp [Function.onFun]
        rw [SetTheory.Set.disjoint_iff]
        apply ext
        intro x
        repeat rw [mem_inter]
        repeat rw [mem_sdiff]
        have e := emptyset_mem
        tauto
      . simp [Function.onFun]
        rw [SetTheory.Set.disjoint_iff]
        apply ext
        intro x
        repeat rw [mem_inter]
        repeat rw [mem_sdiff]
        have e := emptyset_mem
        tauto
    . intro i j h
      fin_cases i
      . fin_cases j
        simp at h
        simp [Function.onFun]
        rw [SetTheory.Set.disjoint_iff]
        rw [inter_comm A B]
        rw [inter_assoc _ _ _]
        rw [inter_compl']
        apply ext
        intro x
        rw [mem_inter]
        have e := emptyset_mem
        tauto
      . fin_cases j
        . simp [Function.onFun]
          rw [SetTheory.Set.disjoint_iff]
          rw [← inter_assoc]
          rw [inter_comm _ A]
          rw [inter_compl']
          rw [inter_comm]
          exact inter_empty
        . simp [Function.onFun]
          contradiction

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_union] at h
    simp [mem_union, mem_inter, mem_sdiff]
    tauto
  . intro h
    simp [mem_union, mem_inter, mem_sdiff] at h
    simp [mem_union, mem_inter, mem_sdiff]
    tauto

/--
  Exercise 3.1.11.
  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`,
  `Set.specification_axiom'`, or anything built from them (like differences and intersections).
-/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} :
    ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by
    let B := replace A (P:= fun x y => x.val = y ∧ P x) (by
      intro x y y' h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨h1', _⟩ := h1
      obtain ⟨h2', _⟩ := h2
      rw [← h1', ← h2']
    )
    -- how to not have to copy/paste this?
    have h := replacement_axiom (P:= fun x y => x.val = y ∧ P x) (by
    intro x y y' h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', _⟩ := h1
    obtain ⟨h2', _⟩ := h2
    rw [← h1', ← h2']
    )
    simp at h
    use B
    constructor
    . intro x
      rw [h]
      intro h1
      obtain ⟨x1, h1'⟩ := h1
      exact x1
    . intro x
      rw [h]
      simp
      intro _
      exact x.property

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∪ B' ⊆ A ∪ B := by
  intro x
  intro h
  rw [mem_union] at *
  cases h with
  | inl ha => left; exact hA'A _ ha
  | inr hb => right; exact hB'B _ hb

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by
  intro x h
  rw [mem_inter] at *
  obtain ⟨ h1, h2 ⟩ := h
  exact ⟨ hA'A _ h1, hB'B _ h2 ⟩

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter :
    ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by
  -- interestingly use can only take a single arg
  use ({1, 2, 3} : Set)
  use ({2} : Set)
  use ({1, 2} : Set)
  use ({} : Set)
  constructor
  . intro x hx
    simp
    rw [mem_pair] at hx
    tauto
  . constructor
    . intro x
      have e := emptyset_mem x
      tauto
    . intro h
      have h2 : 2 ∈ ({1, 2}: Set) \ ∅ := by
        rw [mem_sdiff]
        rw [mem_pair]
        simp
      have h3 := h _ h2
      simp at h3

/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/
theorem SetTheory.Set.subset_diff_subset (A B A' B':Set): (A' ⊆ A) → (B' ⊆ B) → (A' \ B) ⊆ (A \ B') := by
  intro ha hb x h
  rw [mem_sdiff]
  rw [mem_sdiff] at h
  tauto

/-- Exercise 3.1.13 -/
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x} := by
  apply nonempty_def at hA
  obtain ⟨x, hx⟩ := hA
  constructor
  . intro h
    use x
    have h2 : A \ {x} = ∅ := by
      contrapose! h
      apply nonempty_def at h
      obtain ⟨y, hy⟩ := h
      simp at hy
      use {x}
      constructor
      . constructor
        . intro a
          rw [mem_singleton]
          intro h
          rw [h]
          exact hx
        . by_contra ha
          rw [← ha] at hy
          obtain ⟨hxy, nxy⟩ := hy
          rw [mem_singleton] at hxy
          contradiction
      . by_contra hsx
        have hxt : x ∈ ({x}:Set) := by rw [mem_singleton]
        rw [hsx] at hxt
        exact (emptyset_mem _) hxt
    have sub : ({x}:Set) ⊆ A := by intro a; rw [mem_singleton]; intro ax; rw [ax]; assumption;
    have c := union_compl sub
    rw [h2] at c
    rw [union_empty] at c
    exact c.symm
  . intro h
    obtain ⟨ x, hx ⟩ := h
    rw [hx]
    simp
    intro B hB
    rw [ssubset_def] at hB
    obtain ⟨hs, hne⟩ := hB
    have heither : ∀ S: Set, S ⊆ ({x}:Set) → S = ∅ ∨ S = {x} := by
      intro S hS
      by_cases he: S = ∅
      . left
        exact he
      . right
        apply ext
        intro y
        constructor
        . intro yS
          exact hS _ yS
        . intro h
          rw [mem_singleton] at h
          rw [h]
          by_contra!
          apply nonempty_def at he
          obtain ⟨z, hz ⟩ := he
          have hzx := hS _ hz
          rw [mem_singleton] at hzx
          rw [hzx] at hz
          contradiction
    . have h3 := heither B hs
      tauto

/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

-- Now we can convert our `Set` into a Mathlib `_root_.Set`.
-- Notice that Mathlib sets are parameterized by the element type, in our case `Object`.
example (X: Set) : _root_.Set Object := X

/--
  Injectivity of the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h; apply ext; intro x
    apply_fun (fun S ↦ x ∈ S) at h
    simp at h; assumption
  intro h; subst h; rfl

/-- Compatibility of the membership operation ∈ -/
theorem SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp [Coe.coe]

/-- Compatibility of the emptyset -/
theorem SetTheory.Set.coe_empty : ((∅:Set) : _root_.Set Object) = ∅ := by simp

/-- Compatibility of subset -/
theorem SetTheory.Set.coe_subset (X Y:Set) :
    (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by
  simp
  constructor
  . intro h x hx
    exact h x hx
  . intro h a ha
    exact h a ha

theorem SetTheory.Set.coe_ssubset (X Y:Set) :
    (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by
  rw [ssubset_def]
  rw [Set.ssubset_iff_subset_ne]
  simp
  -- same proof as above but can't apply the theorem
  intro h
  constructor
  . intro h x hx
    exact h x hx
  . intro h a ha
    exact h a ha

/-- Compatibility of singleton -/
theorem SetTheory.Set.coe_singleton (x: Object) : ({x} : _root_.Set Object) = {x} := by simp

/-- Compatibility of union -/
theorem SetTheory.Set.coe_union (X Y: Set) :
    (X ∪ Y : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by simp

/-- Compatibility of pair -/
theorem SetTheory.Set.coe_pair (x y: Object) : ({x, y} : _root_.Set Object) = {x, y} := by simp

/-- Compatibility of subtype -/
theorem SetTheory.Set.coe_subtype (X: Set) :  (X : _root_.Set Object) = X.toSubtype := by simp

/-- Compatibility of intersection -/
theorem SetTheory.Set.coe_intersection (X Y: Set) :
    (X ∩ Y : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by simp

/-- Compatibility of set difference-/
theorem SetTheory.Set.coe_diff (X Y: Set) :
    (X \ Y : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by simp

/-- Compatibility of disjointness -/
theorem SetTheory.Set.coe_Disjoint (X Y: Set) :
    Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by
  rw [disjoint_iff]
  rw [Set.disjoint_iff_inter_eq_empty]
  rw [← coe_inj']
  -- no idea why the state after simp is the one that is accepted by rfl.
  simp only [mem_inter, not_mem_empty, Set.setOf_false]
  rfl

end Chapter3
