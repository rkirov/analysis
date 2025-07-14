import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  sorry

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    rw [Function.Injective]
    intro a b h
    simp only [EmbeddingLike.apply_eq_iff_eq] at h
    rw [SetTheory.Set.ext_iff] at h
    simp only [SetTheory.Set.mem_pair] at h
    have h1 := h (SetTheory.set_to_object {a.fst})
    have h2 := h (SetTheory.set_to_object {a.fst, a.snd})
    simp only [EmbeddingLike.apply_eq_iff_eq, true_or, true_iff, or_true] at h1 h2
    have fst_eq : a.fst = b.fst := by
      cases h1 with
        | inl h =>
            rw [SetTheory.Set.ext_iff] at h
            have := h a.fst
            simp only [SetTheory.Set.mem_singleton, true_iff] at this
            exact this
        | inr h =>
          rw [SetTheory.Set.ext_iff] at h
          have := h a.fst
          simp at this
          cases this with
          | inl h' => exact h'
          | inr h' =>
            simp_all only [SetTheory.Set.mem_singleton, SetTheory.Set.mem_pair, iff_or_self,
              forall_eq]
    simp_all [fst_eq]
    have h3 := h (SetTheory.set_to_object {b.fst, a.snd})
    have h4 := h (SetTheory.set_to_object {b.fst, b.snd})
    simp only [EmbeddingLike.apply_eq_iff_eq, or_true, true_iff] at h3
    simp only [EmbeddingLike.apply_eq_iff_eq, or_true, iff_true] at h4
    have h5 : a.snd = b.fst ∨ a.snd = b.snd := by
      rcases h3 with h | h
      . rw [SetTheory.Set.ext_iff] at h
        simp only [SetTheory.Set.mem_pair, SetTheory.Set.mem_singleton, or_iff_left_iff_imp,
          forall_eq] at h
        left
        exact h
      . rw [SetTheory.Set.ext_iff] at h
        simp only [SetTheory.Set.mem_pair] at h
        have := h a.snd
        simp only [or_true, true_iff] at this
        exact this
    have h6 : b.snd = b.fst ∨ b.snd = a.snd := by
      rcases h4 with h | h
      . rw [SetTheory.Set.ext_iff] at h
        simp only [SetTheory.Set.mem_pair, SetTheory.Set.mem_singleton, or_iff_left_iff_imp,
          forall_eq] at h
        left
        exact h
      . rw [SetTheory.Set.ext_iff] at h
        simp only [SetTheory.Set.mem_pair] at h
        have := h b.snd
        simp only [or_true, true_iff] at this
        exact this
    have snd_eq : a.snd = b.snd := by
      rcases h5 with h | h
      . rcases h6 with h' | h'
        . rw [h, h']
        . exact h'.symm
      . exact h
    ext
    . exact fst_eq
    . exact snd_eq

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by grind))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

-- todo: find a shorter, more direct proof of this
theorem SetTheory.Set.fst_eval {X Y: Set} (x: X) (y: Y) :
    fst (⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [mem_cartesian]
    use x
    use y
  ⟩: X ×ˢ Y) = x := by
  generalize_proofs a
  rw [mem_cartesian] at a
  have := a.choose_spec
  obtain ⟨y', h⟩ := this
  apply OrderedPair.toObject.inj' at h
  simp only [OrderedPair.mk.injEq] at h
  have := h.1
  rw [coe_inj] at this
  simp only [fst]
  exact this.symm

-- todo: find a shorter, more direct proof of this
theorem SetTheory.Set.snd_eval {X Y:Set} (x: X) (y: Y) :
    snd (⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [SetTheory.Set.mem_cartesian]
    use x
    use y
  ⟩: X ×ˢ Y) = y := by
  generalize_proofs a
  rw [mem_cartesian] at a
  rw [exists_comm] at a -- key difference from fst
  have := a.choose_spec
  obtain ⟨y', h⟩ := this
  apply OrderedPair.toObject.inj' at h
  simp only [OrderedPair.mk.injEq] at h
  have := h.2
  rw [coe_inj] at this
  simp only [snd]
  exact this.symm

-- todo: find a shorter, more direct proof of this
theorem SetTheory.Set.fst_eval {X Y: Set} (x: X) (y: Y) :
    fst (⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [mem_cartesian]
    use x
    use y
  ⟩: X ×ˢ Y) = x := by
  generalize_proofs a
  rw [mem_cartesian] at a
  have := a.choose_spec
  obtain ⟨y', h⟩ := this
  apply OrderedPair.toObject.inj' at h
  simp only [OrderedPair.mk.injEq] at h
  have := h.1
  rw [coe_inj] at this
  simp only [fst]
  exact this.symm

-- todo: find a shorter, more direct proof of this
theorem SetTheory.Set.snd_eval {X Y:Set} (x: X) (y: Y) :
    snd (⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [SetTheory.Set.mem_cartesian]
    use x
    use y
  ⟩: X ×ˢ Y) = y := by
  generalize_proofs a
  rw [mem_cartesian] at a
  rw [exists_comm] at a -- key difference from fst
  have := a.choose_spec
  obtain ⟨y', h⟩ := this
  apply OrderedPair.toObject.inj' at h
  simp only [OrderedPair.mk.injEq] at h
  have := h.2
  rw [coe_inj] at this
  simp only [snd]
  exact this.symm

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

noncomputable abbrev SetTheory.Set.uncurry {X Y Z:Set} (f: X → Y → Z) : X ×ˢ Y → Z :=
  fun z ↦ f (fst z) (snd z)

theorem SetTheory.Set.curry_uncurry {X Y Z:Set} (f: X → Y → Z) : curry (uncurry f) = f := by
  unfold uncurry
  unfold curry
  simp only
  ext x y
  rw [fst_eval, snd_eval]

theorem SetTheory.Set.uncurry_curry {X Y Z:Set} (f: X ×ˢ Y → Z) : uncurry (curry f) = f := by
  unfold uncurry
  unfold curry
  ext z
  have := z.property
  rw [mem_cartesian] at this
  obtain ⟨ x, y, h ⟩ := this
  have hf: fst z = x := by convert fst_eval x y
  have hs: snd z = y := by convert snd_eval x y
  rw [hf, hs]
  congr!
  exact h.symm


noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun z ↦ ⟨(⟨ snd z, fst z ⟩ : OrderedPair), by
    rw [mem_cartesian]
    use snd z
    use fst z
  ⟩
  invFun := fun z ↦ ⟨(⟨ snd z, fst z ⟩ : OrderedPair), by
    rw [mem_cartesian]
    use snd z
    use fst z
  ⟩
  left_inv := by
    intro z
    have zp := z.property
    rw [mem_cartesian] at zp
    obtain ⟨ x, y, h ⟩ := zp
    simp only [h]
    rw [fst_eval, snd_eval]
    congr!
    rw [h]
    congr!
    -- not quite sure why this works
    convert fst_eval x y
    convert snd_eval x y
  right_inv := by
    intro z
    have zp := z.property
    rw [mem_cartesian] at zp
    obtain ⟨ x, y, h ⟩ := zp
    simp only [h]
    rw [fst_eval, snd_eval]
    congr!
    rw [h]
    congr!
    convert fst_eval x y
    convert snd_eval x y

noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun := fun z ↦
    let yz : Y ×ˢ Z := ⟨(⟨ snd (fst z), snd z ⟩:OrderedPair), by
      rw [mem_cartesian]
      use snd (fst z)
      use snd z⟩
    ⟨(⟨fst (fst z), yz⟩ : OrderedPair), by
      rw [mem_cartesian]
      use fst (fst z)
      use yz
    ⟩
  invFun := fun z ↦
    let xy : X ×ˢ Y := ⟨(⟨ fst z, fst (snd z) ⟩:OrderedPair), by
        rw [mem_cartesian]
        use fst z
        use fst (snd z)
      ⟩
    ⟨(⟨xy, snd (snd z)⟩: OrderedPair), by
    rw [mem_cartesian]
    use xy
    use snd (snd z)
  ⟩
  left_inv := by
    intro t
    have zp := t.property
    rw [mem_cartesian] at zp
    obtain ⟨ xy, z, h ⟩ := zp
    have xyp := xy.property
    rw [mem_cartesian] at xyp
    obtain ⟨ x, y, h' ⟩ := xyp
    generalize_proofs a b c d
    rw [h'] at h
    simp only [coe_inj]
    have hx : fst (fst t) = x := by sorry
    have hy : snd (fst t) = y := by sorry
    have hz : snd t = z := by sorry
    simp only [hx, hy, hz]
    ext
    rw [h]
    simp only
    congr!
    . rw [fst]
      generalize_proofs a b
      have h' := Classical.choose_spec b
      have h'' := Classical.choose_spec h'
      sorry
    . sorry
    . sorry
    sorry

  right_inv := by
    intro t
    have zp := t.property
    rw [mem_cartesian] at zp
    obtain ⟨ x, yz, h ⟩ := zp
    have yzp := yz.property
    rw [mem_cartesian] at yzp
    obtain ⟨ y, z, h' ⟩ := yzp
    -- goal state is too hard to read :(
    sorry

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv _ := by simp
  right_inv _ := by simp [←pair_eq_fst_snd]

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

theorem SetTheory.Set.object_of_inj {X Y:Set} (f g: X → Y): object_of f = object_of g ↔ f = g := by
  constructor
  . intro h
    rw [object_of] at h
    simp only [EmbeddingLike.apply_eq_iff_eq] at h
    exact h
  . intro h
    rw [h]

/-- Definition 3.5.7 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
  constructor
  . intro h
    rw [tuple, tuple] at h
    simp only [EmbeddingLike.apply_eq_iff_eq] at h
    ext i
    have h' := congr_fun h i
    simp only at h'
    rw [Subtype.mk.injEq] at h'
    exact h'
  . intro h
    rw [h]


lemma SetTheory.Set.iUnion_singleton (i:Object) (X:Set): X = ({i}:Set).iUnion fun _ ↦ X := by
  apply ext
  intro z
  rw [mem_iUnion]
  simp only [nonempty_subtype, mem_singleton, exists_eq, exists_const]

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun := fun x ↦
    have h := (mem_iProd _).mp x.property
    (Classical.choose h) ⟨i, by simp⟩
  invFun := fun x ↦
    ⟨ tuple (fun _ ↦ x), by
      rw [mem_iProd]
      use fun _:({i}:Set) ↦ x
    ⟩
  left_inv := by
    intro x
    simp only
    have h := (mem_iProd _).mp x.property
    have hp := Classical.choose_spec h
    apply Subtype.ext
    generalize_proofs a b
    symm
    rw [tuple] at hp
    simp only [hp]
    congr! with x1 x2
    have := x2.property
    rw [mem_singleton] at this
    exact this
  right_inv := by
    intro h
    simp only
    generalize_proofs a b
    have := Classical.choose_spec a
    simp only at this
    rw [tuple] at this
    have hI : (({i}:Set).iUnion fun x ↦ X) = X := by
      apply ext
      intro z
      constructor
      . intro h
        rw [mem_iUnion] at h
        obtain ⟨ _, hz ⟩ := h
        exact hz
      . intro h
        rw [mem_iUnion]
        use ⟨i, b⟩
    -- somehow use `hI` to change the inferred types in `object_of`
    change @object_of _ ({i}:Set) X _ = @object_of _ ({i}:Set) X _ at this


def emptyFun (X : Set) : (x : (∅:Set)) → X := fun x ↦
  have hf : False := by
    have := x.property
    have := SetTheory.Set.not_mem_empty x.val
    contradiction
  False.elim hf


/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := fun _ ↦ ()
  invFun := fun _ ↦
  let e: (i: (∅:Set)) → X i := fun i ↦
    have hf : False := by
      have := i.property
      have := SetTheory.Set.not_mem_empty i.val
      contradiction
    False.elim hf
  ⟨ tuple e, by
    rw [mem_iProd]
    use e
  ⟩
  left_inv := by
    intro x
    simp only
    ext
    have := x.property
    rw [mem_iProd] at this
    obtain ⟨ e, he ⟩ := this
    rw [he]
    congr! with x1
    exfalso
    have := x1.property
    have nempty := SetTheory.Set.not_mem_empty x1.val
    contradiction
  right_inv := by
    intro x
    simp only

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun i:I ↦ X) ≃ (I → X) where
  toFun := fun x ↦ fun i ↦
    have h := (mem_iProd _).mp x.property
    (Classical.choose h) i
  invFun := fun f ↦ ⟨ tuple (fun i ↦ f i), by
    rw [mem_iProd]
    use f
  ⟩
  left_inv := by
    intro x
    simp only
    have h := (mem_iProd _).mp x.property
    have hp' := Classical.choose_spec h
    congr!
    exact hp'.symm

  right_inv := by
    intro x
    simp only
    generalize_proofs a
    ext i
    have := Classical.choose_spec a
    simp [tuple] at this
    have h := congr_fun this i
    rw [Subtype.mk.injEq] at h
    exact h.symm

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := fun x ↦ ⟨
    have h := (mem_iProd _).mp x.property
    (⟨ (Classical.choose h) ⟨0, by simp⟩ , (Classical.choose h) ⟨1, by simp⟩⟩ : OrderedPair), by
    extract_lets hl
    rw [mem_cartesian]
    use (Classical.choose hl) ⟨0, by simp⟩
    use (Classical.choose hl) ⟨1, by simp⟩
  ⟩
  invFun := fun z ↦ ⟨ object_of ((fun i ↦
    -- failed to synthesize decidable
    if i = ⟨0, by simp⟩  then z.val.1 else z.val.2): (i:({0,1}:Set)) → X i), by
    sorry
  ⟩
  left_inv := sorry
  right_inv := sorry

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]

/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

theorem SetTheory.Set.Fin_mk_ext {n x y: ℕ} {h1: x < n} {h2: y < n}:
    Fin_mk n x h1 = Fin_mk n y h2 → x = y := by
  intro h
  repeat rw [Fin_mk] at h
  simp only [Subtype.mk.injEq, Object.natCast_inj] at h
  exact h

/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro a b h
    simp only [EmbeddingLike.apply_eq_iff_eq] at h
    rw [SetTheory.Set.ext_iff] at h
    have h1 := h a.fst
    have h2 := h b.fst
    simp only [SetTheory.Set.mem_pair, true_or, true_iff, iff_true] at h1 h2
    have hfst : a.fst = b.fst := by
      by_contra! hne
      simp [hne] at h1
      -- why no hne.symm?
      have : b.fst ≠ a.fst := by
        contrapose! hne
        simp [hne]
      simp [this] at h2
      have hi1 : SetTheory.set_to_object {b.fst, b.snd} ∈ ({a.fst, a.snd}:Set) := by
        rw [h1]
        simp only [SetTheory.Set.mem_pair, true_or]
      have hi2 : SetTheory.set_to_object {a.fst, a.snd} ∈ ({b.fst, b.snd}:Set) := by
        rw [h2]
        simp only [SetTheory.Set.mem_pair, true_or]
      exfalso
      have h_not_mem := SetTheory.Set.not_mem_mem ({a.fst, a.snd}:Set) ({b.fst, b.snd}:Set)
      tauto
    ext
    . exact hfst
    . have h3 := h (SetTheory.set_to_object {a.fst, a.snd})
      have h4 := h (SetTheory.set_to_object {b.fst, b.snd})
      simp [hfst] at h3 h4
      have h3ne : SetTheory.set_to_object {b.fst, a.snd} ≠ b.fst := by
        by_contra! hne
        have h_not_mem := SetTheory.Set.not_mem_self ({b.fst, a.snd}:Set)
        have : SetTheory.set_to_object {b.fst, a.snd} ∈ ({b.fst, a.snd}:Set) := by
          rw [hne]
          simp only [SetTheory.Set.mem_pair, true_or]
        contradiction
      simp [h3ne] at h3
      rw [SetTheory.Set.ext_iff] at h3
      have h3f := h3 a.snd
      simp at h3f
      have h4ne : SetTheory.set_to_object {b.fst, b.snd} ≠ b.fst := by
        by_contra! hne
        have h_not_mem := SetTheory.Set.not_mem_self ({b.fst, b.snd}:Set)
        have : SetTheory.set_to_object {b.fst, b.snd} ∈ ({b.fst, b.snd}:Set) := by
          rw [hne]
          simp only [SetTheory.Set.mem_pair, true_or]
        contradiction
      simp [h4ne] at h4
      rw [SetTheory.Set.ext_iff] at h4
      have h4f := h4 b.snd
      simp at h4f
      have hsnd : a.snd = b.snd := by
        by_contra! hne
        simp [hne] at h3f
        have hne' : b.snd ≠ a.snd := by
          contrapose! hne
          simp [hne]
        simp [hne'] at h4f
        rw [← h4f] at h3f
        contradiction
      exact hsnd

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n):
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  constructor
  . intro h
    intro i
    rw [h]
  . intro h
    cases t with | mk tX tx surj
    cases t' with | mk tX' tx' surj'
    simp only at h
    let S : Set := iUnion (Fin n) (fun i ↦ ({(tx i).val}:Set))
    have h1 : tX = S := by
      apply ext
      intro y
      constructor
      . intro h2
        unfold S
        rw [mem_iUnion]
        have hs := surj ⟨y, h2⟩
        obtain ⟨ i, hi ⟩ := hs
        use i
        rw [hi]
        rw [mem_singleton]
      . intro h2
        unfold S at h2
        rw [mem_iUnion] at h2
        obtain ⟨ i, hi ⟩ := h2
        rw [mem_singleton] at hi
        rw [hi]
        exact (tx i).property
    let S' : Set := iUnion (Fin n) (fun i ↦ ({(tx' i).val}:Set))
    have hS : S = S' := by
      apply ext
      intro y
      unfold S S'
      constructor
      . intro h2
        rw [mem_iUnion] at h2
        obtain ⟨ i, hi ⟩ := h2
        rw [mem_singleton] at hi
        specialize h i
        rw [h] at hi
        rw [hi]
        rw [mem_iUnion]
        use i
        rw [mem_singleton]
      . intro h2
        rw [mem_iUnion] at h2
        obtain ⟨ i, hi ⟩ := h2
        rw [mem_singleton] at hi
        specialize h i
        rw [← h] at hi
        rw [hi]
        rw [mem_iUnion]
        use i
        rw [mem_singleton]
    -- repeat for tX', there must be a way to do with wlog?
    have h1' : tX' = S' := by
      apply ext
      intro y
      constructor
      . intro h2
        unfold S'
        rw [mem_iUnion]
        have hs := surj' ⟨y, h2⟩
        obtain ⟨ i, hi ⟩ := hs
        use i
        rw [hi]
        rw [mem_singleton]
      . intro h2
        unfold S at h2
        rw [mem_iUnion] at h2
        obtain ⟨ i, hi ⟩ := h2
        rw [mem_singleton] at hi
        rw [hi]
        exact (tx' i).property
    have htX : tX = tX' := by
      rw [h1, hS, h1']
    subst htX
    have : tx = tx' := by
      funext i
      have := h i
      rw [Subtype.mk.injEq]
      exact this
    subst this
    rfl

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun := fun x ↦
    let h := (mem_iProd _).mp x.property
    let t := (Classical.choose h)
    have ht := Classical.choose_spec h
    ⟨{
      X := iUnion (Fin n) (fun i ↦ ({(t i).val}:Set)),
      x := fun i ↦ ⟨(t i).val, by
        rw [mem_iUnion]
        use i
        rw [mem_singleton]
      ⟩,
      surj := by
        intro x
        have h2 := x.property
        rw [mem_iUnion] at h2
        obtain ⟨ i, hi ⟩ := h2
        rw [mem_singleton] at hi
        use i
        simp only
        rw [Subtype.mk.injEq]
        exact hi.symm
    }, by
      intro i
      simp only
      exact (t i).property
    ⟩
  invFun := fun t ↦ ⟨
    tuple (X:=X) fun i ↦ ⟨t.val.x i, by exact t.property i⟩
  , by
    rw [mem_iProd]
    use fun i ↦ ⟨t.val.x i, by
      exact t.property i
    ⟩
  ⟩
  left_inv := by
    intro x
    simp only
    generalize_proofs a b c
    have := Classical.choose_spec a
    rw [Subtype.mk.injEq]
    -- why forward direction doesn't work but opposite does
    rw [← this]
  right_inv := by
    intro t
    simp only
    generalize_proofs a b c d e
    have := Classical.choose_spec b
    sorry

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by sorry

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by sorry

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by sorry

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by sorry

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by sorry

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by sorry

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by sorry

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by sorry

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by sorry

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by sorry

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by sorry

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by sorry

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by sorry

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by sorry

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := sorry

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by sorry

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' sorry sorry
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · sorry
        sorry
      sorry
    sorry
  sorry


end Chapter3
