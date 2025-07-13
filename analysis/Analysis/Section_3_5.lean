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

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Exercise 3.5.1 -/
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
  coe := OrderedPair.toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by
    intro y z z' ⟨ hz, hz'⟩
    simp_all
  )

theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.2 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by
    intro x z z' ⟨ hz, hz' ⟩
    simp_all
  ))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]
  constructor
  . intro h
    obtain ⟨ S, hz, hS ⟩ := h
    rw [replacement_axiom] at hS
    obtain ⟨ x, hx ⟩ := hS
    simp at hx
    rw [hx, mem_slice] at hz
    obtain ⟨ y, rfl ⟩ := hz
    use x, y
  intro h
  obtain ⟨ x, y, rfl ⟩ := h
  use slice x Y
  constructor
  . rw [mem_slice]
    use y
  rw [replacement_axiom]
  use x

abbrev SetTheory.Set.curry {X Y Z:Set} (f: X ×ˢ Y → Z) : X → Y → Z :=
  fun x y ↦ f ⟨ (⟨ x, y ⟩:OrderedPair), by rw [mem_cartesian]; use x, y ⟩

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  (show ∃ x:X, ∃ y:Y, z.val = (⟨ x, y ⟩:OrderedPair)
  by exact (mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (show ∃ y:Y, ∃ x:X, z.val = (⟨ x, y ⟩:OrderedPair)
  by rw [exists_comm]; exact (mem_cartesian _ _ _).mp z.property).choose

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
  obtain ⟨ y, hy ⟩ := ((mem_cartesian _ _ _).mp z.property).choose_spec
  obtain ⟨ x, hx ⟩ := (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose_spec
  change z.val = (⟨ fst z, y ⟩:OrderedPair) at hy
  change z.val = (⟨ x, snd z ⟩:OrderedPair) at hx
  simp only [hx, EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq] at hy ⊢
  simp [hy.1]

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

/-- Connections with the Mathlib set product -/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun := fun z ↦ ⟨(fst z, snd z), by simp only [Set.mem_prod, Subtype.coe_prop, and_self]⟩
  invFun := fun z ↦
    ⟨(⟨ z.val.1, z.val.2 ⟩ : OrderedPair).toObject, by
      have h := z.property
      rw [Set.mem_prod] at h
      simp only [Set.mem_setOf_eq]
      rw [SetTheory.Set.mem_cartesian]
      use ⟨ z.val.1, h.1 ⟩
      use ⟨ z.val.2, h.2 ⟩
    ⟩
  left_inv := by
    intro z
    have hz := z.property
    have h := (mem_cartesian _ _ _).mp hz
    obtain ⟨ x, y, h' ⟩ := h
    simp only
    congr!
    rw [SetTheory.Set.pair_eq_fst_snd]
  right_inv := by
    intro z
    have hz := z.property
    rw [Set.mem_prod] at hz
    simp only [Set.mem_setOf_eq] at hz
    obtain ⟨ hx, hy ⟩ := hz
    simp only
    rw [fst_eval ⟨z.val.1, hx⟩ ⟨ z.val.2, hy⟩]
    rw [snd_eval ⟨z.val.1, hx⟩ ⟨ z.val.2, hy⟩]

/-- Definition 3.5.7 -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (a: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ a i, by rw [mem_iUnion]; use i; exact (a i).property ⟩):I → iUnion I X)

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
  ((iUnion I X)^I).specify (fun t ↦ ∃ a : ∀ i, X i, t = tuple a)

/-- Definition 3.5.7 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ a: ∀ i, X i, t = tuple a := by
  simp only [iProd, specification_axiom'']
  constructor
  . intro ⟨ ht, a, h ⟩
    use a
  intro ⟨ a, ha ⟩
  have h : t ∈ (I.iUnion X)^I := by
    rw [powerset_axiom, ha]
    use fun i ↦ ⟨ a i, by rw [mem_iUnion]; use i; exact (a i).property ⟩
  use h, a

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a ∈ iProd X := by rw [mem_iProd]; use a

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ a = b := by
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

/--
  Example 3.5.11. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun := fun x ↦
    have h := (mem_iProd _).mp x.property
    (Classical.choose h) ⟨i, by simp⟩
  invFun := fun x ↦
    ⟨ object_of (fun _ ↦ x), by
      rw [mem_iProd]
      use fun _:({i}:Set) ↦ x
      rw [tuple]
      congr!
      exact iUnion_singleton i X
    ⟩
  left_inv := by
    intro x
    simp only
    have h := (mem_iProd _).mp x.property
    have hp := Classical.choose_spec h
    apply Subtype.ext
    generalize_proofs a b
    simp only
    symm
    rw [tuple] at hp
    simp only [hp]
    congr! with x1 x2 x3 x4
    . apply ext
      intro z
      rw [mem_iUnion]
      constructor
      . intro h
        obtain ⟨ _, hz ⟩ := h
        exact hz
      . intro h
        use ⟨i, a⟩
    . subst x4
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


/-- Example 3.5.11 -/
noncomputable abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := fun _ ↦ ()
  invFun := fun _ ↦ ⟨ object_of (
    (fun i ↦
    have hf : False := by
      have := i.property
      have := SetTheory.Set.not_mem_empty i.val
      contradiction
    False.elim hf) : ((i: (∅:Set)) → iUnion (∅:Set) X)), by
    rw [mem_iProd]
    -- todo: avoid copy/paste
    use (fun i ↦
    have hf : False := by
      have := i.property
      have := SetTheory.Set.not_mem_empty i.val
      contradiction
    False.elim hf)
    rw [tuple]
    rw [object_of_inj]
    funext z
    exfalso
    have zp := z.property
    have := SetTheory.Set.not_mem_empty z.val
    contradiction
  ⟩
  left_inv := sorry
  right_inv := sorry

/-- Example 3.5.11 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun i:I ↦ X) ≃ (I → X) where
  toFun := fun x ↦ fun i ↦
    have h := (mem_iProd _).mp x.property
    (Classical.choose h) i
  invFun := fun f ↦ ⟨ object_of (fun i ↦ f i), by
    by_cases hI : I = ∅
    .
      subst hI
      have h : f = emptyFun X := by
        ext x
        exfalso
        exact False.elim ((SetTheory.Set.not_mem_empty x) x.property)
      rw [h]
      simp [mem_iProd]
      use emptyFun X
      rw [tuple]
      sorry

    rw [mem_iProd]
    use f
    simp [tuple]
    congr!
    apply ext
    intro x
    rw [mem_iUnion]
    constructor
    . intro h
      have := SetTheory.Set.nonempty_def hI
      obtain ⟨ i, hi ⟩ := this
      use ⟨i, hi⟩
    . intro h
      obtain ⟨ i, hi ⟩ := h
      exact hi
  ⟩
  left_inv := by
    intro x
    simp only
    have h := (mem_iProd _).mp x.property
    have hp' := Classical.choose_spec h
    congr!
    sorry

  right_inv := sorry

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
    if i.val = 0 then z.val.1 else z.val.2): (i:({0,1}:Set)) → X i), by
    sorry
  ⟩
  left_inv := sorry
  right_inv := sorry

/-- Example 3.5.9 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi Set.univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun := fun x ↦ ⟨ fun i ↦
    have h := (mem_iProd _).mp x.property
    (Classical.choose h) i,
    by
      extract_lets hl
      rw [Set.mem_pi]
      intro i hi
      simp [Classical.choose_spec hl]
  ⟩
  invFun := fun f ↦ ⟨
    have h := Set.mem_pi.mp f.property
    tuple (fun i ↦
      ⟨f.val i, h i (by simp)⟩)
  , by
    extract_lets hl
    rw [mem_iProd]
    have h := Set.mem_pi.mp f.property
    use (fun i ↦
      ⟨f.val i, h i (by simp)⟩)
  ⟩
  left_inv := by
    intro h
    simp
    generalize_proofs a b
    have := Classical.choose_spec a
    congr!
    -- rw [this]
    sorry
  right_inv := sorry

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
  rw [specification_axiom'']
  constructor
  . intro ⟨ h1, h2 ⟩
    use ((⟨ x, h1 ⟩:nat):ℕ)
    simp [h2]
    calc
      x = (⟨ x, h1 ⟩:nat) := by rfl
      _ = _ :=  by congr; simp
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←SetTheory.Object.ofnat_eq]; exact (m:nat).property)
  convert hm
  simp [h, Equiv.symm_apply_eq]
  rfl

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  have := x.property
  rw [mem_Fin] at this
  obtain ⟨ m, hm, this ⟩ := this
  use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property
  rw [mem_Fin] at this ⊢
  obtain ⟨ m, hm, im ⟩ := this
  use m, by linarith
⟩

/--
  I suspect that this equivalence is non-computable and requires classical logic,
  unless there is a clever trick.
-/
noncomputable abbrev SetTheory.Set.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

/-- Lemma 3.5.12 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x
      by_contra! h
      simp [specification_axiom''] at h
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty)
    rw [mem_iProd]
    use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  specialize hn hX'
  obtain ⟨ x'_obj, hx' ⟩ := nonempty_def hn
  rw [mem_iProd] at hx'
  obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  obtain ⟨ a, ha ⟩ := nonempty_def (h last)
  set x : ∀ i, X i := by
    intro i
    have := mem_Fin' i
    classical
    -- it is unfortunate here that classical logic is required to perform this gluing; this is
    -- because `nat` is technically not an inductive type.  There should be some workaround
    -- involving the equivalence between `nat` and `ℕ` (which is an inductive type).
    cases decEq i last with
      | isTrue heq =>
        rw [heq]
        exact ⟨ a, ha ⟩
      | isFalse heq =>
        have : ∃ m, ∃ h: m < n, X i = X' (Fin_mk n m h) := by
          obtain ⟨ m, h, this ⟩ := this
          have h' : m ≠ n := by
            contrapose! heq
            simp [this, last, heq]
          replace h' : m < n := by contrapose! h'; linarith
          use m, h'
          simp [X']; congr
        rw [this.choose_spec.choose_spec]
        exact x' _
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by sorry

/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
@[ext]
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: SetTheory.Set.Fin n → X
  surj: Function.Surjective x

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by sorry

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

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
theorem SetTheory.Set.recursion (X: Type) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by sorry

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by sorry


end Chapter3
