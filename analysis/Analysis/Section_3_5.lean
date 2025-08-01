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

theorem OrderedPair.toObject_eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair).toObject = (⟨ x', y' ⟩ : OrderedPair).toObject ↔ x = x' ∧ y = y' := by
  rw [EmbeddingLike.apply_eq_iff_eq]
  rw [OrderedPair.eq]


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
    fst ⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [mem_cartesian]
    use x
    use y
  ⟩ = x := by
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

theorem SetTheory.Set.fst_eval' {X Y: Set} (z: X ×ˢ Y) (x: X) (y: Y) (h: z.val = OrderedPair.toObject { fst := x.val, snd := y.val }):
    fst z = x := by
  obtain ⟨val, property⟩ := z
  subst h
  rw [fst_eval]

/--
  Extra eval theorems needed for when one of the components of the ordered pair is not
  an Object directly, but an OrderedPair that is cast to an Object using toObject.
-/
theorem SetTheory.Set.fst_eval_fst_op {X Y: Set} (p: OrderedPair) (h: p.toObject ∈ X) (y: Y) :
  fst ⟨OrderedPair.toObject { fst := p.toObject, snd := y }, by
    rw [mem_cartesian]
    use ⟨ p.toObject, h⟩
    use y
  ⟩ = ⟨p.toObject, h⟩ := by
  simp [fst]
  generalize_proofs a
  have := a.choose_spec
  rw [Subtype.mk.injEq]
  exact this.symm

theorem SetTheory.Set.fst_eval_snd_op {X Y: Set} (x: X) (p: OrderedPair) (h: p.toObject ∈ Y) :
  fst ⟨OrderedPair.toObject { fst := x, snd := p.toObject }, by
    rw [mem_cartesian]
    use x
    use ⟨ p.toObject, h ⟩
  ⟩ = x := by
  simp [fst]
  generalize_proofs a
  have := a.choose_spec
  rw [Subtype.mk.injEq]
  exact this.1.symm

theorem SetTheory.Set.snd_eval_fst_op {X Y: Set} (p: OrderedPair) (h: p.toObject ∈ X) (y: Y) :
  snd ⟨OrderedPair.toObject { fst := p.toObject, snd := y }, by
    rw [mem_cartesian]
    use ⟨ p.toObject, h⟩
    use y
  ⟩ = y := by
  simp [snd]
  generalize_proofs a
  have := a.choose_spec
  rw [Subtype.mk.injEq]
  exact this.2.symm

theorem SetTheory.Set.snd_eval_snd_op {X Y: Set} (x: X) (p: OrderedPair) (h: p.toObject ∈ Y) :
  snd ⟨OrderedPair.toObject { fst := x, snd := p.toObject }, by
    rw [mem_cartesian]
    use x
    use ⟨ p.toObject, h ⟩
  ⟩ = ⟨p.toObject, h⟩ := by
  simp [snd]
  generalize_proofs a
  have := a.choose_spec
  rw [Subtype.mk.injEq]
  exact this.symm

-- todo: find a shorter, more direct proof of this
theorem SetTheory.Set.snd_eval {X Y:Set} (x: X) (y: Y) :
    snd ⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [SetTheory.Set.mem_cartesian]
    use x
    use y
  ⟩ = y := by
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

theorem SetTheory.Set.snd_eval' {X Y: Set} (z: X ×ˢ Y) (x: X) (y: Y) (h: z.val = OrderedPair.toObject { fst := x.val, snd := y.val }):
    snd z = y := by
  obtain ⟨val, property⟩ := z
  subst h
  rw [snd_eval]

theorem SetTheory.Set.set_eq_ordered_pair {X Y : Set} {x:X} {y:Y} {t : X ×ˢ Y} : t.val = (OrderedPair.toObject { fst := x, snd := y }) →
  t = (⟨OrderedPair.toObject { fst := x, snd := y }, by
    rw [SetTheory.Set.mem_cartesian]
    use x
    use y
  ⟩ :X ×ˢ Y) := by
  intro h
  ext
  rw [h]

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

def SetTheory.Set.mk_cart {X Y: Set} (x: X) (y: Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by
    rw [mem_cartesian]
    use x
    use y
  ⟩

@[simp]
theorem SetTheory.Set.mk_cart_fst {X Y: Set} (x: X) (y: Y) :
    fst (mk_cart x y) = x := by
  rw [mk_cart]
  rw [fst_eval]

@[simp]
theorem SetTheory.Set.mk_cart_snd {X Y: Set} (x: X) (y: Y) :
    snd (mk_cart x y) = y := by
  rw [mk_cart]
  rw [snd_eval]

@[simp]
theorem SetTheory.Set.mk_cart_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cart (fst z) (snd z)) = z := by
  rw [mk_cart]
  rw [Subtype.mk.injEq]
  rw [SetTheory.Set.pair_eq_fst_snd]

theorem SetTheory.Set.mk_cart_inj {X Y: Set} (x x': X) (y y': Y) :
    (mk_cart x y) = (mk_cart x' y') ↔ x = x' ∧ y = y' := by
  constructor
  . intro h
    repeat rw [mk_cart] at h
    simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at h
    repeat rw [Subtype.val_inj] at h
    exact h
  . intro ⟨ h1, h2 ⟩
    rw [h1, h2]

theorem SetTheory.Set.cart_fst_snd_ext {X Y: Set} (z z': X ×ˢ Y) :
    fst z = fst z' ∧ snd z = snd z' ↔ z = z' := by
  constructor
  . intro h
    obtain ⟨ h1, h2 ⟩ := h
    have := z.property
    rw [mem_cartesian] at this
    obtain ⟨ x, y, h3 ⟩ := this
    have := z'.property
    rw [mem_cartesian] at this
    obtain ⟨ x', y', h4 ⟩ := this
    rw [Subtype.mk.injEq]
    rw [h3, h4]
    simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq]
    have : fst z = x := fst_eval' z x y h3
    have : snd z = y := snd_eval' z x y h3
    have : fst z' = x' := fst_eval' z' x' y' h4
    have : snd z' = y' := snd_eval' z' x' y' h4
    simp_all
  . intro h
    subst z'
    constructor <;> rfl

noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun z ↦ mk_cart (snd z) (fst z)
  invFun := fun z ↦ mk_cart (snd z) (fst z)
  left_inv := by
    intro z
    simp

  right_inv := by
    intro z
    simp

noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun := fun z ↦ mk_cart (fst (fst z)) (mk_cart (snd (fst z)) (snd z))
  invFun := fun z ↦ mk_cart (mk_cart (fst z) (fst (snd z))) (snd (snd z))

  left_inv := by
    intro t
    simp

  right_inv := by
    intro t
    simp

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

theorem SetTheory.Set.cartesian_of_empty (X:Set) :
    (∅:Set) ×ˢ X = ∅ := by
  apply ext
  intro z
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ x, y, h' ⟩ := h
    have := SetTheory.Set.not_mem_empty x.val
    have := x.property
    contradiction
  . intro h
    exfalso
    exact (SetTheory.Set.not_mem_empty z) h

/-- Definition 3.5.7 -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (a: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ a i, by rw [mem_iUnion]; use i; exact (a i).property ⟩):I → iUnion I X)

theorem SetTheory.Set.object_of_inj {X Y:Set} (f g: X → Y): function_to_object _ _ f = function_to_object _ _ g ↔ f = g := by
  constructor
  . intro h
    rw [function_to_object] at h
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
    ext i
    simp only [coe_of_fun_inj] at h
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
    simp [tuple] at this
    have h := congr_fun this ⟨ i, b ⟩
    rw [Subtype.mk.injEq] at h
    ext
    exact h.symm

/-- Example 3.5.11 -/
noncomputable abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
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

/-- Example 3.5.11 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun _:I ↦ X) ≃ (I → X) where
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

-- need to use if statements with non-decidable equality
open Classical
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := fun x ↦
    have h := (mem_iProd _).mp x.property
    mk_cart ((Classical.choose h) ⟨0, by simp⟩) ((Classical.choose h) ⟨1, by simp⟩)

  invFun := fun z ↦
    let f : (i : ({0,1}:Set)) → X i := fun i ↦
      have hi := i.property
      if h: i = ⟨0, by simp⟩ then ⟨(fst z), by
        rw [h]
        exact (fst z).property
      ⟩ else ⟨(snd z), by
        have h2 : i = ⟨1, by simp⟩ := by
          have := i.property
          rw [mem_pair] at this
          rw [Subtype.mk.injEq] at h ⊢
          tauto
        rw [h2]
        exact (snd z).property
      ⟩
    ⟨ tuple f, by rw [mem_iProd]; use f ⟩

  left_inv := by
    intro h
    have hi := h.prop
    rw [mem_iProd] at hi
    have f := Classical.choose hi
    have hf := Classical.choose_spec hi
    rw [Subtype.mk.injEq]
    rw [hf]
    simp only [mk_cart_fst, mk_cart_snd, coe_of_fun_inj]
    funext i
    by_cases hi: i = ⟨ 0, by simp ⟩
    . rw [hi]
      simp
    . have hi1 : i = ⟨ 1, by simp ⟩ := by
        have := i.prop
        rw [mem_pair] at this
        cases' this with h0 h1
        . exfalso
          rw [Subtype.mk.injEq] at hi
          exact hi h0
        . rw [Subtype.mk.injEq]
          exact h1
      rw [hi1]
      simp

  right_inv := by
    intro h
    have hi := h.property
    rw [mem_cartesian] at hi
    obtain ⟨ x0, x1, hx ⟩ := hi
    rw [Subtype.mk.injEq]
    rw [hx]
    rw [mk_cart]
    simp
    constructor
    . generalize_proofs a b c d e
      have := Classical.choose_spec e
      rw [tuple_inj] at this
      rw [← this]
      simp
      rw [fst_eval' _ _ _ hx]
    . generalize_proofs a b c d e
      have := Classical.choose_spec e
      rw [tuple_inj] at this
      rw [← this]
      simp
      rw [snd_eval' _ _ _ hx]

set_option maxHeartbeats 10000000 in
/-- Example 3.5.9 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := fun z ↦
    have h := (mem_iProd _).mp z.property
    mk_cart ((Classical.choose h) ⟨0, by simp⟩)
      (mk_cart ((Classical.choose h) ⟨1, by simp⟩) ((Classical.choose h) ⟨2, by simp⟩))

  invFun := fun z ↦
    let f : (i : ({0,1,2}:Set)) → X i := fun i ↦
      have hi := i.property
      if h: i = ⟨0, by simp⟩ then ⟨(fst z), by
        rw [h]
        exact (fst z).property
      ⟩ else if h': i = ⟨1, by simp⟩ then ⟨(fst (snd z)), by
        rw [h']
        exact (fst (snd z)).property
      ⟩ else ⟨snd (snd z), by
        have h2 : i = ⟨2, by simp⟩ := by
          have := i.property
          rw [mem_triple] at this
          rw [Subtype.mk.injEq] at h h' ⊢
          tauto
        rw [h2]
        exact (snd (snd z)).property
      ⟩
    ⟨ tuple f, by rw [mem_iProd]; use f ⟩

  left_inv := by
    intro h
    simp
    have hi := h.prop
    rw [mem_iProd] at hi
    have f := Classical.choose hi
    have hf := Classical.choose_spec hi
    rw [Subtype.mk.injEq]
    conv_rhs => rw [hf]
    rw [tuple_inj]
    funext i
    have hi := i.property
    rw [mem_triple] at hi
    cases' hi with h0 h12
    . have : i = ⟨ 0, by simp ⟩ := by rw [Subtype.mk.injEq]; exact h0
      rw [this]
      simp
    . cases' h12 with h1 h2
      . have : i = ⟨ 1, by simp ⟩ := by rw [Subtype.mk.injEq]; exact h1
        rw [this]
        simp
      . have : i = ⟨ 2, by simp ⟩ := by rw [Subtype.mk.injEq]; exact h2
        rw [this]
        simp

  right_inv := by
    intro z
    have hi := z.property
    rw [mem_cartesian] at hi
    obtain ⟨ x0, x12, hx ⟩ := hi
    have hi1 := x12.property
    rw [mem_cartesian] at hi1
    obtain ⟨ x1, x2, hx12 ⟩ := hi1
    rw [Subtype.mk.injEq]
    rw [hx]
    repeat rw [mk_cart]
    simp
    generalize_proofs a b c d e f g
    have hg := Classical.choose_spec g
    rw [tuple_inj] at hg
    constructor
    . rw [← hg]
      simp
      rw [fst_eval' _ _ _ hx]
    . rw [← hg]
      simp
      rw [hx12]
      rw [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq]
      constructor
      . rw [snd_eval' _ _ _ hx]
        rw [fst_eval' _ _ _ hx12]
      . rw [snd_eval' _ _ _ hx]
        rw [snd_eval' _ _ _ hx12]


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
    simp only
    generalize_proofs a b
    have := Classical.choose_spec a
    ext
    simp only
    rw [← this]
  right_inv := by
    intro x
    simp only
    generalize_proofs a b c
    have := Classical.choose_spec b
    simp only [Set.mem_setOf_eq, forall_const] at this
    simp [tuple] at this
    rw [Subtype.mk.injEq]
    ext i
    have h := congr_fun this i
    rw [Subtype.mk.injEq] at h
    exact h.symm

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

theorem SetTheory.Set.Fin_mk_ext {n x y: ℕ} {h1: x < n} {h2: y < n}:
    Fin_mk n x h1 = Fin_mk n y h2 → x = y := by
  intro h
  repeat rw [Fin_mk] at h
  simp only [Subtype.mk.injEq, Object.natCast_inj] at h
  exact h

/--
  I suspect that this equivalence is non-computable and requires classical logic,
  unless there is a clever trick.
-/
noncomputable abbrev SetTheory.Set.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun := fun x ↦
    let m := Classical.choose (mem_Fin' x)
    let n := Classical.choose (Classical.choose_spec (mem_Fin' x))
    _root_.Fin.mk m n
  invFun := fun x ↦ SetTheory.Set.Fin_mk n x.val x.isLt
  left_inv := by
    intro x
    simp only
    generalize_proofs a b
    have h1 := Classical.choose_spec a
    have h2 := Classical.choose_spec h1
    exact h2.symm
  right_inv := by
    intro x
    simp only
    generalize_proofs a b c d
    have h1 := Classical.choose_spec c
    have h2 := Classical.choose_spec h1
    ext
    apply Fin_mk_ext at h2
    exact h2.symm

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
@[ext]
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: SetTheory.Set.Fin n → X
  surj: Function.Surjective x

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
    rw [← this]

  right_inv := by
    intro t
    simp only
    generalize_proofs a b c d e
    cases t with | mk tuple ht
    cases tuple with | mk tX tx surj
    rw [Subtype.mk.injEq]
    rw [Tuple.eq]
    intro i
    simp only
    have := Classical.choose_spec b
    simp only [coe_of_fun_inj] at this
    have := congr_fun this i
    rw [Subtype.mk.injEq] at this
    rw [this]
    congr! with x
    simp only [coe_of_fun_inj]


/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  cases p with | mk fst snd
  rw [OrderedPair.eq]
  tauto

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  cases p with | mk pfst psnd
  cases q with | mk qfst qsnd
  rw [OrderedPair.eq, OrderedPair.eq]
  tauto

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  cases p with | mk pfst psnd
  cases q with | mk qfst qsnd
  cases r with | mk rfst rsnd
  rw [OrderedPair.eq] at hpq hqr
  rw [OrderedPair.eq]
  -- why tauto doesn't close
  simp_all only [and_self]

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by
  rw [SetTheory.Set.tuple_inj]

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
  repeat rw [SetTheory.Set.tuple_inj]
  tauto

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
  repeat rw [SetTheory.Set.tuple_inj] at hab hbc ⊢
  trans b
  . exact hab
  . exact hbc

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have hb := b.property
    rw [mem_union] at hb ⊢
    rcases hb with h | h
    . left
      rw [mem_cartesian]
      use a
      use ⟨b , h⟩
    . right
      rw [mem_cartesian]
      use a
      use ⟨b , h⟩
  . intro h
    rw [mem_union] at h
    rcases h with h | h
    . rw [mem_cartesian] at h ⊢
      obtain ⟨ a, b, ha, hb ⟩ := h
      use a
      use ⟨b, by rw [mem_union]; left; exact b.property⟩
    . rw [mem_cartesian] at h ⊢
      obtain ⟨ a, b, ha, hb ⟩ := h
      use a
      use ⟨b, by rw [mem_union]; right; exact b.property⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have hb := b.property
    rw [mem_inter] at hb ⊢
    rcases hb with ⟨ h1, h2 ⟩
    repeat rw [mem_cartesian]
    constructor
    . use a
      use ⟨b, h1⟩
    . use a
      use ⟨b, h2⟩
  . intro h
    rw [mem_inter] at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [mem_cartesian] at h1 h2 ⊢
    obtain ⟨ a1, b1, ha1, hb1 ⟩ := h1
    obtain ⟨ a2, b2, ha2 ⟩ := h2
    use a1
    rw [EmbeddingLike.apply_eq_iff_eq] at ha2
    simp at ha2
    use ⟨b1.val, by
      rw [mem_inter]
      constructor
      . exact b1.property
      . rw [ha2.2]; exact b2.property
    ⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have hb := b.property
    rw [mem_sdiff] at ⊢
    constructor
    . rw [mem_cartesian]
      use a
      use ⟨b, by
        rw [mem_sdiff] at hb
        exact hb.1
      ⟩
    . intro h2
      rw [mem_cartesian] at h2
      obtain ⟨ a2, b2, ha2 ⟩ := h2
      rw [mem_sdiff] at hb
      rw [EmbeddingLike.apply_eq_iff_eq] at ha2
      rw [OrderedPair.mk.injEq] at ha2
      rw [ha2.2] at hb
      exact hb.2 b2.property
  . intro h
    rw [mem_sdiff] at h
    rw [mem_cartesian] at h ⊢
    obtain ⟨ h1, h2 ⟩ := h
    obtain ⟨ a, b, ha, hb ⟩ := h1
    use a
    use ⟨ b, by
      rw [mem_sdiff]
      constructor
      . exact b.property
      . contrapose! h2
        rw [mem_cartesian]
        use a
        use ⟨ b, h2 ⟩
    ⟩

/-- Exercise 3.5.4 -/
-- same as prod_union, can it be proved by using prod_union?
-- going through commutativity, we lose equality and only have equivalence
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have hb := b.property
    rw [mem_union]
    have ha := a.property
    rw [mem_union] at ha
    rcases ha with h | h
    . left
      rw [mem_cartesian]
      use ⟨ a, h ⟩
      use b
    . right
      rw [mem_cartesian]
      use ⟨ a, h ⟩
      use b
  . intro h
    rw [mem_union] at h
    rcases h with h | h
    . rw [mem_cartesian] at h ⊢
      obtain ⟨ a, b, ha, hb ⟩ := h
      use ⟨a, by rw [mem_union]; left; exact a.property⟩
      use b
    . rw [mem_cartesian] at h ⊢
      obtain ⟨ a, b, ha, hb ⟩ := h
      use ⟨a, by rw [mem_union]; right; exact a.property⟩
      use b


/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have ha := a.property
    rw [mem_inter] at ha ⊢
    constructor
    . rw [mem_cartesian]
      use ⟨ a , ha.1 ⟩
      use b
    . rw [mem_cartesian]
      use ⟨ a , ha.2 ⟩
      use b
  . intro h
    rw [mem_inter] at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [mem_cartesian] at h1 h2 ⊢
    obtain ⟨ a1, b1, ha1, hb1 ⟩ := h1
    obtain ⟨ a2, b2, ha2 ⟩ := h2
    rw [EmbeddingLike.apply_eq_iff_eq] at ha2
    rw [OrderedPair.mk.injEq] at ha2
    use ⟨ a1, by
      rw [mem_inter]
      constructor
      . exact a1.property
      . rw [ha2.1]; exact a2.property
    ⟩
    use b1

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have hb := b.property
    rw [mem_sdiff] at ⊢
    repeat rw [mem_cartesian]
    have ha := a.property
    rw [mem_sdiff] at ha
    obtain ⟨ h1, h2 ⟩ := ha
    constructor
    . use ⟨ a, h1⟩
      use b
    . contrapose! h2
      obtain ⟨ a2, b2, ha2 ⟩ := h2
      simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at ha2
      rw [ha2.1]
      exact a2.property
  . intro h
    rw [mem_sdiff] at h
    rw [mem_cartesian] at h ⊢
    obtain ⟨ h1, h2 ⟩ := h
    obtain ⟨ a, b, ha, hb ⟩ := h1
    use ⟨a, by
      rw [mem_sdiff]
      constructor
      . exact a.property
      . contrapose! h2
        rw [mem_cartesian]
        simp [OrderedPair.mk.injEq]
        exact h2
    ⟩
    use b

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_inter] at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [mem_cartesian] at h1 h2 ⊢
    obtain ⟨ a1, b1, ha1 ⟩ := h1
    obtain ⟨ a2, b2, ha2 ⟩ := h2
    rw [ha1] at ha2
    simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at ha2
    obtain ⟨ ha1a2, ha1b2 ⟩ := ha2
    use ⟨ a1, by rw [mem_inter]; constructor; exact a1.property; rw [ha1a2]; exact a2.property ⟩
    use ⟨ b1, by rw [mem_inter]; constructor; exact b1.property; rw [ha1b2]; exact b2.property ⟩
  . intro h
    rw [mem_cartesian] at h
    obtain ⟨ a, b, ha, hb ⟩ := h
    have ha := a.property
    have hb := b.property
    rw [mem_inter] at ha hb
    rw [mem_inter] at ⊢
    constructor
    . rw [mem_cartesian]
      use ⟨a, ha.1⟩
      use ⟨b, hb.1⟩
    . rw [mem_cartesian]
      use ⟨a, ha.2⟩
      use ⟨b, hb.2⟩

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  apply isFalse
  push_neg
  use {0, 1}
  use {0, 1}
  use {1, 2}
  use {1, 2}
  by_contra! h
  rw [ext_iff] at h
  specialize h (⟨0, 2⟩: OrderedPair).toObject
  have : {0, 1} ∪ {1, 2} = ({0, 1, 2}:Set) := by
    rw [SetTheory.Set.ext_iff]
    intro x
    constructor
    . intro hx
      rw [mem_union] at hx
      repeat rw [mem_pair] at hx
      rw [mem_triple]
      tauto
    . intro hx
      rw [mem_union]
      repeat rw [mem_pair]
      rw [mem_triple] at hx
      tauto
  rw [this] at h
  have : OrderedPair.toObject { fst := 0, snd := 2 } ∈ ({0, 1, 2}: Set) ×ˢ ({0, 1, 2} :Set) := by
    rw [mem_cartesian]
    use ⟨ 0, by rw [mem_triple]; left; rfl⟩
    use ⟨ 2, by rw [mem_triple]; right; right; rfl ⟩
  have := h.mpr this
  rw [mem_union] at this
  cases' this with h h
  . rw [mem_cartesian] at h
    obtain ⟨ a, b, ha ⟩ := h
    simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at ha
    have hb := b.property
    rw [mem_pair] at hb
    have ha' := ha.2
    rw [← ha'] at hb
    repeat rw [ofNat_inj'] at hb
    contradiction
  . rw [mem_cartesian] at h
    obtain ⟨ a, b, ha ⟩ := h
    simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at ha
    have ha' := a.property
    rw [mem_pair] at ha'
    have hb := ha.1
    rw [← hb] at ha'
    repeat rw [ofNat_inj'] at ha'
    contradiction


/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  apply isFalse
  push_neg
  use {0, 1}
  use {0, 1}
  use {0}
  use {0}
  by_contra! h
  rw [ext_iff] at h
  specialize h (⟨0, 1⟩: OrderedPair).toObject
  have : {0, 1} \ {0} = ({1}:Set) := by
    rw [SetTheory.Set.ext_iff]
    intro x
    constructor
    . intro hx
      rw [mem_sdiff] at hx
      repeat rw [mem_pair] at hx
      rw [mem_singleton] at hx ⊢
      tauto
    . intro hx
      rw [mem_singleton] at hx
      rw [hx]
      rw [mem_sdiff]
      rw [mem_pair]
      rw [mem_singleton]
      constructor
      . right; rfl
      . rw [ofNat_inj']
        simp only [one_ne_zero, not_false_eq_true]
  rw [this] at h
  have : OrderedPair.toObject { fst := 0, snd := 1 } ∈ ({0, 1}:Set) ×ˢ ({0, 1}:Set) \ ({0}:Set) ×ˢ ({0}:Set) := by
    rw [mem_sdiff]
    constructor
    . rw [mem_cartesian]
      use ⟨0, by rw [mem_pair]; left; rfl⟩
      use ⟨1, by rw [mem_pair]; right; rfl⟩
    . by_contra! h2
      rw [mem_cartesian] at h2
      obtain ⟨ a, b, ha ⟩ := h2
      simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq] at ha
      have hb := b.property
      rw [mem_singleton] at hb
      rw [← ha.2] at hb
      repeat rw [ofNat_inj'] at hb
      contradiction
  have := h.mp this
  rw [mem_cartesian] at this
  obtain ⟨ a, b, ha ⟩ := this
  simp at ha
  have ha' := a.property
  rw [mem_singleton] at ha'
  rw [← ha.1] at ha'
  repeat rw [ofNat_inj'] at ha'
  contradiction

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (_: C ≠ ∅) (_: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  constructor
  . intro h
    constructor
    . intro a ha
      have hbn := nonempty_def hB
      obtain ⟨ b, hb ⟩ := hbn
      have hp : OrderedPair.toObject { fst := a, snd := b } ∈ A ×ˢ B := by
        rw [mem_cartesian]
        use ⟨a, ha⟩
        use ⟨b, hb⟩
      have h' := h _ hp
      rw [mem_cartesian] at h'
      simp at h'
      exact h'.1
    . intro b hb
      have han := nonempty_def hA
      obtain ⟨ a, ha ⟩ := han
      have hp : OrderedPair.toObject { fst := a, snd := b } ∈ A ×ˢ B := by
        rw [mem_cartesian]
        use ⟨a, ha⟩
        use ⟨b, hb⟩
      have h' := h _ hp
      rw [mem_cartesian] at h'
      simp at h'
      exact h'.2
  . intro h
    obtain ⟨ hA', hB' ⟩ := h
    intro x hx
    rw [mem_cartesian] at hx ⊢
    obtain ⟨ a, b, ha, hb ⟩ := hx
    simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq, exists_and_left, Subtype.exists,
      exists_prop, exists_eq_right', exists_and_right]
    constructor
    . exact hA' _ a.property
    . exact hB' _ b.property

/--
  Answer to the question which hypothesis can be removed.
  Lean immediately shows that in original proof we can drop C and D non-zero.
  This shows we can't drop A and by symmetry we know we can't drop B either.
-/
def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  apply isFalse
  push_neg
  use ∅
  use {0}
  use {0}
  use ∅
  left
  constructor
  . rw [cartesian_of_empty]
    intro x hx
    exfalso
    exact not_mem_empty x hx
  . intro x hx
    have : 0 ∈ ({0}:Set) := by
      rw [mem_singleton]
    have := hx _ this
    exact not_mem_empty _ this

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
  apply existsUnique_of_exists_of_unique
  . use fun z ↦ ⟨(⟨f z, g z⟩: OrderedPair), by
      rw [mem_cartesian]
      use f z
      use g z
    ⟩
    constructor
    . ext z
      simp only [Function.comp_apply]
      rw [fst_eval]
    . ext z
      simp only [Function.comp_apply]
      rw [snd_eval]
  . intro h1 h2 h
    obtain ⟨ h1', h2' ⟩ := h
    subst f
    subst g
    intro h'
    obtain ⟨ h1', h2' ⟩ := h'
    ext z
    have h1c := congr_fun h1' z
    have h2c := congr_fun h2' z
    repeat rw [Function.comp_apply] at h1c h2c
    have h1z := (h1 z).property
    have h2z := (h2 z).property
    rw [mem_cartesian] at h1z h2z
    obtain ⟨ a1, b1, ha1⟩ := h1z
    obtain ⟨ a2, b2, ha2⟩ := h2z
    repeat rw [ha1, ha2] at ⊢
    simp only [EmbeddingLike.apply_eq_iff_eq, OrderedPair.mk.injEq]
    have p1 := (h1 z).property
    rw [← Subtype.mk.injEq _ p1] at ha1
    simp at ha1
    have p2 := (h2 z).property
    rw [← Subtype.mk.injEq _ p2] at ha2
    simp at ha2
    rw [ha1] at h1c h2c
    conv_lhs at h1c => rw [ha2]
    conv_lhs at h2c => rw [ha2]
    repeat rw [fst_eval] at h1c
    repeat rw [snd_eval] at h2c
    rw [Subtype.mk.injEq] at h1c h2c
    constructor
    . exact h1c.symm
    . exact h2c.symm

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  constructor
  . intro h
    contrapose! h
    apply nonempty_of_inhabited
    rw [mem_iProd]
    use fun i ↦
      have := h i
      have h2 := nonempty_def this
      let x := Classical.choose h2
      ⟨x, by
        exact Classical.choose_spec h2
      ⟩
  . intro h
    obtain ⟨ i, hi ⟩ := h
    contrapose! hi
    apply nonempty_def at hi
    obtain ⟨ x, hx ⟩ := hi
    rw [mem_iProd] at hx
    obtain ⟨ f, hf ⟩ := hx
    apply nonempty_of_inhabited
    exact (f i).property

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
  apply ext
  intro x
  constructor
  . intro h
    rw [mem_inter] at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [mem_iUnion] at h1 h2
    obtain ⟨ i, hi1 ⟩ := h1
    obtain ⟨ j, hj2 ⟩ := h2
    rw [mem_iUnion]
    let p : I ×ˢ J := ⟨(⟨i, j⟩:OrderedPair), by
      rw [mem_cartesian]
      use i
      use j
    ⟩
    use p
    rw [mem_inter]
    constructor
    . simp [p]
      exact hi1
    . simp [p]
      exact hj2
  . intro h
    rw [mem_iUnion] at h
    obtain ⟨ p, hp ⟩ := h
    rw [mem_inter] at hp
    obtain ⟨ hi, hj ⟩ := hp
    have := p.property
    rw [mem_cartesian] at this
    obtain ⟨ i, j, hij⟩ := this
    have hfst : fst p = i := by
      -- curiously subst fails until I break down p
      obtain ⟨val, property⟩ := p
      subst hij
      rw [fst_eval]
    have hsnd : snd p = j := by
      obtain ⟨val, property⟩ := p
      subst hij
      rw [snd_eval]
    rw [mem_inter]
    constructor
    . rw [mem_iUnion]
      use i
      rw [← hfst]
      exact hi
    . rw [mem_iUnion]
      use j
      rw [← hsnd]
      exact hj

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
  constructor
  . intro h
    repeat rw [graph] at h
    ext x
    rw [ext_iff] at h
    specialize h (⟨( ⟨x, f x⟩:OrderedPair), by
      rw [mem_cartesian]
      use x
      use (f x)
    ⟩ : X ×ˢ Y)
    repeat rw [specification_axiom'] at h
    simp [fst_eval, snd_eval] at h
    rw [h]
  . intro h
    rw [h]

theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by
  apply existsUnique_of_exists_of_unique
  . use fun x ↦
      let h := hvert x
      let y := Classical.choose h.exists
      y
    apply ext
    intro x
    constructor
    . intro hx
      have h := hG _ hx
      rw [graph]
      rw [specification_axiom'']
      use h
      simp only
      generalize_proofs a
      have := Classical.choose_spec a
      have hq := (hvert (fst ⟨x, h⟩))
      have h2 : OrderedPair.toObject { fst := ↑(fst ⟨x, h⟩), snd := snd ⟨x, h⟩ } ∈ G := by
        suffices hg : OrderedPair.toObject { fst := ↑(fst ⟨x, h⟩), snd := ↑(snd ⟨x, h⟩) } = x by
          rw [hg]
          exact hx
        have := (mem_cartesian x _ _).mp h
        obtain ⟨ x', y', h'⟩ := this
        conv_rhs => rw [h']
        rw [OrderedPair.toObject_eq]
        constructor
        . simp [h']
        . simp [h']
      exact hq.unique this h2
    . intro h
      simp only at h
      rw [graph] at h
      rw [specification_axiom''] at h
      obtain ⟨ h1, h2 ⟩ := h
      rw [mem_cartesian] at h1
      obtain ⟨ x', y, h'⟩ := h1
      specialize hvert x'
      rw [h']
      generalize_proofs a at h2
      have := Classical.choose_spec a
      rw [h2] at this
      suffices h: OrderedPair.toObject { fst := ↑(fst ⟨x, h1⟩), snd := ↑(snd ⟨x, h1⟩) } =
        OrderedPair.toObject { fst := ↑x', snd := ↑y } by
        rw [← h]
        exact this
      rw [OrderedPair.toObject_eq]
      simp [h']
  . intro f f' h h'
    rw [graph] at h h'
    rw [ext_iff] at h h'
    ext x
    specialize hvert x
    obtain ⟨ y, hp ⟩ := hvert.exists
    let p : X ×ˢ Y := ⟨(⟨x, y⟩:OrderedPair), by
      rw [mem_cartesian]
      use x
      use y
    ⟩
    specialize h p.val
    specialize h' p.val
    have : p.val ∈ G := by
      apply hp
    have hf := h.mp this
    have hf' := h'.mp this
    rw [specification_axiom''] at hf hf'
    obtain ⟨ h1, h2 ⟩ := hf
    obtain ⟨ h1', h2' ⟩ := hf'
    simp at h2 h2'
    rw [h2, h2']

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
  apply existsUnique_of_exists_of_unique
  . let g := (Y ×ˢ X).powerset.specify (fun T ↦
      have p := (mem_powerset T).mp T.property
      have S := choose p
      ∀ y : Y, ∃! x : X, OrderedPair.toObject { fst := y, snd := x } ∈ S
    )
    use g.replace (P := fun T F ↦ ∃ f: Y → X, function_to_object _ _ f = F ∧ graph f = T.val) (by
      intro T y y'
      simp
      intro f hf hG f' hf' hG'
      rw [← hf, ← hf']
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [← hG] at hG'
      simp only [EmbeddingLike.apply_eq_iff_eq] at hG'
      rw [SetTheory.Set.graph_inj] at hG'
      exact hG'.symm
    )
    intro F
    rw [replacement_axiom]
    constructor
    . intro h
      obtain ⟨ T, hT, hF, hF' ⟩ := h
      use hT
      rw [← hF]
      exact rfl
    . intro h
      obtain ⟨ T, hT ⟩ := h
      have : set_to_object (graph T) ∈ g := by
        simp [g]
        rw [specification_axiom'']
        constructor
        . intro y hy
          apply existsUnique_of_exists_of_unique
          . use T ⟨y, hy⟩
            generalize_proofs a
            have := Classical.choose_spec a
            obtain ⟨ h1, h2 ⟩ := this
            rw [EmbeddingLike.apply_eq_iff_eq] at h1
            rw [← h1]
            rw [graph]
            rw [specification_axiom'']
            constructor
            . let y': Y := ⟨ y , hy ⟩
              have : y = y'.val := by rfl
              simp [this]
            . rw [mem_cartesian]
              use ⟨y, hy⟩
              use T ⟨y, hy⟩
          . intro x x' hx hx'
            generalize_proofs a at hx hx'
            have := Classical.choose_spec a
            rw [EmbeddingLike.apply_eq_iff_eq] at this
            rw [← this.1] at hx hx'
            rw [graph] at hx hx'
            rw [specification_axiom''] at hx hx'
            obtain ⟨ h1, h2 ⟩ := hx
            obtain ⟨ h1', h2' ⟩ := hx'
            let y': Y := ⟨ y , hy ⟩
            have : y = y'.val := by rfl
            simp [this] at h2 h2'
            rw [← h2, ← h2']
            . rw [mem_powerset]
              use graph T
              simp only [true_and]
              rw [graph]
              apply specification_axiom
      use ⟨ set_to_object (graph T), this⟩
      use T
      constructor
      . rw [← hT]
        rfl
      . rfl
  . intro S S' h h'
    apply ext
    intro x
    specialize h x
    specialize h' x
    rw [h, h']

/-- some helper lemmas to deal with zeros and literals -/
lemma nat_equiv_symm_zero : SetTheory.Set.nat_equiv.symm 0 = 0 := by
  rw [Equiv.symm_apply_eq]
  exact rfl

lemma nat_equiv_symm_x_zero (x: Nat): SetTheory.Set.nat_equiv.symm x = 0
    ↔ x = 0 := by
  constructor
  . intro h
    rw [Equiv.symm_apply_eq] at h
    rw [h]
    exact rfl
  . intro h
    rw [h]
    exact nat_equiv_symm_zero

lemma nat_equiv_zero : SetTheory.Set.nat_equiv 0 = 0 := by rfl

lemma nat_equiv_cast (n: ℕ) : SetTheory.Set.nat_equiv.symm (n: Nat) = n := by
  simp_all only [SetTheory.Set.nat_equiv_coe_of_coe]

set_option pp.proofs true in
/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  apply existsUnique_of_exists_of_unique
  . have h (N: ℕ): ∃! a: {n: Nat // (n:ℕ) ≤ N} → X,
    a ⟨0, by
      rw [nat_equiv_symm_zero]
      exact zero_le N
    ⟩ = c ∧ ∀ n, (h: n < N) → a ⟨(n + 1:ℕ), by
      simp only [nat_equiv_coe_of_coe]
      exact h
    ⟩ = f n (a ⟨n, by
      simp only [nat_equiv_coe_of_coe]
      exact Nat.le_of_lt h
    ⟩) := by
      induction' N with N ih
      . use fun _ ↦ c
        simp
        intro h h'
        ext x
        have hp := x.prop
        have : x = ⟨0, by
            simp only [nonpos_iff_eq_zero]
            rw [Equiv.symm_apply_eq]
            rfl
        ⟩ := by
          simp only [nonpos_iff_eq_zero] at hp
          rw [Equiv.symm_apply_eq] at hp
          rw [Subtype.mk.injEq]
          rw [hp]
          rfl
        rw [this]
        rw [h']
      . apply existsUnique_of_exists_of_unique
        . let ap := choose ih
          use fun n ↦ if h:(n = N + 1) then f N (ap ⟨N, by rw [nat_equiv_coe_of_coe]⟩)
          else ap ⟨n, by
            have := n.prop
            rw [le_iff_lt_or_eq] at this
            simp [h] at this
            exact Nat.lt_succ_iff.mp this
          ⟩
          constructor
          have ap_spec := choose_spec ih
          simp at ap_spec
          . simp
            have hN : nat_equiv.symm 0 ≠ N + 1 := by
              rw [nat_equiv_symm_zero]
              simp only [ne_eq, Nat.right_eq_add, Nat.add_eq_zero, one_ne_zero, and_false,
                not_false_eq_true]
            exact ap_spec.1.1
          . intro n hn
            simp [hn]
            generalize_proofs a b c d e f'
            by_cases h: n = N
            . simp [h]
            . simp [h]
              have hne : n ≠ N + 1 := by linarith
              simp [hne]
              -- why did we lose it from the state?
              have ap_spec := choose_spec ih
              simp at ap_spec
              have ap_spec := ap_spec.1.2
              cases' n with n'
              . specialize ap_spec 0
                have : 0 < N := by exact Nat.zero_lt_of_ne_zero fun a ↦ h (Eq.symm a)
                specialize ap_spec this
                exact ap_spec
              . specialize ap_spec (n' + 1)
                have : n' + 1 < N := by
                  apply Nat.lt_of_le_of_ne
                  exact Nat.le_of_lt_succ hn
                  exact h
                specialize ap_spec this
                exact ap_spec
        . intro y y' hy hy'
          have h1 := hy.1
          have h2 := hy'.1
          ext x
          induction' h: (nat_equiv.symm x) with x' hx generalizing x
          . rw [Equiv.symm_apply_eq] at h
            have : x = ⟨nat_equiv 0, by simp⟩ := by
              exact Subtype.coe_eq_of_eq_mk h
            rw [this]
            simp only [nat_equiv_zero]
            simp only [h1, h2]
          . obtain ⟨_, hy⟩ := hy
            obtain ⟨_, hy'⟩ := hy'
            specialize hy x'
            specialize hy' x'
            have : x' < N + 1 := by
              have := x.prop
              rw [h] at this
              exact this
            have hy1 := hy this
            have hy1' := hy' this
            rw [Equiv.symm_apply_eq] at h
            have hxx': x = ⟨↑(x' + 1), by
              simp [Equiv.symm_apply_apply]
              exact Nat.le_of_lt_succ this
            ⟩ := by exact Subtype.coe_eq_of_eq_mk h
            rw [hxx']
            rw [hy1, hy1']
            specialize hx ⟨nat_equiv.symm x', by
              simp
              exact Nat.le_of_succ_le this
            ⟩
            simp only [nat_equiv_coe_of_coe, forall_const] at hx
            congr! 2
            rw [Subtype.mk.injEq]
            exact hx
    use fun n ↦ (h n).choose ⟨n, by
      exact Nat.le_refl (nat_equiv.symm n)
    ⟩
    constructor
    . generalize_proofs a b c d e f
      have h := choose_spec d
      have := h.1.1
      simp [this]
    . intro n
      have := (h (n + 1)).choose_spec.1.2
      simp at this
      specialize this n (Nat.lt_succ_self n)
      -- this is only swapping eq.symm (symm x) = x by because it
      -- is captured in types I have to do a whole rebuilding this functions
      have hw : Exists.choose (h (nat_equiv.symm ↑(n + 1))) ⟨↑(n + 1), Nat.le_refl (nat_equiv.symm ↑(n + 1))⟩ =
          Exists.choose (h (n + 1)) ⟨↑(n + 1), Nat.le_of_eq (nat_equiv_cast (n + 1))⟩ := by
        have eq : nat_equiv.symm ↑(n + 1) = n + 1 := nat_equiv_cast (n + 1)
        -- sadly rw doesn't work here, even conv_lhs arg 1 doesn't.
        -- so we will use uniqueness
        let f : {m: Nat // (m:ℕ) ≤ n + 1} → X :=
          fun m => Exists.choose (h (nat_equiv.symm ↑(n + 1))) ⟨m.val, by
            simp [Equiv.symm_apply_apply]
            exact m.property
          ⟩
        have : f = Exists.choose (h (n + 1)) := by
          ext z
          induction' hi: (nat_equiv.symm z) with z' ih generalizing z
          . rw [Equiv.symm_apply_eq] at hi
            have : z = ⟨0, by
              rw [nat_equiv_symm_zero]
              exact Nat.zero_le (n + 1)
            ⟩ := by
              exact Subtype.coe_eq_of_eq_mk hi
            repeat rw [this]
            dsimp [f]
            rw [(h (n + 1)).choose_spec.1.1]
            rw [(h (nat_equiv.symm ↑(n + 1))).choose_spec.1.1]
          . rw [Equiv.symm_apply_eq] at hi
            have hz := z.prop
            rw [hi] at hz
            rw [Equiv.symm_apply_apply] at hz
            have : z = ⟨↑(z' + 1), by
              simp [Equiv.symm_apply_apply]
              exact Nat.le_of_lt_succ hz
            ⟩ := by
              exact Subtype.coe_eq_of_eq_mk hi
            repeat rw [this]
            dsimp [f]
            rw [(h (n + 1)).choose_spec.1.2]
            rw [(h (nat_equiv.symm ↑(n + 1))).choose_spec.1.2]
            . congr!
              have := ih ⟨z', by
                rw [nat_equiv_cast]
                exact Nat.le_of_succ_le hz
              ⟩ (by exact nat_equiv_cast _)
              dsimp [f] at this
              rw [Subtype.mk.injEq]
              rw [this]
            . rw [nat_equiv_cast]
              have zp := z.prop
              rw [hi] at zp
              simp at zp
              exact Order.lt_add_one_iff.mpr zp
            . have := z.prop
              suffices h: z' < nat_equiv.symm ↑z by
                exact Nat.lt_of_lt_of_le h this
              rw [hi]
              rw [Equiv.symm_apply_apply]
              exact lt_add_one z'
        rw [← this]
      rw [hw]
      rw [this]
      congr!
      let f_n := (h (nat_equiv.symm ↑n)).choose
      let f_n1 := (h (n + 1)).choose
      have agree : ∀ m : ℕ, (hm : m ≤ n) →
        f_n ⟨m, by simp [Equiv.symm_apply_apply]; exact hm⟩ =
        f_n1 ⟨m, by
          simp [Equiv.symm_apply_apply]
          exact Nat.le_add_right_of_le hm
        ⟩ := by
        intro m hm
        induction' m with m ih
        . -- why unfold + rw spec.1.1 doesn't work?
          have : f_n ⟨↑(0: ℕ), by
            rw [nat_equiv_cast]
            exact Nat.zero_le _
          ⟩ = c := (h (nat_equiv.symm ↑n)).choose_spec.1.1
          simp [this]
          have : f_n1 ⟨↑(0: ℕ), by
            rw [nat_equiv_cast]
            exact Nat.zero_le _
          ⟩ = c := (h (n + 1)).choose_spec.1.1
          simp [this]
        . unfold f_n f_n1
          rw [(h (nat_equiv.symm ↑n)).choose_spec.1.2]
          rw [(h (n + 1)).choose_spec.1.2]
          congr!
          . exact ih (Nat.le_of_succ_le hm)
          . exact Nat.lt_add_right 1 hm
          . rw [nat_equiv_cast]
            exact hm
      change f_n1 ⟨↑n, _⟩ = f_n ⟨↑n, _⟩
      rw [agree n (Nat.le_refl n)]
  . intro y y' h h'
    ext n
    induction' hi: nat_equiv.symm n with n' ih generalizing n
    . rw [Equiv.symm_apply_eq] at hi
      rw [nat_equiv_zero] at hi
      rw [hi]
      rw [h.1, h'.1]
    . rw [Equiv.symm_apply_eq] at hi
      have h := h.2
      have h' := h'.2
      specialize h n'
      specialize h' n'
      change n = ↑(n' + 1) at hi
      rw [← hi] at h h'
      rw [h, h']
      congr! 2
      specialize ih n'
      simp only [nat_equiv_coe_of_coe, forall_const] at ih
      rw [Subtype.mk.injEq]
      exact ih

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have f := recursion nat' (fun n n' ↦ succ n') zero
  apply existsUnique_of_exists_of_unique
  . use f.choose
    have h := choose_spec f
    obtain ⟨ ⟨ h1, h2 ⟩, h3⟩  := h
    constructor
    . rw [Function.Bijective]
      constructor
      . intro x1 x2 h
        induction' hi: nat_equiv.symm x1 with n1 ih generalizing x1 x2
        . rw [nat_equiv_symm_x_zero] at hi
          subst x1
          simp [h1] at h
          cases' hx : nat_equiv.symm x2 with n2
          . rw [nat_equiv_symm_x_zero] at hx
            exact hx.symm
          . specialize h2 n2
            exfalso
            rw [← hx] at h2
            simp only [nat_equiv_coe_of_coe'] at h2
            simp only [← h] at h2
            exact succ_ne _ h2.symm
        . rw [Equiv.symm_apply_eq] at hi
          subst x1
          cases' hi2: nat_equiv.symm x2 with n2
          have hsucc1 := h2 n1
          . rw [nat_equiv_symm_x_zero] at hi2
            subst x2
            exfalso
            simp [h1] at h
            change Exists.choose f (↑ (n1 + 1)) = zero at h
            simp [hsucc1] at h
            exact succ_ne _ h
          . rw [Equiv.symm_apply_eq] at hi2
            subst x2
            specialize @ih (nat_equiv n1) (nat_equiv n2)
            simp at ih
            -- why was it consumed in zero case?
            have hsucc1 := h2 n1
            have hsucc2 := h2 n2
            change Exists.choose f (↑(n1 + 1)) = Exists.choose f (↑(n2 + 1)) at h
            simp [hsucc1, hsucc2] at h
            have := succ_of_ne (choose f n1) (choose f n2)
            have hf := Mathlib.Tactic.Contrapose.mtr this
            have hn12feq := hf h
            have hn12eq := ih hn12feq
            rw [hn12eq]
      . intro y
        apply ind fun y ↦ ∃ a, Exists.choose f a = y
        . use (0:Nat)
        . intro n' ih
          obtain ⟨ a, ha ⟩ := ih
          use nat_equiv ((nat_equiv.symm a) + 1)
          specialize h2 (nat_equiv.symm a)
          -- change from explicit nat_equiv to natCast
          change Exists.choose f (↑(nat_equiv.symm a + 1)) = succ n'
          simp [h2]
          congr!
    . constructor
      . exact h1
      . intro n n'
        constructor
        . intro h
          specialize h2 (nat_equiv.symm n)
          simp [h2, h]
        . intro h
          specialize h2 (nat_equiv.symm n)
          simp [h2] at h
          have := succ_of_ne (choose f n) n'
          apply Mathlib.Tactic.Contrapose.mtr at this
          exact this h
  . intro g g' hg hg'
    obtain ⟨a, ha, unique_a⟩ := f
    have g_satisfies : g 0 = zero ∧ ∀ (n : ℕ), g ↑(n + 1) = succ (g ↑n) := by
      constructor
      . exact hg.2.1
      . intro n
        have := hg.2.2 n (g ↑n)
        simp at this
        rw [this]
    have g_satisfies' : g' 0 = zero ∧ ∀ (n : ℕ), g' ↑(n + 1) = succ (g' ↑n) := by
      constructor
      . exact hg'.2.1
      . intro n
        have := hg'.2.2 n (g' ↑n)
        simp at this
        rw [this]
    rw [unique_a g g_satisfies, unique_a g' g_satisfies']
end Chapter3
