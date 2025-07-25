import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

lemma nat_equiv_symm_lit {n: ℕ}: SetTheory.Set.nat_equiv.symm ofNat(n) = ofNat(n) := by
  rw [Equiv.symm_apply_eq]
  exact rfl

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  rw [EqualCard]
  have : ({0,1,2}:Set) ⊆ Nat := by
    rw [subset_def]
    intro x hx
    rw [mem_triple] at hx
    cases hx with
    | inl h =>
      rw [h]
      exact (0: Nat).prop
    | inr h_1 =>
      cases h_1 with
      | inl h =>
        rw [h]
        exact (1: Nat).prop
      | inr h_2 =>
        rw [h_2]
        exact (2: Nat).prop
  use fun x ↦ ⟨nat_equiv (((⟨x.val, this x.val x.prop⟩ : Nat) : ℕ) + 3), by
    simp only [mem_triple, nat_coe_eq_iff', Equiv.symm_apply_apply, Nat.reduceEqDiff]
    have := x.property
    rw [mem_triple] at this
    repeat rw [Equiv.symm_apply_eq]
    aesop
  ⟩
  constructor
  . intro x y hxy
    simp at hxy
    rw [Subtype.val_inj] at hxy
    simp only [EmbeddingLike.apply_eq_iff_eq, Nat.add_right_cancel_iff, Subtype.mk.injEq] at hxy
    rw [Subtype.val_inj] at hxy
    exact hxy
  . intro y
    have := y.property
    rw [mem_triple] at this
    rcases this with h3 | h4 | h5
    . use ⟨0, by rw [mem_triple]; tauto⟩
      simp only
      rw [← Subtype.val_inj]
      rw [h3]
      simp only [nat_coe_eq_iff', Equiv.symm_apply_apply, Nat.add_eq_right]
      exact nat_equiv_symm_lit
    . use ⟨1, by rw [mem_triple]; tauto⟩
      simp only
      rw [← Subtype.val_inj]
      rw [h4]
      simp only [nat_coe_eq_iff', Equiv.symm_apply_apply, Nat.add_eq_right]
      change nat_equiv.symm ⟨1, _⟩ + 3 = 1 + 3
      simp only [Nat.reduceAdd, Nat.reduceEqDiff]
      exact nat_equiv_symm_lit
    . use ⟨2, by rw [mem_triple]; tauto⟩
      simp only
      rw [← Subtype.val_inj]
      rw [h5]
      simp only [nat_coe_eq_iff', Equiv.symm_apply_apply, Nat.add_eq_right]
      change nat_equiv.symm ⟨2, _⟩ + 3 = 2 + 3
      simp only [Nat.reduceAdd, Nat.reduceEqDiff]
      exact nat_equiv_symm_lit

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  rw [EqualCard]
  use fun x ↦ ⟨ nat_equiv (2 * (x: ℕ)), by
    rw [specification_axiom'']
    use (nat_equiv (2 * nat_equiv.symm x)).prop
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, even_two, Even.mul_right]
  ⟩
  constructor
  . intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    rw [Subtype.val_inj] at hxy
    simp only [EmbeddingLike.apply_eq_iff_eq, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
      or_false] at hxy
    exact hxy
  . intro y
    have := y.property
    rw [specification_axiom''] at this
    obtain ⟨ m, hm, hmeven ⟩ := this
    use hm
    rw [← Nat.mul_two] at hmeven
    simp only [nat_equiv_coe_of_coe]
    rw [mul_comm] at hmeven
    rw [Subtype.mk.injEq]
    rw [Equiv.symm_apply_eq] at hmeven
    rw [← hmeven]

theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  rw [EqualCard]
  use id
  constructor
  . intro x y hxy
    exact hxy
  . intro x
    use x
    simp only [id_eq]

-- using Equiv is kinda cheating.
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  rw [EqualCard] at h ⊢
  obtain ⟨ f, hf ⟩ := h
  let e := Equiv.ofBijective f hf
  use e.symm
  exact Equiv.bijective e.symm

theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  rw [EqualCard] at h1 h2 ⊢
  obtain ⟨ f1, hf1 ⟩ := h1
  obtain ⟨ f2, hf2 ⟩ := h2
  let e1 := Equiv.ofBijective f1 hf1
  let e2 := Equiv.ofBijective f2 hf2
  let et := e1.trans e2
  use et
  exact Equiv.bijective et

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := {
  r := EqualCard,
  iseqv := {refl, symm, trans}
}

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.Fin_sub_nat (n: ℕ) : Fin n ⊆ nat := by
  rw [Fin]
  rw [subset_def]
  intro x h
  have := specification_axiom h
  exact this


/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  rw [has_card]
  apply Setoid.symm
  use fun x ↦ ⟨nat_equiv (((⟨x, (Fin_sub_nat _) _ x.prop⟩: Nat) : ℕ) + 1), by
    rw [specification_axiom'']
    use (nat_equiv (nat_equiv.symm ⟨↑x, _⟩ + 1)).prop
    constructor
    . simp_all only [Subtype.coe_eta, Equiv.symm_apply_apply, le_add_iff_nonneg_left, zero_le]
    . have hx := x.property
      rw [mem_Fin] at hx
      obtain ⟨ m, hm, hmn ⟩ := hx
      simp [hmn]
      change nat_equiv.symm ⟨↑m, _⟩ < n
      suffices h: nat_equiv.symm ⟨↑m, _⟩ = m by
        rw [h]
        exact hm
      rw [Equiv.symm_apply_eq]
      rfl
  ⟩
  constructor
  . intro x y hxy
    simp at hxy
    rw [Subtype.val_inj] at hxy
    simp only [EmbeddingLike.apply_eq_iff_eq, Nat.add_right_cancel_iff, Subtype.mk.injEq] at hxy
    rw [Subtype.val_inj] at hxy
    exact hxy
  . intro y
    have := y.property
    rw [specification_axiom''] at this
    obtain ⟨ m, hm, hmn ⟩ := this
    have hneq : nat_equiv.symm ⟨↑y, m⟩ ≠ 0 := by exact Nat.ne_zero_of_lt hm
    have hm := Nat.exists_eq_succ_of_ne_zero hneq
    obtain ⟨ n', hn' ⟩ := hm
    use ⟨n', by
      rw [mem_Fin]
      use n'
      simp only [and_true]
      simp_all only [Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le, ne_eq, Nat.add_eq_zero, one_ne_zero,
        and_false, not_false_eq_true]
      exact hmn
    ⟩
    simp
    rw [Subtype.mk.injEq]
    rw [Equiv.symm_apply_eq] at hn'
    rw [Subtype.mk.injEq] at hn'
    conv_rhs => rw [hn']
    simp only [Nat.succ_eq_add_one]
    rw [Subtype.val_inj]
    congr!
    rw [Equiv.symm_apply_eq]
    rfl

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card]
  rw [Fin]
  simp only [Nat.lt_one_iff]
  use fun x ↦ ⟨0, by
    rw [specification_axiom'']
    use (0:Nat).prop
    exact nat_equiv_symm_lit
  ⟩
  constructor
  . intro x y hxy
    have hx := x.property
    have hy := y.property
    rw [mem_singleton] at hx hy
    conv_rhs at hy => rw [← hx]
    rw [Subtype.val_inj] at hy
    exact hy.symm
  . intro y
    use ⟨a, by rw [mem_singleton]⟩
    simp only
    have := y.property
    rw [specification_axiom''] at this
    obtain ⟨ m, hm⟩ := this
    rw [Equiv.symm_apply_eq] at hm
    rw [Subtype.mk.injEq] at hm ⊢
    rw [hm]
    rfl

open Classical
set_option maxHeartbeats 1000000 in
theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
  (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]
  let f : ({a,b,c,d}:Set) → Fin 4 := fun x ↦
    if x.val = a then ⟨0, by rw [mem_Fin]; aesop⟩
    else if x.val = b then ⟨1, by rw [mem_Fin]; aesop⟩
      else if x.val = c then ⟨2, by rw [mem_Fin]; aesop⟩
        else (⟨3, by rw [mem_Fin]; aesop⟩: Fin 4)
  use f
  constructor
  . intro x y hxy
    have hx := x.property
    have hy := y.property
    rw [mem_quad] at hx hy
    unfold f at hxy
    rcases hx with xa | xb | xc | xd <;> aesop
  . intro y
    have hy := y.property
    rw [mem_Fin] at hy
    obtain ⟨ m, hm, hmn ⟩ := hy
    match m, hm with
    | 0, _ =>
      use ⟨a, by simp⟩
      simp [f]
      simp_all only [Nat.ofNat_pos, f]
      obtain ⟨val, property⟩ := y
      subst hmn
      simp_all only [Subtype.mk.injEq, f]
      rfl
    | 1, _ =>
      use ⟨b, by simp⟩
      simp [f]
      -- aesop needs some help here
      simp [hab.symm]
      obtain ⟨val, property⟩ := y
      rw [Subtype.mk.injEq]
      exact hmn.symm
    | 2, _ =>
      use ⟨c, by simp⟩
      simp [f]
      aesop
    | 3, _ =>
      use ⟨d, by simp⟩
      simp [f]
      aesop
    | n + 4, h =>
      exfalso
      have : ¬ n + 4 < 4 := by omega
      contradiction

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

theorem SetTheory.Set.card_fin_eq (n:ℕ) : (Fin n).has_card n := by
  rw [has_card_iff]
  use id
  exact Function.bijective_id

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0)
    rw [mem_Fin]
    use 0, (by linarith); rfl
  rw [has_card_iff] at hX
  obtain ⟨ f, hf ⟩ := hX
  rw [this] at f
  have ⟨_, bj⟩ := hf
  have := nonempty_def hnon
  obtain ⟨ x, hx ⟩ := this
  have := bj ⟨ x , hx ⟩
  obtain ⟨ m, hm ⟩ := this
  rw [this] at m
  have h1 := m.prop
  have h2 := not_mem_empty m
  contradiction

theorem SetTheory.Set.Fin_zero_empty : Fin 0 = ∅ := by
  rw [Fin]
  apply ext
  intro x
  constructor
  . intro h
    rw [specification_axiom''] at h
    obtain ⟨ m, hm, hmn ⟩ := h
  . intro h
    exfalso
    have := SetTheory.Set.nonempty_of_inhabited h
    contradiction

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  constructor
  . intro h
    rw [has_card_iff] at h
    obtain ⟨ f, hf ⟩ := h
    rw [Fin] at f
    simp at f
    rw [SetTheory.Set.eq_empty_iff_forall_notMem]
    intro x
    by_contra! hx
    have := (f ⟨x, hx⟩).property
    rw [specification_axiom''] at this
    obtain ⟨ m, hm, hmn ⟩ := this
  . intro h
    rw [has_card_iff]
    rw [Fin_zero_empty]
    subst X
    use fun x ↦ absurd x.property (by simp only [not_mem_empty, not_false_eq_true])
    rw [Function.Bijective]
    constructor
    . intro x y hxy
      exfalso
      have h := x.property
      have hneq := not_mem_empty x
      contradiction
    . intro y
      exfalso
      have h := y.property
      have hneq := not_mem_empty y
      contradiction

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof is written to follow the structure of the original text, though with some extra
  -- notations to track some coercions that are "invisible" in the human-readable proof.
  rw [has_card_iff] at hX; obtain ⟨ f, hf ⟩ := hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun y ↦ ⟨ y.val, by have := y.property; simp [X'] at this; tauto ⟩
  have := (f x).property
  rw [mem_Fin] at this; obtain ⟨ m₀, hm₀, hm₀f ⟩ := this

  set g : X' → Fin (n-1) := fun y ↦ by
    have hy := y.property
    simp [X'] at hy; obtain ⟨ hy1, hy2 ⟩ := hy
    have := (f ⟨ y.val, hy1⟩).property
    rw [mem_Fin] at this
    have ⟨ hmn, hmm ⟩ := this.choose_spec
    set m' := this.choose
    classical
    cases m'.decLt m₀ with
    | isTrue hlt =>
      exact Fin_mk _ m' (by omega)
    | isFalse hlt =>
      have : m' ≠ m₀ := by
        contrapose! hy2
        rwa [hy2,←hm₀f,Subtype.val_inj, hf.injective.eq_iff,←Subtype.val_inj] at hmm
      exact Fin_mk _ (m'-1) (by omega)

  have Xsub : X' ⊆ X := by
    rw [subset_def]
    intro y hy
    simp [X'] at hy
    exact hy.1
  have hg : Function.Bijective g := by
    constructor
    . intro y1 y2 h
      simp [g] at h
      sorry
    . intro y
      let e := Equiv.ofBijective f hf
      sorry
      -- by_cases h: y < m₀
      -- . use e.symm ⟨y, by have := y.prop; rw [mem_Fin] at this; exact Xsub y _⟩
      --   sorry
      -- . use e.symm y + 1
      --   sorry

  have : EqualCard X' (Fin (n-1)) := by use g
  exact this

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro X m h1 h2
    rw [has_card_zero] at h1; contrapose! h1
    exact pos_card_nonempty (by omega) h2
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  obtain ⟨ x, hx ⟩ := nonempty_def this
  set x':X := ⟨ x, hx ⟩
  have : m ≥ 1 := by
    by_contra! hm; simp at hm
    rw [hm, has_card_zero] at h2; contradiction
  have hc : (X \ {x'.val}).has_card (n+1-1) := card_erase (by omega) h1 x'
  have hc' : (X \ {x'.val}).has_card (m-1) := card_erase this h2 x'
  simp at hc; specialize hn hc hc'
  omega

lemma ex1 : ({0,1,2}:Set).has_card 3 := by
  rw [SetTheory.Set.has_card_iff]
  have : SetTheory.Set.Fin 3 = {0,1,2} := by
    apply SetTheory.Set.ext
    intro x
    rw [SetTheory.Set.mem_Fin]
    rw [SetTheory.Set.mem_triple]
    constructor
    . intro h
      obtain ⟨ m, hm, hmn ⟩ := h
      match m, hm with
      | 0, _ => left; exact hmn
      | 1, _ => right; left; exact hmn
      | 2, _ => right; right; exact hmn
    . intro h
      rcases h with h | h | h
      . use 0
        simp
        rw [h]
        rfl
      . use 1
        simp
        rw [h]
        rfl
      . use 2
        simp
        rw [h]
  rw [this]
  use id
  exact Function.bijective_id

lemma ex2: ({3,4}:Set).has_card 2 := by
  rw [SetTheory.Set.has_card_iff]
  have : SetTheory.Set.Fin 2 = {0,1} := by
    apply SetTheory.Set.ext
    intro x
    rw [SetTheory.Set.mem_Fin]
    rw [SetTheory.Set.mem_pair]
    constructor
    . intro h
      obtain ⟨ m, hm, hmn ⟩ := h
      match m, hm with
      | 0, _ => left; exact hmn
      | 1, _ => right; exact hmn
    . intro h
      rcases h with h | h
      . use 0
        simp
        rw [h]
        rfl
      . use 1
        simp
        rw [h]
        rfl
  rw [this]
  use fun x ↦
    if x.val = 3 then ⟨0, by rw [SetTheory.Set.mem_pair]; aesop⟩
    else ⟨1, by rw [SetTheory.Set.mem_pair]; aesop⟩
  constructor
  . intro x y hxy
    have hx := x.property
    have hy := y.property
    rw [SetTheory.Set.mem_pair] at hx hy
    cases' hx with h3 h4 <;> cases' hy with h3' h4' <;> aesop
  . intro y
    have hy := y.property
    rw [SetTheory.Set.mem_pair] at hy
    cases' hy with h3 h4 <;> aesop

example : ¬ ({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1: ({0,1,2}:Set) ≈ SetTheory.Set.Fin 3 := by exact ex1
  have h2: ({3,4}:Set) ≈ SetTheory.Set.Fin 2 := by exact ex2
  have hf : SetTheory.Set.Fin 3 ≈ SetTheory.Set.Fin 2 := h1.symm.trans (h.trans h2)
  simp [HasEquiv.Equiv, Setoid.r, SetTheory.Set.EqualCard] at hf
  rw [← SetTheory.Set.has_card_iff] at hf
  have h1' := SetTheory.Set.card_fin_eq 3
  have := SetTheory.Set.card_uniq h1' hf
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  let f' : _root_.Fin n → ℕ := (fun i ↦ nat_equiv.symm (f ⟨nat_equiv i, by rw [mem_Fin]; aesop⟩))
  let S := Finset.image f' (Finset.univ : (Finset (_root_.Fin n)))
  let M := Finset.max' S
  by_cases h: S.Nonempty
  . let M' := M h
    use M'
    simp only [Subtype.forall]
    intro x x'
    dsimp [M', M, S, f']
    apply Finset.le_max'
    simp only [Finset.mem_image, Finset.mem_univ, EmbeddingLike.apply_eq_iff_eq, true_and, S, M',
      f', M]
    rw [mem_Fin] at x'
    obtain ⟨ m, hm, hmn ⟩ := x'
    use ⟨m, hm⟩
    congr!
    subst hmn
    rfl
  . simp at h
    simp [S] at h
    simp_all
    rw [← Finset.card_eq_zero, Finset.card_fin] at h
    use 0
    intro a b
    rw [h] at b
    rw [Fin_zero_empty] at b
    have nb := not_mem_empty a
    contradiction

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  unfold infinite
  by_contra this; obtain ⟨ n, hn⟩ := this
  simp [has_card] at hn; replace hn := Setoid.symm hn
  simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  obtain ⟨ f, hf ⟩ := hn
  obtain ⟨ M, hM ⟩ := bounded_on_finite f
  replace hf := hf.surjective (M+1:ℕ)
  have : ∀ i, f i ≠ (M+1:ℕ) := by
    intro i; specialize hM i; contrapose! hM
    apply_fun nat_equiv.symm at hM
    simp_all
  contrapose! this; exact hf

/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable abbrev SetTheory.Set.card (X:Set) : ℕ := by
  classical
  exact if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card (X:Set) (n: ℕ): X.has_card n → X.card = n := by
  intro h
  rw [card]
  have hf : X.finite := by rw [finite]; use n
  simp only [hf, ↓reduceDIte]
  generalize_proofs a
  have ha := a.choose_spec
  exact card_uniq ha h

theorem SetTheory.Set.card_to_has_card (X:Set) (n: ℕ) (hn: n ≠ 0): X.card = n → X.has_card n := by
  intro h
  rw [← h]
  exact has_card_card (by
    by_contra! h0
    simp only [card, h0, ↓reduceDIte] at h
    have := h.symm
    contradiction
  )

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  obtain ⟨n, Xn⟩ := hX
  obtain ⟨f, hf⟩ := Xn
  let f': ((X ∪ {x}):Set) → Fin (n + 1) := fun z ↦ if h: z = x
    then ⟨nat_equiv n, by
      rw [mem_Fin]
      use n
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, true_and]
      rfl
    ⟩ else ⟨f ⟨z, by
      have := z.prop
      rw [mem_union] at this
      simp only [mem_singleton, h, or_false] at this
      exact this
    ⟩, by
      have := (f ⟨z, by aesop⟩).prop
      rw [mem_Fin] at this
      obtain ⟨ m, hm, hmn ⟩ := this
      rw [mem_Fin]
      use m
      constructor
      . omega
      . exact hmn
    ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro z1 z2 h
      by_cases hz1: z1 = x
      . simp [f', hz1] at h
        by_cases hz2: z2 = x
        . simp [f', hz2] at h
          rw [← Subtype.val_inj]
          rw [hz1, hz2]
        . simp [f', hz2] at h
          exfalso
          generalize_proofs a at h
          have := (f ⟨z2, a⟩).prop
          rw [mem_Fin] at this
          rw [← h] at this
          obtain ⟨ m, hm, hmn ⟩ := this
          have : n = m := by exact (ofNat_inj' n m).mp hmn
          linarith
      . simp [f', hz1] at h
        by_cases hz2: z2 = x
        . simp [f', hz2] at h
          exfalso
          generalize_proofs a at h
          have := (f ⟨z1, a⟩).prop
          rw [mem_Fin] at this
          rw [h] at this
          obtain ⟨ m, hm, hmn ⟩ := this
          have : n = m := by exact (ofNat_inj' n m).mp hmn
          linarith
        . simp [f', hz2] at h
          rw [Subtype.val_inj] at h
          have := hf.injective h
          obtain ⟨z1', hz1'⟩ := z1
          obtain ⟨z2', hz2'⟩ := z2
          simp only at this
          rw [Subtype.mk.injEq] at this ⊢
          exact this
    . intro z
      by_cases hz: z = ⟨n, by rw [mem_Fin]; use n; simp⟩
      . use ⟨x, by rw [mem_union]; right; rw [mem_singleton]⟩
        simp [f', hz]
        rfl
      . have := hf.surjective ⟨z, by
          have := z.property
          rw [mem_Fin] at this ⊢
          obtain ⟨ m, hm, hmn ⟩ := this
          have : m ≠ n := by
            contrapose! hz
            subst m
            rw [Subtype.mk.injEq]
            exact hmn
          use m
          constructor
          . omega
          . exact hmn
        ⟩
        obtain ⟨z', hz'⟩ := this
        use ⟨z', by rw [mem_union]; left; exact z'.prop⟩
        simp [f']
        have hzneqx : z'.val ≠ x := by
          intro h
          rw [← h] at hx
          have hc := z'.property
          contradiction
        simp only [hzneqx, ↓reduceDIte, f']
        simp only [hz', Subtype.coe_eta, f']
  have : (X ∪ {x}) ≈  (Fin (n + 1)) := by use f'
  have fin : (X ∪ {x}).finite := by
    rw [finite]
    use n + 1
  constructor
  . exact fin
  . have : (X ∪ {x}).has_card (n + 1) := by
      rw [has_card]
      exact this
    apply has_card_to_card at this
    rw [this]
    simp only [Nat.add_right_cancel_iff]
    symm
    apply has_card_to_card
    rw [has_card]
    use f


/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by sorry

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by sorry

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by sorry

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by sorry

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by sorry

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by sorry

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by sorry

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ^ Y).finite ∧ (X ^ Y).card = X.card ^ Y.card := by sorry

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.card_eq_zero {X:Set} (hX: X.finite) :
    X.card = 0 ↔ X = ∅ := by sorry

/-- Exercise 3.6.5 -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by sorry

/-- Exercise 3.6.6 -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

example (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry

example (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := sorry

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by sorry

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by  sorry

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by sorry

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by sorry

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by sorry

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by sorry

end Chapter3
