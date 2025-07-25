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

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

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
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

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

@[refl]
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
@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  rw [EqualCard] at h ⊢
  obtain ⟨ f, hf ⟩ := h
  let e := Equiv.ofBijective f hf
  use e.symm
  exact Equiv.bijective e.symm

@[trans]
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
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

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
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

theorem SetTheory.Set.card_fin_eq (n:ℕ) : (Fin n).has_card n := by
  rw [has_card_iff]
  use id
  exact Function.bijective_id

theorem SetTheory.Set.card_fin_eq (n:ℕ) : (Fin n).has_card n := by
  rw [has_card_iff]
  use id
  exact Function.bijective_id

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
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
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']

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

  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
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
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  sorry

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

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

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by sorry

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by sorry

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by sorry

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

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

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by sorry

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by sorry

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by sorry

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by sorry

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by sorry

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by sorry

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by sorry

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by sorry

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by sorry)
  else
    Fin_mk _ ((x:ℕ) - 1) (by sorry)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by sorry) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by sorry)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by sorry

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by sorry

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by sorry

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := sorry
    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  sorry

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by sorry

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
