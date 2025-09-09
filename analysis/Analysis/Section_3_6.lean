import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
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

  have hX'mem (y: X) (hy: y ≠ x): y.val ∈ X' := by
    unfold X'
    rw [mem_sdiff]
    constructor
    . exact y.property
    . rw [mem_singleton]
      rw [Subtype.val_inj]
      exact hy

  have hι_inj : Function.Injective ι := by
    intro x y hxy
    rw [← Subtype.val_inj] at hxy
    rw [hι x] at hxy
    rw [hι y] at hxy
    rwa [Subtype.val_inj] at hxy
  have hι_neq (x': X') : ι x' ≠ x := by
    by_contra! h
    rw [← Subtype.val_inj] at h
    rw [hι x'] at h
    have hx' := x'.property
    unfold X' at hx'
    rw [mem_sdiff] at hx'
    rw [mem_singleton] at hx'
    simp [h] at hx'
  have hg : Function.Bijective g := by
    constructor
    . intro y1 y2 h
      have hm1_ne : Fin.toNat (f (ι y1)) ≠ m₀ := by
        by_contra! h
        rw [← h] at hm₀f
        simp only [Fin.coe_toNat] at hm₀f
        rw [Subtype.val_inj] at hm₀f
        apply hf.injective at hm₀f
        specialize hι_neq y1
        symm at hm₀f
        contradiction
      have hm2_ne : Fin.toNat (f (ι y2)) ≠ m₀ := by
        by_contra! h
        rw [← h] at hm₀f
        simp only [Fin.coe_toNat] at hm₀f
        rw [Subtype.val_inj] at hm₀f
        apply hf.injective at hm₀f
        specialize hι_neq y2
        symm at hm₀f
        contradiction
      have h1e := hg_def y1
      have h2e := hg_def y2
      by_cases h1_lt : f (ι y1) < m₀
      . by_cases h2_lt : f (ι y2) < m₀
        . simp [h1_lt] at h1e
          simp [h2_lt] at h2e
          rw [h] at h1e
          rw [h1e] at h2e
          rw [Fin.toNat_inj] at h2e
          apply hf.injective at h2e
          apply hι_inj at h2e
          exact h2e
        . simp [h1_lt] at h1e
          simp [h2_lt] at h2e
          rw [h] at h1e
          rw [h1e] at h2e
          exfalso
          omega
      . by_cases h2_lt : f (ι y2) < m₀
        . simp [h1_lt] at h1e
          simp [h2_lt] at h2e
          rw [h] at h1e
          rw [h1e] at h2e
          exfalso
          omega
        . simp [h1_lt] at h1e
          simp [h2_lt] at h2e
          rw [h] at h1e
          rw [h1e] at h2e
          rw [not_lt] at h1_lt
          rw [not_lt] at h2_lt
          have h1_gt : f (ι y1) > m₀ := by exact Nat.lt_of_le_of_ne h1_lt (id (Ne.symm hm1_ne))
          have h2_gt : f (ι y2) > m₀ := by exact Nat.lt_of_le_of_ne h2_lt (id (Ne.symm hm2_ne))
          have h1nz : Fin.toNat (f (ι y1)) > 0 := by exact Nat.zero_lt_of_lt h1_gt
          have h2nz : Fin.toNat (f (ι y2)) > 0 := by exact Nat.zero_lt_of_lt h2_gt
          have := Nat.sub_one_cancel h1nz h2nz h2e
          rw [Fin.toNat_inj] at this
          apply hf.injective at this
          apply hι_inj at this
          exact this
    . intro y
      by_cases h : y < m₀
      . set hx := hf.surjective (Fin_mk _ y (by omega))
        have hx' := hx.choose_spec
        have hneq : hx.choose ≠ x := by
          by_contra! he
          rw [he] at hx'
          rw [hx'] at hm₀f
          simp only [Fin.coe_toNat] at hm₀f
          have : Fin.toNat y = m₀ := by
            rw [← Fin.coe_toNat] at hm₀f
            rwa [Object.natCast_inj] at hm₀f
          linarith
        have hx'' : hx.choose.val ∈ X' := hX'mem hx.choose hneq
        use ⟨hx.choose, hx''⟩
        specialize hg_def ⟨hx.choose, hx''⟩
        have : ι ⟨↑hx.choose, hx''⟩ = hx.choose := by rfl
        simp [this, hx', h] at hg_def
        rwa [Fin.toNat_inj] at hg_def
      .
        set hx := hf.surjective (Fin_mk _ (y + 1) (by
          have hy := Fin.toNat_lt y
          omega
        ))
        have hx' := hx.choose_spec
        have hneq : hx.choose ≠ x := by
          by_contra! he
          rw [he] at hx'
          rw [hx'] at hm₀f
          simp only [Fin.coe_toNat] at hm₀f
          have : (Fin.toNat y) + 1 = m₀ := by rwa [Object.natCast_inj] at hm₀f
          linarith
        have hx'': hx.choose.val ∈ X' := hX'mem hx.choose hneq
        use ⟨hx.choose, hx''⟩
        specialize hg_def ⟨hx.choose, hx''⟩
        have : ι ⟨↑hx.choose, hx''⟩ = hx.choose := by rfl
        have h': ¬ ((Fin.toNat y) + 1 < m₀) := by exact Mathlib.Tactic.Order.not_lt_of_not_le h
        simp [this, hx', h'] at hg_def
        rwa [Fin.toNat_inj] at hg_def
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
    simp only [Finset.mem_image, Finset.mem_univ, EmbeddingLike.apply_eq_iff_eq, true_and]
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
    intro a b hab
    rw [h] at hab
    omega

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

theorem SetTheory.Set.has_card_to_card (X:Set) (n: ℕ): X.has_card n → X.card = n := by
  intro h; have hf : X.finite := ⟨ n, h ⟩
  simp [card, hf, card_uniq hf.choose_spec h]

theorem SetTheory.Set.card_to_has_card (X:Set) {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n := by
  rintro rfl; apply has_card_card
  contrapose! hn; simp [card, hn]

theorem SetTheory.Set.card_to_has_card_fin (X:Set) {n: ℕ} (hfin: X.finite): X.card = n → X.has_card n := by
  rintro rfl
  exact has_card_card hfin

theorem SetTheory.Set.Fin_card (n:ℕ) : (Fin n).card = n := by
  exact has_card_to_card _ _ (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ) : (Fin n).finite := by
  exact ⟨n, card_fin_eq n⟩

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

theorem SetTheory.Set.card_zero {X:Set}: X = ∅ → X.card = 0 := by
  intro h
  have hX := SetTheory.Set.has_card_zero.mpr h
  apply has_card_to_card
  exact hX

theorem SetTheory.Set.card_singleton (x:Object) : ({x}:Set).card = 1 := by
  rw [card]
  have hX := Example_3_6_7a x
  exact has_card_to_card _ _ hX

theorem SetTheory.Set.singleton_finite (x:Object) : ({x}:Set).finite := by
  use 1
  exact Example_3_6_7a x

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
        simp only [hzneqx, ↓reduceDIte]
        simp only [hz', Subtype.coe_eta]
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
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  obtain ⟨n, hX⟩ := hX
  obtain ⟨m, hY⟩ := hY
  induction' n with n hn generalizing X
  . rw [has_card_zero] at hX
    subst hX
    have : ∅ ∪ Y = Y := by
      apply SetTheory.Set.ext
      intro x
      rw [mem_union]
      have : (x ∈ (∅:Set)) = False := by
        simp [not_mem_empty x]
      simp only [this, false_or]
    repeat rw [this]
    constructor
    . exact ⟨m, hY⟩
    . rw [card_zero rfl]
      exact Nat.le_add_left Y.card 0
  . have := pos_card_nonempty (by simp) hX
    have := nonempty_def this
    obtain ⟨ x, hx ⟩ := this
    set X' := X \ {x}
    have hX' : X'.has_card n := by
      dsimp [X']
      apply card_erase (by omega) hX ⟨x, hx⟩
    specialize hn hX'
    by_cases hxY: x ∈ Y
    . have : (X' ∪ Y) = X ∪ Y := by
        dsimp [X']
        apply ext
        intro z
        rw [mem_union, mem_union, mem_sdiff, mem_singleton]
        constructor
        . intro h
          obtain ⟨ h1, h2 ⟩ := h
          left
          . exact h1
          . right
            assumption
        . intro h
          cases' h with h1 h2
          . by_cases hxz : z = x
            . right
              subst z
              exact hxY
            . left
              constructor
              . exact h1
              . exact hxz
          . right
            assumption
      rw [this] at hn
      constructor
      . exact hn.1
      . apply hn.2.trans
        simp only [add_le_add_iff_right]
        have h1 := has_card_to_card _ _ hX
        have h2 := has_card_to_card _ _ hX'
        rw [h1, h2]
        exact Nat.le_add_right _ _
    . have hneq : x ∉ (X' ∪ Y) := by aesop
      have hin : (X' ∪ Y) ∪ {x} = X ∪ Y := by
        apply ext
        intro z
        rw [mem_union, mem_union, mem_singleton, mem_union]
        constructor
        . intro h
          cases' h with h1 h2
          . cases' h1 with h11 h12
            . dsimp [X'] at h11
              rw [mem_sdiff] at h11
              left
              exact h11.1
            . right
              exact h12
          . subst z
            left
            exact hx
        . intro h
          cases' h with h1 h2
          . by_cases hxz : z = x
            . subst z
              right
              rfl
            . left
              left
              dsimp [X']
              rw [mem_sdiff, mem_singleton]
              constructor
              . exact h1
              . exact hxz
          . left
            right
            exact h2
      have := card_insert hn.1 hneq
      rw [hin] at this
      constructor
      . exact this.1
      . rw [this.2]
        calc
          (X' ∪ Y).card + 1 ≤ X'.card + Y.card + 1 := by
            simp only [add_le_add_iff_right]
            exact hn.2
          _ = X.card + Y.card := by
            have h1 := has_card_to_card _ _ hX
            have h2 := has_card_to_card _ _ hX'
            rw [h1, h2]
            omega
          _ ≤ X.card + Y.card := by exact Nat.le_refl (X.card + Y.card)

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  -- copy/paste from previous theorem, but with the disjointness condition removed.
  -- todo - swap the order and reuse this. Might need some extra lemmas though.
  -- like subset of finite is finite.
  obtain ⟨n, hX⟩ := hX
  obtain ⟨m, hY⟩ := hY
  induction' n with n hn generalizing X
  . rw [has_card_zero] at hX
    subst hX
    have : ∅ ∪ Y = Y := by
      apply SetTheory.Set.ext
      intro x
      rw [mem_union]
      have : (x ∈ (∅:Set)) = False := by
        simp [not_mem_empty x]
      simp only [this, false_or]
    repeat rw [this]
    simp only [Nat.right_eq_add]
    rw [card_zero rfl]
  . have := pos_card_nonempty (by simp) hX
    have := nonempty_def this
    obtain ⟨ x, hx ⟩ := this
    set X' := X \ {x}
    have hX' : X'.has_card n := by
      dsimp [X']
      apply card_erase (by omega) hX ⟨x, hx⟩
    have : x ∉ Y := by
      rw [disjoint_iff] at hdisj
      rw [eq_empty_iff_forall_notMem] at hdisj
      specialize hdisj x
      rw [mem_inter] at hdisj
      push_neg at hdisj
      exact hdisj hx
    specialize hn (by
      dsimp [X']
      rw [disjoint_iff]
      rw [eq_empty_iff_forall_notMem]
      intro x'
      rw [mem_inter, mem_sdiff, mem_singleton]
      push_neg
      intro h
      rw [disjoint_iff] at hdisj
      rw [eq_empty_iff_forall_notMem] at hdisj
      specialize hdisj x'
      contrapose! hdisj
      rw [mem_inter]
      constructor
      . exact h.1
      . exact hdisj
    ) hX'
    . have hneq : x ∉ (X' ∪ Y) := by aesop
      have hin : (X' ∪ Y) ∪ {x} = X ∪ Y := by
        apply ext
        intro z
        rw [mem_union, mem_union, mem_singleton, mem_union]
        constructor
        . intro h
          cases' h with h1 h2
          . cases' h1 with h11 h12
            . dsimp [X'] at h11
              rw [mem_sdiff] at h11
              left
              exact h11.1
            . right
              exact h12
          . subst z
            left
            exact hx
        . intro h
          cases' h with h1 h2
          . by_cases hxz : z = x
            . subst z
              right
              rfl
            . left
              left
              dsimp [X']
              rw [mem_sdiff, mem_singleton]
              constructor
              . exact h1
              . exact hxz
          . left
            right
            exact h2
      -- todo: simplify this proof
      have hx'ufin : (X' ∪ Y).finite := by
        by_contra! h0
        have : (X' ∪ Y).card = 0 := by
          rw [card]
          simp only [h0, ↓reduceDIte]
        rw [this] at hn
        have hXc := has_card_to_card _ _ hX'
        have hYc := has_card_to_card _ _ hY
        rw [hXc, hYc] at hn
        symm at hn
        rw [Nat.add_eq_zero] at hn
        obtain ⟨ hn0, hn1 ⟩ := hn
        rw [hn0] at hX'
        rw [hn1] at hY
        rw [has_card_zero] at hX' hY
        rw [hX', hY] at h0
        have : ∅ ∪ ∅ = (∅:Set) := by
          apply SetTheory.Set.ext
          intro x
          rw [mem_union]
          simp only [not_mem_empty, or_self]
        rw [this] at h0
        have : (∅:Set).finite := by
          rw [finite]
          use 0
          exact has_card_zero.mpr rfl
        contradiction
      have := card_insert hx'ufin hneq
      rw [hin] at this
      rw [this.2]
      calc
        (X' ∪ Y).card + 1 = X'.card + Y.card + 1 := by
          simp only [Nat.add_right_cancel_iff]
          exact hn
        _ = X.card + Y.card := by
          have h1 := has_card_to_card _ _ hX
          have h2 := has_card_to_card _ _ hX'
          rw [h1, h2]
          omega

/--
  The proof roughly goes as follows:
  - use induction on `n`
  - for the induction step, use cases on whether `f` is surjective or not
  - if `f` is not surjective, then we can find a gap in the range of `f` and define f'
    to map that gap to the value `n` and use induction on `n`.
  - if `f` is surjective, then it is already the bijection.

  todo: Clean up the proof, it is a bit messy.
-/
lemma SetTheory.Set.Fin_injective_to_subset_bijective {n:ℕ} (X:Set)
    (f: X → Fin n) (hf: Function.Injective f):
    ∃ m: ℕ, m ≤ n ∧ ∃ g: X → Fin m, Function.Bijective g := by
  induction' n with n hn generalizing X
  . use 0
    constructor
    . rfl
    . use f
      constructor
      . exact hf
      . intro x
        rw [SetTheory.Set.Fin_zero_empty] at x
        have h := x.property
        have neq := not_mem_empty x
        exfalso
        contradiction
  .
    by_cases hfsur: ¬ Function.Surjective f
    . rw [Function.Surjective] at hfsur
      push_neg at hfsur
      obtain ⟨ m, hmn ⟩ := hfsur
      by_cases h: ∃ x: X, (f x).val = nat_equiv n
      -- same as f, but map x to the gap m to pack it in Fin n and use induction
      . obtain ⟨ x, hxf ⟩ := h
        have hmneq : m.val ≠ nat_equiv n := by
          rw [← hxf]
          specialize hmn x
          contrapose! hmn
          rw [Subtype.val_inj] at hmn
          exact hmn.symm
        let f' : X → Fin n := fun x' ↦
          if h: x' = x then ⟨m, by
            have := m.prop
            rw [mem_Fin] at this ⊢
            obtain ⟨ m', hm', hmn' ⟩ := this
            use m'
            constructor
            . by_cases hmneq: m' = n
              . exfalso
                subst m'
                contradiction
              . omega
            . exact hmn'
          ⟩ else ⟨f x', by
            by_cases hmn: (f x').val = (nat_equiv n)
            . rw [← hxf] at hmn
              rw [Subtype.val_inj] at hmn
              apply hf at hmn
              contradiction
            . have := (f x').property
              rw [mem_Fin] at this ⊢
              obtain ⟨ m', hm', hmn' ⟩ := this
              by_cases hmneq: m' = n
              . subst n
                contradiction
              . use m'
                constructor
                . omega
                . exact hmn'
          ⟩
        have hf' : Function.Injective f' := by
          intro x1 x2 h
          simp only [f'] at h
          by_cases hx1: x1 = x
          . by_cases hx2: x2 = x
            . rw [Subtype.mk.injEq]
              rw [hx1, hx2]
            . simp [hx1, hx2] at h
              exfalso
              subst x
              specialize hmn x2
              rw [Subtype.val_inj] at h
              rw [h] at hmn
              contradiction
          . by_cases hx2: x2 = x
            . simp [hx1, hx2] at h
              subst x
              specialize hmn x1
              rw [Subtype.val_inj] at h
              rw [← h] at hmn
              exfalso
              simp at hmn
            . simp [hx1, hx2] at h
              apply hf
              rw [Subtype.val_inj] at h
              exact h
        specialize hn X f' hf'
        obtain ⟨m, hm, g, hg⟩ := hn
        use m
        constructor
        . exact Nat.le_add_right_of_le hm
        . use g
      . push_neg at h
        let f': X → Fin n := fun x ↦ ⟨(f x).val, by
          specialize h x
          simp at h
          have := (f x).property
          rw [mem_Fin] at this
          obtain ⟨ m, hm, hmn ⟩ := this
          rw [mem_Fin]
          use m
          constructor
          . by_cases hmneq: m = n
            . exfalso
              subst m
              contradiction
            . omega
          . exact hmn
        ⟩
        have hf' : Function.Injective f' := by
          intro x1 x2 h
          simp [f'] at h
          apply hf
          rw [Subtype.val_inj] at h
          exact h
        specialize hn X f' hf'
        obtain ⟨m, hm, g, hg⟩ := hn
        use m
        constructor
        . exact Nat.le_add_right_of_le hm
        . use g
    . push_neg at hfsur
      use (n + 1)
      constructor
      . rfl
      . use f
        constructor
        . exact hf
        . exact hfsur

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  obtain ⟨n, hX⟩ := hX
  have hX' := hX
  rw [has_card_iff] at hX
  obtain ⟨f, hf⟩ := hX
  let f': Y → Fin n := fun y ↦ f ⟨y, hY _ y.prop⟩
  have hf'Inj : Function.Injective f' := by
    intro y1 y2 h
    simp only [f'] at h
    apply hf.injective at h
    simp only [Subtype.mk.injEq] at h
    rw [Subtype.val_inj] at h
    exact h
  have := Fin_injective_to_subset_bijective Y f' hf'Inj
  obtain ⟨m, hm, g, hg⟩ := this
  have card_eq : Y.has_card m := by
    rw [has_card_iff]
    use g
  constructor
  . use m
  . have card_eq' := has_card_to_card _ _ card_eq
    rw [card_eq']
    have h1 := has_card_to_card _ _ hX'
    rw [h1]
    exact hm

theorem SetTheory.Set.subset_diff_empty_eq {X Y:Set} (hX: Y ⊆ X) (hd: X \ Y = ∅) :
    X = Y := by
  apply ext
  intro x
  constructor
  . intro hx
    rw [eq_empty_iff_forall_notMem] at hd
    specialize hd x
    contrapose! hd
    rw [mem_sdiff]
    constructor
    . exact hx
    . exact hd
  . intro hx
    exact hX _ hx

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  let X' := X \ Y
  have disj : Disjoint Y X' := by
    rw [disjoint_iff]
    dsimp [X']
    rw [eq_empty_iff_forall_notMem]
    intro x
    by_contra h
    rw [mem_inter] at h
    rw [mem_sdiff] at h
    tauto
  have hu : X' ∪ Y = X := by
    apply SetTheory.Set.ext
    intro x
    dsimp [X']
    rw [mem_union, mem_sdiff]
    constructor
    . intro h
      cases' h with h1 h2
      . exact h1.1
      . exact hY.1 _ h2
    . intro h
      by_cases hy: x ∈ Y
      . right
        exact hy
      . left
        constructor
        . exact h
        . exact hy
  have hX'sub : X' ⊆ X := by
    dsimp [X']
    intro z hz
    rw [mem_sdiff] at hz
    exact hz.1
  have hX' := SetTheory.Set.card_subset hX hX'sub
  have hY' := SetTheory.Set.card_subset hX hY.1
  have := SetTheory.Set.card_union_disjoint hY'.1 hX'.1 disj
  rw [union_comm, hu] at this
  rw [this]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  by_contra h
  have hz : X'.card = 0 := by aesop
  have hz' : X'.has_card 0 := by
    have := has_card_card hX'.1
    rw [hz] at this
    exact this
  rw [has_card_zero] at hz'
  dsimp [X'] at hz'
  apply subset_diff_empty_eq hY.1 at hz'
  rw [hz'] at hY
  have hY' := hY.2
  contradiction

/--
  Using `Function.surjInv` requires axiom of choice.
  Todo: prove without using Function.surjInv.
-/
lemma SetTheory.Set.Fin_surjective_from_subset_bijective {n:ℕ} {X:Set}
    (f: Fin n → X) (hf: Function.Surjective f):
    ∃ m: ℕ, m ≤ n ∧ ∃ g: X → Fin m, Function.Bijective g := by
  let f_inv : X → Fin n := Function.surjInv hf
  have f_inv_inj := Function.injective_surjInv hf
  exact Fin_injective_to_subset_bijective X f_inv f_inv_inj

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  obtain ⟨n, hX⟩ := hX
  have hX' := hX
  obtain ⟨g, hg⟩ := hX
  let f': X → image f X := fun x ↦ ⟨f x, by
    rw [mem_image]
    use x
    constructor
    . exact x.prop
    . exact rfl
  ⟩
  have hf' : Function.Surjective f' := by
    intro y
    have := y.prop
    rw [mem_image] at this
    obtain ⟨x, hx, hfx⟩ := this
    use x
    rw [Subtype.mk.injEq]
    exact hfx
  have e := Equiv.ofBijective g hg
  let fc := f' ∘ e.symm
  have hfcSurj : Function.Surjective fc := by
    dsimp [fc]
    apply Function.Surjective.comp
    . exact hf'
    . exact e.symm.surjective
  have := Fin_surjective_from_subset_bijective fc hfcSurj
  obtain ⟨m, hm, g', hg'⟩ := this
  have hIm : (image f X).has_card m := by
    rw [has_card_iff]
    use g'
  have h1 := has_card_to_card _ _ hX'
  have h2 := has_card_to_card _ _ hIm
  constructor
  . exact Exists.intro m hIm
  . rw [h1, h2]
    exact hm

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
  -- copy/paste from previous theorem, but with the injectivity condition added
  obtain ⟨n, hX⟩ := hX
  have hX' := hX
  obtain ⟨g, hg⟩ := hX
  let f': X → image f X := fun x ↦ ⟨f x, by
    rw [mem_image]
    use x
    constructor
    . exact x.prop
    . exact rfl
  ⟩
  have hf' : Function.Surjective f' := by
    intro y
    have := y.prop
    rw [mem_image] at this
    obtain ⟨x, hx, hfx⟩ := this
    use x
    rw [Subtype.mk.injEq]
    exact hfx
  have hf'inj : Function.Injective f' := by
    intro y1 y2 h
    simp only [f'] at h
    simp at h
    apply hf
    rw [Subtype.mk.injEq]
    exact h
  have e := Equiv.ofBijective g hg
  let fc := f' ∘ e.symm
  have hfcSurj : Function.Surjective fc := by
    dsimp [fc]
    apply Function.Surjective.comp
    . exact hf'
    . exact e.symm.surjective
  -- different from here on
  have hfcInj : Function.Injective fc := by
    apply Function.Injective.comp
    . exact hf'inj
    . exact e.symm.injective
  have hf'bij : Function.Bijective fc := by
    constructor
    . exact hfcInj
    . exact hfcSurj
  have e' := Equiv.ofBijective fc hf'bij
  have : (image f X).has_card n := by
    rw [has_card_iff]
    use e'.symm
    exact e'.symm.bijective
  have h1 := has_card_to_card _ _ hX'
  have h2 := has_card_to_card _ _ this
  rw [h1, h2]

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  obtain ⟨n, hX⟩ := hX
  obtain ⟨m, hY⟩ := hY
  have hX' := hX
  have hY' := hY
  obtain ⟨fX, hfX⟩ := hX
  obtain ⟨fY, hfY⟩ := hY
  have hmn : (X ×ˢ Y).has_card (n * m) := by
    rw [has_card_iff]
    use fun p: X ×ˢ Y ↦
      let x := fX (fst p)
      let y := fY (snd p)
      let x' := Classical.choose ((mem_Fin _ x).mp x.prop)
      let y' := Classical.choose ((mem_Fin _ y).mp y.prop)
      ⟨x' * m + y', by
        rw [mem_Fin]
        use x' * m + y'
        have xs := Classical.choose_spec ((mem_Fin _ x).mp x.prop)
        have ys := Classical.choose_spec ((mem_Fin _ y).mp y.prop)
        constructor
        . calc
            x' * m + y' < x' * m + m := by
              simp only [add_lt_add_iff_left]
              exact ys.1
            _ = (x' + 1) * m := by exact Eq.symm (Nat.succ_mul x' m)
            _ ≤ n * m := by
              have (a b c: ℕ): a ≤ b → a * c ≤ b * c := by intro h; exact Nat.mul_le_mul_right _ h
              apply this
              suffices x' < n by omega
              exact xs.1
        . rfl
      ⟩
    constructor
    . intro a b h
      simp at h
      generalize_proofs xa ya xb yb at h
      have xas := Classical.choose_spec xa
      have yas := Classical.choose_spec ya
      have xbs := Classical.choose_spec xb
      have ybs := Classical.choose_spec yb
      have hmy1: choose ya % m = choose ya := Nat.mod_eq_of_lt yas.1
      have hmy2: choose yb % m = choose yb := Nat.mod_eq_of_lt ybs.1
      have h_mod := congr_arg (· % m) h
      simp at h_mod
      rw [hmy1, hmy2] at h_mod
      have yeq := h_mod
      rw [yeq] at h
      simp at h
      rw [← mk_cartesian_fst_snd_eq a]
      rw [← mk_cartesian_fst_snd_eq b]
      rw [mk_cartesian_inj]
      constructor
      . apply hfX.injective
        rw [Subtype.mk.injEq]
        rw [xas.2, xbs.2]
        cases' h with h h'
        . rw [h]
        . exfalso
          omega
      . apply hfY.injective
        rw [Subtype.mk.injEq]
        rw [yas.2, ybs.2]
        rw [yeq]
    . intro z
      have := z.property
      rw [mem_Fin] at this
      obtain ⟨ k, hk, hkm ⟩ := this
      let x := k / m
      let y := k % m
      obtain ⟨x', hx'⟩ := hfX.surjective ⟨x, by
        rw [mem_Fin]
        use k / m
        constructor
        . rw [mul_comm] at hk
          apply Nat.div_lt_of_lt_mul hk
        . dsimp [x]
      ⟩
      obtain ⟨y', hy'⟩ := hfY.surjective ⟨y, by
        rw [mem_Fin]
        use k % m
        constructor
        . apply Nat.mod_lt k
          by_contra hm0
          simp at hm0
          rw [hm0] at hk
          contradiction
        . dsimp [y]
      ⟩
      use mk_cartesian x' y'
      simp
      rw [Subtype.mk.injEq]
      rw [hkm]
      simp only [Object.natCast_inj, x, y]
      generalize_proofs a b
      have hxa := (Classical.choose_spec a).2
      have hya := (Classical.choose_spec b).2
      conv_lhs at hxa => rw [hx']
      conv_lhs at hya => rw [hy']
      simp only [Object.natCast_inj, x, y] at hxa hya
      rw [← hxa, ← hya]
      exact Nat.div_add_mod' k m
  constructor
  . rw [finite]
    use n * m
  . have h1 := has_card_to_card _ _ hX'
    have h2 := has_card_to_card _ _ hY'
    have h' := has_card_to_card _ _ hmn
    rw [h1, h2, h']


def empty_fn {X: Set} [SetTheory] : (∅:Set) → X := fun x ↦
  absurd x.prop (SetTheory.emptyset_mem x)

lemma SetTheory.Set.empty_pow_inhabited (X: Set) : ∃ a, a ∈ X ^ (∅:Set) := by
  let F := function_to_object (∅: Set) X empty_fn
  have hF : F ∈ X ^ (∅:Set) := by
    rw [powerset_axiom]
    use empty_fn
    rfl
  use F

lemma SetTheory.Set.empty_fn_unique {X: Set} (f g: (∅:Set) → X) :
    f = g := by
  ext x
  have := x.prop
  have ne := not_mem_empty x
  contradiction

omit [SetTheory] in
lemma le_lemma {a b m n: ℕ} (ha: a < m) (hb: b < n) :
    a * n + b < m * n := by
  calc a * n + b < a * n + n := by apply Nat.add_lt_add_left hb _
    _ = (a + 1) * n := by rw [Nat.succ_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt ha)

omit [SetTheory] in
lemma div_lemma {a b c d n: ℕ} (hb: b < n) (hd: d < n)
    (h: a * n + b = c * n + d) : a = c ∧ b = d := by
  have h1 := Nat.mod_eq_of_lt hb
  have h2 := Nat.mod_eq_of_lt hd
  -- reduce mod n
  have h_mod := congrArg (· % n) h
  simp at h_mod
  rw [h1, h2] at h_mod
  subst b
  simp at h
  cases' h with h1 h2
  . constructor
    . exact h1
    . rfl
  . subst n
    contradiction

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ^ Y).finite ∧ (X ^ Y).card = X.card ^ Y.card := by
  obtain ⟨n, hX⟩ := hX
  obtain ⟨m, hY⟩ := hY
  have hX' := hX
  have hY' := hY
  obtain ⟨fX, hfX⟩ := hX
  obtain ⟨fY, hfY⟩ := hY
  have hnm : (X ^ Y).has_card (n ^ m) := by
    induction' m with m ih generalizing Y
    . rw [has_card_zero] at hY'
      rw [hY']
      by_cases hn: n = 0
      . simp [hn]
        rw [hn] at hX'
        rw [has_card_zero] at hX'
        rw [hX']
        rw [has_card_iff]
        use fun _ ↦ ⟨0, by rw [mem_Fin]; use 0; aesop⟩
        constructor
        . intro x y h
          have xp := x.property
          have yp := y.property
          rw [powerset_axiom] at xp yp
          obtain ⟨x', hx'⟩ := xp
          obtain ⟨y', hy'⟩ := yp
          rw [Subtype.mk.injEq]
          rw [← hx', ← hy']
          suffices x' = y' by exact congrArg coe_of_fun this
          ext z
          exfalso
          have zp := z.property
          have zpn := not_mem_empty z
          contradiction
        . intro x
          have xp := x.property
          rw [mem_Fin] at xp
          obtain ⟨x', hx'⟩ := xp
          simp at hx'
          obtain ⟨x'', hx''⟩ := hx'
          subst x''
          simp only [Subtype.exists]
          obtain ⟨a, ha⟩ := empty_pow_inhabited ∅
          use a, ha
          rw [Subtype.mk.injEq]
          exact hx''.symm
      . simp [hn]
        have := pos_card_nonempty (by exact Nat.one_le_iff_ne_zero.mpr hn) hX'
        apply nonempty_def at this
        obtain ⟨x, hx⟩ := this
        rw [has_card_iff]
        use fun F ↦ ⟨0, by rw [mem_Fin]; use 0; aesop⟩
        constructor
        . intro x y h
          have xp := x.property
          have yp := y.property
          rw [powerset_axiom] at xp yp
          obtain ⟨x', hx'⟩ := xp
          obtain ⟨y', hy'⟩ := yp
          have := empty_fn_unique x' y'
          rw [this] at hx'
          rw [hx'] at hy'
          rw [Subtype.mk.injEq]
          exact hy'
        . intro z
          let F := function_to_object (∅: Set) X empty_fn
          have hF : F ∈ X ^ (∅:Set) := by
            rw [powerset_axiom]
            use empty_fn
            rfl
          use ⟨F, hF⟩
          simp only [F]
          have zp := z.property
          rw [mem_Fin] at zp
          simp at zp
          symm
          rw [← Subtype.val_inj]
          exact zp
    . have := hfY.surjective ⟨m, by rw [mem_Fin]; use m; aesop⟩
      obtain ⟨y, hy⟩ := this
      let Y' := Y \ {y.val}
      have hY' : Y'.has_card m := card_erase (by omega) hY' y
      have hY'' := hY'
      obtain ⟨fY', hfY'⟩ := hY'
      specialize ih hY'' fY' hfY'
      rw [has_card_iff] at ih
      obtain ⟨gY, hgY⟩ := ih
      -- we have a function g that gives a count for Y' -> X
      -- to count function f in Y -> X, we count the inferred f' in Y' -> X
      -- and multiply the value for f y through the X bijection
      let f: (X ^ Y: Set) → Fin (n ^ (m + 1)) := fun F ↦
        have hF := F.property
        have := (powerset_axiom F).mp hF
        let g := Classical.choose this
        let x' := g y
        let f': Y' → X := fun y' ↦ g ⟨y', by aesop⟩
        let F' := function_to_object Y' X f'
        have hF' : F' ∈ X ^ Y' := by
          rw [powerset_axiom]
          use f'
          dsimp [F']
          rfl
        -- count from the induction
        let cf' := gY ⟨F', hF'⟩
        -- count from y
        let cy := fX x'
        have cf'p := cf'.property
        have cyp := cy.property
        have hcf' := (mem_Fin _ cf').mp cf'p
        have hcyp := (mem_Fin _ cy).mp cyp
        ⟨Classical.choose hcf' * n + Classical.choose hcyp, by
          have hcf's := Classical.choose_spec hcf'
          have hcys := Classical.choose_spec hcyp
          rw [mem_Fin]
          use Classical.choose hcf' * n + Classical.choose hcyp
          constructor
          . rw [pow_succ]
            exact le_lemma hcf's.1 hcys.1
          . rfl
        ⟩
      use f
      constructor
      . intro F1 F2 h
        unfold f at h
        simp at h
        generalize_proofs a b c d e f' g h' i at h
        have ha := Classical.choose_spec a
        have hd := Classical.choose_spec d
        have he := Classical.choose_spec e
        have hf' := Classical.choose_spec f'
        have hh' := Classical.choose_spec h'
        have hi := Classical.choose_spec i
        apply div_lemma he.1 hi.1 at h
        rw [Subtype.mk.injEq]
        rw [← hf', ← ha]
        simp at hh'
        repeat rw [coe_of_fun]
        rw [object_of_inj]
        ext z
        by_cases hz: z = y
        . rw [hz]
          rw [Subtype.val_inj]
          apply hfX.injective
          rw [Subtype.mk.injEq]
          rw [he.2, hi.2]
          simp only [Object.natCast_inj]
          exact h.2
        . have hd' := hd.2
          have hh'' := hh'.2
          have := h.1
          rw [← Object.natCast_inj] at this
          rw [← hh'', ← hd'] at this
          rw [Subtype.val_inj] at this
          apply hgY.injective at this
          rw [← Subtype.val_inj] at this
          simp only at this
          rw [object_of_inj] at this
          have := congrFun this ⟨z, by
            dsimp [Y']
            rw [mem_sdiff]
            constructor
            . exact z.property
            . intro h
              rw [mem_singleton] at h
              rw [Subtype.val_inj] at h
              contradiction
          ⟩
          simp only [Subtype.coe_eta] at this
          rw [Subtype.val_inj]
          exact this
      . intro z
        have zp := z.property
        rw [mem_Fin] at zp
        obtain ⟨k, hk, hkm⟩ := zp
        have hnz : n > 0 := by
          by_contra! hnz
          simp at hnz
          rw [hnz] at hk
          contradiction
        let xs := k % n
        let ys := k / n
        obtain ⟨x', hx'⟩ := hfX.surjective ⟨xs, by
          rw [mem_Fin]
          use xs
          constructor
          . dsimp [xs]
            exact Nat.mod_lt k hnz
          . rfl
        ⟩
        obtain ⟨fy', hfy'⟩ := hgY.surjective ⟨ys, by
          rw [mem_Fin]
          use ys
          constructor
          . dsimp [ys]
            rw [pow_succ] at hk
            rw [mul_comm] at hk
            exact Nat.div_lt_of_lt_mul hk
          . rfl
        ⟩
        have fy'p := fy'.property
        rw [powerset_axiom] at fy'p
        obtain ⟨g', hg'⟩ := fy'p
        let fs := (fun y'' ↦
          if hy: y'' = y then x' else g' ⟨y''.val, by
            dsimp [Y']
            rw [mem_sdiff]
            constructor
            . exact y''.property
            . intro h
              rw [mem_singleton] at h
              rw [Subtype.val_inj] at h
              contradiction
          ⟩)
        let Fs := function_to_object Y X fs
        have hF : Fs ∈ X ^ Y := by
          rw [powerset_axiom]
          use fs
          rfl
        use ⟨Fs, hF⟩
        simp only [Fs, fs, f]
        generalize_proofs a b c d e f' g
        rw [← Subtype.val_inj]
        rw [hkm]
        simp only [Object.natCast_inj, Fs, fs, f]
        have hb := Classical.choose_spec b
        rw [coe_of_fun] at hb
        rw [object_of_inj] at hb
        have he1 : choose e = ys := by
          have he := (Classical.choose_spec e).2
          rw [← Object.natCast_inj]
          rw [← he]
          simp [hb]
          rw [← Subtype.val_inj] at hfy'
          simp at hfy'
          rw [← hfy']
          congr!
          rw [← hg']
          rw [coe_of_fun]
          rw [object_of_inj]
          ext yt
          have hyt := yt.property
          dsimp [Y'] at hyt
          rw [mem_sdiff] at hyt
          have := hyt.2
          rw [mem_singleton] at this
          rw [if_neg]
          contrapose! this
          rw [← Subtype.val_inj] at this
          simp at this
          exact this
        have hf'1 : choose f' = xs := by
          have hf' := (Classical.choose_spec f').2
          rw [← Object.natCast_inj]
          rw [← hf']
          rw [hb]
          simp only [↓reduceDIte, ys, xs, Y', fs, f, Fs]
          rw [hx']
        rw [he1, hf'1]
        simp [xs, ys]
        exact Nat.div_add_mod' k n
  constructor
  . rw [finite]
    use n ^ m
  . have h1 := has_card_to_card _ _ hX'
    have h2 := has_card_to_card _ _ hY'
    have h' := has_card_to_card _ _ hnm
    rw [h1, h2, h']

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.card_eq_zero {X:Set} (hX: X.finite) :
    X.card = 0 ↔ X = ∅ := by
  constructor
  . intro h
    rw [card] at h
    simp [hX] at h
    generalize_proofs a at h
    have := Classical.choose_spec a
    simp [h] at this
    rw [has_card_zero] at this
    exact this
  . intro h
    rw [h]
    rw [card_zero rfl]

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  rw [EqualCard]
  use fun p: A ×ˢ B ↦ mk_cartesian (snd p) (fst p)
  constructor
  . intro p q h
    simp only at h
    rw [mk_cartesian_inj] at h
    rw [← cart_fst_snd_ext]
    tauto
  . intro p
    use mk_cartesian (snd p) (fst p)
    simp only [snd_of_mk_cartesian, fst_of_mk_cartesian, mk_cartesian_fst_snd_eq]

/-- Exercise 3.6.6 -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  rw [EqualCard]
  let f : (((A ^ B) ^ C): Set) → ((A ^ (B ×ˢ C)):Set) := fun F ↦
    fn_to_powerset (fun x ↦
    let f := Classical.choose ((powerset_axiom F).mp F.property)
    let F' := f (snd x)
    let f' := Classical.choose ((powerset_axiom F').mp F'.property)
    f' (fst x))
  use f
  constructor
  . intro F1 F2 h
    unfold f at h
    simp at h
    generalize_proofs a b c d at h
    have ha := Classical.choose_spec a
    have hc := Classical.choose_spec c
    rw [Subtype.mk.injEq]
    rw [← ha, ← hc]
    simp only [coe_of_fun_inj]
    ext c'
    rw [Subtype.val_inj]
    have hl := (choose a c').prop
    have hr := (choose c c').prop
    rw [powerset_axiom] at hl hr
    obtain ⟨f, hf⟩ := hl
    obtain ⟨f', hf'⟩ := hr
    suffices f = f' by
      rw [← coe_of_fun_inj] at this
      rw [hf, hf'] at this
      rw [Subtype.val_inj] at this
      exact this
    ext b'
    specialize b (mk_cartesian b' c')
    specialize d (mk_cartesian b' c')
    obtain ⟨b'', hb''⟩ := b
    obtain ⟨d'', hd''⟩ := d
    simp at hb'' hd''
    repeat rw [fn_to_powerset] at h
    simp only [Subtype.mk.injEq, coe_of_fun_inj] at h
    have := congrFun h (mk_cartesian b' c')
    simp at this
    generalize_proofs sa sb at this
    have hsa := Classical.choose_spec sa
    have hsb := Classical.choose_spec sb
    conv_rhs at hsa => simp only [snd_of_mk_cartesian]
    conv_rhs at hsb => simp only [snd_of_mk_cartesian]
    rw [← hsa] at hf
    rw [← hsb] at hf'
    rw [coe_of_fun_inj] at hf hf'
    rw [hf, hf']
    rw [Subtype.mk.injEq] at this
    exact this
  . intro F
    have hF := F.property
    rw [powerset_axiom] at hF
    obtain ⟨g, hg⟩ := hF
    use fn_to_powerset (fun c ↦ (fn_to_powerset fun b ↦ g (mk_cartesian b c)))
    unfold f
    simp
    rw [Subtype.mk.injEq]
    rw [← hg]
    rw [fn_to_powerset]
    simp
    ext bc
    rw [Subtype.val_inj]
    generalize_proofs h1 h2
    have hc1 := Classical.choose_spec h1
    have hc2 := Classical.choose_spec h2
    -- ughh, I guessed that there is some rewriting possible and had exact? find it
    -- can this be done with a simpler rw?
    have : choose h1 = fun c ↦ fn_to_powerset fun b ↦ g (mk_cartesian b c) := by exact
      (coe_of_fun_inj (choose h1) fun c ↦ fn_to_powerset fun b ↦ g (mk_cartesian b c)).mp hc1
    conv_rhs at hc2 => rw [this]
    simp at hc2
    -- same trick
    have : choose h2 = fun b ↦ g (mk_cartesian b (snd bc)) := by exact
      (coe_of_fun_inj (choose h2) fun b ↦ g (mk_cartesian b (snd bc))).mp hc2
    rw [this]
    simp only [mk_cartesian_fst_snd_eq]

example (a b c:ℕ): (a^b)^c = a^(b*c) := by
  let A := SetTheory.Set.Fin a
  let B := SetTheory.Set.Fin b
  let C := SetTheory.Set.Fin c
  have hAfin : A.finite := SetTheory.Set.Fin_finite a
  have hBfin : B.finite := SetTheory.Set.Fin_finite b
  have hCfin : C.finite := SetTheory.Set.Fin_finite c
  have h := SetTheory.Set.pow_pow_EqualCard_pow_prod A B C
  have hA : A.card = a := SetTheory.Set.Fin_card a
  have hB : B.card = b := SetTheory.Set.Fin_card b
  have hC : C.card = c := SetTheory.Set.Fin_card c
  apply SetTheory.Set.EquivCard_to_card_eq at h
  have hAb := SetTheory.Set.card_pow hAfin hBfin
  rw [hA, hB] at hAb
  obtain ⟨hAbfin, hAbcard⟩ := hAb
  have hAbc := SetTheory.Set.card_pow hAbfin hCfin
  rw [hC] at hAbc
  obtain ⟨_, hAbccard⟩ := hAbc
  rw [hAbccard, hAbcard] at h
  have h := SetTheory.Set.card_prod hBfin hCfin
  obtain ⟨hbcfin, hbccard⟩ := h
  rw [hB, hC] at hbccard
  have habc := SetTheory.Set.card_pow hAfin hbcfin
  rw [hA, hbccard] at habc
  rw [habc.2] at h
  exact h

open Classical in
theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  rw [EqualCard]
  use fun p ↦ fn_to_powerset (fun bc ↦ if h: bc.val ∈ B then
    let f := Classical.choose ((powerset_axiom (fst p)).mp (fst p).property)
    f ⟨bc, h⟩
  else
    let f := Classical.choose ((powerset_axiom (snd p)).mp (snd p).property)
    f ⟨bc, by aesop⟩)
  constructor
  . intro p q h
    simp at h
    rw [fn_to_powerset_inj] at h
    generalize_proofs a b c d e f at h
    have ha := Classical.choose_spec a
    have hc := Classical.choose_spec c
    have he := Classical.choose_spec e
    have hf := Classical.choose_spec f
    rw [← cart_fst_snd_ext]
    constructor
    . rw [← Subtype.val_inj]
      rw [← ha, ← he]
      rw [coe_of_fun_inj]
      ext b
      have := congrFun h ⟨b, by aesop⟩
      have hb : ↑b ∈ B := by aesop
      simp [hb] at this
      rw [Subtype.val_inj]
      exact this
    . rw [← Subtype.val_inj]
      rw [← hc, ← hf]
      rw [coe_of_fun_inj]
      ext c
      have := congrFun h ⟨c, by aesop⟩
      have hc : ↑c ∉ B := by
        by_contra! hb
        have hc := c.prop
        have : c.val ∈ B ∩ C := by
          rw [mem_inter]
          constructor
          . exact hb
          . exact hc
        rw [disjoint_iff] at hd
        rw [hd] at this
        have := not_mem_empty c.val
        contradiction
      simp [hc] at this
      rw [Subtype.val_inj]
      exact this
  . intro F
    have hF := F.property
    rw [powerset_axiom] at hF
    obtain ⟨g, hg⟩ := hF
    use mk_cartesian (fn_to_powerset fun b ↦ g ⟨b, by aesop⟩)
      (fn_to_powerset fun c ↦ g ⟨c, by aesop⟩)
    simp
    rw [Subtype.mk.injEq]
    conv_rhs => rw [← hg]
    rw [fn_to_powerset]
    simp only [coe_of_fun_inj]
    ext bc
    by_cases h: bc.val ∈ B
    . simp [h]
      generalize_proofs a b c
      have hc := Classical.choose_spec c
      conv_rhs at hc => simp
      -- todo: clean up
      have : choose c = fun (b: B) ↦ g ⟨b.val, by aesop⟩ := by
        rw [coe_of_fun] at hc
        conv_rhs at hc => simp [fn_to_powerset]
        rw [coe_of_fun] at hc
        rw [object_of_inj] at hc
        exact hc
      rw [this]
    . simp [h]
      generalize_proofs a b c d
      have hc := Classical.choose_spec c
      conv_rhs at hc => simp
      -- todo: clean up
      have : choose c = fun (c: C) ↦ g ⟨c.val, by aesop⟩ := by
        rw [coe_of_fun] at hc
        conv_rhs at hc => simp [fn_to_powerset]
        rw [coe_of_fun] at hc
        rw [object_of_inj] at hc
        exact hc
      rw [this]

example (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  let A := SetTheory.Set.Fin a
  let BC := SetTheory.Set.Fin (b + c)
  let B := BC.specify (fun x ↦ ∃ m, m < b ∧ x.val = m)
  let C := BC.specify (fun x ↦ ∃ m, b ≤ m ∧ m < b + c ∧ x.val = m)
  have disj: Disjoint B C := by
    rw [SetTheory.Set.disjoint_iff]
    apply SetTheory.Set.ext
    intro x
    rw [SetTheory.Set.mem_inter]
    constructor
    . intro ⟨hB, hC⟩
      dsimp [B, C] at hB hC
      rw [SetTheory.Set.specification_axiom''] at hB hC
      obtain ⟨b', hb', ⟨hb'', hbc⟩⟩ := hB
      obtain ⟨c', hc', ⟨hc'', hbc'⟩⟩ := hC
      exfalso
      simp at hbc hbc'
      subst x
      simp at hbc'
      rw [hbc'.2] at hb''
      omega
    . intro h
      have := SetTheory.Set.not_mem_empty x
      contradiction

  let Beq : SetTheory.Set.EqualCard B (SetTheory.Set.Fin b) := by
    rw [SetTheory.Set.EqualCard]
    use fun x ↦ ⟨x.val, by
      have h := x.property
      dsimp [B] at h
      rw [SetTheory.Set.specification_axiom''] at h
      obtain ⟨m, hm, hmb⟩ := h
      rw [SetTheory.Set.mem_Fin]
      use hm
    ⟩
    constructor
    . intro x y h
      rw [Subtype.mk.injEq] at h
      rw [Subtype.val_inj] at h
      exact h
    . intro x
      have h := x.property
      rw [SetTheory.Set.mem_Fin] at h
      obtain ⟨m, hm, hmb⟩ := h
      use ⟨x.val, by
        dsimp [B]
        rw [SetTheory.Set.specification_axiom'']
        simp
        constructor
        . dsimp [BC]
          rw [SetTheory.Set.mem_Fin]
          use m
          constructor
          . exact Nat.lt_add_right c hm
          . exact hmb
        . use m
      ⟩
  have hB := SetTheory.Set.EquivCard_to_card_eq Beq
  have hB'card := SetTheory.Set.Fin_card b
  rw [hB'card] at hB
  have hBfin : B.finite := by
    have := SetTheory.Set.EquivCard_to_has_card_eq b Beq
    rw [SetTheory.Set.finite]
    use b
    rw [this]
  let Ceq : SetTheory.Set.EqualCard C (SetTheory.Set.Fin c) := by
    rw [SetTheory.Set.EqualCard]
    use fun x ↦
      have h := (SetTheory.Set.specification_axiom'' _ _).mp x.prop
      -- can't use Exist.comm for some reason
      let m := Classical.choose (Classical.choose_spec h)
    ⟨m - b, by
      have h := x.property
      dsimp [C] at h
      rw [SetTheory.Set.specification_axiom''] at h
      obtain ⟨m', hm', hmb'⟩ := h
      rw [SetTheory.Set.mem_Fin]
      use hm' - b
      constructor
      . omega
      . obtain ⟨h1, h2, h3⟩ := hmb'
        simp at h3
        generalize_proofs _ c at m
        have hc := Classical.choose_spec c
        simp [m]
        have : choose c - b = hm' - b := by
          have := hc.2.2
          simp at this
          rw [this] at h3
          simp at h3
          rw [h3]
        rw [this]
    ⟩
    constructor
    . intro x y h
      rw [Subtype.mk.injEq] at h
      generalize_proofs _ p1 _ p2 at h
      have h1 := Classical.choose_spec p1
      have h2 := Classical.choose_spec p2
      simp at h
      have : choose p1 = choose p2 := by
        rw [← Nat.sub_add_cancel h1.1, ← Nat.sub_add_cancel h2.1]
        rw [h]
      rw [this] at h1
      rw [← h2.2.2] at h1
      have := h1.2.2
      simp at this
      rw [Subtype.val_inj] at this
      exact this
    . intro z
      have hz := z.property
      rw [SetTheory.Set.mem_Fin] at hz
      obtain ⟨m, hm, hmb⟩ := hz
      use ⟨m + b, by
        dsimp [C]
        rw [SetTheory.Set.specification_axiom'']
        simp
        constructor
        . dsimp [BC]
          rw [SetTheory.Set.mem_Fin]
          use m + b
          constructor
          . omega
          . simp only
        . omega
      ⟩
      simp
      generalize_proofs p1 p2
      have h1 := Classical.choose_spec p1
      have : m = choose p1 - b := by omega
      rw [← SetTheory.Object.natCast_inj m (choose p1 - b)] at this
      rw [← hmb] at this
      rw [← Subtype.val_inj]
      rw [this]
  have hC := SetTheory.Set.EquivCard_to_card_eq Ceq
  have hC'card := SetTheory.Set.Fin_card c
  rw [hC'card] at hC
  have hCfin : C.finite := by
    have := SetTheory.Set.EquivCard_to_has_card_eq c Ceq
    rw [SetTheory.Set.finite]
    use c
    rw [this]
  have hAfin : A.finite := SetTheory.Set.Fin_finite a
  have h := SetTheory.Set.pow_prod_pow_EqualCard_pow_union A B C
  have hA : A.card = a := SetTheory.Set.Fin_card a

  have h := SetTheory.Set.pow_prod_pow_EqualCard_pow_union A B C disj
  apply SetTheory.Set.EquivCard_to_card_eq at h
  have hAb := SetTheory.Set.card_pow hAfin hBfin
  rw [hA, hB] at hAb
  have hAc := SetTheory.Set.card_pow hAfin hCfin
  rw [hA, hC] at hAc
  have hl := SetTheory.Set.card_prod hAb.1 hAc.1
  rw [hAb.2, hAc.2] at hl
  rw [hl.2] at h
  have hBunionC := SetTheory.Set.card_union_disjoint hBfin hCfin disj
  have hBunionCFin := (SetTheory.Set.card_union hBfin hCfin).1
  rw [hB, hC] at hBunionC
  have hr := SetTheory.Set.card_pow hAfin hBunionCFin
  rw [hA, hBunionC] at hr
  rw [hr.2] at h
  exact h

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  . intro ⟨f, hf⟩
    have him_card:= card_image_inj hA hf
    have him_card_finite := (card_image hA f).1
    have hsub := card_subset hB (image_in_codomain f A)
    rw [him_card] at hsub
    exact hsub.2
  . intro h
    rw [finite] at hA
    rw [finite] at hB
    obtain ⟨n, hA⟩ := hA
    obtain ⟨m, hB⟩ := hB
    have hA' := has_card_to_card _ _ hA
    have hB' := has_card_to_card _ _ hB
    simp [hA', hB'] at h
    rw [has_card_iff] at hA hB
    obtain ⟨fA, hfA⟩ := hA
    obtain ⟨fB, hfB⟩ := hB
    let eA := Equiv.ofBijective fA hfA
    let eB := Equiv.ofBijective fB hfB
    let inc : Fin n → Fin m := fun x ↦ ⟨x.val, by
      have hx := x.property
      rw [mem_Fin] at hx ⊢
      obtain ⟨k, hk, hkm⟩ := hx
      use k
      constructor
      . exact Nat.lt_of_lt_of_le hk h
      . exact hkm
    ⟩
    have hinc : Function.Injective inc := by
      intro x y hxy
      rw [Subtype.mk.injEq] at hxy
      rw [Subtype.val_inj] at hxy
      exact hxy
    use eB.symm.toFun ∘ inc ∘ eA.toFun
    apply Function.Injective.comp
    . exact eB.symm.injective
    . apply Function.Injective.comp
      . exact hinc
      . exact eA.injective

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  apply nonempty_def at hA
  obtain ⟨a, ha⟩ := hA
  let g: B → A := fun b ↦
    -- using unique choise instead of full AC here
    if hb: ∃! a, f a = b then Classical.choose hb.exists else ⟨a, ha⟩
  use g
  intro a
  use f a
  have huqinue : ∃! a', f a' = f a := by
    apply existsUnique_of_exists_of_unique
    . use a
    . intro x y hxy
      rw [← hxy]
      intro h
      apply hf
      exact h.symm
  unfold g
  simp only [huqinue, ↓reduceDIte]
  generalize_proofs p1
  have h1 := Classical.choose_spec p1
  apply hf
  exact h1

lemma SetTheory.Set.inter_finite {X Y: Set} (hX: X.finite): (X ∩ Y).finite := by
  have : X ∩ Y ⊆ X := by exact inter_subset_left X Y
  exact (card_subset hX this).1


lemma SetTheory.Set.diff_finite {X Y: Set} (hX: X.finite): (X \ Y).finite := by
  have : X \ Y ⊆ X := by
    intro x hx
    rw [SetTheory.Set.mem_sdiff] at hx
    exact hx.1
  exact (card_subset hX this).1

lemma SetTheory.Set.diff_disjoint {X Y: Set}: Disjoint (X \ Y) Y := by
  rw [disjoint_iff]
  apply SetTheory.Set.ext
  intro x
  constructor
  . intro hx
    rw [mem_inter] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [mem_sdiff] at h1
    exfalso
    tauto
  . intro h
    have := not_mem_empty x
    contradiction

lemma SetTheory.Set.union_diff {X Y: Set}: (X \ (X ∩ Y)) ∪ (X ∩ Y) = X := by
  apply SetTheory.Set.ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    cases' hx with h1 h2
    . rw [mem_sdiff] at h1
      exact h1.1
    . rw [mem_inter] at h2
      exact h2.1
  . intro hx
    rw [mem_union]
    by_cases hxy: x ∈ X ∩ Y
    . right
      exact hxy
    . left
      rw [mem_sdiff]
      constructor
      . exact hx
      . exact hxy

lemma SetTheory.Set.diff_inter_union {X Y: Set}: (X \ (X ∩ Y)) ∪ Y = X ∪ Y := by
  apply SetTheory.Set.ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    cases' hx with h1 h2
    . rw [mem_sdiff] at h1
      obtain ⟨h1, h2⟩ := h1
      rw [mem_union]
      left
      exact h1
    . rw [mem_union]
      right
      exact h2
  . intro hx
    rw [mem_union] at hx
    rw [mem_union]
    rw [mem_sdiff]
    by_cases hxy: x ∈ X ∩ Y
    . rw [mem_inter] at hxy
      right
      exact hxy.2
    . cases' hx with h1 h2
      . left
        constructor
        . exact h1
        . exact hxy
      . right
        exact h2

lemma SetTheory.Set.diff_inter_disj {X Y: Set}: Disjoint (X \ (X ∩ Y)) Y := by
  rw [disjoint_iff]
  apply SetTheory.Set.ext
  intro x
  constructor
  . intro hx
    rw [mem_inter] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [mem_sdiff] at h1
    obtain ⟨h1, h3⟩ := h1
    rw [mem_inter] at h3
    tauto
  . intro hx
    have := not_mem_empty x
    contradiction

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  have hAD : Disjoint (A \ (A ∩ B)) (A ∩ B) := diff_disjoint
  have hADU : (A \ (A ∩ B)) ∪ (A ∩ B) = A := union_diff
  have hAcard := card_union_disjoint (diff_finite hA) (inter_finite hA) hAD
  rw [hADU] at hAcard
  rw [hAcard]
  have hBD : Disjoint (A \ (A ∩ B)) B := diff_inter_disj
  have hBU : (A \ (A ∩ B)) ∪ B = A ∪ B := diff_inter_union
  have hBcard := card_union_disjoint (diff_finite hA) hB hBD
  rw [hBU] at hBcard
  rw [hBcard]
  exact Nat.add_right_comm _ _ B.card

lemma SetTheory.Set.iUnion_of_finite {n:ℕ} {A: Fin n → Set} (hA: ∀ i, (A i).finite): ((Fin n).iUnion A).finite := by
  induction' n with n ih
  . have := Fin_zero_empty
    have hempty := iUnion_of_empty
    rw [← this] at hempty
    specialize hempty A
    rw [hempty]
    exact Fin_finite 0
  . let A' : Fin n → Set := fun i ↦ A (Fin_embed _ _ (by omega) i)
    have hA' : ∀ i, (A' i).finite := by
      intro i
      exact hA (Fin_embed _ _ (by omega) i)
    have hA'fin := ih hA'
    let n': Fin (n + 1) := ⟨n, by rw [mem_Fin]; use n; constructor; linarith; rfl⟩
    specialize hA n'
    -- copy/paste from below. Todo: refactor
    have hu: ((Fin n).iUnion A') ∪ A n' = (Fin (n + 1)).iUnion A := by
      apply ext
      intro x
      constructor
      . intro hx
        rw [mem_union] at hx
        rw [mem_iUnion] at hx ⊢
        cases' hx with h1 h2
        . obtain ⟨i, hi⟩ := h1
          use Fin_embed _ _ (by omega) i
        . use n'
      . intro h
        rw [mem_union]
        rw [mem_iUnion] at h ⊢
        obtain ⟨i, hi⟩ := h
        by_cases hi': i = n'
        . right
          rw [hi'] at hi
          exact hi
        . left
          dsimp [n'] at hi'
          use ⟨i.val, by
            have h := i.property
            rw [mem_Fin] at h ⊢
            obtain ⟨k, hk, hkm⟩ := h
            use k
            constructor
            . by_cases hk : k = n
              . subst n
                exfalso
                apply hi'
                rw [Subtype.mk.injEq]
                exact hkm
              . omega
            . exact hkm
          ⟩
    have := card_union hA'fin hA
    rw [hu] at this
    exact this.1

/-- Exercise 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  induction' n with n ih
  . simp at hAcard
    rw [card_zero] at hAcard
    . contradiction
    . revert A
      rw [Fin_zero_empty]
      simp [iUnion_of_empty]
  . let n' : Fin (n + 1) := ⟨n, by rw [mem_Fin]; use n; aesop⟩
    let A': Fin n → Set := fun i ↦ A (Fin_embed _ _ (by omega) i)
    have hA': (∀ (i : (Fin n).toSubtype), (A' i).finite) := by
      intro i
      exact hA (Fin_embed _ _ (by omega) i)
    have hu: ((Fin n).iUnion A') ∪ A n' = (Fin (n + 1)).iUnion A := by
      apply ext
      intro x
      constructor
      . intro hx
        rw [mem_union] at hx
        rw [mem_iUnion] at hx ⊢
        cases' hx with h1 h2
        . obtain ⟨i, hi⟩ := h1
          use Fin_embed _ _ (by omega) i
        . use n'
      . intro h
        rw [mem_union]
        rw [mem_iUnion] at h ⊢
        obtain ⟨i, hi⟩ := h
        by_cases hi': i = n'
        . right
          rw [hi'] at hi
          exact hi
        . left
          dsimp [n'] at hi'
          use ⟨i.val, by
            have h := i.property
            rw [mem_Fin] at h ⊢
            obtain ⟨k, hk, hkm⟩ := h
            use k
            constructor
            . by_cases hk : k = n
              . subst n
                exfalso
                apply hi'
                rw [Subtype.mk.injEq]
                exact hkm
              . omega
            . exact hkm
          ⟩
    have hA'fin : ((Fin n).iUnion A').finite := iUnion_of_finite hA'
    have hucard := card_union (X:=((Fin n).iUnion A')) (Y:= A n') hA'fin (hA n')
    rw [hu] at hucard
    have hucard := hucard.2
    by_cases hn' : (A n').card ≥ 2
    . use n'
    . specialize ih hA'
      have := lt_of_lt_of_le hAcard hucard
      simp at hn'
      have : n + 1 ≤ ((Fin n).iUnion A').card + 2 := by linarith [hn']
      have : n < ((Fin n).iUnion A').card := by linarith [this]
      specialize ih this
      obtain ⟨i, hi⟩ := ih
      have ip := i.property
      rw [mem_Fin] at ip
      obtain ⟨k, hk, hkm⟩ := ip
      use Fin_embed _ _ (by omega) i

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  . intro hf S hS hcard
    let f': S → image f S := fun x ↦ ⟨f ⟨x.val, hS _ x.prop⟩, by
      rw [mem_image]
      use ⟨x, hS _ x.prop⟩
      simp
      exact x.prop
    ⟩
    have h : image f' S = image f S := by
      apply ext
      intro z
      repeat rw [mem_image]
      unfold f'
      aesop
    have hf' : Function.Injective f' := by
      intro x y hfxy
      rw [Subtype.mk.injEq] at hfxy
      rw [Subtype.val_inj] at hfxy
      apply hf at hfxy
      rw [Subtype.mk.injEq] at hfxy
      rw [Subtype.val_inj] at hfxy
      exact hfxy
    rw [← h]
    have him_finite : S.finite := by
      rw [finite]
      use 2
      exact card_to_has_card _ (by omega) hcard
    rw [card_image_inj him_finite hf']
    exact hcard
  . intro h
    intro x y hfxy
    let S: Set := {x.val, y.val}
    have hS : S ⊆ X := by
      intro z hz
      dsimp [S] at hz
      rw [mem_pair] at hz
      cases' hz with hz1 hz2
      . rw [hz1]
        exact x.property
      . rw [hz2]
        exact y.property
    specialize h S hS
    by_contra! hxy
    have : S.card = 2 := by
      unfold S
      have hxfin: ({x.val}:Set).finite := by exact singleton_finite _
      have hynotin: y.val ∉ ({x.val}:Set) := by
        by_contra! h
        rw [mem_singleton] at h
        rw [Subtype.val_inj] at h
        symm at h
        contradiction
      have := (card_insert hxfin hynotin).2
      rw [card_singleton] at this
      have hu : ({x.val}:Set) ∪ ({y.val}:Set) = ({x.val, y.val}:Set) := by
        apply ext
        intro z
        rw [mem_union]
        repeat rw [mem_singleton]
        rw [mem_pair]
      rw [hu] at this
      exact this
    have himcard := h this
    have him_eq : image f S = ({(f x).val, (f y).val}:Set) := by
      rw [image]
      apply ext
      intro z
      rw [replacement_axiom]
      rw [mem_pair]
      aesop
    rw [him_eq] at himcard
    have : ({(f x).val, (f y).val}:Set) = {(f x).val} := by
      apply ext
      intro z
      rw [mem_pair, mem_singleton]
      rw [hfxy]
      tauto
    rw [this] at himcard
    rw [card_singleton] at himcard
    omega

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    let f := Classical.choose ((powerset_axiom F).mp F.prop)
    Function.Bijective f)

theorem SetTheory.Set.mem_Permutations (n: ℕ) (F: Object): F ∈ Permutations n ↔
    ∃ f: Fin n → Fin n, Function.Bijective f ∧ F = function_to_object _ _ f := by
  rw [Permutations]
  rw [specification_axiom'']
  constructor
  . intro h
    obtain ⟨hf, hf'⟩ := h
    rw [powerset_axiom] at hf
    obtain ⟨f, hf''⟩ := hf
    simp at hf'
    use f
    generalize_proofs a at hf'
    have ha := Classical.choose_spec a
    subst F
    rw [coe_of_fun_inj] at ha
    constructor
    . rw [ha] at hf'
      exact hf'
    . rw [powerset_axiom] at hf
      exact rfl
  . intro h
    obtain ⟨f, hf, he⟩ := h
    have h: F ∈ Fin n ^ Fin n := by rw [powerset_axiom]; use f; rw [he]; rfl
    use h
    simp only
    generalize_proofs a
    have ha := Classical.choose_spec a
    subst F
    rw [coe_of_fun] at ha
    simp only [EmbeddingLike.apply_eq_iff_eq] at ha
    rw [ha]
    exact hf

noncomputable def SetTheory.Set.eval {n:ℕ} (f: Permutations n) (i: Fin n): Fin n :=
  let f' := Classical.choose ((mem_Permutations n f.val).mp f.prop)
  f' i

theorem SetTheory.Set.perm_ext (n: ℕ) (f g: Permutations n): (∀ i: Fin n, eval f i = eval g i) ↔ f = g := by
  constructor
  . intro h
    have hf := (mem_Permutations n f.val).mp f.prop
    have hg := (mem_Permutations n g.val).mp g.prop
    obtain ⟨f', hf'⟩ := hf
    obtain ⟨g', hg'⟩ := hg
    rw [← Subtype.val_inj]
    rw [hg'.2, hf'.2]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    ext i
    specialize h i
    repeat rw [eval] at h
    generalize_proofs a b at h
    have ha := (Classical.choose_spec a).2
    have hb := (Classical.choose_spec b).2
    conv_lhs at ha => simp [hf']
    conv_lhs at hb => simp [hg']
    rw [EmbeddingLike.apply_eq_iff_eq] at ha
    rw [EmbeddingLike.apply_eq_iff_eq] at hb
    rw [ha, hb]
    rw [Subtype.val_inj]
    exact h
  . intro h
    rw [h]
    intro i
    rfl

/-- Exercise 3.6.12 (i) -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have hpow_fin := card_pow (Fin_finite n) (Fin_finite n)
  have hsub: Permutations n ⊆ (Fin n ^ Fin n) := by
    intro x h
    rw [Permutations] at h
    apply specification_axiom
    exact h
  exact (card_subset hpow_fin.1 hsub).1

lemma SetTheory.Set.finite_eq_of_subset_eq_card {X Y: Set} (hf: Y.finite)
    (hxy: X ⊆ Y) (h: X.card = Y.card): X = Y := by
  by_contra h'
  have : X ⊂ Y := by exact ⟨hxy, h'⟩
  have := card_ssubset hf this
  linarith

lemma SetTheory.Set.fin_to_fin_surjective_of_injective {n: ℕ} {f: Fin n → Fin n}
    (h: Function.Injective f): Function.Surjective f := by
  by_contra h'
  have him := SetTheory.Set.card_image_inj (Fin_finite n) h
  rw [Function.Surjective] at h'
  push_neg at h'
  obtain ⟨y, hy⟩ := h'
  have hn: y.val ∉ image f (Fin n) := by
    rw [mem_image]
    push_neg
    intro x hx
    specialize hy x
    contrapose hy
    simp_all
    rw [Subtype.val_inj] at hy
    exact hy
  have : image f (Fin n) = Fin n := SetTheory.Set.finite_eq_of_subset_eq_card
    (Fin_finite n) (image_in_codomain f (Fin n)) him
  rw [this] at hn
  have hp := y.prop
  contradiction

-- this proof will take a long time to check
set_option maxHeartbeats 1000000 in
/-- Exercise 3.6.12 (i) -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  -- we will construct a bijection between `Permutations (n + 1)` and `Fin (n + 1) × Permutations n`
  -- the basic idea is take f n as the first component
  -- construct a function g from `Fin n` to `Fin n` that
  -- skips f n in the image, by subtracting 1 from all images above f n.
  let fP : Permutations (n + 1) → Fin (n + 1) ×ˢ Permutations n := fun F ↦
    have hF := (mem_Permutations (n + 1) F).mp F.prop
    let f := Classical.choose hF
    have hf := Classical.choose_spec hF
    let y₀ := f (Fin_mk _ n (by omega))
    let f' : Fin n → Fin n := fun x ↦
      let y := f (Fin_embed _ _ (by omega) x)
      have yneq : y ≠ y₀ := by
        intro h
        apply hf.1.injective at h
        dsimp [Fin_embed, Fin_mk] at h
        simp only [Subtype.mk.injEq] at h
        rw [Fin.val_eq_natCast] at h
        have := Fin.toNat_lt x
        omega
      if h: Fin.toNat y < y₀ then Fin_mk n y (by
        have h' := Fin.toNat_lt y₀
        linarith
      ) else Fin_mk n (y - 1) (by
        have h' := Fin.toNat_lt y
        rwa [← Nat.sub_lt_iff_lt_add] at h'
        simp only [not_lt] at h
        have hl : Fin.toNat y₀ < Fin.toNat y := by
          by_contra! hg
          have := le_antisymm hg h
          rw [Fin.toNat_inj] at this
          contradiction
        exact Nat.one_le_of_lt hl
      )
    have hf_def (x: Fin n) : if Fin.toNat (f (Fin_embed _ _ (by omega) x)) < y₀ then
        Fin.toNat (f' x) = f (Fin_embed _ _ (by omega) x) else
        Fin.toNat (f' x) = f (Fin_embed _ _ (by omega) x) - 1 := by
      by_cases h : Fin.toNat (f (Fin_embed _ _ (by omega) x)) < y₀ <;> simp [f', h]

    let G := function_to_object (Fin n) (Fin n) f'

    have hG : G ∈ Permutations n := by
      rw [mem_Permutations]
      use f'
      -- will come useful later
      have toNat_inj: Function.Injective (Fin.toNat (n := n + 1)) := by
        intro x y hxy
        rw [Fin.toNat_inj] at hxy
        exact hxy
      constructor
      .
        have : Function.Injective f' := by
          intro i j h
          have hneqy (i: Fin n) : f (Fin_embed _ _ (by omega) i) ≠ y₀ := by
            unfold y₀
            rw [hf.1.injective.ne_iff]
            simp only [ne_eq, Subtype.mk.injEq]
            have := Fin.toNat_lt i
            apply ne_of_lt at this
            contrapose! this
            rwa [Fin.val_eq_natCast] at this
          have hi := hneqy i
          have hj := hneqy j
          rw [← Fin.toNat_inj] at h
          set i' : Fin (n + 1) := Fin_embed _ _ (by omega) i
          set j' : Fin (n + 1) := Fin_embed _ _ (by omega) j

          by_cases hi_lt : Fin.toNat (f i') < y₀
          . have hf_def_i := hf_def i
            simp [hi_lt] at hf_def_i
            simp [hf_def_i] at h
            by_cases hj_ly : Fin.toNat (f j') < y₀
            . have hf_def_j := hf_def j
              simp [hj_ly] at hf_def_j
              simp [hf_def_j] at h
              rw [Fin.toNat_inj] at h
              apply hf.1.injective at h
              simp only [Subtype.mk.injEq] at h
              rwa [Subtype.val_inj] at h
            . have hf_def_j := hf_def j
              simp [hj_ly] at hf_def_j
              simp [hf_def_j] at h
              simp only [not_lt] at hj_ly
              apply_fun Fin.toNat (n := n + 1) at hj using toNat_inj
              have hj_gt: Fin.toNat y₀ < Fin.toNat (f j') := by
                exact Nat.lt_of_le_of_ne hj_ly (id (Ne.symm hj))
              change Fin.toNat (f i') = Fin.toNat (f j') - 1 at h
              omega  -- contradiction
          . have hf_def_i := hf_def i
            simp [hi_lt] at hf_def_i
            simp [hf_def_i] at h
            simp only [not_lt] at hi_lt
            apply_fun Fin.toNat (n := n + 1) at hi using toNat_inj
            have hi_gt: Fin.toNat y₀ < Fin.toNat (f i') := by
              exact Nat.lt_of_le_of_ne hi_lt (id (Ne.symm hi))
            by_cases hj_lt : Fin.toNat (f j') < y₀
            . have hf_def_j := hf_def j
              simp [hj_lt] at hf_def_j
              simp [hf_def_j] at h
              change Fin.toNat (f i') - 1 = Fin.toNat (f j') at h
              omega  -- contradiction
            . have hf_def_j := hf_def j
              simp [hj_lt] at hf_def_j
              simp [hf_def_j] at h
              simp only [not_lt] at hj_lt
              have hj_gt: Fin.toNat y₀ < Fin.toNat (f j') := by
                exact Nat.lt_of_le_of_ne hj_lt fun a ↦ hneqy j (toNat_inj (id (Eq.symm a)))
              have hi_nez : Fin.toNat (f i') ≠ 0 := by
                exact Nat.ne_zero_of_lt hi_gt
              have hj_nez : Fin.toNat (f j') ≠ 0 := by
                exact Nat.ne_zero_of_lt hj_gt
              change Fin.toNat (f i') - 1 = Fin.toNat (f j') - 1 at h
              have : Fin.toNat (f i') = Fin.toNat (f j') := by omega
              rw [Fin.toNat_inj] at this
              apply hf.1.injective at this
              simp only [i', j', Subtype.mk.injEq] at this
              rwa [Subtype.val_inj] at this
        constructor
        . exact this
        . exact fin_to_fin_surjective_of_injective this
      . rfl -- from mem_Permutations
    mk_cartesian y₀ ⟨G, hG⟩

  have hf : Function.Bijective fP := by
    constructor
    .
      intro x1 x2 hxy
      unfold fP at hxy
      rw [SetTheory.Set.mk_cartesian_inj] at hxy
      obtain ⟨hx1, hy1⟩ := hxy
      generalize_proofs a _ b at hx1
      have ⟨hab, hae⟩ := Classical.choose_spec a
      have ⟨hba, hbe⟩ := Classical.choose_spec b
      rw [← perm_ext]
      intro i
      simp only [eval]
      generalize_proofs
      set n' : Fin (n + 1) := Fin_mk _ n (by omega)
      by_cases hi: i = n'
      . rw [hi]
        exact hx1
      . simp at hy1
        have := congrFun hy1 (Fin_mk _ i (by
          have h := Fin.toNat_lt i
          suffices Fin.toNat i ≠ n by omega
          contrapose! hi
          dsimp [n']
          rw [← Fin.toNat_inj]
          simp only [Fin.toNat_mk]
          exact hi
        ))
        generalize_proofs at this
        simp [SetTheory.Set.Fin.embed_mk_ofNat] at this
        by_cases ha: Fin.toNat (choose a i) < Fin.toNat (choose a n')
        .
          by_cases hb: Fin.toNat (choose b i) < Fin.toNat (choose b n')
          . simp [ha, hb] at this
            rwa [Subtype.val_inj] at this
          . simp [ha, hb] at this
            rw [Fin.val_eq_natCast] at this
            rw [hx1] at ha
            have hb_le : Fin.toNat (choose b n') ≠ Fin.toNat (choose b i) := by
              intro h
              rw [Fin.toNat_inj] at h
              apply hba.injective at h
              symm at h
              contradiction
            omega
        .
          have ha_le : Fin.toNat (choose b n') ≠ Fin.toNat (choose a i) := by
            intro h
            rw [Fin.toNat_inj] at h
            rw [← hx1] at h
            apply hab.injective at h
            symm at h
            contradiction
          by_cases hb: Fin.toNat (choose b i) < Fin.toNat (choose b n')
          . simp [ha, hb] at this
            symm at this
            rw [Fin.val_eq_natCast] at this
            rw [hx1] at ha
            simp at ha

            omega
          . simp [ha, hb] at this
            have hb_le : Fin.toNat (choose b n') ≠ Fin.toNat (choose b i) := by
              intro h
              rw [Fin.toNat_inj] at h
              apply hba.injective at h
              symm at h
              contradiction
            have ha_neq : Fin.toNat (choose a i) ≠ 0 := by
              simp only [not_lt] at ha
              rw [hx1] at ha
              contrapose! ha
              rw [ha]
              rw [ha] at ha_le
              exact Nat.zero_lt_of_ne_zero ha_le
            have ha_neq : Fin.toNat (choose b i) ≠ 0 := by
              simp only [not_lt] at hb
              contrapose! hb
              rw [hb]
              rw [hb] at hb_le
              exact Nat.zero_lt_of_ne_zero hb_le
            rw [← Fin.toNat_inj]
            omega
    . intro p
      have hp := p.property
      rw [mem_cartesian] at hp
      obtain ⟨x, y, h⟩ := hp
      have hpfst : (fst p) = x := by exact fst_eval' p x y h
      have hpsnd : (snd p) = y := by exact snd_eval' p x y h

      obtain ⟨f, hfb, hf⟩ := (mem_Permutations _ y.val).mp y.prop
      let f' : Fin (n + 1) → Fin (n + 1) := fun i ↦
        if hin: i = n then x else
        let i' : Fin n := Fin_mk _ i (by have := Fin.toNat_lt i; omega)
        if hix: Fin.toNat (f i') < Fin.toNat x then Fin_embed _ _ (by omega) (f i')
        else Fin_mk _ (Fin.toNat (f i') + 1) (by have := Fin.toNat_lt (f i'); omega)

      have hf_def (i: Fin (n + 1)) : if hin: i = n then
          Fin.toNat (f' i) = Fin.toNat x
        else
          let i' : Fin n := Fin_mk _ i (by have := Fin.toNat_lt i; omega)
          if hix: Fin.toNat (f i') < Fin.toNat x then
            Fin.toNat (f' i) = Fin.toNat (f i')
          else Fin.toNat (f' i) = Fin.toNat (f i') + 1
        := by
        by_cases hi: i = n
        . simp [hi, f']
        . simp [hi, f']
          . let i' : Fin n := Fin_mk _ i (by have := Fin.toNat_lt i; omega)
            by_cases hix: Fin.toNat (f i') < Fin.toNat x
            . simp [hix, i']
              rw [Fin.Fin_embed_toNat]
            . simp [hix, i']

      let F' := function_to_object (Fin (n + 1)) (Fin (n + 1)) f'
      have hF' : F' ∈ Permutations (n + 1) := by
        rw [mem_Permutations]
        use f'
        constructor
        .
          have : Function.Injective f' := by
            intro i j h
            have hdefi := hf_def i
            have hdefj := hf_def j
            by_cases hi: i = n
            . by_cases hj: j = n
              . conv_rhs at hj => rw [← hi]
                rw [Fin.toNat_inj] at hj
                exact hj.symm
              . simp [hi] at hdefi
                simp [hj] at hdefj
                rw [Fin.toNat_inj] at hdefi
                rw [hdefi] at h
                rw [← h] at hdefj
                exfalso
                generalize_proofs a at hdefj
                by_cases hj': Fin.toNat (f (Fin_mk n (Fin.toNat j) a)) < Fin.toNat x
                . simp [hj'] at hdefj
                  omega
                . simp [hj'] at hdefj
                  omega
            . by_cases hj: j = n
              . simp [hi] at hdefi
                simp [hj] at hdefj
                rw [Fin.toNat_inj] at hdefj
                rw [hdefj] at h
                rw [h] at hdefi
                exfalso
                generalize_proofs a at hdefi
                by_cases hi': Fin.toNat (f (Fin_mk n (Fin.toNat i) a)) < Fin.toNat x
                . simp [hi'] at hdefi
                  omega
                . simp [hi'] at hdefi
                  omega
              . simp [hi] at hdefi
                simp [hj] at hdefj
                generalize_proofs a b at hdefi hdefj
                by_cases hi': Fin.toNat (f (Fin_mk n (Fin.toNat i) a)) < Fin.toNat x
                . by_cases hj': Fin.toNat (f (Fin_mk n (Fin.toNat j) b)) < Fin.toNat x
                  . simp [hi', hj'] at hdefi hdefj
                    simp [h] at hdefi
                    simp [hdefj] at hdefi
                    rw [Fin.toNat_inj] at hdefi
                    apply hfb.injective at hdefi
                    simp at hdefi
                    rw [Subtype.val_inj] at hdefi
                    exact hdefi.symm
                  . simp [hi', hj'] at hdefi hdefj
                    simp [h] at hdefi
                    simp [hdefj] at hdefi
                    omega
                . by_cases hj': Fin.toNat (f (Fin_mk n (Fin.toNat j) b)) < Fin.toNat x
                  . simp [hi', hj'] at hdefi hdefj
                    simp [h] at hdefi
                    simp [hdefj] at hdefi
                    omega
                  . simp [hi', hj'] at hdefi hdefj
                    simp [h] at hdefi
                    simp [hdefj] at hdefi
                    rw [Fin.toNat_inj] at hdefi
                    apply hfb.injective at hdefi
                    simp at hdefi
                    rw [Subtype.val_inj] at hdefi
                    exact hdefi.symm
          constructor
          . exact this
          . exact fin_to_fin_surjective_of_injective this
        . rfl
      use ⟨F', hF'⟩
      dsimp [fP, F']
      conv_rhs => rw [← mk_cartesian_fst_snd_eq p]
      rw [mk_cartesian_inj]
      constructor
      . generalize_proofs a b
        have ha := Classical.choose_spec a
        have : choose a = f' := by
          have := ha.2
          rw [EmbeddingLike.apply_eq_iff_eq] at this
          exact this.symm
        rw [this]
        dsimp [f']
        simp only [Fin.toNat_mk, ↓reduceDIte]
        rw [hpfst]
      . conv_rhs => rw [hpsnd]
        rw [← Subtype.val_inj]
        conv_rhs => rw [hf]
        simp only
        rw [EmbeddingLike.apply_eq_iff_eq]
        generalize_proofs b
        have hb := Classical.choose_spec b
        have : choose b = f' := by
          have := hb.2
          rw [EmbeddingLike.apply_eq_iff_eq] at this
          exact this.symm
        simp [this]
        ext i
        have hfx: f' (Fin_mk _ n (by omega)) = x := by
          specialize hf_def (Fin_mk _ n (by omega))
          simp [Fin.toNat_mk] at hf_def
          rwa [Fin.toNat_inj] at hf_def
        by_cases hix: Fin.toNat (f' (Fin_embed _ _ (by omega) i)) < Fin.toNat x
        . specialize hf_def (Fin_embed _ _ (by omega) i)
          set i': Fin (n + 1) := Fin_embed _ _ (by omega) i with hi'
          have hi'': Fin.toNat i = Fin.toNat i' := by
            dsimp [i']
            rw [Fin.Fin_embed_toNat _ (n + 1)]
          have hneq: Fin.toNat i' ≠ n := by
            intro h
            have := Fin.toNat_lt i
            omega
          simp [hneq] at hf_def
          rw [hi'] at hix
          simp [hfx]
          simp [hix]
          have : f (Fin_mk n (Fin.toNat i') (by have := Fin.toNat_lt i; rwa [hi''] at this)) < Fin.toNat x := by
            by_contra h
            simp [h] at hf_def
            rw [hf_def] at hix
            omega
          simp [this] at hf_def
          change ↑(f' i') = Subtype.val (f i)
          conv_rhs at hf_def => dsimp [i']
          conv_rhs at hf_def => simp [Fin.Fin_embed_toNat _ (n + 1)]
          exact Fin.toFin_eq_of_val_eq _ _ hf_def
        . specialize hf_def (Fin_embed _ _ (by omega) i)
          set i': Fin (n + 1) := Fin_embed _ _ (by omega) i with hi'
          have hi'': Fin.toNat i = Fin.toNat i' := by
            dsimp [i']
            rw [Fin.Fin_embed_toNat _ (n + 1)]
          have hneq: Fin.toNat i' ≠ n := by
            intro h
            have := Fin.toNat_lt i
            omega
          simp [hneq] at hf_def
          rw [hi'] at hix
          simp [hfx]
          simp [hix]
          have : ¬ f (Fin_mk n (Fin.toNat i') (by have := Fin.toNat_lt i; rwa [hi''] at this)) < Fin.toNat x := by
            by_contra h
            simp [h] at hf_def
            rw [hf_def] at hix
            omega
          simp [this] at hf_def
          simp [← hi']
          conv_rhs at hf_def => dsimp [i']
          conv_rhs at hf_def => simp [Fin.Fin_embed_toNat _ (n + 1)]
          simp [hf_def]
  have e : EqualCard (Permutations (n + 1)) (Fin (n + 1) ×ˢ Permutations n) := by
    use fP
  rw [EquivCard_to_card_eq e]
  have hprod := card_prod (Fin_finite (n + 1)) (Permutations_finite n)
  rw [hprod.2]
  rw [Fin_card]

/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = Nat.factorial n := by
  induction' n with n ih
  . suffices Permutations 0 = ({function_to_object ∅ ∅ empty_fn}: Set) by
      rw [this]
      rw [card_singleton]
      simp only [Nat.factorial_zero]
    apply ext
    intro x
    rw [Permutations]
    rw [specification_axiom'']
    rw [mem_singleton]
    simp only
    constructor
    . intro h
      obtain ⟨hf, hf'⟩ := h
      rw [powerset_axiom] at hf
      obtain ⟨f, hf⟩ := hf
      rw [← hf]
      rw [coe_of_fun]
      revert f
      rw [Fin_zero_empty]
      intro f hf
      simp only [EmbeddingLike.apply_eq_iff_eq]
      ext x
      exfalso
      have hp := x.prop
      have := not_mem_empty x
      contradiction
    . simp [Fin_zero_empty]
      intro h
      have : ∃ f : (∅:Set) → (∅:Set), ↑f = x := by exact Exists.intro empty_fn (id (Eq.symm h))
      use this
      constructor
      . intro x1 x2 h
        have h := x1.property
        simp only [Fin_zero_empty, not_mem_empty] at h
      . intro y
        have hy := y.property
        simp only [Fin_zero_empty, not_mem_empty] at hy
  . rw [Permutations_ih, ih]
    exact rfl

theorem SetTheory.Set.Fin_mathlib_eq (n: ℕ) : ∃ f: (Fin n) → (_root_.Fin n), Function.Bijective f := by
  use fun x ↦
    have h := x.property
    have hfin := (mem_Fin _ _).mp h
    let m := Classical.choose hfin
    have h1 := Classical.choose_spec hfin
    ⟨m, by
      dsimp [m]
      exact h1.1
    ⟩
  constructor
  . intro x y hxy
    simp at hxy
    generalize_proofs a b at hxy
    have ha := Classical.choose_spec a
    have hb := Classical.choose_spec b
    rw [Subtype.mk.injEq]
    rw [ha.2, hb.2]
    rw [hxy]
  . intro z
    use ⟨z.val, by
      rw [mem_Fin]
      use z.val
      simp
    ⟩
    simp
    generalize_proofs a b
    have ha := Classical.choose_spec a
    rw [Fin.mk.injEq]
    exact ha.2.symm

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases h : X.finite
  . rw [finite] at h
    obtain ⟨n, hX⟩ := h
    have hX' := hX
    rw [has_card_iff] at hX
    obtain ⟨f, hf⟩ := hX
    obtain ⟨fFin, hfFin⟩ := SetTheory.Set.Fin_mathlib_eq n
    let composed := fFin ∘ f
    have hcomp : Function.Bijective composed := Function.Bijective.comp hfFin hf
    let e := Equiv.ofBijective composed hcomp
    let fintype_inst : Fintype X := Fintype.ofBijective e.symm e.symm.bijective
    have : Nat.card X = n := by
      rw [Nat.card_eq_fintype_card]
      have := Fintype.card_of_bijective e.symm.bijective
      rw [← this]
      simp only [Fintype.card_fin]
    rw [this]
    exact has_card_to_card _ _ hX'
  . have : X.card = 0 := by dsimp [card]; simp [h]
    rw [finite] at h
    rw [this]
    symm
    by_contra! hX
    let hE: X ≃ _root_.Fin (Nat.card X) := by
      have : Finite X.toSubtype := Nat.finite_of_card_ne_zero hX
      have I: Fintype X.toSubtype := Fintype.ofFinite X.toSubtype
      have := Fintype.equivFin X.toSubtype
      rw [← Nat.card_eq_fintype_card] at this
      exact this
    let f := Classical.choose (Fin_mathlib_eq (Nat.card X))
    have hf := Classical.choose_spec (Fin_mathlib_eq (Nat.card X))
    let e := Equiv.ofBijective f hf
    let e' := hE.trans e.symm
    have : X.has_card (Nat.card X) := by
      rw [has_card_iff]
      use e'
      exact e'.bijective
    push_neg at h
    specialize h (Nat.card X)
    contradiction

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [SetTheory.Set.card_eq_nat_card]
  rfl

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
