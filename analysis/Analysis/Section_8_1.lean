import Mathlib.Tactic

/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe.
This is analogous to `Chapter3.SetTheory.Set.EqualCard`, but we are not using the latter since
the Chapter 3 set theory is deprecated. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Relation with Mathlib's `Equiv` concept -/
theorem EqualCard.iff {X Y : Type} : EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]; constructor
  . intro ⟨ f, hf ⟩; exact ⟨ .ofBijective f hf ⟩
  intro ⟨ e ⟩; exact ⟨ e.toFun, e.bijective ⟩

/-- Equivalence with Mathlib's `Cardinal.mk` concept -/
theorem EqualCard.iff' {X Y : Type} : EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

theorem EqualCard.refl (X : Type) : EqualCard X X := by
  use id
  exact Function.bijective_id

theorem EqualCard.symm {X Y : Type} (hXY : EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, hf⟩ := hXY
  let e := Equiv.ofBijective f hf
  exact ⟨e.symm, e.symm.bijective⟩

theorem EqualCard.trans {X Y Z : Type} (hXY : EqualCard X Y) (hYZ : EqualCard Y Z) :
  EqualCard X Z := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  use g ∘ f
  exact hg.comp hf

instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩

theorem EqualCard.univ (X : Type) : EqualCard (.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's `Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's `Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto

theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext; simp; constructor
    . intro hx; use g ⟨ _, hx ⟩; simp [hleft _]
    rintro ⟨ _, rfl ⟩; aesop
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by
  unfold CountablyInfinite; use id; exact Function.bijective_id

example : CountablyInfinite (.univ \ {0}: Set ℕ) := by
  use fun ⟨x, hx⟩ ↦ x - 1
  constructor
  · intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp at ha hb h; congr; omega
  · intro n; use ⟨n + 1, by simp⟩; simp

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' .univ) := by
  use fun ⟨x, hx⟩ ↦ x / 2
  constructor
  · intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp at ha hb h
    obtain ⟨m, rfl⟩ := ha; obtain ⟨n, rfl⟩ := hb
    congr 1; omega
  · intro n; use ⟨2 * n, by simp⟩; simp

/-- Proposition 8.1.4 (Well ordering principle / Exercise 8.1.2 -/
theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
  obtain ⟨x, hx⟩ := hX
  induction x using Nat.strongRecOn with
  | _ x ih =>
    by_cases h : ∃ y ∈ X, y < x
    · obtain ⟨y, hy, hyx⟩ := h
      exact ih y hyx hy
    · push_neg at h
      use x
      exact ⟨⟨hx, h⟩, fun y ⟨hy, hle⟩ ↦ le_antisymm (hle x hx) (h y hy)⟩

def Int.exists_unique_min : Decidable (∀ (X : Set ℤ) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use .univ
  simp only [Set.univ_nonempty, Set.mem_univ, forall_const, true_and]
  intro h
  obtain ⟨m, hm, hmin⟩ := h
  specialize hm (m - 1)
  linarith


def NNRat.exists_unique_min : Decidable (∀ (X : Set NNRat) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use .univ \ {0}
  constructor
  · exact ⟨1, by simp⟩
  · intro h
    obtain ⟨m, ⟨⟨_, hm_ne⟩, hle⟩, _⟩ := h
    simp at hm_ne
    have hm_pos : 0 < m := pos_iff_ne_zero.mpr hm_ne
    have hmem : m / 2 ∈ Set.univ \ {(0:NNRat)} := by
      simp; exact ne_of_gt (by positivity)
    exact absurd (hle (m / 2) hmem) (not_le.mpr (div_lt_self hm_pos one_lt_two))

open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]; exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (.Ici 1)) = 2 := by
  apply Nat.min_eq ⟨2, by simp⟩
  refine ⟨⟨1, by simp, by simp⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  simp only [Set.mem_Ici] at hk
  dsimp only
  omega

theorem Nat.min_eq_sInf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  apply Nat.min_eq hX
  exact ⟨Nat.sInf_mem hX, fun _ hn ↦ Nat.sInf_le hn⟩

open Classical in
/-- Equivalence with Mathlib's `Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]; have := min_spec hX; grind

/-- Proposition 8.1.5 -/
theorem Nat.monotone_enum_of_infinite (X : Set ℕ) [Infinite X] : ∃! f : ℕ → X, Function.Bijective f ∧ StrictMono f := by
  -- This proof is written to follow the structure of the original text.
  let a : ℕ → ℕ := Nat.strongRec (fun n a ↦ min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m h })
  have ha : ∀ n, a n = min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := Nat.strongRec.eq_def _
  have ha_infinite (n:ℕ) : Infinite { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
    have : {x | x ∈ X ∧ ∀ m < n, x ≠ a m} = X \ (a '' (Finset.range n : Set ℕ)) := by
      ext x; simp; tauto
    rw [this]
    exact Set.Infinite.to_subtype ((Set.infinite_coe_iff.mp ‹_›).diff
      (Set.Finite.image _ (Finset.finite_toSet _)))
  have ha_nonempty (n:ℕ) : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty := Set.Nonempty.of_subtype
  have ha_mono : StrictMono a := by
    apply strictMono_nat_of_lt_succ; intro n
    have spec_n := min_spec (ha_nonempty n)
    have spec_sn := min_spec (ha_nonempty (n + 1))
    rw [ha n, ha (n + 1)]
    have hsub : {x | x ∈ X ∧ ∀ m < n + 1, x ≠ a m} ⊆ {x | x ∈ X ∧ ∀ m < n, x ≠ a m} :=
      fun x ⟨hx, hm⟩ ↦ ⟨hx, fun m hm' ↦ hm m (by omega)⟩
    have hle := spec_n.2 _ (hsub spec_sn.1)
    have hne := spec_sn.1.2 n (by omega)
    rw [ha n] at hne; omega
  have ha_injective : Function.Injective a := ha_mono.injective
  have haX (n:ℕ) : a n ∈ X := by
    rw [ha n]; exact (min_spec (ha_nonempty n)).1.1
  set f : ℕ → X := fun n ↦ ⟨ a n, haX n ⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy; simp [f] at hxy; solve_by_elim
  have hf_surjective : Function.Surjective f := by
    intro ⟨ x, hx ⟩; simp [f]; by_contra hne; push_neg at hne
    have h1 (n:ℕ) : x ∈ { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } :=
      ⟨hx, fun m _ ↦ Ne.symm (hne m)⟩
    have h2 (n:ℕ) : x ≥ a n := by
      rw [ha n]; exact ge_iff_le.mpr ((min_spec (ha_nonempty n)).2 _ (h1 n))
    have h3 (n:ℕ) : a n ≥ n := ha_mono.id_le n
    have h4 (n:ℕ) : x ≥ n := (h3 n).trans (h2 n)
    linarith [h4 (x+1)]
  apply ExistsUnique.intro _ ⟨ ⟨ hf_injective, hf_surjective ⟩, ha_mono ⟩
  intro g ⟨ hg_bijective, hg_mono ⟩; by_contra!
  replace : { n | g n ≠ f n }.Nonempty := by
    contrapose! this
    apply funext; simpa [Set.eq_empty_iff_forall_notMem] using this
  set m := min { n | g n ≠ f n }
  have hm : g m ≠ f m := (min_spec this).1
  have hm' {n:ℕ} (hn: n < m) : g n = f n := by by_contra hgfn; linarith [(min_spec this).2 n (by simp [hgfn])]
  have hgm : g m = min { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } := by
    symm; apply min_eq (ha_nonempty m)
    have hgk (k : ℕ) (hk : k < m) : ↑(g k) = a k := by
      have := hm' hk; simp [f] at this; exact congrArg Subtype.val this
    refine ⟨⟨(g m).2, fun k hk h ↦ ?_⟩, fun y ⟨hy, hy'⟩ ↦ ?_⟩
    · exact absurd (hg_bijective.1 (Subtype.val_injective (h ▸ hgk k hk))) (by omega)
    · by_contra hlt; push_neg at hlt
      obtain ⟨k, hk⟩ := hg_bijective.2 ⟨y, hy⟩
      have hgky : ↑(g k) = y := congrArg Subtype.val hk
      have hkm : k ≥ m := by
        by_contra hlt'; push_neg at hlt'
        exact hy' k hlt' (hgky ▸ hgk k hlt')
      have : (↑(g m) : ℕ) ≤ ↑(g k) := Subtype.coe_le_coe.2 (hg_mono.monotone hkm)
      omega
  rw [←ha m] at hgm; contrapose! hm; exact Subtype.val_injective hgm

theorem Nat.countable_of_infinite (X : Set ℕ) [Infinite X] : CountablyInfinite X := by
  have := (monotone_enum_of_infinite X).exists
  exact EqualCard.symm ⟨ this.choose, this.choose_spec.1 ⟩

/-- Corollary 8.1.6 -/
theorem Nat.atMostCountable_subset (X: Set ℕ) : AtMostCountable X := by
  obtain _ | _ := finite_or_infinite X
  . tauto
  simp [AtMostCountable, countable_of_infinite]

/-- Corollary 8.1.7 -/
theorem AtMostCountable.subset {X: Type} (hX : AtMostCountable X) (Y: Set X) : AtMostCountable Y := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ f, hf ⟩ | hX := hX
  . let f' : Y → f '' Y := fun y ↦ ⟨ f y, by aesop ⟩
    have hf' : Function.Bijective f' := by
      constructor
      · intro y1 y2 hy; simp [f'] at hy; exact Subtype.ext (hf.1 hy)
      · rintro ⟨_, y, hy, rfl⟩; exact ⟨⟨y, hy⟩, by simp [f']⟩
    rw [equiv ⟨ _, hf' ⟩ ]; apply Nat.atMostCountable_subset
  simp [AtMostCountable, show Finite Y by infer_instance]

theorem AtMostCountable.subset' {A: Type} {X Y: Set A} (hX: AtMostCountable X) (hY: Y ⊆ X) : AtMostCountable Y := by
  refine' (equiv ⟨ fun y ↦ ⟨ ↑↑y, y.property ⟩, _, _ ⟩).mp (subset hX { x : X | ↑x ∈ Y })
  . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _; simp_all
  intro ⟨ y, hy ⟩; use ⟨ ⟨ y, hY hy ⟩, by aesop ⟩

/-- Proposition 8.1.8 / Exercise 8.1.4 -/
theorem AtMostCountable.image_nat (Y: Type) (f: ℕ → Y) : AtMostCountable (f '' .univ) := by
  let A := {n : ℕ | ∀ m < n, f m ≠ f n}
  let f' : A → f '' .univ := fun ⟨ n, hn ⟩ ↦ ⟨ f n, by aesop ⟩
  have hf' : Function.Injective f' := by
    intro ⟨n, hn⟩ ⟨k, hk⟩ h
    simp [f'] at h
    by_contra hne; simp [Subtype.mk.injEq] at hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact hk n h' h
    · exact hn k h' h.symm
  have hf'' : Function.Surjective f' := by
    rintro ⟨y, n, -, rfl⟩
    set S := {k | f k = f n}
    have hne : S.Nonempty := ⟨n, rfl⟩
    have hmin := Nat.min_spec hne
    use ⟨Nat.min S, fun m hm h ↦
      absurd (hmin.2 m (by rw [Set.mem_setOf, h]; exact hmin.1)) (not_le.mpr hm)⟩
    simp [f']; exact (Nat.min_spec hne).1
  have hA : AtMostCountable A := Nat.atMostCountable_subset A
  exact (equiv ⟨f', hf', hf''⟩).mp hA

/-- Corollary 8.1.9 / Exercise 8.1.5 -/
theorem AtMostCountable.image {X:Type} (hX: CountablyInfinite X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  obtain ⟨g, hg⟩ := hX
  choose ginv hleft hright using Function.bijective_iff_has_inverse.mp hg
  have : f '' .univ = (f ∘ ginv) '' .univ := by
    ext y; simp; constructor
    · rintro ⟨x, rfl⟩; exact ⟨g x, by simp [hleft x]⟩
    · rintro ⟨n, rfl⟩; exact ⟨_, rfl⟩
  rw [this]; exact image_nat _ _


/-- Proposition 8.1.10 / Exercise 8.1.7 -/
theorem CountablyInfinite.union {A:Type} {X Y: Set A} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X ∪ Y: Set A) := by
  let hX' := hX
  obtain ⟨fX, hfX⟩ := hX
  obtain ⟨fY, hfY⟩ := hY
  choose fXinv hXleft hXright using Function.bijective_iff_has_inverse.mp hfX
  choose fYinv hYleft hYright using Function.bijective_iff_has_inverse.mp hfY
  -- Interleave the two inverse enumerations
  let f : ℕ → (X ∪ Y : Set A) := fun n ↦
    if Even n then ⟨fXinv (n / 2), Set.mem_union_left _ (fXinv (n / 2)).2⟩
    else ⟨fYinv (n / 2), Set.mem_union_right _ (fYinv (n / 2)).2⟩
  -- f is surjective (but not necessarily injective when X ∩ Y ≠ ∅)
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, ha | ha⟩
    · use 2 * fX ⟨a, ha⟩
      have hev : Even (2 * fX ⟨a, ha⟩) := ⟨fX ⟨a, ha⟩, by omega⟩
      simp [f, hev]
      exact congrArg Subtype.val (hXleft ⟨a, ha⟩)
    · use 2 * fY ⟨a, ha⟩ + 1
      have hev : ¬Even (2 * fY ⟨a, ha⟩ + 1) := Nat.not_even_two_mul_add_one _
      have hdiv : (2 * fY ⟨a, ha⟩ + 1) / 2 = fY ⟨a, ha⟩ := by omega
      simp [f, hev, hdiv]
      exact congrArg Subtype.val (hYleft ⟨a, ha⟩)
  -- X ∪ Y is countable via surjection from ℕ
  have hc : Countable ↑(X ∪ Y) := by
    have : Function.Surjective f := hf_surj
    exact Function.Surjective.countable this
  -- X ∪ Y is infinite since X is
  have hi : Infinite ↑(X ∪ Y) := by
    have : Infinite X := ((iff' _).mp hX').2
    exact Set.infinite_coe_iff.mpr ((Set.infinite_coe_iff.mp this).mono Set.subset_union_left)
  exact (iff' _).2 ⟨hc, hi⟩

/-- Corollary 8.1.11 --/
theorem Int.countablyInfinite : CountablyInfinite ℤ := by
  -- This proof is written to follow the structure of the original text.
  have h1 : CountablyInfinite {n:ℤ | n ≥ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    . intro h; use n.toNat; simp [h]
  have h2 : CountablyInfinite {n:ℤ | n ≤ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (-↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    intro h; use (-n).toNat; simp [h]
  have : CountablyInfinite (.univ : Set ℤ) := by
    convert h1.union h2; ext; simp; omega
  rwa [←CountablyInfinite.equiv (.univ _)]

/-- Lemma 8.1.12 -/
theorem CountablyInfinite.lower_diag : CountablyInfinite { n : ℕ × ℕ | n.2 ≤ n.1 } := by
  -- This proof is written to follow the structure of the original text.
  let A := { n : ℕ × ℕ | n.2 ≤ n.1 }
  let a : ℕ → ℕ := fun n ↦ ∑ m ∈ .range (n+1), m
  have ha : StrictMono a := by
    intro p q hpq
    show ∑ i ∈ .range (p + 1), i < ∑ i ∈ .range (q + 1), i
    exact Finset.sum_lt_sum_of_subset (i := q) (Finset.range_mono (by omega))
      (by simp) (by simp; omega) (by omega) (by intros; omega)
  let f : A → ℕ := fun ⟨ (n, m), _ ⟩ ↦ a n + m
  have hf : Function.Injective f := by
    rintro ⟨ ⟨ n, m ⟩, hnm ⟩ ⟨ ⟨ n',m'⟩, hnm' ⟩ h
    simp [A,f] at hnm hnm' ⊢ h
    obtain hnn' | rfl | hnn' := lt_trichotomy n n'
    . have : a n' + m' > a n + m := by calc
        _ ≥ a n' := by linarith
        _ ≥ a (n+1) := ha.monotone (by linarith)
        _ = a n + (n + 1) := Finset.sum_range_succ id _
        _ > a n + m := by linarith
      linarith
    . simpa using h
    have : a n + m > a n' + m' := by calc
        _ ≥ a n := by linarith
        _ ≥ a (n'+1) := ha.monotone (by linarith)
        _ = a n' + (n' + 1) := Finset.sum_range_succ id _
        _ > a n' + m' := by linarith
    linarith
  let f' : A → f '' .univ := fun p ↦ ⟨ f p, by aesop ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro p q hpq; simp [f'] at hpq; solve_by_elim
    intro ⟨ l, hl ⟩; simp at hl
    obtain ⟨ n, m, q, rfl ⟩ := hl; use ⟨ (n, m), q ⟩
  have : AtMostCountable A := by rw [AtMostCountable.equiv ⟨ _, hf' ⟩]; apply Nat.atMostCountable_subset
  have hfin : ¬ Finite A := by
    intro h
    have : Infinite ↑A := Set.infinite_coe_iff.mpr
      (Set.Infinite.mono (s := Set.range (fun n ↦ (n, 0)))
        (fun ⟨n, m⟩ ⟨k, hk⟩ ↦ by simp [A] at hk ⊢; omega)
        (Set.infinite_range_of_injective (fun a b h ↦ by simpa using h)))
    exact not_finite ↑A
  simp [AtMostCountable] at this; tauto

/-- Corollary 8.1.13 -/
theorem CountablyInfinite.prod_nat : CountablyInfinite (ℕ × ℕ) := by
  have upper_diag : CountablyInfinite { n : ℕ × ℕ | n.1 ≤ n.2 } := by
    refine (equiv ⟨ fun ⟨ (n, m), _ ⟩ ↦ ⟨ (m, n), by aesop ⟩, ?_, ?_ ⟩).mp lower_diag
    . intro ⟨ (_, _), _ ⟩ ⟨ (_, _), _ ⟩ _; aesop
    intro ⟨ (n, m), _ ⟩; use ⟨ (m, n), by aesop ⟩
  have : CountablyInfinite (.univ : Set (ℕ × ℕ)) := by
    convert union lower_diag upper_diag; ext ⟨ n, m ⟩; simp; omega
  exact (equiv (.univ _)).mp this

/-- Corollary 8.1.14 / Exercise 8.1.8 -/
theorem CountablyInfinite.prod {X Y:Type} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X × Y) := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  choose finv hfinv_left hfinv_right using Function.bijective_iff_has_inverse.mp hf
  choose ginv hginv_left hginv_right using Function.bijective_iff_has_inverse.mp hg
  let f' : X × Y → ℕ × ℕ := fun ⟨x, y⟩ ↦ ⟨f x, g y⟩
  have hf' : Function.Bijective f' := by
    constructor
    · intro ⟨x1, y1⟩ ⟨x2, y2⟩ h
      simp [f'] at h
      exact Prod.ext (hf.1 h.1) (hg.1 h.2)
    · intro ⟨n, m⟩; use ⟨finv n, ginv m⟩
      simp [f', hfinv_right n, hginv_right m]
  exact (equiv ⟨f', hf'⟩).mpr prod_nat

/-- Corollary 8.1.15 -/
theorem Rat.countablyInfinite : CountablyInfinite ℚ := by
  -- This proof is written to follow the structure of the original text.
  have : CountablyInfinite { n:ℤ | n ≠ 0 } := by
    rw [CountablyInfinite.iff']
    refine ⟨inferInstance, ?_⟩
    apply Infinite.of_injective (fun n : ℕ ↦ (⟨(n : ℤ) + 1, by exact ne_of_gt (by positivity)⟩ : {n : ℤ | n ≠ 0}))
    intro a b h; simp at h; omega
  apply Int.countablyInfinite.prod at this
  let f : ℤ × { n:ℤ | n ≠ 0 } → ℚ := fun (a,b) ↦ (a/b:ℚ)
  replace := AtMostCountable.image this f
  have h : f '' .univ = .univ := by
    ext q; simp [f]
    exact ⟨q.num, q.den, by exact_mod_cast q.den_ne_zero, by push_cast; exact q.num_div_den⟩
  simp [h, AtMostCountable.equiv (EqualCard.univ _), AtMostCountable] at this
  have hfin : ¬ Finite ℚ := by
    by_contra!
    replace : Finite (.univ : Set ℕ) := by
      apply @Finite.Set.finite_of_finite_image ℕ ℚ _ (↑·); intro _ _ _ _; simp
    rw [Set.finite_coe_iff, Set.finite_univ_iff,←not_infinite_iff_finite] at this
    apply this; infer_instance
  tauto

open Classical in
/-- Exercise 8.1.1 -/
example (X: Type) : Infinite X ↔ ∃ Y : Set X, Y ≠ .univ ∧ EqualCard Y X := by
  constructor
  . intro h
    -- Use ℕ ↪ X to build a proper subset bijective with X.
    -- Let g : ℕ ↪ X. Set Y = X \ {g 0}.
    -- Define f : Y → X that "shifts back" the g-indexed elements:
    --   f (g (n+1)) = g n    (shift back by 1)
    --   f x = x              (if x ∉ range g)
    -- This is a bijection Y → X, so EqualCard Y X.
    let g := Infinite.natEmbedding X
    use Set.univ \ {g 0}
    refine ⟨by simp, ?_⟩
    let f : (Set.univ \ {g 0} : Set X) → X := fun ⟨x, _⟩ =>
      if h : ∃ n, g (n + 1) = x then g h.choose else x
    use f
    have hmem : ∀ x : X, x ≠ g 0 → x ∈ (Set.univ \ {g 0} : Set X) :=
      fun x hx => Set.mem_diff_singleton.mpr ⟨Set.mem_univ _, hx⟩
    constructor
    · -- Injective
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have ha_ne : a ≠ g 0 := (Set.mem_diff_singleton.mp ha).2
      have hb_ne : b ≠ g 0 := (Set.mem_diff_singleton.mp hb).2
      simp only [f] at hab
      split_ifs at hab with h1 h2
      · have := g.injective hab
        exact Subtype.ext (h1.choose_spec.symm.trans (this ▸ h2.choose_spec))
      · exfalso
        rcases Nat.eq_zero_or_pos h1.choose with h0 | h0
        · exact hb_ne (hab.symm ▸ congrArg g h0)
        · exact h2 ⟨h1.choose - 1, by rw [show h1.choose - 1 + 1 = h1.choose from by omega]; exact hab⟩
      · exfalso; rename_i h2
        rcases Nat.eq_zero_or_pos h2.choose with h0 | h0
        · exact ha_ne (hab ▸ congrArg g h0)
        · exact h1 ⟨h2.choose - 1, by rw [show h2.choose - 1 + 1 = h2.choose from by omega]; exact hab.symm⟩
      · exact Subtype.ext hab
    · -- Surjective
      intro x
      by_cases hx : ∃ n, g n = x
      · obtain ⟨n, rfl⟩ := hx
        refine ⟨⟨g (n + 1), hmem _ (fun h => Nat.succ_ne_zero n (g.injective h))⟩, ?_⟩
        show (if h : ∃ m, g (m + 1) = g (n + 1) then g h.choose else g (n + 1)) = g n
        rw [dif_pos ⟨n, rfl⟩]
        have := Nat.succ_injective (g.injective (Exists.choose_spec (⟨n, rfl⟩ : ∃ m, g (m + 1) = g (n + 1))))
        exact congrArg g this
      · refine ⟨⟨x, hmem _ (fun h => hx ⟨0, h.symm⟩)⟩, ?_⟩
        show (if h : ∃ n_1, g (n_1 + 1) = x then g h.choose else x) = x
        exact dif_neg (fun ⟨n, h⟩ => hx ⟨n + 1, h⟩)
  . intro ⟨Y, hY, e⟩
    by_contra hfin
    have hfin : Finite X := Finite.of_not_infinite hfin
    obtain ⟨f, hf⟩ := e
    have heq : Nat.card Y = Nat.card X := Nat.card_eq_of_bijective f hf
    have hlt : Nat.card Y < Nat.card X := by
      calc Nat.card Y
          < Nat.card (Set.univ : Set X) :=
            Set.Finite.card_lt_card Set.finite_univ (Set.ssubset_univ_iff.mpr hY)
        _ = Nat.card X := Nat.card_univ
    omega


/-- Exercise 8.1.6 -/
theorem atMost_iff_injective (A: Type) : AtMostCountable A ↔ ∃ f : A → ℕ, Function.Injective f := by
  constructor
  . intro h
    cases' h with h h
    . obtain ⟨f, hf⟩ := h
      use f; exact hf.1
    . obtain ⟨f, hf⟩ := h
      use Fin.val ∘ f
      exact Fin.val_injective.comp (Function.HasLeftInverse.injective ⟨hf, ‹_›⟩)
  . intro ⟨f, hf⟩
    have hbij : Function.Bijective (fun a => (⟨f a, Set.mem_image_of_mem _ (Set.mem_univ a)⟩ : f '' Set.univ)) :=
      ⟨fun a b h => hf (Subtype.mk.inj h), fun ⟨_, a, _, rfl⟩ => ⟨a, rfl⟩⟩
    exact (AtMostCountable.equiv ⟨_, hbij⟩).mpr (Nat.atMostCountable_subset _)

private lemma fA_transport {I X : Type} {A : I → Set X}
    (fA : (i : I) → A i → ℕ) {i j : I} (hij : i = j)
    {x : X} (hi : x ∈ A i) (hj : x ∈ A j) :
    fA i ⟨x, hi⟩ = fA j ⟨x, hj⟩ := by subst hij; rfl

open Classical in
/-- Exercise 8.1.9 -/
example {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by
  obtain ⟨fi, hfi⟩ := (atMost_iff_injective I).mp hI
  choose fA hfA using fun i => (atMost_iff_injective (A i)).mp (hA i)
  obtain ⟨g, hg⟩ := CountablyInfinite.prod_nat
  let e := Equiv.ofBijective g hg
  let idx : (⋃ i, A i) → I := fun ⟨x, hx⟩ => (Set.mem_iUnion.mp hx).choose
  have hidx : ∀ (p : ⋃ i, A i), p.val ∈ A (idx p) :=
    fun ⟨x, hx⟩ => (Set.mem_iUnion.mp hx).choose_spec
  let f : (⋃ i, A i) → ℕ := fun p => e (fi (idx p), fA (idx p) ⟨p.val, hidx p⟩)
  have hf : Function.Injective f := by
    intro p q h
    have h' := e.injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have hi := hfi h1
    have hp_mem : p.val ∈ A (idx q) := hi ▸ hidx p
    have key : fA (idx q) ⟨p.val, hp_mem⟩ = fA (idx q) ⟨q.val, hidx q⟩ := by
      linarith [fA_transport fA hi (hidx p) hp_mem]
    exact Subtype.ext (congrArg (Subtype.val (p := (· ∈ A (idx q)))) (hfA _ key))
  exact (atMost_iff_injective _).mpr ⟨f, hf⟩

/-- Stern's diatomic sequence (fusc function).
  fusc(0) = 0, fusc(1) = 1, fusc(2n) = fusc(n), fusc(2n+1) = fusc(n) + fusc(n+1). -/
def fusc : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then fusc ((n + 2) / 2)
    else fusc ((n + 2) / 2) + fusc ((n + 2) / 2 + 1)

@[simp] theorem fusc_zero : fusc 0 = 0 := by native_decide
@[simp] theorem fusc_one : fusc 1 = 1 := by native_decide
@[simp] theorem fusc_two : fusc 2 = 1 := by native_decide

theorem fusc_even (n : ℕ) (hn : n ≥ 1) : fusc (2 * n) = fusc n := by
  rw [show 2 * n = (2 * n - 2) + 2 from by omega]
  simp only [fusc]
  rw [if_pos (show (2 * n - 2 + 2) % 2 = 0 from by omega)]
  congr 1; omega

theorem fusc_odd (n : ℕ) (hn : n ≥ 1) : fusc (2 * n + 1) = fusc n + fusc (n + 1) := by
  rw [show 2 * n + 1 = (2 * n - 1) + 2 from by omega]
  simp only [fusc]
  rw [if_neg (show ¬ ((2 * n - 1 + 2) % 2 = 0) from by omega)]
  congr 1 <;> congr 1 <;> omega

theorem fusc_pos (n : ℕ) (hn : n ≥ 1) : fusc n > 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  obtain rfl | hn1 := eq_or_lt_of_le' hn
  · simp
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n = 2 * k from by omega, fusc_even _ (by omega)]
    exact ih _ (by omega) (by omega)
  · rw [show n = 2 * k + 1 from by omega, fusc_odd _ (by omega)]
    have := ih k (by omega) (by omega)
    omega

theorem fusc_coprime (n : ℕ) (hn : n ≥ 1) : Nat.Coprime (fusc n) (fusc (n + 1)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  obtain rfl | hn1 := eq_or_lt_of_le' hn
  · simp [Nat.Coprime]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n = 2 * k from by omega, fusc_even _ (by omega),
        show 2 * k + 1 = 2 * k + 1 from rfl, fusc_odd _ (by omega)]
    exact Nat.coprime_self_add_right.mpr (ih k (by omega) (by omega))
  · rw [show n = 2 * k + 1 from by omega, fusc_odd _ (by omega),
        show 2 * k + 1 + 1 = 2 * (k + 1) from by omega, fusc_even _ (by omega)]
    exact Nat.coprime_add_self_left.mpr (ih k (by omega) (by omega))

theorem fusc_even_lt (k : ℕ) (hk : k ≥ 1) : fusc (2 * k) < fusc (2 * k + 1) := by
  rw [fusc_even _ hk, fusc_odd _ hk]; linarith [fusc_pos (k + 1) (by omega)]

theorem fusc_odd_gt (k : ℕ) (hk : k ≥ 1) : fusc (2 * k + 1) > fusc (2 * (k + 1)) := by
  rw [fusc_odd _ hk, fusc_even _ (by omega)]; linarith [fusc_pos k (by omega)]

theorem even_of_fusc_lt (n : ℕ) (hn : n ≥ 2) (h : fusc n < fusc (n + 1)) :
    ∃ k ≥ 1, n = 2 * k := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, by omega, by omega⟩
  · exfalso; have h1 := fusc_odd_gt k (by omega)
    rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega] at h; linarith

theorem odd_of_fusc_gt (n : ℕ) (hn : n ≥ 2) (h : fusc n > fusc (n + 1)) :
    ∃ k ≥ 1, n = 2 * k + 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso; have h1 := fusc_even_lt k (by omega)
    -- hk : n = k + k, so h becomes fusc(k+k) > fusc(k+k+1)
    -- rewrite k+k to 2*k and k+k+1 to 2*k+1
    rw [show n = 2 * k from by omega] at h
    rw [show 2 * k + 1 = 2 * k + 1 from rfl] at h; linarith
  · exact ⟨k, by omega, by omega⟩

theorem fusc_ne_succ (n : ℕ) (hn : n ≥ 2) : fusc n ≠ fusc (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have := fusc_even_lt k (by omega)
    rw [show n = 2 * k from by omega]; exact ne_of_lt (by linarith)
  · have := fusc_odd_gt k (by omega)
    rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega]; omega

private theorem fusc_pair_one (n : ℕ) (hn : n ≥ 1) (h1 : fusc n = 1) (h2 : fusc (n + 1) = 1) :
    n = 1 := by
  obtain rfl | hn2 := eq_or_lt_of_le' hn; · rfl
  exact absurd (h1.symm ▸ h2.symm ▸ rfl : fusc n = fusc (n + 1)) (fusc_ne_succ n hn2)

theorem fusc_pair_injective (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (h1 : fusc m = fusc n) (h2 : fusc (m + 1) = fusc (n + 1)) : m = n := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
  obtain rfl | hm2 := eq_or_lt_of_le' hm
  · simp at h1 h2; exact (fusc_pair_one n hn h1.symm h2.symm).symm
  obtain rfl | hn2 := eq_or_lt_of_le' hn
  · simp at h1 h2; exact fusc_pair_one m hm h1 h2
  -- m, n ≥ 2: detect parity from fusc m vs fusc(m+1)
  rcases lt_trichotomy (fusc m) (fusc (m + 1)) with hlt | heq | hgt
  · -- fusc m < fusc(m+1) ⇒ m even; same comparison for n via h1,h2 ⇒ n even
    obtain ⟨j, hj, rfl⟩ := even_of_fusc_lt m hm2 hlt
    obtain ⟨l, hl, rfl⟩ := even_of_fusc_lt n hn2 (h1 ▸ h2 ▸ hlt)
    rw [fusc_even _ hj, fusc_even _ hl] at h1
    rw [show 2 * j + 1 = 2 * j + 1 from rfl, show 2 * l + 1 = 2 * l + 1 from rfl,
        fusc_odd _ hj, fusc_odd _ hl] at h2
    have := ih j (by omega) l (by omega) (by omega) h1 (by linarith)
    omega
  · exact absurd heq (fusc_ne_succ m hm2)
  · -- fusc m > fusc(m+1) ⇒ m odd; same for n
    obtain ⟨j, hj, rfl⟩ := odd_of_fusc_gt m hm2 hgt
    obtain ⟨l, hl, rfl⟩ := odd_of_fusc_gt n hn2 (h1 ▸ h2 ▸ hgt)
    rw [fusc_odd _ hj, fusc_odd _ hl] at h1
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by omega,
        show 2 * l + 1 + 1 = 2 * (l + 1) from by omega,
        fusc_even _ (by omega), fusc_even _ (by omega)] at h2
    have := ih j (by omega) l (by omega) (by omega) (by linarith) h2
    omega

theorem fusc_pair_surjective (a b : ℕ) (ha : a > 0) (hb : b > 0) (hc : Nat.Coprime a b) :
    ∃ n ≥ 1, fusc n = a ∧ fusc (n + 1) = b := by
  suffices h : ∀ s, ∀ a b : ℕ, a + b = s → a > 0 → b > 0 → Nat.Coprime a b →
      ∃ n ≥ 1, fusc n = a ∧ fusc (n + 1) = b from h _ a b rfl ha hb hc
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
  intro a b hs ha hb hc
  obtain rfl | hab := eq_or_ne a b
  · have : a = 1 := by rwa [Nat.Coprime, Nat.gcd_self] at hc
    subst this; exact ⟨1, by omega, by simp, by simp⟩
  rcases lt_or_gt_of_ne hab with hab | hab
  · -- a < b: IH with (a, b - a), then n = 2k
    have hc' : Nat.Coprime a (b - a) := (Nat.coprime_sub_self_right (by omega)).mpr hc
    obtain ⟨k, hk, hfk, hfk1⟩ := ih (a + (b - a)) (by omega) a (b - a) (by omega) ha (by omega) hc'
    refine ⟨2 * k, by omega, ?_, ?_⟩
    · rw [fusc_even _ (by omega)]; exact hfk
    · rw [fusc_odd _ (by omega), hfk, hfk1]; omega
  · -- a > b: IH with (a - b, b), then n = 2k+1
    have hc' : Nat.Coprime (a - b) b := (Nat.coprime_sub_self_left (by omega)).mpr hc
    obtain ⟨k, hk, hfk, hfk1⟩ := ih (a - b + b) (by omega) (a - b) b (by omega) (by omega) hb hc'
    refine ⟨2 * k + 1, by omega, ?_, ?_⟩
    · rw [fusc_odd _ (by omega), hfk, hfk1]; omega
    · rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega, fusc_even _ (by omega)]; exact hfk1

/-- The n-th positive rational in the Calkin-Wilf sequence (for n ≥ 1). -/
def calkinWilf (n : ℕ) : ℚ := fusc n / fusc (n + 1)

theorem calkinWilf_pos (n : ℕ) (hn : n ≥ 1) : calkinWilf n > 0 := by
  simp only [calkinWilf]
  exact div_pos (Nat.cast_pos.mpr (fusc_pos n hn)) (Nat.cast_pos.mpr (fusc_pos (n + 1) (by omega)))

theorem calkinWilf_injective (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1)
    (h : calkinWilf m = calkinWilf n) : m = n := by
  simp only [calkinWilf] at h
  rw [show (fusc m : ℚ) = ((fusc m : ℤ) : ℚ) from by push_cast; ring,
      show (fusc (m + 1) : ℚ) = ((fusc (m + 1) : ℤ) : ℚ) from by push_cast; ring,
      show (fusc n : ℚ) = ((fusc n : ℤ) : ℚ) from by push_cast; ring,
      show (fusc (n + 1) : ℚ) = ((fusc (n + 1) : ℤ) : ℚ) from by push_cast; ring] at h
  have := Rat.div_int_inj
    (by exact_mod_cast fusc_pos (m + 1) (by omega))
    (by exact_mod_cast fusc_pos (n + 1) (by omega))
    (by exact_mod_cast fusc_coprime m hm)
    (by exact_mod_cast fusc_coprime n hn) h
  exact fusc_pair_injective m n hm hn (by exact_mod_cast this.1) (by exact_mod_cast this.2)

theorem calkinWilf_surjective (q : ℚ) (hq : q > 0) :
    ∃ n ≥ 1, calkinWilf n = q := by
  have hnum : q.num > 0 := Rat.num_pos.mpr hq
  obtain ⟨n, hn, hfn, hfn1⟩ := fusc_pair_surjective q.num.natAbs q.den
    (by omega) q.pos q.reduced
  refine ⟨n, hn, ?_⟩
  simp only [calkinWilf, hfn, hfn1]
  have : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum.le
  rw [show (q.num.natAbs : ℚ) = ((q.num.natAbs : ℤ) : ℚ) from by simp, this]
  exact Rat.num_div_den q

/-- Exercise 8.1.10.  Note the lack of the `noncomputable` keyword in the `abbrev`.
  Uses the Calkin-Wilf enumeration: 0 ↦ 0, 2k+1 ↦ CW(k+1), 2k+2 ↦ -CW(k+1). -/
abbrev explicit_bijection (n : ℕ) : ℚ :=
  if n = 0 then 0
  else if n % 2 = 1 then calkinWilf ((n + 1) / 2)
  else -calkinWilf (n / 2)

@[simp] private theorem eb_zero : explicit_bijection 0 = 0 := rfl

@[simp] private theorem eb_odd (k : ℕ) :
    explicit_bijection (2 * k + 1) = calkinWilf (k + 1) := by
  unfold explicit_bijection; simp [show (2 * k + 1 + 1) / 2 = k + 1 from by omega]

@[simp] private theorem eb_even (k : ℕ) :
    explicit_bijection (2 * (k + 1)) = -calkinWilf (k + 1) := by
  unfold explicit_bijection; simp [show 2 * (k + 1) / 2 = k + 1 from by omega]

private theorem eb_pos_of_odd (k : ℕ) : explicit_bijection (2 * k + 1) > 0 := by
  rw [eb_odd]; exact calkinWilf_pos _ (by omega)

private theorem eb_neg_of_even (k : ℕ) : explicit_bijection (2 * (k + 1)) < 0 := by
  rw [eb_even]; linarith [calkinWilf_pos (k + 1) (by omega)]

theorem explicit_bijection_spec : Function.Bijective explicit_bijection := by
  have cases (n : ℕ) (hn : n ≠ 0) : (∃ k, n = 2 * k + 1) ∨ (∃ k, n = 2 * (k + 1)) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · right; exact ⟨k - 1, by omega⟩
    · left; exact ⟨k, by omega⟩
  constructor
  · -- Injective
    intro a b h
    by_contra hab
    rcases eq_or_ne a 0 with rfl | ha <;> rcases eq_or_ne b 0 with rfl | hb
    · exact hab rfl
    · rcases cases b hb with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp at h; linarith [calkinWilf_pos (k + 1) (by omega)]
      · simp at h; linarith [calkinWilf_pos (k + 1) (by omega)]
    · rcases cases a ha with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp at h; linarith [calkinWilf_pos (k + 1) (by omega)]
      · simp at h; linarith [calkinWilf_pos (k + 1) (by omega)]
    · rcases cases a ha with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> rcases cases b hb with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp at h; exact hab (by have := calkinWilf_injective _ _ (by omega) (by omega) h; omega)
      · simp at h; linarith [calkinWilf_pos (j + 1) (by omega), calkinWilf_pos (k + 1) (by omega)]
      · simp at h; linarith [calkinWilf_pos (j + 1) (by omega), calkinWilf_pos (k + 1) (by omega)]
      · simp at h; exact hab (by have := calkinWilf_injective _ _ (by omega) (by omega) h; omega)
  · -- Surjective
    intro q
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · obtain ⟨k, hk, hcwk⟩ := calkinWilf_surjective (-q) (by linarith)
      refine ⟨2 * ((k - 1) + 1), ?_⟩
      rw [eb_even, show k - 1 + 1 = k from by omega]; linarith
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk, hcwk⟩ := calkinWilf_surjective q hq
      refine ⟨2 * (k - 1) + 1, ?_⟩; simp; rw [show k - 1 + 1 = k from by omega]; exact hcwk

end Chapter8
