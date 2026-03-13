import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

/-!
# Analysis I, Section 8.3: Uncountable sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Uncountable sets.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

-/

namespace Chapter8

/-- Theorem 8.3.1 -/
theorem EqualCard.power_set_false (X:Type) : ¬ EqualCard X (Set X) := by
  -- This proof is written to follow the structure of the original text.
  by_contra!; choose f hf using this
  set A := {x | x ∉ f x }; choose x hx using hf.2 A
  by_cases h : x ∈ A <;> have h' := h
  . simp [A] at h'; simp_all
  rw [←hx] at h'
  have : x ∈ A := by simp [A, h']
  contradiction

theorem Uncountable.iff (X:Type) : Uncountable X ↔ ¬ AtMostCountable X := by
  rw [AtMostCountable.iff, uncountable_iff_not_countable]


theorem Uncountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Uncountable X ↔ Uncountable Y := by
    simp [Uncountable.iff, AtMostCountable.equiv hXY]

/-- Corollary 8.3.3 -/
theorem Uncountable.power_set_nat : Uncountable (Set ℕ) := by
  -- This proof is written to follow the structure of the original text.
  rw [Uncountable.iff]
  unfold AtMostCountable
  have : ¬ CountablyInfinite (Set ℕ) := by
    have := EqualCard.power_set_false ℕ
    contrapose! this; exact this.symm
  have : ¬ Finite (Set ℕ) := by
    by_contra!
    have : Finite ((fun x:ℕ ↦ ({x}:Set ℕ)) '' .univ) := Finite.Set.subset (s := .univ) (by aesop)
    replace : Finite ℕ := by
      apply Finite.of_finite_univ
      rw [←Set.finite_coe_iff]
      apply Finite.Set.finite_of_finite_image (f := fun x ↦ ({x}:Set ℕ))
      intro _ _ _ _ _; aesop
    have hinf : ¬ Finite ℕ := by rw [not_finite_iff_infinite]; infer_instance
    contradiction
  tauto

open Real in
/-- Corollary 8.3.4 -/
theorem Uncountable.real : Uncountable ℝ := by
  -- This proof is written to follow the structure of the original text.
  set a : ℕ → ℝ := fun n ↦ (10:ℝ)^(-(n:ℝ))
  set f : Set ℕ → ℝ := fun A ↦ ∑' n:A, a n
  have hsummable (A: Set ℕ) : Summable (fun n:A ↦ a n) := by
    apply Summable.subtype (f := a)
    convert summable_geometric_of_lt_one (?_:0 ≤ (1/10:ℝ)) ?_ using 2 with n <;> try norm_num
    unfold a
    rw [one_div_pow, rpow_neg, one_div]; simp; norm_num
  have h_decomp {A B C: Set ℕ} (hC : C = A ∪ B) (hAB: ∀ n, n ∉ A ∩ B) :  ∑' n:C, a n = ∑' n:A, a n + ∑' n:B, a n := by
    convert Summable.tsum_union_disjoint ?_ ?_ ?_ <;> first | infer_instance | try apply hsummable
    . rw [hC]
    rw [Set.disjoint_iff_inter_eq_empty]; grind
  have h_nonneg (A:Set ℕ) : ∑' n:A, a n ≥ 0 := by simp [a]; positivity
  have h_congr {A B: Set ℕ} (hAB: A = B) : ∑' n:A, a n = ∑' n:B, a n  := by rw [hAB]
  have : Function.Injective f := by
    intro A B hAB; by_contra!
    rw [←Set.symmDiff_nonempty] at this
    apply Nat.min_spec at this
    set n₀ := Nat.min (symmDiff A B)
    simp [symmDiff] at this; choose h1 h2 using this
    wlog h : n₀ ∈ A ∧ n₀ ∉ B generalizing A B
    . simp [h] at h1
      apply this hAB.symm <;> simp [symmDiff_comm] <;> grind
    replace h2 {n:ℕ} (hn: n < n₀) : n ∈ A ↔ n ∈ B := by grind
    have : (0:ℝ) > 0 := calc
      _ = f A - f B := by linarith
      _ = ∑' n:A, a n - ∑' n:B, a n := rfl
      _ = (∑' n:{n ∈ A|n ≤ n₀}, a n + ∑' n:{n ∈ A|n > n₀}, a n) -
          (∑' n:{n ∈ B|n ≤ n₀}, a n + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp; grind
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + ∑' n:{n ∈ A|n = n₀}, a n) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + ∑' n:{n ∈ B|n = n₀}, a n) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp [le_iff_lt_or_eq]
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + a n₀) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + 0) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr 3
        . calc
            _ = ∑' n:({n₀}:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
        . calc
            _ = ∑' n:(∅:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
      _ = (∑' n:{n ∈ A|n < n₀}, a n - ∑' n:{n ∈ B|n < n₀}, a n) + a n₀ +
          ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by abel
      _ = 0 + a n₀ + ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by
        congr; rw [sub_eq_zero]; apply tsum_congr_set_coe; grind
      _ ≥ 0 + a n₀ + 0 - ∑' n:{n|n > n₀}, a n := by
        gcongr; positivity
        calc
          _ = ∑' (n : {n ∈ B|n > n₀}), a n + ∑' (n : {n ∉ B|n > n₀}), a n := by
            apply h_decomp
            . ext n; simp; tauto
            intro n hn; simp at hn; tauto
          _ ≥ ∑' (n : {n ∈ B|n > n₀}), a n + 0 := by gcongr; solve_by_elim
          _ = _ := by simp
      _ = 0 + (10:ℝ)^(-(n₀:ℝ)) + 0 - (1 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by
        congr
        set ι : ℕ → {n | n > n₀} := fun j ↦ ⟨ j+(n₀+1), by simp; linarith ⟩
        have hι : Function.Bijective ι := by
          split_ands
          . intro j k hjk; simpa [ι] using hjk
          intro ⟨ n, hn ⟩; simp [ι] at hn ⊢; use n - n₀ - 1; omega
        rw [←(Equiv.ofBijective ι hι).tsum_eq]
        simp [ι,a]
        calc
          _ = ∑' j:ℕ, (10:ℝ)^(-1-n₀:ℝ) * (1/(10:ℝ))^j := by
            apply tsum_congr; intro j
            rw [pow_add, pow_add, rpow_sub, rpow_neg, rpow_one, rpow_natCast] <;> try positivity
            simp; congr
          _ = (10:ℝ)^(-1-n₀:ℝ) * ∑' j:ℕ, (1/(10:ℝ))^j := tsum_mul_left
          _ = _ := by
            rw [tsum_geometric_of_lt_one, (?_:-1 - (n₀:ℝ) = (-n₀:ℝ) + (-1:ℝ)),
                rpow_add, rpow_neg, rpow_natCast] <;> try positivity
            ring; abel; norm_num
      _ = (8 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by ring
      _ > 0 := by positivity
    simp at this
  replace : EqualCard (Set ℕ) (Set.range f) := ⟨(Equiv.ofInjective _ this).toFun, (Equiv.ofInjective _ this).bijective⟩
  replace := (equiv this).mp power_set_nat
  contrapose this
  rw [not_uncountable_iff] at this ⊢
  apply SetCoe.countable

open Classical in
/-- Exercise 8.3.1 -/
example {X:Type} [Finite X] : Nat.card (Set X) = 2 ^ Nat.card X := by
  have := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card]
  induction' h : Fintype.card X with n' ih generalizing X
  · haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp h
    have : Unique (Set X) := Set.uniqueEmpty
    simp [Fintype.card_unique]
  · have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨x₀⟩ := this
    set Y := {x : X | x ≠ x₀}
    -- Each subset S of X is determined by: its restriction to Y, and whether x₀ ∈ S
    have equiv : Set X ≃ Set Y × Prop := {
      toFun := fun S ↦ (fun ⟨x, hx⟩ ↦ S x, x₀ ∈ S)
      invFun := fun ⟨T, p⟩ ↦ fun x ↦ if h : x = x₀ then p else T ⟨x, h⟩
      left_inv := by
        intro S; ext x
        show (if h : x = x₀ then x₀ ∈ S else S x) ↔ S x
        split_ifs with h <;> [subst h; skip] <;> rfl
      right_inv := by
        intro ⟨T, p⟩
        ext ⟨x, hx⟩
        · show (if h : (x : X) = x₀ then p else T ⟨x, h⟩) ↔ T ⟨x, hx⟩
          rw [dif_neg hx]
        · show (if h : x₀ = x₀ then p else T ⟨x₀, h⟩) ↔ p
          simp
    }
    have hcard_Y : Fintype.card Y = n' := by
      have : Y = ({x₀}ᶜ : Set X) := by ext; simp [Y, ne_eq]
      rw [Fintype.card_congr (Equiv.setCongr this), Fintype.card_compl_set]; simp [h]
    rw [Fintype.card_congr equiv, Fintype.card_prod, Fintype.card_prop,
        @ih Y _ _ hcard_Y]
    omega


open Classical in
/-- Exercise 8.3.2.  Some subtle type changes due to how sets are implemented in Mathlib. Also we shift the sequence `D` by one so that we can work in `Set A` rather than `Set B`. -/
theorem Schroder_Bernstein_lemma {X: Type} {A B C: Set X} (hAB: A ⊆ B) (hBC: B ⊆ C) (f: C ↪ A) :
    let D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A})
      (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
    Set.univ.PairwiseDisjoint D ∧
    let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
    Function.Bijective g := by
  constructor
  . intro n hn m hm hmn
    wlog h : n < m
    . simp at this
      have h' : m < n := by omega
      have h := this hAB hBC f hmn.symm h'
      exact disjoint_comm.mpr h
    -- x ∈ D n means x = f(b) for some chain of n applications; similarly for D m.
    -- Since n < m, cancelling gives f applied (m-n) times lands in B \ A, contradicting f : C ↪ A.
    rw [Function.onFun]
    set D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A})
      (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
    change Disjoint (D n) (D m)
    set g := (A.embeddingOfSubset _ hAB)
    set e := (B.embeddingOfSubset _ hBC)
    -- All D k elements are in the range of f ∘ e
    have hD_range : ∀ k x, x ∈ D k → ∃ b : B, f (e b) = x := by
      intro k x hx
      cases k with
      | zero =>
        change x ∈ f.image (e.image {x : B | ↑x ∉ A}) at hx
        rw [Function.Embedding.image, Function.Embedding.image] at hx
        obtain ⟨c, ⟨b, _, rfl⟩, rfl⟩ := hx
        exact ⟨b, rfl⟩
      | succ k =>
        change x ∈ (f.image ∘ e.image ∘ g.image) (D k) at hx
        simp [Function.Embedding.image] at hx
        obtain ⟨a, ha_C, ⟨a₁, ha₁_B, ⟨a₂, ha₂_A, _, hga⟩, hea⟩, rfl⟩ := hx
        exact ⟨⟨a₁, ha₁_B⟩, by simp [e] at hea ⊢; exact hea⟩
    -- If x ∈ D (k+1) and f(e(b)) = x, then b ∈ A and the corresponding element of A is in D k
    have hD_preimage : ∀ k x, x ∈ D (k + 1) → ∀ b : B, f (e b) = x →
        ∃ (h : ↑b ∈ A), (⟨↑b, h⟩ : A) ∈ D k := by
      intro k x hx b hfb
      change x ∈ (f.image ∘ e.image ∘ g.image) (D k) at hx
      simp [Function.Embedding.image] at hx
      obtain ⟨c, hc_C, ⟨b', hb'_B, ⟨a, ha_A, ha_D, hga⟩, heb'⟩, hfc⟩ := hx
      have heq : e b = ⟨c, hc_C⟩ := f.injective (hfb.trans hfc.symm)
      have hb_eq_b' : (b : X) = b' := by
        have h1 : (e b).val = c := congr_arg Subtype.val heq
        have h2 : (e ⟨b', hb'_B⟩).val = c := congr_arg Subtype.val heb'
        simp [e, Set.embeddingOfSubset] at h1 h2; rw [h1, h2]
      have hb_eq_a : (b : X) = a := by
        have : (g ⟨a, ha_A⟩).val = a := rfl
        have : (⟨b', hb'_B⟩ : B).val = a := by
          rw [← this]; exact congr_arg Subtype.val hga.symm
        simp at this; rw [hb_eq_b']; exact this
      refine ⟨hb_eq_a ▸ ha_A, ?_⟩
      convert ha_D using 1
      ext; exact hb_eq_a
    -- D 0 elements come from B \ A: if f(e(b)) ∈ D 0 then ↑b ∉ A
    have hD0_preimage : ∀ x, x ∈ D 0 → ∀ b : B, f (e b) = x → ↑b ∉ A := by
      intro x hx b hfb
      change x ∈ f.image (e.image {x : B | ↑x ∉ A}) at hx
      simp [Function.Embedding.image] at hx
      obtain ⟨c, hc_C, ⟨b', hb'_notA, hb'_B, heb'⟩, hfc⟩ := hx
      have heq : e b = ⟨c, hc_C⟩ := f.injective (hfb.trans hfc.symm)
      have hb_eq_b' : (b : X) = b' := by
        have h1 : (e b).val = c := congr_arg Subtype.val heq
        have h2 : (e ⟨b', hb'_B⟩).val = c := congr_arg Subtype.val heb'
        simp [e, Set.embeddingOfSubset] at h1 h2; rw [h1, h2]
      rwa [hb_eq_b']
    suffices ∀ n m, n < m → Disjoint (D n) (D m) from this n m h
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Set.disjoint_left]
      intro x hx0 hxm
      obtain ⟨b₀, hb₀⟩ := hD_range 0 x hx0
      obtain ⟨b₁, hb₁⟩ := hD_range m x hxm
      have heq : e b₀ = e b₁ := f.injective (hb₀.trans hb₁.symm)
      have : b₀ = b₁ := e.injective heq
      subst this
      have hnotA := hD0_preimage x hx0 b₀ hb₀
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact hnotA (hD_preimage m' x hxm b₀ hb₁).1
    | succ n ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Set.disjoint_left]
      intro x hxn hxm
      obtain ⟨bn, hbn⟩ := hD_range (n + 1) x hxn
      obtain ⟨bm, hbm⟩ := hD_range (m' + 1) x hxm
      have : bn = bm := e.injective (f.injective (hbn.trans hbm.symm))
      subst this
      obtain ⟨_, h1⟩ := hD_preimage n x hxn bn hbn
      obtain ⟨_, h2⟩ := hD_preimage m' x hxm bn hbm
      exact Set.disjoint_left.mp (ih m' (by omega)) h1 h2
  . intro g
    set D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A})
      (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
    set e := (B.embeddingOfSubset _ hBC)
    set ι := (A.embeddingOfSubset _ hAB)
    set P : A → Prop := fun x ↦ x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x
    -- Every D k element is in the range of f ∘ e
    have hD_range : ∀ k x, x ∈ D k → ∃ b : B, f (e b) = x := by
      intro k x hx; cases k with
      | zero =>
        change x ∈ f.image (e.image {x : B | ↑x ∉ A}) at hx
        rw [Function.Embedding.image, Function.Embedding.image] at hx
        obtain ⟨c, ⟨b, _, rfl⟩, rfl⟩ := hx; exact ⟨b, rfl⟩
      | succ k =>
        change x ∈ (f.image ∘ e.image ∘ ι.image) (D k) at hx
        simp [Function.Embedding.image] at hx
        obtain ⟨a, ha_C, ⟨a₁, ha₁_B, ⟨a₂, ha₂_A, _, hga⟩, hea⟩, rfl⟩ := hx
        exact ⟨⟨a₁, ha₁_B⟩, by simp [e] at hea ⊢; exact hea⟩
    -- P holds iff x ∈ ⋃ n, D n (the ∃ y part is always satisfiable)
    have hP_iff : ∀ x, P x ↔ x ∈ ⋃ n, D n := by
      intro x; constructor
      · exact fun ⟨h, _⟩ ↦ h
      · intro hx; refine ⟨hx, ?_⟩
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        exact hD_range n x hn
    -- When P x holds, f(e(g x)) = x (g picks the preimage under f ∘ e)
    have hg_eq : ∀ x (h : P x), f (e (g x)) = x := by
      intro x hx
      have : f ⟨↑(g x), hBC (g x).property⟩ = x := by
        have : g x = hx.2.choose := dif_pos hx; simp [this, hx.2.choose_spec]
      exact this
    -- When P x doesn't hold, g x = ⟨↑x, hAB x.prop⟩
    have hg_not : ∀ x, ¬P x → g x = ⟨↑x, hAB x.property⟩ := by
      intro x hx; simp only [g]; rw [dif_neg hx]
    -- If x ∈ D (k+1) and f(e(b)) = x, then ↑b ∈ A and ⟨↑b, _⟩ ∈ D k
    have hD_preimage : ∀ k x, x ∈ D (k + 1) → ∀ b : B, f (e b) = x →
        ∃ (h : ↑b ∈ A), (⟨↑b, h⟩ : A) ∈ D k := by
      intro k x hx b hfb
      change x ∈ (f.image ∘ e.image ∘ ι.image) (D k) at hx
      simp [Function.Embedding.image] at hx
      obtain ⟨c, hc_C, ⟨b', hb'_B, ⟨a, ha_A, ha_D, hga⟩, heb'⟩, hfc⟩ := hx
      have heq : e b = ⟨c, hc_C⟩ := f.injective (hfb.trans hfc.symm)
      have hb_eq_b' : (b : X) = b' := by
        have h1 : (e b).val = c := congr_arg Subtype.val heq
        have h2 : (e ⟨b', hb'_B⟩).val = c := congr_arg Subtype.val heb'
        simp [e, Set.embeddingOfSubset] at h1 h2; rw [h1, h2]
      have hb_eq_a : (b : X) = a := by
        have : (ι ⟨a, ha_A⟩).val = a := rfl
        have : (⟨b', hb'_B⟩ : B).val = a := by
          rw [← this]; exact congr_arg Subtype.val hga.symm
        simp at this; rw [hb_eq_b']; exact this
      refine ⟨hb_eq_a ▸ ha_A, ?_⟩
      convert ha_D using 1; ext; exact hb_eq_a
    -- D 0 elements come from B \ A
    have hD0_preimage : ∀ x, x ∈ D 0 → ∀ b : B, f (e b) = x → ↑b ∉ A := by
      intro x hx b hfb
      change x ∈ f.image (e.image {x : B | ↑x ∉ A}) at hx
      simp [Function.Embedding.image] at hx
      obtain ⟨c, hc_C, ⟨b', hb'_notA, hb'_B, heb'⟩, hfc⟩ := hx
      have heq : e b = ⟨c, hc_C⟩ := f.injective (hfb.trans hfc.symm)
      have hb_eq_b' : (b : X) = b' := by
        have h1 : (e b).val = c := congr_arg Subtype.val heq
        have h2 : (e ⟨b', hb'_B⟩).val = c := congr_arg Subtype.val heb'
        simp [e, Set.embeddingOfSubset] at h1 h2; rw [h1, h2]
      rwa [hb_eq_b']
    -- If x ∈ D (k+1), g x lands in D k; if x ∈ D 0, g x lands outside A
    have hg_preimage : ∀ x, P x → ∀ k, x ∈ D (k + 1) →
        ∃ (h : ↑(g x) ∈ A), (⟨↑(g x), h⟩ : A) ∈ D k := by
      intro x hx k hxk
      exact hD_preimage k x hxk (g x) (hg_eq x hx)
    have hg_D0 : ∀ x, P x → x ∈ D 0 → ↑(g x) ∉ A := by
      intro x hx hx0
      exact hD0_preimage x hx0 (g x) (hg_eq x hx)
    constructor
    . intro x y hxy
      by_cases hx : P x <;> by_cases hy : P y
      · -- Both in ⋃ D: f(e(g x)) = x and f(e(g y)) = y, g x = g y → x = y
        calc x = f (e (g x)) := (hg_eq x hx).symm
          _ = f (e (g y)) := by rw [hxy]
          _ = y := hg_eq y hy
      -- Neither in ⋃ D: g is identity, so ↑x = ↑y
      on_goal 3 =>
        have hgx := hg_not x hx; have hgy := hg_not y hy
        ext; show (x : X) = ↑y
        have : (g x : X) = ↑(g y) := congr_arg Subtype.val hxy
        simp [hgx, hgy] at this; exact this
      -- One in ⋃ D, one not: the two mixed cases are symmetric
      all_goals {
        exfalso
        have ⟨a, b, hab, ha, hb⟩ : ∃ a b, g a = g b ∧ P a ∧ ¬P b := by
          first | exact ⟨x, y, hxy, ‹_›, ‹_›⟩ | exact ⟨y, x, hxy.symm, ‹_›, ‹_›⟩
        have hgb := hg_not b hb
        have hval : (g a : X) = ↑b := by rw [hab, hgb]
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ((hP_iff a).mp ha)
        cases n with
        | zero =>
          have := hg_D0 a ha hn
          rw [hval] at this; exact this b.property
        | succ n =>
          obtain ⟨hgA, hgDn⟩ := hg_preimage a ha n hn
          have : (⟨↑b, by rwa [← hval]⟩ : A) ∈ D n := by convert hgDn using 1; ext; exact hval.symm
          exact hb ((hP_iff b).mpr (Set.mem_iUnion.mpr ⟨n, this⟩))
      }
    -- SURJECTIVITY
    . intro y
      by_cases hy_A : (y : X) ∈ A
      · set x : A := ⟨↑y, hy_A⟩
        by_cases hx : P x
        · -- x ∈ ⋃ D: lift x to D (n+1) via z = f(e(ι(x))), then g z = ι(x) = y
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ((hP_iff x).mp hx)
          set z : A := f (e (ι x))
          have hz : z ∈ D (n + 1) := by
            change z ∈ (f.image ∘ e.image ∘ ι.image) (D n)
            simp [Function.Embedding.image]
            exact ⟨(e (ι x)).val, (e (ι x)).property,
              ⟨(ι x).val, (ι x).property, ⟨x.val, x.property, hn, rfl⟩, rfl⟩, rfl⟩
          have hPz : P z := (hP_iff z).mpr (Set.mem_iUnion.mpr ⟨n + 1, hz⟩)
          use z
          have : g z = ι x :=
            e.injective (f.injective ((hg_eq z hPz).trans rfl))
          rw [this]; ext; simp [ι, x, Set.embeddingOfSubset]
        · -- x ∉ ⋃ D: g x = ⟨↑x, _⟩ = ⟨↑y, _⟩ = y
          exact ⟨x, by rw [hg_not x hx]⟩
      · -- y ∉ A: y ∈ B \ A, so f(e(y)) ∈ D 0
        have hD0 : f (e y) ∈ D 0 := by
          change f (e y) ∈ f.image (e.image {x : B | ↑x ∉ A})
          rw [Function.Embedding.image, Function.Embedding.image]
          exact ⟨e y, ⟨y, hy_A, rfl⟩, rfl⟩
        set z := f (e y)
        have hPz : P z := (hP_iff z).mpr (Set.mem_iUnion.mpr ⟨0, hD0⟩)
        use z
        exact e.injective (f.injective ((hg_eq z hPz).trans rfl))

abbrev LeCard (X Y: Type) : Prop := ∃ f: X → Y, Function.Injective f

/-- Exercise 8.3.3 -/
theorem Schroder_Bernstein {X Y:Type} (hXY : LeCard X Y) (hYX : LeCard Y X) : EqualCard X Y := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYX
  -- Embed into X: A = range(g ∘ f) ⊆ B = range(g) ⊆ C = univ
  set A := Set.range (g ∘ f)
  set B := Set.range g
  set C := Set.univ (α := X)
  have hAB : A ⊆ B := by intro x ⟨y, hy⟩; exact ⟨f y, hy⟩
  have hBC : B ⊆ C := Set.subset_univ _
  -- g ∘ f is injective, so it gives an embedding C ↪ A
  have hgf_inj := Function.Injective.comp hg hf
  let emb : C ↪ A := ⟨fun ⟨x, _⟩ ↦ ⟨g (f x), x, rfl⟩, by
    intro ⟨a, _⟩ ⟨b, _⟩ h; simp at h; exact Subtype.ext (hgf_inj h)⟩
  obtain ⟨_, hbij⟩ := Schroder_Bernstein_lemma hAB hBC emb
  -- Compose X ≃ A, A ≃ B (from the lemma), and B ≃ Y to get X ≃ Y
  let eqAB := Equiv.ofBijective _ hbij
  let eqX_A := Equiv.ofInjective (g ∘ f) hgf_inj
  let eqB_Y : B → Y := fun b ↦ (Set.mem_range.mp b.property).choose
  have eqB_Y_spec : ∀ b : B, g (eqB_Y b) = ↑b := fun b ↦
    (Set.mem_range.mp b.property).choose_spec
  have eqB_Y_bij : Function.Bijective eqB_Y := by
    constructor
    · intro a b h
      exact Subtype.ext ((eqB_Y_spec a).symm.trans (congr_arg g h |>.trans (eqB_Y_spec b)))
    · intro y; exact ⟨⟨g y, Set.mem_range.mpr ⟨y, rfl⟩⟩, hg (eqB_Y_spec _)⟩
  exact ⟨eqB_Y ∘ eqAB ∘ eqX_A, eqB_Y_bij.comp (eqAB.bijective.comp eqX_A.bijective)⟩

abbrev LtCard (X Y: Type) : Prop := LeCard X Y ∧ ¬ EqualCard X Y

/-- Exercise 8.3.4 -/
example {X:Type} : LtCard X (Set X) := by
  let f : X → Set X := fun x ↦ {x}
  have hf : Function.Injective f := by
    intro x y h
    simp [f] at h
    exact h
  have : ¬ EqualCard X (Set X) := EqualCard.power_set_false X
  exact ⟨⟨f, hf⟩, this⟩

example {A B C: Type} (hAB: LtCard A B) (hBC: LtCard B C) :
    LtCard A C := by
  obtain ⟨⟨f, hf⟩, hAB_lt⟩ := hAB
  obtain ⟨⟨g, hg⟩, hBC_lt⟩ := hBC
  constructor
  . use g ∘ f
    exact Function.Injective.comp hg hf
  . intro h
    have : EqualCard B C := by
      apply Schroder_Bernstein
      . exact ⟨g, hg⟩
      . obtain ⟨r, hr⟩ := h
        exact ⟨f ∘ (Equiv.ofBijective r hr).symm, hf.comp (Equiv.ofBijective r hr).symm.injective⟩
    contradiction

abbrev CardOrder : Preorder Type := {
  le := LeCard
  lt := LtCard
  le_refl := by
    intro x
    use id
    intro x y h
    simp at h
    exact h
  le_trans := by
    intro x y z hxy hyz
    obtain ⟨f, hf⟩ := hxy
    obtain ⟨g, hg⟩ := hyz
    use g ∘ f
    exact Function.Injective.comp hg hf
  lt_iff_le_not_ge := by
    intro x y
    constructor
    . rintro ⟨hxy, h⟩
      constructor
      . exact hxy
      . intro h'
        have := Schroder_Bernstein hxy h'
        contradiction
    . rintro ⟨hxy, h⟩
      constructor
      . exact hxy
      . intro h'
        have : EqualCard y x := by exact EqualCard.symm h'
        obtain ⟨r, hr⟩ := this
        rw [LeCard] at h
        push_neg at h
        specialize h r
        exact h hr.injective
}

/-- Exercise 8.3.5 -/
example (X:Type) : ¬ CountablyInfinite (Set X) := by
  intro hci
  have hXc : AtMostCountable X := by
    rw [AtMostCountable.iff]
    obtain ⟨f, hf⟩ := hci
    exact (hf.injective.comp Set.singleton_injective).countable
  rcases hXc with hX | hX
  · -- X countably infinite: transfer to Set ℕ
    obtain ⟨e, he⟩ := hX
    have : EqualCard (Set X) (Set ℕ) := by
      set eq := Equiv.ofBijective e he
      exact ⟨fun S ↦ eq '' S,
        fun S T h ↦ eq.injective.image_injective h,
        fun S ↦ ⟨eq.symm '' S, by ext n; simp⟩⟩
    exact absurd (Or.inl ((CountablyInfinite.equiv this).mp hci) : AtMostCountable (Set ℕ))
      ((Uncountable.iff (Set ℕ)).mp Uncountable.power_set_nat)
  · -- X finite: Set X finite, can't be countably infinite
    haveI := Fintype.ofFinite X
    exact absurd hci.toInfinite (not_infinite_iff_finite.mpr inferInstance)


end Chapter8
