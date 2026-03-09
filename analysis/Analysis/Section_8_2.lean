import Mathlib.Tactic
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_8_1

/-!
# Analysis I, Section 8.2: Summation on infinite sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Absolute convergence and summation on countably infinite or general sets.
- Connections with Mathlib's `Summable` and `tsum`.
- The Riemann rearrangement theorem.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

After this section, the summation notation developed here will be deprecated in favor of Mathlib's API for `Summable` and `tsum`.

-/

namespace Chapter8
open Chapter7 Chapter7.Series Finset Function Filter

/-- Definition 8.2.1 (Series on countable sets).  Note that with this definition, functions defined
on finite sets will not be absolutely convergent; one should use `AbsConvergent'` instead for such
cases.-/
abbrev AbsConvergent {X:Type} (f: X → ℝ) : Prop := ∃ g: ℕ → X, Bijective g ∧ (f ∘ g: Series).absConverges

theorem AbsConvergent.mk {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : AbsConvergent f := by use g

open Classical in
/-- The definition has been chosen to give a sensible value when `X` is finite, even though
`AbsConvergent` is by definition false in this context. -/
noncomputable abbrev Sum {X:Type} (f: X → ℝ) : ℝ := if h: AbsConvergent f then (f ∘ h.choose:Series).sum else
  if _hX: Finite X then (∑ x ∈ @univ X (Fintype.ofFinite X), f x) else 0

theorem Sum.of_finite {X:Type} [hX:Finite X] (f:X → ℝ) : Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x := by
  have : ¬ AbsConvergent f := by
    by_contra!; choose g hg _ using this
    rw [←hg.finite_iff, ←not_infinite_iff_finite] at hX; apply hX; infer_instance
  simp [Sum, this, hX]

theorem AbsConvergent.comp {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hf: AbsConvergent f) : (f ∘ g:Series).absConverges := by
  choose g' hbij hconv using hf
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).1 using 4 with n
  simp [hright (g n.toNat)]

theorem Sum.eq {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : (f ∘ g:Series).convergesTo (Sum f) := by
  have : AbsConvergent f := .mk h hfg
  simp [Sum, this]
  choose hbij hconv using this.choose_spec
  set g' := this.choose
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  convert convergesTo_sum (converges_of_absConverges hfg) using 1
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).2 using 4 with _ n
  by_cases hn : n ≥ 0 <;> simp [hn, hright (g n.toNat)]

theorem Sum.of_comp {X Y:Type} {f:X → ℝ} (h: AbsConvergent f) {g: Y → X} (hbij: Bijective g) : AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) := by
  choose g' hbij' hconv' using h
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hbij_g_inv_g' : Bijective (g_inv ∘ g') := .comp ⟨hright.injective, hleft.surjective⟩ hbij'
  have hident : (f ∘ g) ∘ g_inv ∘ g' = f ∘ g' := by ext n; simp [hright (g' n)]
  refine ⟨ ⟨ g_inv ∘ g', ⟨ hbij_g_inv_g', by convert hconv' ⟩ ⟩, ?_ ⟩
  have h := eq (f := f ∘ g) hbij_g_inv_g' (by convert hconv')
  rw [hident] at h
  solve_by_elim [convergesTo_uniq, eq]

@[simp]
theorem Finset.Icc_eq_cast (N:ℕ) : Icc 0 (N:ℤ) = map Nat.castEmbedding (.Icc 0 N) := by
  ext n; simp; constructor
  . intro ⟨ hn, _ ⟩; lift n to ℕ using hn; use n; simp_all
  rintro ⟨ _, ⟨ _, rfl ⟩ ⟩; simp_all

theorem Finset.Icc_empty {N:ℤ} (h: ¬ N ≥ 0) : Icc 0 N = ∅ := by
  ext; simp; intros; contrapose! h; linarith

/-- Theorem 8.2.2, preliminary version.  The arguments here are rearranged slightly from the text. -/
theorem sum_of_sum_of_AbsConvergent_nonneg {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) (hpos: ∀ n m, 0 ≤ f (n, m)) :
  (∀ n, ((fun m ↦ f (n, m)):Series).converges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set L := Sum f
  set a : ℕ → Series := fun n ↦ ((fun m ↦ f (n, m)):Series)
  have hLpos : 0 ≤ L := by
    simp [L, Sum, hf]; apply sum_of_nonneg; intro n; by_cases h: n ≥ 0 <;> simp [h]; grind
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by
    obtain ⟨ g, hg, hconv ⟩ := hf
    have hnn : (f ∘ g : Series).nonneg := by
      intro n; simp; split_ifs <;> simp [hpos]
    have hc := converges_of_absConverges hconv
    have hL := Sum.eq hg (AbsConvergent.comp hg ⟨g, hg, hconv⟩)
    have heq : (f ∘ g : Series).sum = L := sum_of_converges hL
    choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
    set N : ℕ := (X.image g_inv).sup id
    calc ∑ p ∈ X, f p
        ≤ ∑ p ∈ (Finset.Icc 0 N).image g, f p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_image]
            exact ⟨ g_inv p, Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Finset.le_sup (f := id)
              (Finset.mem_image_of_mem _ hp) ⟩, hright p ⟩
          · intro p _ _; exact hpos p.1 p.2
      _ = ∑ n ∈ Finset.Icc 0 N, f (g n) := by
          rw [Finset.sum_image]; intro _ _ _ _ h; exact hg.1 h
      _ = (f ∘ g : Series).partial ↑N := by
          simp [Series.partial, Finset.Icc_eq_cast]
      _ ≤ (f ∘ g : Series).sum := partial_le_sum_of_nonneg hnn hc ↑N
      _ = L := heq
  have hfinsum' (n M:ℕ) : (a n).partial M ≤ L := by
    simp [a, Series.partial, Finset.Icc_eq_cast]
    convert_to ∑ x ∈ .map (Embedding.sectR n ℕ) (.Icc 0 M), f x ≤ L
    . simp
    solve_by_elim
  have hnon (n:ℕ) : (a n).nonneg := by
    simp [a, nonneg]; intro m; split_ifs <;> simp [hpos]
  have hconv (n:ℕ) : (a n).converges := by
    rw [converges_of_nonneg_iff (hnon n)]
    use L; intro N; by_cases h: N ≥ 0
    . lift N to ℕ using h; solve_by_elim
    rw [partial_of_lt (by simp [a]; linarith)]; simp [hLpos]
  have (N M:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).partial M ≤ L := by
    by_cases hN : N ≥ 0; swap
    . simp [Finset.Icc_empty hN, hLpos]
    lift N to ℕ using hN
    by_cases hM : M ≥ 0; swap
    . convert hLpos; unfold Series.partial
      apply sum_eq_zero; intro n _
      simp [a, Finset.Icc_empty hM]
    lift M to ℕ using hM
    convert_to ∑ x ∈ (Icc 0 N) ×ˢ (.Icc 0 M), f x ≤ L
    . simp [a, sum_product, Series.partial]
    solve_by_elim
  replace (N:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).sum ≤ L := by
    apply le_of_tendsto' (x := .atTop) (tendsto_finset_sum _ _) (this N)
    solve_by_elim [convergesTo_sum]
  replace (N:ℤ) : (fun n ↦ (a n).sum:Series).partial N ≤ L := by
    convert this N with n hn; simp_all
  have hnon' : (fun n ↦ (a n).sum:Series).nonneg := by
    intro n; simp; split_ifs
    . exact sum_of_nonneg (hnon n.toNat)
    simp
  have hconv' : (fun n ↦ (a n).sum:Series).converges := by
    rw [converges_of_nonneg_iff hnon']; use L
  replace : (fun n ↦ (a n).sum:Series).sum ≤ L := le_of_tendsto' (convergesTo_sum hconv') this
  replace : (fun n ↦ (a n).sum:Series).sum = L := by
    apply le_antisymm this (le_of_forall_sub_le _); intro ε hε
    replace : ∃ X, ∑ p ∈ X, f p ≥ L - ε := by
      obtain ⟨ g, hg, hconv ⟩ := hf
      have hnn : (f ∘ g : Series).nonneg := by
        intro n; simp; split_ifs <;> simp [hpos]
      have hc := converges_of_absConverges hconv
      have hL := Sum.eq hg (AbsConvergent.comp hg ⟨g, hg, hconv⟩)
      obtain ⟨ N₀, hN ⟩ := (Metric.tendsto_atTop.mp hL ε hε)
      set N : ℕ := N₀.toNat
      use (Finset.Icc 0 N).image g
      rw [Finset.sum_image (by intro _ _ _ _ h; exact hg.1 h)]
      have := hN ↑N (by omega)
      rw [Real.dist_eq, abs_lt] at this
      simp [Series.partial, Finset.Icc_eq_cast] at this ⊢
      linarith [this.1]
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc 0 N) ×ˢ (Icc 0 M) := by
      use (X.image Prod.fst).sup id, (X.image Prod.snd).sup id
      intro ⟨ a, b ⟩ hx
      simp only [Finset.mem_product, Finset.mem_Icc]
      exact ⟨ ⟨ Nat.zero_le _, Finset.le_sup (f := id)
                (Finset.mem_image_of_mem Prod.fst hx) ⟩,
              ⟨ Nat.zero_le _, Finset.le_sup (f := id)
                (Finset.mem_image_of_mem Prod.snd hx) ⟩ ⟩
    choose N M hX' using this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Icc 0 N) ×ˢ (Icc 0 M), f p := sum_le_sum_of_subset_of_nonneg hX' (by solve_by_elim)
      _ = ∑ n ∈ Icc 0 N, ∑ m ∈ Icc 0 M, f (n, m) := sum_product _ _ _
      _ ≤ ∑ n ∈ Icc 0 N, (a n).sum := by
        apply sum_le_sum; intro n _
        convert partial_le_sum_of_nonneg (hnon n) (hconv n) M
        simp [a, Series.partial]
      _ = (fun n ↦ (a n).sum:Series).partial N := by simp [Series.partial]
      _ ≤ _ := partial_le_sum_of_nonneg hnon' hconv' _
  simp [a, hconv, ← this, Series.convergesTo_sum hconv']

/-- Theorem 8.2.2, second version -/
theorem sum_of_sum_of_AbsConvergent {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ n, ((fun m ↦ f (n, m)):Series).absConverges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set fplus := max f 0
  set fminus := max (-f) 0
  have hfplus_nonneg : ∀ n m, 0 ≤ fplus (n, m) := by intro n m; simp [fplus]
  have hfminus_nonneg : ∀ n m, 0 ≤ fminus (n, m) := by intro n m; simp [fminus]
  have hdiff : f = fplus - fminus := by
    ext ⟨ n, m ⟩; simp [fplus, fminus, max_def]; split_ifs <;> linarith
  have hfplus_conv : AbsConvergent fplus := by
    obtain ⟨ g, hg, hconv ⟩ := hf
    have h := (converges_of_le (s := (fplus ∘ g : Series)) (t := (f ∘ g : Series).abs)
      rfl (fun n hn ↦ ?_) hconv).1
    · exact ⟨ g, hg, h⟩
    simp only [fplus]; split_ifs with h
    · rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
    · exact absurd (by linarith [hn]) h
  have hfminus_conv : AbsConvergent fminus := by
    obtain ⟨ g, hg, hconv ⟩ := hf
    have h := (converges_of_le (s := (fminus ∘ g : Series)) (t := (f ∘ g : Series).abs)
      rfl (fun n hn ↦ ?_) hconv).1
    · exact ⟨ g, hg, h⟩
    simp only [fminus]; split_ifs with h
    · rw [abs_of_nonneg (le_max_right _ _)]
      simp only [Function.comp] at *
      exact max_le (neg_le_abs _) (abs_nonneg _)
    · exact absurd (by linarith [hn]) h
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    have hsum_conv := (Series.add (hfplus_conv' n) (hfminus_conv' n)).1
    set s : Series := ((fun m ↦ f (n, m)) : Series)
    set t : Series := ((fun m ↦ fplus (n, m)) : Series) + ((fun m ↦ fminus (n, m)) : Series)
    suffices h : ∀ k ≥ s.m, |s.seq k| ≤ t.seq k from
      (converges_of_le (s := s) (t := t) rfl h hsum_conv).1
    intro k hk
    show |s.seq k| ≤ (((fun m ↦ fplus (n, m)) : Series).seq k + ((fun m ↦ fminus (n, m)) : Series).seq k)
    simp only [s]; split_ifs with h
    · rw [show fplus (n, k.toNat) + fminus (n, k.toNat) = |f (n, k.toNat)| from by
        simp [fplus, fminus]]
    · exact absurd (by linarith [hk]) h
  convert convergesTo.sub hfplus_sum hfminus_sum using 1
  . -- encountered surprising difficulty with definitional equivalence here
    simp [hdiff]
    change (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum:Series)
      - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum:Series)
    convert_to (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (((fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum) - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum):ℕ → ℝ):Series)
    . convert sub_coe _ _
    rcongr _ n; simp
    convert (sub _ _).2 with m; rfl
    split_ifs with h <;> simp [h, HSub.hSub, Sub.sub]
    . solve_by_elim
    convert hfminus_conv' n.toNat
  have ⟨ g, hg, _ ⟩ := hf
  have h1 := Sum.eq hg (hf.comp hg)
  have hplus := Sum.eq hg (hfplus_conv.comp hg)
  have hminus := Sum.eq hg (hfminus_conv.comp hg)
  apply convergesTo_uniq h1 _
  convert (convergesTo.sub hplus hminus) using 3 with n
  split_ifs with h <;> simp [h, hdiff, HSub.hSub, Sub.sub]

/-- Theorem 8.2.2, third version -/
theorem sum_of_sum_of_AbsConvergent' {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
  (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set π: ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, p.1)
  have hπ: Bijective π := Involutive.bijective (congrFun rfl)
  have ⟨ g, hg, hconv ⟩ := hf
  convert sum_of_sum_of_AbsConvergent (f := f ∘ π) _ using 2
  . exact (Sum.of_comp hf hπ).2
  refine ⟨ _, hπ.comp hg, ?_ ⟩
  convert hconv using 2

/-- Theorem 8.2.2, fourth version -/
theorem sum_comm {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum := by
  simp [sum_of_converges (sum_of_sum_of_AbsConvergent hf).2,
        sum_of_converges (sum_of_sum_of_AbsConvergent' hf).2]

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
    AbsConvergent f ↔ BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ ) := by
  constructor
  . intro h
    have ⟨ g, hg, hconv ⟩ := h
    have hsum := Sum.eq hg hconv
    simp [bddAbove_def]; use (f ∘ g : Series).abs.sum; intro A
    have hnn : (f ∘ g : Series).abs.nonneg := fun n ↦ by simp; split_ifs <;> simp
    choose g_inv hleft hright using bijective_iff_has_inverse.mp hg
    classical
    set N : ℕ := (A.image g_inv).sup id
    calc ∑ x ∈ A, |f x|
        ≤ ∑ x ∈ (Finset.Icc 0 N).image g, |f x| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx; rw [Finset.mem_image]
            exact ⟨ g_inv x, Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Finset.le_sup (f := id)
              (Finset.mem_image_of_mem _ hx) ⟩, hright x ⟩
          · intro _ _ _; exact abs_nonneg _
      _ = ∑ n ∈ Finset.Icc 0 N, |f (g n)| := by
          rw [Finset.sum_image]; intro _ _ _ _ h; exact hg.1 h
      _ = (f ∘ g : Series).abs.partial ↑N := by
          simp [Series.partial, Finset.Icc_eq_cast]
      _ ≤ _ := partial_le_sum_of_nonneg hnn hconv ↑N
  . intro h
    simp [bddAbove_def] at h; choose L hL using h
    have ⟨ g, hg ⟩ := hX.symm
    refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    use L; intro N; by_cases hN: N ≥ 0
    . lift N to ℕ using hN
      set g':= Embedding.mk g hg.1
      convert hL (map g' (Icc 0 N))
      simp [Series.partial]; rfl
    rw [partial_of_lt (by simp; omega)]; exact le_trans (by simp) (hL ∅)
    · intro n; simp; split_ifs <;> simp

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]; use ∑ x, |f x|; intro A; apply Finset.sum_le_univ_sum_of_nonneg; simp

/-- Not in textbook, but should have been included. -/
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f := by
  constructor
  . intro hf; simp [bddAbove_def] at hf; choose L hL using hf
    have ⟨ g, hg ⟩ := hX.symm; refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    . use L; intro N; by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Embedding.mk g hg.1
        convert hL (map g' (Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp; apply partial_of_lt; grind
    simp [nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  intro hf; rwa [AbsConvergent.iff hX f] at hf

/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
  obtain ⟨ L, hL ⟩ := hf
  simp at hL
  set S := fun n : ℕ ↦ { x | |f x| > 1 / (↑n + 1) }
  have hfin (n : ℕ) : Set.Finite (S n) := by
    suffices ∀ A : Finset (S n), A.card ≤ ⌈L * (↑n + 1)⌉₊ from
      Set.finite_coe_iff.mp (have := fintypeOfFinsetCardLe _ this; Finite.of_fintype (S n))
    intro A
    by_contra h; push_neg at h
    have hle := Finset.card_nsmul_le_sum A (fun x ↦ |f x|) (1 / (↑n + 1))
      (fun x _ ↦ le_of_lt x.2)
    rw [nsmul_eq_mul] at hle
    have : L < ∑ x ∈ A.map (Embedding.subtype _), |f x| := by
      rw [Finset.sum_map]; exact
      calc L ≤ ⌈L * (↑n + 1)⌉₊ / (↑n + 1 : ℝ) := le_div_iff₀ (by positivity) |>.mpr (Nat.le_ceil _)
        _ < A.card * (1 / (↑n + 1)) := by rw [div_eq_mul_one_div]; gcongr
        _ ≤ _ := hle
    linarith [hL (Set.mem_range.mpr ⟨A.map (Embedding.subtype _), rfl⟩)]
  have hunion : { x | f x ≠ 0 } = ⋃ n, S n := by
    ext x; simp [S]; constructor
    · intro hx
      have habs : 0 < |f x| := abs_pos.mpr hx
      obtain ⟨ n, hn ⟩ := exists_nat_gt |f x|⁻¹
      exact ⟨n, inv_lt_of_inv_lt₀ (by positivity) (lt_of_lt_of_le hn (by simp))⟩
    · rintro ⟨ n, hn ⟩; exact abs_ne_zero.mp (ne_of_gt (lt_trans (by positivity) hn))
  rw [hunion]
  exact AtMostCountable.iUnion (.inl ⟨id, Function.bijective_id⟩) S fun n ↦ .inr (hfin n)


/-- Compare with Mathlib's `Summable.subtype`-/
theorem AbsConvergent'.subtype {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (A: Set X) :
  AbsConvergent' (fun x:A ↦ f x) := by
  apply BddAbove.mono _ hf
  intro z hz; simp at *; choose A hA using hz
  use A.map (Embedding.subtype _); simp [hA]

/-- A generalized sum.  Note that this will give junk values if `f` is not `AbsConvergent'`. -/
noncomputable abbrev Sum' {X:Type} (f: X → ℝ) : ℝ := Sum (fun x : { x | f x ≠ 0 } ↦ f x)

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_finsupp {X:Type} {f:X → ℝ} {A: Finset X} (h: ∀ x ∉ A, f x = 0) : Sum' f = ∑ x ∈ A, f x := by
  unfold Sum'
  set E := { x | f x ≠ 0 }
  have hE : E ⊆ A := by intro _; simp [E]; grind
  have hfin : Finite E := Finite.Set.subset _ hE
  set E' := E.toFinite.toFinset
  rw [Sum.of_finite (fun x:E ↦ f x), ←E'.sum_subtype (by simp [E'])]
  replace hE : E' ⊆ A := by aesop
  apply sum_subset hE; aesop

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_countable_supp {X:Type} {f:X → ℝ} {A: Set X} (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0) (hconv: AbsConvergent' f):
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) := by
  -- We can adapt the proof of `AbsConvergent'.of_countable` to establish absolute convergence on A.
  have hconv' : AbsConvergent (fun x:A ↦ f x) :=
    (AbsConvergent'.of_countable hA).mp (hconv.subtype A)
  rw [AbsConvergent'.of_countable hA]
  refine ⟨ hconv', ?_ ⟩
  set E := { x | f x ≠ 0 }
  -- The main challenge here is to relate a sum on E with a sum on A.  First, we show containment.
  have hE : E ⊆ A := by intro _; simp [E]; by_contra!; aesop
  -- Now, we map A back to the natural numbers, thus identifying E with a subset E' of ℕ.
  choose g hg using hA.symm
  have hsum := Sum.eq hg (hconv'.comp hg)
  set E' := { n | ↑(g n) ∈ E }
  set ι : E' → E := fun ⟨ n, hn ⟩ ↦ ⟨ g n, by aesop ⟩
  have hι: Bijective ι := by
    split_ands
    . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩ h; simp [ι, E', Subtype.val_inj] at *; exact hg.1 h
    . intro ⟨ x, hx ⟩; choose n hn using hg.2 ⟨ _, hE hx ⟩; use ⟨ n, by aesop ⟩; grind
  -- The cases of infinite and finite E' are handled separately.
  obtain hE' | hE' := Nat.atMostCountable_subset E'
  . --   use Nat.monotone_enum_of_infinite to enumerate E'
    --   show the partial sums of E' are a subsequence of the partial sums of A
    set hinf : Infinite E' := hE'.toInfinite
    choose a ha_bij ha_mono using (Nat.monotone_enum_of_infinite E').exists
    have : atTop.Tendsto (Nat.cast ∘ Subtype.val ∘ a: ℕ → ℤ) atTop := by
      apply tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop _)
      intro _ _ hnm; simp [ha_mono hnm]
    apply tendsto_nhds_unique  _ (hsum.comp this)
    have hconv'' : AbsConvergent (fun x:E ↦ f x) := by
      rw [←AbsConvergent'.of_countable]
      . exact hconv.subtype E
      apply (CountablyInfinite.equiv _).mp hE'; use ι
    replace := Sum.eq (hι.comp ha_bij) (hconv''.comp (hι.comp ha_bij))
    convert this.comp tendsto_natCast_atTop_atTop using 1; ext N
    simp [Series.partial, ι]
    calc
      _ = ∑ x ∈ .image (Subtype.val ∘ a) (.Icc 0 N), f ↑(g x) := by
        symm; apply sum_subset
        . intro m hm; simp at hm ⊢; obtain ⟨ n, hn, rfl ⟩ := hm
          simp [ha_mono.monotone hn]
        intro x hx hx'; simp at hx hx'; contrapose! hx'
        choose n hn using (hι.comp ha_bij).2 ⟨ g x, hx' ⟩
        simp [ι, Subtype.val_inj] at hn
        apply hg.1 at hn; subst hn
        use n; simpa [ha_mono.le_iff_le] using hx
      _ = _ := by
        apply sum_image
        intro _ _ _ _ h; simp [Subtype.val_inj] at h; exact ha_bij.1 h
  -- When E' is finite, we show that all sufficiently large partial sums of A are equal to
  -- the sum of E'.
  let hEfin : Finite E := hι.finite_iff.mp hE'
  let hE'fintype : Fintype E' := .ofFinite _
  let hEfintype : Fintype E := .ofFinite _
  apply convergesTo_uniq _ hsum
  simp [Sum.of_finite, Series.convergesTo]
  apply tendsto_nhds_of_eventually_eq
  have hE'bound : BddAbove E' := Set.Finite.bddAbove hE'
  rw [bddAbove_def] at hE'bound; choose N hN using hE'bound
  rw [eventually_atTop]
  use N; intro N' hN'
  lift N' to ℕ using (LE.le.trans (by positivity) hN')
  simp [Series.partial] at hN' ⊢
  calc
    _ = ∑ n ∈ E', f (g n) := by
      symm; apply sum_subset
      . intro x hx; simp at *; linarith [hN _ hx]
      intro _ _ hx'; simpa [E',E] using hx'
    _ = ∑ n:E', f (g n) := by convert (sum_set_coe _).symm
    _ = ∑ n, f (ι n) := sum_congr rfl (by grind)
    _ = _ := hι.sum_comp (g := fun x ↦ f x)

/-- Connection with Mathlib's `Summable` property. Some version of this might be suitable
    for Mathlib? -/
theorem AbsConvergent'.iff_Summable {X:Type} (f:X → ℝ) : AbsConvergent' f ↔ Summable f := by
  simp [←summable_abs_iff, AbsConvergent']
  simp [summable_iff_vanishing_norm]
  classical
  constructor
  . intro h ε hε
    set s := Set.range fun A ↦ ∑ x ∈ A, |f x|
    have hnon : s.Nonempty := by simp [s]; use 0, ∅; simp
    have : (sSup s)-ε < sSup s := by linarith
    simp [lt_csSup_iff h hnon,s] at this; choose S hS using this
    use S; intro T hT
    rw [abs_of_nonneg (by positivity)]
    have : ∑ x ∈ T, |f x| + ∑ x ∈ S, |f x| ≤ sSup s := by
      apply ConditionallyCompleteLattice.le_csSup _ _ h
      simp [s]; exact ⟨ T ∪ S, sum_union hT ⟩
    linarith
  intro h; choose S hS using h 1 (by norm_num)
  rw [bddAbove_def]
  use ∑ x ∈ S, |f x| + 1; simp; intro T
  calc
    _ = ∑ x ∈ (T ∩ S), |f x| + ∑ x ∈ (T \ S), |f x| := (sum_inter_add_sum_diff _ _ _).symm
    _ ≤ _ := by
      gcongr
      . exact inter_subset_right
      apply le_of_lt (lt_of_abs_lt (hS _ disjoint_sdiff_self_left))

/-- Maybe suitable for porting to Mathlib?-/
theorem Filter.Eventually.int_natCast_atTop (p: ℤ → Prop) :
  (∀ᶠ n in .atTop, p n) ↔ ∀ᶠ n:ℕ in .atTop, p ↑n := by
  refine ⟨ Eventually.natCast_atTop, ?_ ⟩
  simp [eventually_atTop]
  intro N hN; use N; intro n hn
  lift n to ℕ using (by omega)
  simp at hn; solve_by_elim

theorem Filter.Tendsto.int_natCast_atTop {R:Type} (f: ℤ → R) (l: Filter R) :
atTop.Tendsto f l ↔ atTop.Tendsto (f ∘ Nat.cast) l := by
  simp [tendsto_iff_eventually]
  peel with p h
  simp [←eventually_atTop]
  convert Eventually.int_natCast_atTop _


/-- Connection with Mathlib's `tsum` (or `Σ'`) operation -/
theorem Sum'.eq_tsum {X:Type} (f:X → ℝ) (h: AbsConvergent' f) :
  Sum' f = ∑' x, f x := by
  set E := {x | f x ≠ 0}
  obtain hE | hE := h.countable_supp
  . simp [Sum']
    choose g hg using hE.symm
    have : ((f ∘ Subtype.val) ∘ g:Series).absConverges := by
      apply AbsConvergent.comp hg
      simp [←AbsConvergent'.of_countable hE,]
      exact h.subtype E
    replace this := Sum.eq hg this
    convert convergesTo_uniq this _
    replace : ∑' x, f x = ∑' n, f (g n) := calc
      _ = ∑' x:E, f x := by
        rw [←tsum_univ f]
        have hcompl : E = .univ \ {x | f x = 0 } := by aesop
        convert (tsum_setElem_eq_tsum_setElem_diff _ {x | f x = 0} (by aesop))
      _ = _ := (Equiv.tsum_eq (Equiv.ofBijective _ hg) _).symm
    rw [this]
    unfold convergesTo; rw [Filter.Tendsto.int_natCast_atTop]
    convert (Summable.tendsto_sum_tsum_nat ?_).comp (tendsto_add_atTop_nat 1) with n
    . ext N; simp [Series.partial, Nat.range_succ_eq_Icc_zero]
    rw [AbsConvergent'.iff_Summable] at h
    exact h.comp_injective (i := Subtype.val ∘ g) (Subtype.val_injective.comp hg.1)
  rw [of_finsupp (A := E.toFinite.toFinset)]; symm; apply tsum_eq_sum
  all_goals simp [E]


/-- Proposition 8.2.6 (a) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.add {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f+g) ∧ Sum' (f + g) = Sum' f + Sum' g := by
  have habsconv : AbsConvergent' (f+g) := by
    obtain ⟨Lf, hLf⟩ := hf
    obtain ⟨Lg, hLg⟩ := hg
    simp at hLf hLg
    use Lf + Lg; rintro _ ⟨A, _, rfl⟩
    calc ∑ x ∈ A, |(f + g) x|
        ≤ ∑ x ∈ A, (|f x| + |g x|) := by
          gcongr with x; exact abs_add (f x) (g x)
      _ = ∑ x ∈ A, |f x| + ∑ x ∈ A, |g x| := sum_add_distrib
      _ ≤ Lf + Lg := add_le_add (hLf ⟨A, rfl⟩) (hLg ⟨A, rfl⟩)
  refine ⟨habsconv, ?_⟩
  set A := {x | f x ≠ 0} ∪ {x | g x ≠ 0}
  have hAf : ∀ x ∉ A, f x = 0 := by intro x hx; simp [A] at hx; exact hx.1
  have hAg : ∀ x ∉ A, g x = 0 := by intro x hx; simp [A] at hx; exact hx.2
  have hAfg : ∀ x ∉ A, (f + g) x = 0 := by
    intro x hx; simp [Pi.add_apply, hAf x hx, hAg x hx]
  have hAc : AtMostCountable A := by
    rw [AtMostCountable.iff]; exact Set.countable_union.mpr
      ⟨(AtMostCountable.iff _).mp hf.countable_supp, (AtMostCountable.iff _).mp hg.countable_supp⟩
  obtain hAc | hAc := hAc
  · -- Countably infinite: reduce to Sum on A, then use Series.convergesTo.add
    obtain ⟨_, hfg⟩ := of_countable_supp hAc hAfg habsconv
    obtain ⟨_, hf'⟩ := of_countable_supp hAc hAf hf
    obtain ⟨_, hg'⟩ := of_countable_supp hAc hAg hg
    rw [hfg, hf', hg']
    choose bij hbij using hAc.symm
    have hfA := AbsConvergent.comp hbij ((AbsConvergent'.of_countable hAc).mp (hf.subtype A))
    have hgA := AbsConvergent.comp hbij ((AbsConvergent'.of_countable hAc).mp (hg.subtype A))
    have hfgA := AbsConvergent.comp hbij ((AbsConvergent'.of_countable hAc).mp (habsconv.subtype A))
    have key : ((fun x : A ↦ (f + g) ↑x) ∘ bij : Series) =
               ((fun x : A ↦ f ↑x) ∘ bij : Series) + ((fun x : A ↦ g ↑x) ∘ bij : Series) := by
      rw [Series.add_coe]; rfl
    exact convergesTo_uniq (key ▸ Sum.eq hbij hfgA) ((Sum.eq hbij hfA).add (Sum.eq hbij hgA))
  · -- Finite: reduce to finite sums
    haveI := hAc
    set A' := A.toFinite.toFinset
    have hA'f : ∀ x ∉ A', f x = 0 := by intro x hx; exact hAf x (by simpa [A'] using hx)
    have hA'g : ∀ x ∉ A', g x = 0 := by intro x hx; exact hAg x (by simpa [A'] using hx)
    have hA'fg : ∀ x ∉ A', (f + g) x = 0 := by intro x hx; exact hAfg x (by simpa [A'] using hx)
    rw [of_finsupp hA'fg, of_finsupp hA'f, of_finsupp hA'g, ←sum_add_distrib]; congr 1

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
  have habsconv : AbsConvergent' (c • f) := by
    obtain ⟨L, hL⟩ := hf
    simp at hL
    use |c| * L; rintro _ ⟨A, _, rfl⟩
    calc ∑ x ∈ A, |(c • f) x| = ∑ x ∈ A, |c| * |f x| := by
            congr 1; ext x; simp [Pi.smul_apply, abs_mul]
      _ = |c| * ∑ x ∈ A, |f x| := (mul_sum ..).symm
      _ ≤ |c| * L := by gcongr; exact hL ⟨A, rfl⟩
  refine ⟨habsconv, ?_⟩
  set A := {x | f x ≠ 0}
  have hAf : ∀ x ∉ A, f x = 0 := by intro x hx; simp [A] at hx; exact hx
  have hAcf : ∀ x ∉ A, (c • f) x = 0 := by
    intro x hx; simp [Pi.smul_apply, hAf x hx]
  obtain hAc | hAc := hf.countable_supp
  · -- Countably infinite
    obtain ⟨_, hcf⟩ := of_countable_supp hAc hAcf habsconv
    obtain ⟨_, hf'⟩ := of_countable_supp hAc hAf hf
    rw [hcf, hf']
    choose bij hbij using hAc.symm
    have hfA := AbsConvergent.comp hbij ((AbsConvergent'.of_countable hAc).mp (hf.subtype A))
    have hcfA := AbsConvergent.comp hbij ((AbsConvergent'.of_countable hAc).mp (habsconv.subtype A))
    have key : ((fun x : A ↦ (c • f) ↑x) ∘ bij : Series) =
               c • ((fun x : A ↦ f ↑x) ∘ bij : Series) := by
      rw [Series.smul_coe]; rfl
    exact convergesTo_uniq (key ▸ Sum.eq hbij hcfA) ((Sum.eq hbij hfA).smul)
  · -- Finite
    haveI := hAc
    set A' := A.toFinite.toFinset
    have hA'f : ∀ x ∉ A', f x = 0 := by intro x hx; exact hAf x (by simpa [A'] using hx)
    have hA'cf : ∀ x ∉ A', (c • f) x = 0 := by intro x hx; exact hAcf x (by simpa [A'] using hx)
    rw [of_finsupp hA'cf, of_finsupp hA'f]
    simp [Pi.smul_apply, mul_sum]

/-- This law is not explicitly stated in Proposition 8.2.6, but follows easily from parts (a) and (b).-/
theorem Sum'.sub {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g := by
  convert add hf (smul hg (-1)).1 using 2
  . simp; abel
  . congr; simp; abel
  rw [(smul hg (-1)).2]; ring

/-- Proposition 8.2.6 (c) (Absolutely convergent series laws) / Exercise 8.2.3.  The first
    part of this proposition has been moved to `AbsConvergent'.subtype`. -/
theorem Sum'.of_disjoint_union {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) {X₁ X₂ : Set X} (hdisj: Disjoint X₁ X₂):
  Sum' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
  classical
  -- Decompose f on X₁∪X₂ as g₁ + g₂
  set g₁ : ↥(X₁ ∪ X₂) → ℝ := fun ⟨x, _⟩ ↦ if x ∈ X₁ then f x else 0
  set g₂ : ↥(X₁ ∪ X₂) → ℝ := fun ⟨x, _⟩ ↦ if x ∈ X₂ then f x else 0
  have hfg : (fun x : ↥(X₁ ∪ X₂) ↦ f ↑x) = g₁ + g₂ := by
    ext ⟨x, hx⟩; simp [g₁, g₂, Pi.add_apply]
    rcases hx with h | h
    · simp [h, Set.disjoint_left.mp hdisj h]
    · simp [h, Set.disjoint_right.mp hdisj h]
  have hg₁ : AbsConvergent' g₁ := by
    obtain ⟨L, hL⟩ := hf.subtype (X₁ ∪ X₂)
    simp at hL
    use L; rintro _ ⟨A, _, rfl⟩
    calc ∑ x ∈ A, |g₁ x| ≤ ∑ x ∈ A, |f ↑x| :=
          Finset.sum_le_sum fun x _ ↦ by simp [g₁]; split_ifs <;> simp
      _ ≤ L := hL ⟨A, rfl⟩
  have hg₂ : AbsConvergent' g₂ := by
    obtain ⟨L, hL⟩ := hf.subtype (X₁ ∪ X₂)
    simp at hL
    use L; rintro _ ⟨A, _, rfl⟩
    calc ∑ x ∈ A, |g₂ x| ≤ ∑ x ∈ A, |f ↑x| :=
          Finset.sum_le_sum fun x _ ↦ by simp [g₂]; split_ifs <;> simp
      _ ≤ L := hL ⟨A, rfl⟩
  rw [hfg, (Sum'.add hg₁ hg₂).2]
  -- Suffices: Sum' g₁ = Sum' (f|_{X₁}) and Sum' g₂ = Sum' (f|_{X₂})
  suffices key : ∀ {Y : Set X} (hY : Y ⊆ X₁ ∪ X₂)
      (g : ↥(X₁ ∪ X₂) → ℝ) (hg_abs : AbsConvergent' g)
      (hg_val : ∀ (x : X) (hx : x ∈ X₁ ∪ X₂), g ⟨x, hx⟩ = if x ∈ Y then f x else 0),
      Sum' g = Sum' (fun x : Y ↦ f x) by
    congr 1
    · exact key Set.subset_union_left g₁ hg₁ (fun x hx ↦ rfl)
    · exact key Set.subset_union_right g₂ hg₂ (fun x hx ↦ rfl)
  intro Y hY g hg_abs hg_val
  -- The support of g bijects with the support of f|_Y
  set S := {y : ↥(X₁ ∪ X₂) | g y ≠ 0}
  set T := {y : Y | f ↑y ≠ 0}
  change Sum (fun y : S ↦ g y) = Sum (fun y : T ↦ f ↑↑y)
  set ι : T → S := fun ⟨⟨x, hx⟩, hfx⟩ ↦
    ⟨⟨x, hY hx⟩, by rw [Set.mem_setOf, hg_val x (hY hx), if_pos hx]; exact hfx⟩
  have hι : Bijective ι := by
    constructor
    · intro ⟨⟨x₁, _⟩, _⟩ ⟨⟨x₂, _⟩, _⟩ h
      simp [ι] at h; ext; exact h
    · intro ⟨⟨x, hx_mem⟩, hgx⟩
      simp [S, hg_val x hx_mem] at hgx
      have hxY : x ∈ Y := by by_contra h; simp [h] at hgx
      exact ⟨⟨⟨x, hxY⟩, by simpa [hxY] using hgx⟩,
        by ext; simp [ι]⟩
  have hval : ∀ t : T, g (ι t).1 = f ↑↑t := by
    intro ⟨⟨x, hx⟩, hfx⟩; simp [ι, hg_val x (hY hx), hx]
  obtain hS | hS := hg_abs.countable_supp
  · -- Countably infinite support
    have hS_abs : AbsConvergent (fun y : S ↦ g y) :=
      (AbsConvergent'.of_countable hS).mp (hg_abs.subtype _)
    rw [(Sum.of_comp hS_abs hι).2]
    congr 1; ext t; exact hval t
  · -- Finite support
    haveI : Finite S := hS
    haveI : Finite T := hι.finite_iff.mpr ‹_›
    letI := Fintype.ofFinite ↑S
    letI := Fintype.ofFinite ↑T
    rw [Sum.of_finite, Sum.of_finite, ← hι.sum_comp (fun y : S ↦ g y)]
    congr 1; ext t; exact hval t

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
  have habsconv : AbsConvergent' (f ∘ φ) := by
    obtain ⟨L, hL⟩ := hf; simp at hL
    use L; rintro _ ⟨A, _, rfl⟩
    calc ∑ y ∈ A, |f (φ y)| = ∑ x ∈ A.map ⟨φ, hφ.1⟩, |f x| := by
            rw [Finset.sum_map]; rfl
      _ ≤ L := hL ⟨_, rfl⟩
  refine ⟨habsconv, ?_⟩
  -- Bijection between supports
  set S := {x : X | f x ≠ 0}
  set T := {y : Y | f (φ y) ≠ 0}
  change Sum (fun z : S ↦ f z) = Sum (fun z : T ↦ f (φ z))
  set ι : T → S := fun ⟨y, hy⟩ ↦ ⟨φ y, hy⟩
  have hι : Bijective ι :=
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by ext; exact hφ.1 (by simpa [ι] using h),
     fun ⟨x, hx⟩ ↦ by obtain ⟨y, rfl⟩ := hφ.2 x; exact ⟨⟨y, hx⟩, rfl⟩⟩
  obtain hS | hS := hf.countable_supp
  · have hS_abs := (AbsConvergent'.of_countable hS).mp (hf.subtype _)
    rw [(Sum.of_comp hS_abs hι).2]; rfl
  · haveI : Finite S := hS
    haveI : Finite T := Finite.of_injective ι hι.1
    letI := Fintype.ofFinite ↑S
    letI := Fintype.ofFinite ↑T
    rw [Sum.of_finite, Sum.of_finite, ← hι.sum_comp (fun z : S ↦ f z)]

/-- This technical claim, the analogue of `tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f :=
  (of_comp hf ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, Set.mem_univ _⟩, rfl⟩⟩).2.symm

/-- Lemma 8.2.7 / Exercise 8.2.4 -/
theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by
  -- Strategy: AbsConvergent → AbsConvergent' (index-agnostic) → Summable (for Mathlib API:
  -- summable_of_sum_range_le, tendsto_sum_tsum_nat) → indicator arithmetic → absConverges.
  -- The Summable detour is needed because AbsConvergent' lacks range-sum convergence lemmas.
  -- The ℤ↔ℕ bridge (partial_eq / ha_tendsto) is the main boilerplate cost.
  have hCI_of_abs {S : Set ℕ} : AbsConvergent (fun n : S ↦ a n) → CountablyInfinite S := by
    intro ⟨g, hg, _⟩
    have : Infinite S := Infinite.of_injective g hg.1
    exact (CountablyInfinite.iff' _).mpr ⟨inferInstance, this⟩
  have abs_to_summable : ∀ {S : Set ℕ},
      AbsConvergent (fun n : S ↦ a n) → Summable (fun n : S ↦ a n) :=
    fun h ↦ (AbsConvergent'.iff_Summable _).mp ((AbsConvergent'.of_countable (hCI_of_abs h)).mpr h)
  have partial_eq : ∀ K : ℕ, (a:Series).partial (K : ℤ) = ∑ n ∈ Finset.range (K + 1), a n := by
    intro K
    show ∑ n ∈ Finset.Icc (0:ℤ) K, (if n ≥ 0 then a n.toNat else 0) =
      ∑ n ∈ Finset.range (K + 1), a n
    rw [Finset.Icc_eq_cast, Finset.sum_map]
    apply Finset.sum_congr (by ext; simp; omega) (fun n hn ↦ by simp [show (n:ℤ) ≥ 0 from by omega])
  have ha_tendsto : ∃ S, Filter.Tendsto (fun N ↦ ∑ i ∈ Finset.range N, a i)
      Filter.atTop (nhds S) := by
    obtain ⟨L, hL⟩ := (Chapter6.Sequence.converges_iff_Tendsto'
      ⟨0, (a:Series).partial, by intro n hn; simp [Series.partial, hn]⟩).mp
      (by rw [Chapter6.Sequence.converges_iff_Tendsto']; exact ha)
    refine ⟨L, ?_⟩
    rw [Filter.tendsto_atTop'] at hL ⊢
    intro s hs; obtain ⟨N, hN⟩ := hL s hs
    exact ⟨(N.toNat + 1 : ℕ), fun n hn ↦ by
      have h1 := partial_eq (n - 1)
      simp only [show (n - 1 : ℕ) + 1 = n from by omega] at h1
      rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 from by omega] at h1
      simp only [h1.symm]
      exact hN _ (by omega)⟩
  -- One indicator Summable + complement has constant sign → complement Summable
  have summable_compl {S : Set ℕ} (hS : Summable (S.indicator a))
      (hsign : (∀ n, 0 ≤ Sᶜ.indicator a n) ∨ (∀ n, Sᶜ.indicator a n ≤ 0)) :
      Summable (Sᶜ.indicator a) := by
    obtain ⟨L, hL⟩ := ha_tendsto
    have hconv : Filter.Tendsto (fun N ↦ ∑ i ∈ Finset.range N, Sᶜ.indicator a i)
        Filter.atTop (nhds (L - ∑' i, S.indicator a i)) := by
      have : (fun N ↦ ∑ i ∈ Finset.range N, Sᶜ.indicator a i) =
          (fun N ↦ ∑ i ∈ Finset.range N, a i - ∑ i ∈ Finset.range N, S.indicator a i) := by
        ext N
        have h := Finset.sum_congr (show Finset.range N = Finset.range N from rfl)
          (fun n _ ↦ show a n = S.indicator a n + Sᶜ.indicator a n from by
            by_cases hn : n ∈ S <;> simp [hn])
        linarith [Finset.sum_add_distrib.symm.trans h.symm]
      rw [this]; exact hL.sub hS.tendsto_sum_tsum_nat
    rcases hsign with hnn | hnp
    · apply summable_of_sum_range_le (c := L - ∑' i, S.indicator a i)
      · exact hnn
      · intro N
        exact (isLUB_of_tendsto_atTop (fun m n hmn ↦ Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hmn) (fun i _ _ ↦ hnn i)) hconv).1 ⟨N, rfl⟩
    · rw [← summable_neg_iff]
      apply summable_of_sum_range_le (c := -(L - ∑' i, S.indicator a i))
      · intro n; exact neg_nonneg.mpr (hnp n)
      · intro N
        have hanti : Antitone (fun N ↦ ∑ i ∈ Finset.range N, Sᶜ.indicator a i) :=
          fun m n hmn ↦ by
            have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i ↦ -(Sᶜ.indicator a i))
              (Finset.range_mono hmn) (fun i _ _ ↦ neg_nonneg.mpr (hnp i))
            simp only [Finset.sum_neg_distrib, neg_le_neg_iff] at this; exact this
        have := (isGLB_of_tendsto_atTop hanti hconv).1 ⟨N, rfl⟩
        simp only [Finset.sum_neg_distrib]; linarith
  have compl_eq : {n | a n ≥ 0}ᶜ = {n | a n < 0} := by ext; simp [not_le]
  have compl_eq' : {n | a n < 0}ᶜ = {n | a n ≥ 0} := by ext; simp [not_lt]
  have other_summable_pos : Summable (fun n : {n | a n ≥ 0} ↦ a n) →
      Summable (fun n : {n | a n < 0} ↦ a n) := by
    intro hpos; show Summable (a ∘ Subtype.val)
    rw [summable_subtype_iff_indicator, ← compl_eq]
    exact summable_compl (summable_subtype_iff_indicator.mp hpos) (Or.inr fun n ↦ by
      simp only [compl_eq, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs with h <;> [exact le_of_lt h; exact le_refl _])
  have other_summable_neg : Summable (fun n : {n | a n < 0} ↦ a n) →
      Summable (fun n : {n | a n ≥ 0} ↦ a n) := by
    intro hneg; show Summable (a ∘ Subtype.val)
    rw [summable_subtype_iff_indicator, ← compl_eq']
    exact summable_compl (summable_subtype_iff_indicator.mp hneg) (Or.inl fun n ↦ by
      simp only [compl_eq', Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs with h <;> [exact h; exact le_refl _])
  -- Both parts Summable → whole absConverges
  have both_summable : Summable (fun n : {n | a n ≥ 0} ↦ a n) →
      Summable (fun n : {n | a n < 0} ↦ a n) → (a:Series).absConverges := by
    intro hpos hneg
    have h1 := summable_subtype_iff_indicator.mp hpos
    have h2 := summable_subtype_iff_indicator.mp hneg
    have ha_summable : Summable a := by
      have a_decomp : a = {n | a n ≥ 0}.indicator a + {n | a n < 0}.indicator a := by
        ext n; simp only [Set.indicator, Pi.add_apply, Set.mem_setOf_eq]
        by_cases h : a n ≥ 0 <;> simp [h, not_lt.mpr, lt_of_not_ge]
      rw [a_decomp]; exact h1.add h2
    have ⟨L, hL⟩ := (AbsConvergent'.iff_Summable a).mpr ha_summable
    have hL' : ∀ A : Finset ℕ, ∑ x ∈ A, |a x| ≤ L := fun A ↦ hL ⟨A, ⟨trivial, rfl⟩⟩
    rw [absConverges, converges_of_nonneg_iff (fun n ↦ by simp; split_ifs <;> simp)]
    use L; intro N
    by_cases hN : N ≥ 0
    · lift N to ℕ using hN
      simp only [Series.partial, Finset.Icc_eq_cast]; rw [Finset.sum_map]
      calc ∑ x ∈ Finset.Icc 0 N, (if (x:ℤ) ≥ 0 then |a (x:ℤ).toNat| else 0)
          = ∑ x ∈ Finset.Icc 0 N, |a x| := by
            apply Finset.sum_congr rfl; intro n hn; simp [show (n:ℤ) ≥ 0 from by omega]
        _ ≤ L := hL' _
    · rw [partial_of_lt (show N < (a:Series).abs.m from by simp; omega)]
      exact le_trans (le_refl 0) (hL' ∅)
  constructor
  · intro hpos
    have h1 := abs_to_summable hpos
    have h2 := other_summable_pos h1
    exact ha' (both_summable h1 h2)
  · intro hneg
    have h1 := abs_to_summable hneg
    have h2 := other_summable_neg h1
    exact ha' (both_summable h2 h1)

private theorem absConverges_of_eventually_constant_sign {a: ℕ → ℝ}
    (ha: (a:Series).converges) (N₁ : ℕ)
    (hsign : (∀ n ≥ N₁, a n < 0) ∨ (∀ n ≥ N₁, a n ≥ 0)) :
    (a:Series).absConverges := by
  rw [absConverges, converges_iff_tail_decay]
  have ha_copy := ha; rw [converges_iff_tail_decay] at ha_copy
  intro ε hε; obtain ⟨N₀, hN₀m, hN₀⟩ := ha_copy ε hε
  refine ⟨max N₀ ↑N₁, by simp, fun p hp q hq ↦ ?_⟩
  rcases hsign with hsign | hsign
  · have : ∀ i ∈ Finset.Icc p q, (a:Series).abs.seq i = -(a:Series).seq i := by
      intro i hi
      have hi' := (Finset.mem_Icc.mp hi).1; have hge : i ≥ 0 := by omega
      rw [Series.abs_seq, show (a:Series).seq i = a i.toNat from by simp [hge],
        abs_of_neg (hsign i.toNat (by omega))]
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, abs_neg]
    exact hN₀ p (by omega) q (by omega)
  · have : ∀ i ∈ Finset.Icc p q, (a:Series).abs.seq i = (a:Series).seq i := by
      intro i hi
      have hi' := (Finset.mem_Icc.mp hi).1; have hge : i ≥ 0 := by omega
      rw [Series.abs_seq, show (a:Series).seq i = a i.toNat from by simp [hge],
        abs_of_nonneg (hsign i.toNat (by omega))]
    rw [Finset.sum_congr rfl this]
    exact hN₀ p (by omega) q (by omega)

private theorem infinite_sign_set_of_not_absConverges {a: ℕ → ℝ}
    (ha: (a:Series).converges) (ha': ¬ (a:Series).absConverges) :
    Infinite { n | a n ≥ 0 } ∧ Infinite { n | a n < 0 } := by
  constructor <;> (rw [Set.infinite_coe_iff]; intro hfin; apply ha')
  · obtain ⟨M, hM⟩ := hfin.bddAbove
    exact absConverges_of_eventually_constant_sign ha (M + 1)
      (Or.inl fun n hn ↦ by
        by_contra h; push_neg at h
        exact absurd (hM h) (by omega))
  · obtain ⟨M, hM⟩ := hfin.bddAbove
    exact absConverges_of_eventually_constant_sign ha (M + 1)
      (Or.inr fun n hn ↦ by
        by_contra h; push_neg at h
        exact absurd (hM h) (by omega))

private theorem infinite_available_set {S : Set ℕ} (hS : S.Infinite) (n' : ℕ → ℕ) (j : ℕ) :
    Infinite { n ∈ S | ∀ i : Fin j, n ≠ n' i } := by
  have hsub : S \ (n' '' (Finset.range j : Set ℕ)) ⊆
      {n | n ∈ S ∧ ∀ i : Fin j, n ≠ n' i} := by
    intro x ⟨hx, hne⟩
    exact ⟨hx, fun i ↦ by intro h; exact hne ⟨i, Finset.mem_range.mpr i.isLt, h.symm⟩⟩
  exact hS.diff (Set.Finite.image _ (Finset.finite_toSet _)) |>.mono hsub |>.to_subtype

private theorem cover_of_min_injective {S : Set ℕ} {n' : ℕ → ℕ} {J : ℕ}
    (hn'_inj : Injective n')
    (hn'_eq : ∀ j ≥ J, n' j = Nat.min { n ∈ S | ∀ i : Fin j, n ≠ n' i })
    (hne : ∀ j, { n ∈ S | ∀ i : Fin j, n ≠ n' i }.Nonempty) :
    ∀ m ∈ S, ∃ j, n' j = m := by
  intro m hm; by_contra h; push_neg at h
  have : ∀ j ≥ J, n' j ≤ m := by
    intro j hj; rw [hn'_eq j hj]
    exact (Nat.min_spec (hne j)).2 m ⟨hm, fun i ↦ Ne.symm (h ↑i)⟩
  exact not_injective_infinite_finite
    (fun j : (Set.Ici J : Set ℕ) ↦ (⟨n' j, this j j.2⟩ : Set.Iic m))
    (fun ⟨j₁, _⟩ ⟨j₂, _⟩ h ↦ Subtype.ext (hn'_inj (Subtype.mk.inj h)))

/-- Oscillation damping: if a rearranged series has terms → 0, and the sign of each term
is controlled by whether the partial sum is above or below L, and both cases occur infinitely
often, then the partial sums converge to L. -/
private theorem convergesTo_of_sign_control {b : ℕ → ℝ} {L : ℝ}
    (hconv : atTop.Tendsto b (nhds 0))
    (h_sign_ge : ∀ j, (∑ i : Fin j, b i) ≥ L → b j < 0)
    (h_sign_lt : ∀ j, (∑ i : Fin j, b i) < L → b j ≥ 0)
    (h_inf_ge : {j | ∑ i : Fin j, b i ≥ L}.Infinite)
    (h_inf_lt : {j | ∑ i : Fin j, b i < L}.Infinite) :
    (b : Series).convergesTo L := by
  set S := fun j ↦ ∑ i : Fin j, b i with S_def
  suffices h : atTop.Tendsto S (nhds L) by
    change atTop.Tendsto (b : Series).partial (nhds L)
    rw [show (atTop : Filter ℤ) = Filter.map (Nat.cast : ℕ → ℤ) atTop
      from Nat.map_cast_int_atTop.symm]
    rw [Filter.tendsto_map'_iff]
    suffices heq : (b : Series).partial ∘ (Nat.cast : ℕ → ℤ) = S ∘ (· + 1) by
      rw [heq]; exact h.comp (Filter.tendsto_atTop_atTop.mpr fun n ↦ ⟨n, fun m hm ↦ by omega⟩)
    ext N; simp only [Function.comp, Series.partial, S_def]
    have : ∀ x ∈ Finset.Icc (0 : ℤ) (↑N : ℤ), (if x ≥ 0 then b x.toNat else 0) = b x.toNat := by
      intro x hx; simp [(Finset.mem_Icc.mp hx).1]
    rw [Finset.sum_congr rfl this]
    rw [show Finset.Icc (0 : ℤ) (↑N : ℤ) = (Finset.range (N + 1)).image (Nat.cast) from by
      ext x; simp [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]; constructor
      · intro ⟨h1, h2⟩; exact ⟨x.toNat, by omega, by omega⟩
      · intro ⟨y, hy, hyx⟩; exact ⟨y, by omega, by omega⟩]
    rw [Finset.sum_image (by intro a _ b _ h; omega)]
    simp only [Int.toNat_natCast]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hconv) ε hε
  have hterm : ∀ j ≥ J, |b j| < ε := by
    intro j hj; specialize hJ j hj; rwa [dist_zero_right] at hJ
  have hS_succ : ∀ j, S (j + 1) = S j + b j := by
    intro j; simp [S_def, Fin.sum_univ_castSucc]
  have hrec : ∀ j, |S (j + 1) - L| ≤ max (|S j - L|) (|b j|) := by
    intro j; rw [hS_succ]
    by_cases hge : S j ≥ L
    · have hminus := h_sign_ge j hge
      by_cases hge' : S j + b j ≥ L
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        exact le_max_of_le_left (by linarith)
      · push_neg at hge'
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hminus.le]
        exact le_max_of_le_right (by linarith)
    · push_neg at hge; have := h_sign_lt j hge
      by_cases hge' : S j + b j ≥ L
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg this]
        exact le_max_of_le_right (by linarith)
      · push_neg at hge'
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        exact le_max_of_le_left (by linarith)
  obtain ⟨j₁, hj₁_lt : S j₁ < L, hj₁_ge⟩ := h_inf_lt.exists_gt J
  obtain ⟨j₂, hj₂_ge : S j₂ ≥ L, hj₂_ge'⟩ := h_inf_ge.exists_gt j₁
  have : ∃ k, j₁ ≤ k ∧ k < j₂ ∧ S k < L ∧ S (k + 1) ≥ L := by
    by_contra hall; push_neg at hall
    have : ∀ k, j₁ ≤ k → k ≤ j₂ → S k < L := by
      intro k hk1 hk2
      induction k with
      | zero => rcases Nat.eq_or_lt_of_le hk1 with h | h <;> [exact h ▸ hj₁_lt; omega]
      | succ k ih =>
        rcases Nat.eq_or_lt_of_le hk1 with h | h
        · exact h ▸ hj₁_lt
        · exact hall k (by omega) (by omega) (ih (by omega) (by omega))
    exact absurd (this j₂ (by omega) le_rfl) (not_lt.mpr hj₂_ge)
  obtain ⟨j₀, hj₀_ge₁, _, hj₀_lt, hj₀_ge'⟩ := this
  have hj₀_ge : j₀ ≥ J := by omega
  have hstart : |S (j₀ + 1) - L| < ε := by
    have heq := hS_succ j₀
    rw [abs_of_nonneg (by linarith [heq])]
    have hnn := h_sign_lt j₀ hj₀_lt
    calc S (j₀ + 1) - L = S j₀ + b j₀ - L := by linarith [heq]
      _ ≤ b j₀ := by linarith
      _ = |b j₀| := (abs_of_nonneg hnn).symm
      _ < ε := hterm j₀ hj₀_ge
  use j₀ + 1; intro n hn; rw [Real.dist_eq]
  induction n, hn using Nat.le_induction with
  | base => exact hstart
  | succ n hn ih =>
    calc |S (n + 1) - L| ≤ max (|S n - L|) (|b n|) := hrec n
      _ < ε := max_lt ih (hterm n (by omega))

/-- Theorem 8.2.8 (Riemann rearrangement theorem) / Exercise 8.2.5 -/
theorem permute_convergesTo_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) (L:ℝ) :
  ∃ f : ℕ → ℕ, Bijective f ∧ (a ∘ f:Series).convergesTo L
  := by
  -- This proof is written to follow the structure of the original text.
  choose h1 h2 using divergent_parts_of_divergent ha ha'
  set A_plus := { n | a n ≥ 0 }
  set A_minus := { n | a n < 0 }
  have hdisj : Disjoint A_plus A_minus := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext; simp [A_plus, A_minus]
  have hunion : A_plus ∪ A_minus = .univ := by
    ext; simp [A_plus, A_minus]; grind
  obtain ⟨hA_plus_inf, hA_minus_inf⟩ := infinite_sign_set_of_not_absConverges ha ha'
  obtain ⟨ a_plus, ha_plus_bij, ha_plus_mono ⟩ := (Nat.monotone_enum_of_infinite A_plus).exists
  obtain ⟨ a_minus, ha_minus_bij, ha_minus_mono ⟩ := (Nat.monotone_enum_of_infinite A_minus).exists
  let F : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
    fun j n' ↦ if ∑ i:Fin j, a (n' i (by simp)) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i (by simp) }
  let n' : ℕ → ℕ := Nat.strongRec F
  have hn' (j:ℕ) : n' j = if ∑ i:Fin j, a (n' i) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }
    := Nat.strongRec.eq_def _ j
  have hn'_plus_inf (j:ℕ) : Infinite { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } :=
    infinite_available_set (Set.infinite_coe_iff.mp hA_plus_inf) n' j
  have hn'_minus_inf (j:ℕ) : Infinite { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } :=
    infinite_available_set (Set.infinite_coe_iff.mp hA_minus_inf) n' j
  have hn'_nonempty_plus (j:ℕ) : { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }.Nonempty :=
    Set.Nonempty.of_subtype
  have hn'_nonempty_minus (j:ℕ) : { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }.Nonempty :=
    Set.Nonempty.of_subtype
  have hn'_ne (j:ℕ) : ∀ i : Fin j, n' j ≠ n' i := by
    intro i
    rw [hn' j]
    split
    · exact (Nat.min_spec (hn'_nonempty_plus j)).1.2 i
    · exact (Nat.min_spec (hn'_nonempty_minus j)).1.2 i
  have hn'_mem (j:ℕ) : if ∑ i:Fin j, a (n' i) < L then n' j ∈ A_plus else n' j ∈ A_minus := by
    rw [hn' j]
    split
    · exact (Nat.min_spec (hn'_nonempty_plus j)).1.1
    · exact (Nat.min_spec (hn'_nonempty_minus j)).1.1
  have hn'_inj : Injective n' := by
    intro i j hij
    by_contra hne
    rcases Ne.lt_or_gt hne with h | h
    · have := hn'_ne j ⟨i, h⟩; simp at this; exact this hij.symm
    · have := hn'_ne i ⟨j, h⟩; simp at this; exact this hij
  have h_case_I : Infinite { j | ∑ i:Fin j, a (n' i) < L } := by
    rw [Set.infinite_coe_iff]; intro hfin
    obtain ⟨J, hJ⟩ := hfin.bddAbove
    have hge : ∀ j ≥ J + 1, ∑ i : Fin j, a (n' i) ≥ L := by
      intro j hj; by_contra h; push_neg at h
      have : j ≤ J := hJ h
      omega
    have hminus : ∀ j ≥ J + 1, n' j ∈ A_minus := by
      intro j hj; have := hn'_mem j
      simp [show ¬ (∑ i : Fin j, a (n' i) < L) from not_lt.mpr (hge j hj)] at this
      exact this
    have hcover : ∀ m ∈ A_minus, ∃ j, n' j = m :=
      cover_of_min_injective (J := J + 1) hn'_inj
        (fun j hj ↦ by rw [hn' j]; simp [show ¬ (∑ i : Fin j, a (n' i) < L) from not_lt.mpr (hge j hj)])
        (fun j ↦ hn'_nonempty_minus j)
    apply h2
    have hCI : CountablyInfinite A_minus := (CountablyInfinite.iff' _).mpr ⟨inferInstance, hA_minus_inf⟩
    rw [← AbsConvergent'.of_countable hCI, AbsConvergent'.iff_Summable]
    -- Tail is summable (nonpositive, partial sums bounded below by L)
    have htail : Summable (fun k ↦ a (n' (k + (J + 1)))) := by
      have htail_neg : Summable (fun k ↦ -(a (n' (k + (J + 1))))) := by
        apply summable_of_sum_range_le (fun k ↦ neg_nonneg.mpr (hminus (k + (J + 1)) (by omega)).le)
          (c := ∑ i ∈ Finset.range (J + 1), a (n' i) - L)
        intro N
        have key : ∑ i ∈ Finset.range ((J + 1) + N), a (n' i) =
            ∑ i ∈ Finset.range (J + 1), a (n' i) + ∑ i ∈ Finset.range N, a (n' (i + (J + 1))) := by
          rw [Finset.sum_range_add]; congr 1; apply Finset.sum_congr rfl; intro i _; ring_nf
        have hge' : ∑ i ∈ Finset.range ((J + 1) + N), a (n' i) ≥ L := by
          convert hge ((J + 1) + N) (by omega) using 1
          rw [← Finset.sum_range (n := (J + 1) + N) (f := fun i ↦ a (n' i))]
        rw [Finset.sum_neg_distrib]; linarith
      exact htail_neg.of_neg
    have hfull : Summable (fun k : ℕ ↦ max (-(a (n' k))) 0) := by
      apply Summable.comp_nat_add (k := J + 1)
      exact htail.neg.congr (fun k ↦ (max_eq_left
        (neg_nonneg.mpr (hminus (k + (J + 1)) (by omega)).le)).symm)
    choose g hg using fun m (hm : m ∈ A_minus) ↦ hcover m hm
    have hg_inj : Function.Injective (fun x : A_minus ↦ g x.1 x.2) := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ h; ext
      have : n' (g x hx) = n' (g y hy) := congrArg n' h
      rwa [hg x hx, hg y hy] at this
    exact ((hfull.comp_injective hg_inj).of_nonneg_of_le
      (fun ⟨_, hx⟩ ↦ neg_nonneg.mpr hx.le)
      (fun ⟨x, hx⟩ ↦ by
        show -a x ≤ max (-(a (n' (g x hx)))) 0; rw [hg x hx]; exact le_max_left _ _)).of_neg
  have h_case_II : Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by
    -- If finitely many, eventually ∑ < L so we always pick from A_plus (nonneg terms).
    rw [Set.infinite_coe_iff]; intro hfin
    obtain ⟨J, hJ⟩ := hfin.bddAbove
    have hlt : ∀ j ≥ J + 1, ∑ i : Fin j, a (n' i) < L := by
      intro j hj; by_contra h; push_neg at h
      exact absurd (hJ h) (by omega)
    have hplus : ∀ j ≥ J + 1, n' j ∈ A_plus := by
      intro j hj; have := hn'_mem j
      simp [hlt j hj] at this; exact this
    have hcover : ∀ m ∈ A_plus, ∃ j, n' j = m :=
      cover_of_min_injective (J := J + 1) hn'_inj
        (fun j hj ↦ by rw [hn' j]; simp [hlt j hj])
        (fun j ↦ hn'_nonempty_plus j)
    -- The sum of A_plus terms in the partial sums is bounded → contradicts h1
    apply h1
    have hCI : CountablyInfinite A_plus := (CountablyInfinite.iff' _).mpr ⟨inferInstance, hA_plus_inf⟩
    rw [← AbsConvergent'.of_countable hCI, AbsConvergent'.iff_Summable]
    -- Step 1: The tail fun k ↦ a(n'(k + (J+1))) is summable (nonneg, bounded partial sums)
    have htail : Summable (fun k ↦ a (n' (k + (J + 1)))) := by
      apply summable_of_sum_range_le (c := L - ∑ i ∈ Finset.range (J + 1), a (n' i))
        (fun k ↦ hplus (k + (J + 1)) (by omega))
      intro N
      have key : ∑ i ∈ Finset.range ((J + 1) + N), a (n' i) =
          ∑ i ∈ Finset.range (J + 1), a (n' i) + ∑ i ∈ Finset.range N, a (n' (i + (J + 1))) := by
        rw [Finset.sum_range_add]; congr 1; apply Finset.sum_congr rfl
        intro i _; ring_nf
      have hle' : ∑ i ∈ Finset.range ((J + 1) + N), a (n' i) < L := by
        convert hlt ((J + 1) + N) (by omega) using 1
        rw [← Finset.sum_range (n := (J + 1) + N) (f := fun i ↦ a (n' i))]
      linarith
    -- Step 2: max(a(n' k), 0) is summable, transfer to A_plus via comp_injective
    have hfull : Summable (fun k : ℕ ↦ max (a (n' k)) 0) := by
      apply Summable.comp_nat_add (k := J + 1)
      exact htail.congr (fun k ↦ (max_eq_left (hplus (k + (J + 1)) (by omega))).symm)
    choose g hg using fun m (hm : m ∈ A_plus) ↦ hcover m hm
    have hg_inj : Function.Injective (fun x : A_plus ↦ g x.1 x.2) := by
      intro ⟨x, hx⟩ ⟨y, hy⟩ h; ext
      have : n' (g x hx) = n' (g y hy) := congrArg n' h
      rwa [hg x hx, hg y hy] at this
    exact (hfull.comp_injective hg_inj).of_nonneg_of_le
      (fun ⟨_, hx⟩ ↦ hx)
      (fun ⟨x, hx⟩ ↦ by show a x ≤ max (a (n' (g x hx))) 0; rw [hg x hx]; exact le_max_left _ _)
  have hn'_surj : Surjective n' := by
    intro m; by_contra h; push_neg at h
    have hmem : m ∈ A_plus ∨ m ∈ A_minus := by
      have := hunion ▸ Set.mem_univ m; exact this
    -- m is not in range of n', so for all j, m ≠ n'(i) for i < j
    -- When we pick from the set containing m, n'(j) ≤ m by minimality
    -- Infinitely many such j gives contradiction
    rcases hmem with hm | hm
    · -- m ∈ A_plus: infinitely many j with ∑ < L pick from A_plus
      have hle : ∀ j, (∑ i : Fin j, a (n' i) < L) → n' j ≤ m := by
        intro j hj
        have := hn' j; simp [hj] at this; rw [this]
        exact (Nat.min_spec (hn'_nonempty_plus j)).2 m ⟨hm, fun i ↦ Ne.symm (h ↑i)⟩
      have hsub : {j | ∑ i : Fin j, a (n' i) < L} ⊆ {j | n' j ≤ m} := by
        intro j hj; exact hle j hj
      exact not_injective_infinite_finite
        (fun j : {j | ∑ i : Fin j, a (n' i) < L} ↦ (⟨n' j, hsub j.2⟩ : Set.Iic m))
        (fun ⟨j₁, _⟩ ⟨j₂, _⟩ h ↦ Subtype.ext (hn'_inj (Subtype.mk.inj h)))
    · -- m ∈ A_minus: infinitely many j with ∑ ≥ L pick from A_minus
      have hle : ∀ j, ¬(∑ i : Fin j, a (n' i) < L) → n' j ≤ m := by
        intro j hj
        have := hn' j; simp [hj] at this; rw [this]
        exact (Nat.min_spec (hn'_nonempty_minus j)).2 m ⟨hm, fun i ↦ Ne.symm (h ↑i)⟩
      have hsub : {j | ∑ i : Fin j, a (n' i) ≥ L} ⊆ {j | n' j ≤ m} := by
        intro j hj; exact hle j (not_lt.mpr hj)
      exact not_injective_infinite_finite
        (fun j : {j | ∑ i : Fin j, a (n' i) ≥ L} ↦ (⟨n' j, hsub j.2⟩ : Set.Iic m))
        (fun ⟨j₁, _⟩ ⟨j₂, _⟩ h ↦ Subtype.ext (hn'_inj (Subtype.mk.inj h)))
  have hconv : atTop.Tendsto (a ∘ n') (nhds 0) := by
    have hn'_tendsto : atTop.Tendsto (Nat.cast ∘ n' : ℕ → ℤ) atTop :=
      tendsto_natCast_atTop_atTop.comp (hn'_inj.nat_tendsto_atTop)
    have : atTop.Tendsto (fun j : ℕ ↦ (a : Series).seq (n' j : ℤ)) (nhds 0) :=
      (decay_of_converges ha).comp hn'_tendsto
    rwa [show (fun j : ℕ ↦ (a : Series).seq (↑(n' j) : ℤ)) = a ∘ n' from by ext j; simp] at this
  have hn'_sign_ge : ∀ j, (∑ i : Fin j, a (n' i)) ≥ L → a (n' j) < 0 := by
    intro j hge; have := hn'_mem j
    simp only [show ¬((∑ i : Fin j, a (n' ↑i)) < L) from not_lt.mpr hge, ite_false] at this
    exact this
  have hn'_sign_lt : ∀ j, (∑ i : Fin j, a (n' i)) < L → a (n' j) ≥ 0 := by
    intro j hlt; have := hn'_mem j
    simp only [show (∑ i : Fin j, a (n' ↑i)) < L from hlt, ite_true] at this; exact this
  have hsum : (a ∘ n':Series).convergesTo L :=
    convergesTo_of_sign_control hconv hn'_sign_ge hn'_sign_lt
      (Set.infinite_coe_iff.mp h_case_II) (Set.infinite_coe_iff.mp h_case_I)
  exact ⟨n', ⟨hn'_inj, hn'_surj⟩, by convert hsum⟩

/-- Exercise 8.2.6 -/
theorem permute_diverges_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊤) := by
  sorry

theorem permute_diverges_of_divergent' {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊥) := by
  sorry

end Chapter8
