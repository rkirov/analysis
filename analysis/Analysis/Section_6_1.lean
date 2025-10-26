import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $ε$-closeness, $ε$-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℝ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from ℕ to ℝ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed s, the function ε ↦ ε.Steady s is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed s, the function ε ↦ ε.EventuallySteady s is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as Chapter5.Sequence.IsCauchy.coe -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Chapter5.from_of_rat (n: ℤ) (a: Chapter5.Sequence):
    (Sequence.from (a: Sequence) n) = (a.from n:Sequence) := by
  simp only [Sequence.mk.injEq, ge_iff_le, sup_le_iff, dite_eq_ite, true_and]
  ext m
  by_cases h:a.n₀ ≤ m <;> simp [h]
  by_cases h': n ≤ m <;> simp [h']

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
  constructor
  · intro h
    rw [Real.steady_def]
    intro n hn m hm
    rw [Rat.steady_def] at h
    specialize h n hn m hm
    rw [Real.close_def, Real.dist_eq]
    rw [Rat.Close] at h
    push_cast
    exact_mod_cast h
  · intro h
    rw [Rat.steady_def]
    intro n hn m hm
    rw [Real.steady_def] at h
    specialize h n hn m hm
    rw [Real.close_def, Real.dist_eq] at h
    rw [Rat.Close]
    push_cast at h
    exact_mod_cast h

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
  constructor
  · intro h
    rw [Rat.eventuallySteady_def] at h
    rw [Real.eventuallySteady_def]
    obtain ⟨ N, hN, h' ⟩ := h
    use N
    constructor
    . exact_mod_cast hN
    . have := (is_steady_of_rat ε _).mp h'
      rw [Chapter5.from_of_rat]
      exact this
  · intro h
    rw [Rat.eventuallySteady_def]
    rw [Real.eventuallySteady_def] at h
    obtain ⟨ N, hN, h' ⟩ := h
    use N
    constructor
    . exact_mod_cast hN
    . rw [Chapter5.from_of_rat] at h'
      have := (is_steady_of_rat ε _).mpr h'
      exact this

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
  rw [tendsTo_def]
  constructor
  . intro h ε hε
    specialize h ε hε
    rw [Real.eventuallyClose_def] at h
    obtain ⟨ N, hN, h' ⟩ := h
    use N
    rw [Real.closeSeq_def] at h'
    intro n hn
    simp at h'
    have h : a.m ≤ n := by linarith
    specialize h' n h hn
    rw [Real.dist_eq] at h'
    simp [h, hn] at h'
    exact h'
  . intro h ε hε
    choose N hN using h ε hε
    use max N a.m
    constructor
    . exact le_max_right _ _
    . rw [Real.closeSeq_def]
      intro n hn
      simp at hn
      rw [Real.dist_eq]
      simp [hn]
      specialize hN n hn.1
      exact hN

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  rw [Real.eventuallyClose_def]
  use 1
  rw [seq_6_1_6]
  simp
  rw [Real.CloseSeq]
  intro h hn
  simp at hn
  rw [Real.close_def, Real.dist_eq]
  simp [hn]
  have : 0 ≤ h := by linarith
  simp [this]
  rw [abs_of_nonneg (by positivity)]
  rw [show (1e-2:ℝ) = (10:ℝ)^(-2:ℤ) by norm_num]
  gcongr <;> grind

lemma pow_archimedian (ε: ℝ) (hε: 0 < ε): ∃ N: ℤ, 0 < N ∧ (10:ℝ) ^ (N + 1) > 1 / ε := by
  obtain ⟨ N, hN ⟩ := exists_nat_gt (1 / ε)
  use N
  constructor
  . by_cases h: N = 0
    . subst N
      simp at hN
      linarith
    . positivity
  . simp_all
    suffices (N: ℝ) < 10 ^ (↑N + 1) by
      exact hN.trans this
    norm_cast
    have := Nat.lt_pow_self (a:=10) (n:=N+1) (by omega)
    linarith

/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  rw [Sequence.tendsTo_def]
  intro ε hε
  rw [Real.eventuallyClose_def]
  obtain ⟨n, hn1, hn2⟩ := pow_archimedian ε (by positivity)
  simp at hn2
  use n
  rw [seq_6_1_6]
  simp
  constructor
  . exact hn1.le
  . rw [Real.CloseSeq]
    intro m hm
    simp at hm
    rw [Real.close_def]
    rw [Real.dist_eq]
    simp [hm]
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (10:ℝ) ^ (-n - 1) := by
        gcongr
        . norm_num
        . exact hm.2
      _ = (10:ℝ) ^ (-n - 1) := by norm_cast
      _ = (10:ℝ) ^ (- (n + 1)) := by simp; ring
      _ ≤ 1 / ε⁻¹ := by
        have := one_div_lt_one_div_of_lt (by positivity) hn2
        simp at this ⊢
        rw [← zpow_neg] at this
        simp at this
        exact this.le
      _ = ε := by field_simp

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of 0 if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  rw [Sequence.isCauchy_def]
  rw [Sequence.convergent_def] at h
  obtain ⟨ L, hL ⟩ := h
  intro ε hε
  rw [Sequence.tendsTo_def] at hL
  specialize hL (ε / 2) (by positivity)
  rw [Real.eventuallyClose_def] at hL
  obtain ⟨ N, hN, h' ⟩ := hL
  rw [Real.eventuallySteady_def]
  use N
  constructor
  . exact hN
  . rw [Real.Steady]
    intro n hn m hm
    rw [Real.close_def, Real.dist_eq]
    simp [hn, hm]
    rw [Real.closeSeq_def] at h'
    have h1 := h' n hn
    have h2 := h' m hm
    simp [Real.dist_eq] at h1 h2
    simp at hn hm
    simp [hn, hm] at h1 h2
    calc
      _ = |a.seq n - L + (L - a.seq m)| := by ring
      _ ≤ |a.seq n - L| + |L - a.seq m| := by exact abs_add_le _ _
      _ = |a.seq n - L| + |a.seq m - L| := by simp; rw [abs_sub_comm]
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

/-- Example 6.1.13 -/
lemma ex1 : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  rw [Real.eventuallySteady_def]
  push_neg
  intro N hN
  simp at hN
  have hN' : N + 1 ≥ 0 := by omega
  rw [Real.steady_def]
  push_neg
  use N
  simp
  use hN
  use (N + 1)
  simp
  use hN'
  rw [Real.dist_eq]
  simp [hN, hN']
  lift N to ℕ using hN
  simp
  by_cases h: Even N
  . simp [h]
    norm_num
  . have : Odd N := by exact Nat.not_even_iff_odd.mp h
    simp [this]
    norm_num

/-- Example 6.1.13 -/
lemma ex2 : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  rw [Sequence.isCauchy_def]
  push_neg
  use (0.1:ℝ)
  constructor
  . norm_num
  . exact ex1

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  have := ex2
  contrapose! this
  exact Sequence.IsCauchy.convergent this

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  rw [Chapter5.Sequence.IsCauchy.coe] at h
  obtain ⟨ε', hε', hε''⟩ := exists_pos_rat_lt hε
  specialize h ε' hε'
  obtain ⟨ M, hM ⟩ := h
  use M
  intro n hn
  specialize hM n.toNat (by omega)
  have : 0 ≤ n := by omega
  lift n to ℕ using this
  simp
  sorry

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

-- finitie sequences are bounded
abbrev BoundedBy {n:ℕ} (a: Fin n → ℝ) (M:ℝ) : Prop := ∀ i, |a i| ≤ M

-- copy/pasted the proof 6.1.16
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℝ) : ∃ M ≥ 0, BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℝ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  -- copy/pasted the proof 5.1, with minor modifications
  rw [Sequence.isCauchy_def] at h
  rw [Sequence.isBounded_def]
  specialize h 1 (by norm_num)
  simp [Real.eventuallySteady_def] at h
  obtain ⟨N, hN, h⟩ := h
  have := IsBounded.finite (n:= (N - a.m).toNat) (fun n ↦ a (a.m + n))
  obtain ⟨M, hM, h'⟩ := this
  use max M (|(a N)| + 1)
  constructor
  . exact le_sup_of_le_left hM
  . rw [Sequence.boundedBy_def]
    intro n
    by_cases hn: n < N
    . rw [Chapter6.BoundedBy] at h'
      by_cases hnn : n ≥ a.m
      .
        simp only [le_sup_iff]
        left
        let n': Fin (N - a.m).toNat := ⟨(n - a.m).toNat, by omega⟩
        specialize h' n'
        unfold n' at h'
        have : (n - a.m).toNat + a.m = n := by omega
        rw [← this]
        rw [add_comm]
        exact h'
      . simp only [le_sup_iff]
        right
        simp only [ge_iff_le, not_le] at hnn
        rw [a.vanish n hnn]
        simp only [abs_zero]
        positivity
    . simp at hn
      rw [Real.steady_def] at h
      simp at h
      specialize h n (by linarith) hn N hN (by rfl)
      rw [Real.dist_eq] at h
      have hn': a.m ≤ n := by linarith
      simp [hN, hn', hn] at h
      have : |a.seq n| ≤ 1 + |a.seq N| := by
        calc
          |a.seq n| = |a.seq N - (a.seq N - a.seq n)| := by ring_nf
          _ ≤ |a.seq N| + |a.seq N - a.seq n| := by exact abs_sub _ _
          _ ≤ |a.seq N| + |a.seq n - a.seq N| := by rw [abs_sub_comm]
          _ ≤ |a.seq N| + 1 := by linarith [h]
          _ = 1 + |a.seq N| := by ring
      rw [add_comm] at this
      apply le_trans this
      exact le_max_right _ _


/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  exact Sequence.bounded_of_cauchy (IsCauchy.convergent h)

/-- Example 6.1.18 -/
lemma ex3: ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  push_neg
  intro M hM
  rw [Sequence.boundedBy_def]
  simp
  let B := ⌊M⌋ + 1
  have hB : 0 ≤ B := by positivity
  use B
  simp [hB]
  rw [abs_of_nonneg (by positivity)]
  norm_cast
  suffices h : M < (B:ℝ) by
    trans
    . exact h
    . push_cast
      have : (B.toNat : ℝ) = (B : ℝ) := by
        norm_cast
        rw [Int.toNat_of_nonneg hB]
      rw [this]
      linarith
  unfold B
  simp only [Int.cast_add, Int.cast_one, Int.lt_floor_add_one]

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  by_contra h
  have := Sequence.bounded_of_convergent h
  exact ex3 this

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_idx (a b:Sequence) (n:ℤ) :
  (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  specialize ha (ε / 2) (by positivity)
  specialize hb (ε / 2) (by positivity)
  choose N₁ hN₁ using ha
  choose N₂ hN₂ using hb
  let N := max N₁ N₂
  use N
  intro n hn
  specialize hN₁ n (by omega)
  specialize hN₂ n (by omega)
  calc
    _ = |a n - L + (b n - M)| := by
      congr
      rw [add_idx a b n]
      ring
    _ ≤ |a n - L| + |b n - M| := by exact abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := by linarith [hN₁, hN₂]
    _ = ε := by ring

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  have ha2 := ha
  have hb2 := hb
  rw [Sequence.convergent_def] at ha hb ⊢
  choose L ha' using ha
  choose M hb' using hb
  have := Sequence.tendsTo_add ha' hb'
  constructor
  . use L + M
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hM⟩ := lim_eq.mp hb'
    have ⟨_, hLM⟩ := lim_eq.mp this
    rw [hL, hM, hLM]

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_idx (a b:Sequence) (n:ℤ) :
  (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
  have hba := Sequence.bounded_of_convergent ((Sequence.convergent_def a).mpr ⟨L, ha⟩)
  rw [Sequence.isBounded_def] at hba
  obtain ⟨ B, hBpos, hB ⟩ := hba
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  by_cases hBneg : B = 0
  . subst B
    rw [Sequence.boundedBy_def] at hB
    have : ∀ n, a n = 0 := by
      intro n
      specialize hB n
      simp at hB
      exact hB
    simp [this] at ha
    have : L = 0 := by
      by_contra hL
      have : |L| > 0 := by positivity
      specialize ha (|L| / 2) (by positivity)
      obtain ⟨ N, hN ⟩ := ha
      specialize hN N (by linarith)
      linarith
    subst L
    have : ∀ n, (a * b) n = 0 := by
      intro n
      specialize this n
      rw [mul_idx]
      simp [this]
    intro ε hε
    use 0
    intro n hn
    specialize this n
    simp [this]
    exact hε.le
  intro ε hε
  specialize ha (ε / (2 * (1 + |M|))) (by positivity)
  specialize hb (ε / (2 * B)) (by positivity)
  obtain ⟨ N₁, hN₁ ⟩ := ha
  obtain ⟨ N₂, hN₂ ⟩ := hb
  let N := max N₁ N₂
  use N
  intro n hn
  specialize hN₁ n (by omega)
  specialize hN₂ n (by omega)
  calc
    _ = |a n * b n - L * M| := by rw [mul_idx]
    _ = |a n * b n - a n * M + (a n * M - L * M)| := by ring_nf
    _ ≤ |a n * b n - a n * M| + |a n * M - L * M| := by exact abs_add _ _
    _ = |a n * (b n - M)| + |M * (a n - L)| := by
      congr
      . ring_nf
      . ring_nf
    _ ≤ |a n| * |b n - M| + |M| * |a n - L| := by
      rw [abs_mul, abs_mul]
    _ ≤ B * (ε / (2 * B)) + |M| * (ε / (2 * (1 + |M|))) := by
      gcongr
      exact hB n
    _ = ε / 2 + |M| * (ε / (2 * (1 + |M|))) := by
      suffices B * (ε / (2 * B)) = ε / 2 by rw [this]
      field_simp [hBneg]
      ring
    _ ≤ ε / 2 + ε / 2 := by
      gcongr
      field_simp [hBneg]
      calc
        _ ≤ (|M| + 1) * (ε / (2 * (1 + |M|))) := by
          rw [show |M| * ε / (2 * (1 + |M|)) = |M| * (ε / (2 * (1 + |M|))) by ring]
          apply mul_le_mul_of_nonneg_right
          . linarith
          . positivity
        _ = ε / 2 := by field_simp [hBneg]; ring
    _ = ε := by ring

theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  have ha2 := ha
  have hb2 := hb
  rw [Sequence.convergent_def] at ha hb ⊢
  choose L ha' using ha
  choose M hb' using hb
  have := Sequence.tendsTo_mul ha' hb'
  constructor
  . use L * M
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hM⟩ := lim_eq.mp hb'
    have ⟨_, hLM⟩ := lim_eq.mp this
    rw [hL, hM, hLM]

instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

@[simp]
theorem Sequence.smul_idx (c:ℝ) (a:Sequence) (n:ℤ) :
  (c • a) n = c * a n := by rfl

/-- Theorem 6.1.19(c) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by

  rw [Sequence.tendsTo_iff] at ha ⊢
  intro ε hε
  by_cases h:c = 0
  . subst c
    simp at ha ⊢
    use 0
    intro n hn
    exact hε.le
  specialize ha (ε / |c|) (by positivity)
  obtain ⟨ N, hN ⟩ := ha
  use N
  intro n hn
  specialize hN n (by omega)
  calc
    _ = |c * a n - c * L| := by simp
    _ = |c| * |a n - L| := by rw [show c * a n - c * L = c * (a n - L) by ring, abs_mul]
    _ ≤ |c| * (ε / |c|) := by gcongr
    _ = ε := by field_simp

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  rw [Sequence.convergent_def] at ha ⊢
  obtain ⟨ L, ha' ⟩ := ha
  constructor
  . use c * L
    exact tendsTo_smul c ha'
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hCL⟩ := lim_eq.mp (tendsTo_smul c ha')
    grind only

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  rw [show (a - b) = a + ((-1: ℝ) • b) by
    ext n
    . rw [HSub.hSub, inst_sub, instHSub, Sub.sub, HSMul.hSMul, instHSMul, SMul.smul, inst_smul]
      rw [HAdd.hAdd, inst_add, instHAdd, Add.add]
    . simp
      exact rfl
  ]
  apply Sequence.tendsTo_add ha
  convert Sequence.tendsTo_smul (-1:ℝ) hb
  ext x
  simp only [neg_mul, one_mul]

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  have ha2 := ha
  have hb2 := hb
  rw [Sequence.convergent_def] at ha hb ⊢
  choose L ha' using ha
  choose M hb' using hb
  have := Sequence.tendsTo_sub ha' hb'
  constructor
  . use L - M
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hM⟩ := lim_eq.mp hb'
    have ⟨_, hLM⟩ := lim_eq.mp this
    rw [hL, hM, hLM]

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  rw [Sequence.tendsTo_iff] at ha ⊢
  have hLpos : |L| > 0 := by positivity
  have hB := ha ( |L| / 2 ) (by positivity)
  obtain ⟨ N₁, hN₁ ⟩ := hB
  intro ε hε
  specialize ha (ε * |L|^2 / 2) (by positivity)
  obtain ⟨ N₂, hN₂ ⟩ := ha
  let N := max N₁ N₂
  use N
  intro n hn
  have hanon: 0 < |a n| := by
    specialize hN₁ n (by omega)
    have : |L| / 2 ≤ |a n| := by
      calc
        _ = |L| - |L| / 2 := by ring
        _ ≤ |L| - |a n - L| := by linarith
        _ ≤ |a n| := by
          calc
            _ ≤ |L - (L - a n )| := by
              rw [abs_sub_comm]
              exact abs_sub_abs_le_abs_sub _ _
            _ = |a n| := by ring_nf
    linarith
  have hanon': a n ≠ 0 := by
    intro h
    simp [h] at hanon
  calc
    _ = |(a n)⁻¹ - L⁻¹| := by rw [inv_idx]
    _ = |L - a n| / (|a n| * |L|) := by
      rw [← abs_mul, ← abs_div]
      congr
      field_simp [hnon, hanon]
    _ ≤ |L - a n| / (|L| / 2 * |L|) := by
      gcongr
      specialize hN₁ n (by omega)
      calc
        _ = |L| - |L| / 2 := by ring
        _ ≤ |L| - |a n - L| := by gcongr
        _ ≤ |L - (L - a n)| := by
          rw [abs_sub_comm]
          exact abs_sub_abs_le_abs_sub L (L - a.seq n)
        _ = |a n| := by ring_nf
    _ = 2 * |L - a n| / (|L|^2) := by
      field_simp [hnon]
      ring
    _ ≤ _ := by
      specialize hN₂ n (by omega)
      rw [abs_sub_comm]
      calc
        _ ≤ 2 * (ε * |L|^2 / 2) / |L|^2 := by gcongr
        _ = ε := by field_simp [hnon]

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  rw [Sequence.convergent_def] at ha ⊢
  obtain ⟨ L, ha' ⟩ := ha
  have hL : L ≠ 0 := by
    have ⟨_, hL⟩ := lim_eq.mp ha'
    rw [← hL]
    exact hnon
  have := Sequence.tendsTo_inv ha' hL
  constructor
  · use L⁻¹
  · have ⟨_, hL'⟩ := lim_eq.mp ha'
    have ⟨_, hLinv⟩ := lim_eq.mp this
    rw [hL', hLinv]

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  rw [show a / b = a * (b⁻¹) by rfl]
  apply Sequence.tendsTo_mul ha
  exact Sequence.tendsTo_inv hb hnon

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  have ha2 := ha
  have hb2 := hb
  rw [Sequence.convergent_def] at ha hb ⊢
  choose L ha' using ha
  choose M hb' using hb
  have : M ≠ 0 := by
    have ⟨_, hM⟩ := lim_eq.mp hb'
    grind only
  have := Sequence.tendsTo_div ha' hb' this
  constructor
  . use L / M
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hM⟩ := lim_eq.mp hb'
    have ⟨_, hLM⟩ := lim_eq.mp this
    rw [hL, hM, hLM]

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  wlog h: L ≥ M generalizing L M a b ha hb
  · specialize this hb ha
    simp at h
    specialize this h.le
    have h: max a b = max b a := by
      ext n
      · exact min_comm a.m b.m
      · exact max_comm (a.seq n) (b.seq n)
    rw [max_comm L M, h]
    exact this
  rw [Sequence.tendsTo_iff] at ha hb ⊢
  intro ε hε
  by_cases hLM : L = M
  · subst hLM; simp only [max_self]
    obtain ⟨N₁, hN₁⟩ := ha ε (by positivity)
    obtain ⟨N₂, hN₂⟩ := hb ε (by positivity)
    use max N₁ N₂; intro n hn; simp only [max_idx]
    by_cases hab : a n ≥ b n
    · simp [hab]; linarith [hN₁ n (by omega)]
    · simp at hab; simp [hab.le]; linarith [hN₂ n (by omega)]
  · have hLgt : L > M := by grind only
    set δ := min ε ((L - M) / 2)
    have hδ_pos : δ > 0 := by
      have : L - M > 0 := by linarith
      positivity
    obtain ⟨N₁, hN₁⟩ := ha δ hδ_pos
    obtain ⟨N₂, hN₂⟩ := hb δ hδ_pos
    use max N₁ N₂; intro n hn
    have ha' := hN₁ n (by omega)
    have hb' := hN₂ n (by omega)
    have hab : a n ≥ b n := by
      have ha_lb : a n ≥ L - δ := by
        rcases le_or_gt (a n) L with h | h
        · calc a n = L - (L - a n) := by ring
               _ ≥ L - |a n - L| := by linarith [le_abs_self (L - a n), abs_sub_comm L (a n)]
               _ ≥ L - δ := by linarith
        · linarith [abs_nonneg (a n - L)]
      have hb_ub : b n ≤ M + δ := by
        rcases le_or_gt M (b n) with h | h
        · linarith [le_abs_self (b n - M)]
        · linarith [abs_nonneg (b n - M)]
      calc a n ≥ L - δ := ha_lb
           _ ≥ (L + M) / 2 := by linarith [min_le_right ε ((L - M) / 2)]
           _ ≥ M + δ := by linarith [min_le_right ε ((L - M) / 2)]
           _ ≥ b n := hb_ub
    simp only [max_idx]
    calc
      _ = |a n - L| := by simp [hab, h]
      _ ≤ δ := ha'
      _ ≤ ε := min_le_left _ _

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  have ha2 := ha
  have hb2 := hb
  rw [Sequence.convergent_def] at ha hb ⊢
  choose L ha' using ha
  choose M hb' using hb
  have := Sequence.tendsTo_max ha' hb'
  constructor
  . use max L M
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hM⟩ := lim_eq.mp hb'
    have ⟨_, hLM⟩ := lim_eq.mp this
    rw [hL, hM, hLM]

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  rw [show min a b = (-1:ℝ) •(max ((-1:ℝ) • a)) ((-1:ℝ) • b) by
    ext n
    . rfl
    . simp
      by_cases h: a n ≤ b n
      . simp [h]
      . simp at h; simp [h.le]
  ]
  apply Sequence.tendsTo_smul (-1:ℝ) at ha
  apply Sequence.tendsTo_smul (-1:ℝ) at hb
  have := Sequence.tendsTo_max ha hb
  apply Sequence.tendsTo_smul (-1:ℝ) at this
  suffices h: min L M = -1 * (max (-1 * L) (-1 * M)) by
    rw [h]
    exact this
  simp only [neg_mul, one_mul]
  -- should be a theorem in mathlib but I can't find it
  by_cases hLM : L ≤ M
  . simp [hLM]
  . simp at hLM
    simp [hLM.le]

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  have ha2 := ha
  have hb2 := hb
  rw [Sequence.convergent_def] at ha hb ⊢
  choose L ha' using ha
  choose M hb' using hb
  have := Sequence.tendsTo_min ha' hb'
  constructor
  . use min L M
  . have ⟨_, hL⟩ := lim_eq.mp ha'
    have ⟨_, hM⟩ := lim_eq.mp hb'
    have ⟨_, hLM⟩ := lim_eq.mp this
    rw [hL, hM, hLM]

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  sorry

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  sorry

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  sorry

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
  sorry

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  sorry

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  sorry
end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by sorry

end Chapter6
