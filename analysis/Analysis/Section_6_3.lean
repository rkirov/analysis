import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Pi.Bounds

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  rw [Sequence.sup]
  apply le_antisymm
  . apply csSup_le
    . simp
      use -1
      use 0
      simp
    . simp
      intro h x hx h2
      simp [hx] at h2
      have hxnat : x = x.toNat := (Int.toNat_of_nonneg hx).symm
      by_cases heven : Even x.toNat
      . have hodd : Odd (x.toNat + 1) := Even.add_one heven
        rw [hodd.neg_one_pow] at h2
        rw [h2]
        exact EReal.coe_le_coe_iff.mpr (by norm_num)
      . have heven' : Even (x.toNat + 1) := Nat.not_even_iff_odd.mp heven |>.add_one
        rw [heven'.neg_one_pow] at h2
        rw [h2]
  . apply le_csSup
    . simp only [ge_iff_le, OrderTop.bddAbove]
    . simp only [ge_iff_le, Set.mem_setOf_eq]
      use 1
      simp

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  rw [Sequence.inf]
  apply le_antisymm
  . apply csInf_le
    . simp only [ge_iff_le, OrderBot.bddBelow]
    . simp only [ge_iff_le, Set.mem_setOf_eq]
      use 0
      simp
  . apply le_csInf
    . simp
      use -1
      use 0
      simp
    . simp
      intro h x hx h2
      simp [hx] at h2
      have hxnat : x = x.toNat := (Int.toNat_of_nonneg hx).symm
      by_cases heven : Even x.toNat
      . have hodd : Odd (x.toNat + 1) := Even.add_one heven
        rw [hodd.neg_one_pow] at h2
        rw [h2]
      . have heven' : Even (x.toNat + 1) := Nat.not_even_iff_odd.mp heven |>.add_one
        rw [heven'.neg_one_pow] at h2
        rw [h2]
        exact EReal.coe_le_coe_iff.mpr (by norm_num)

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  rw [Sequence.sup]
  apply le_antisymm
  . apply csSup_le
    . simp; use 1; use 0; simp
    . simp
      intro h x hx h2
      simp [hx] at h2
      rw [h2]
      apply EReal.coe_le_coe_iff.mpr
      apply inv_le_one_of_one_le₀
      linarith
  . apply le_csSup
    . simp only [ge_iff_le, OrderTop.bddAbove]
    . simp only [ge_iff_le, Set.mem_setOf_eq]
      use 0; simp

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  rw [Sequence.inf]
  apply le_antisymm
  . -- show inf ≤ 0: for any ε > 0, there exists n with 1/(n+1) < ε
    apply le_of_forall_gt
    intro c hc
    -- c > 0 in EReal
    cases c with
    | bot => simp at hc
    | top =>
      -- Need to show inf < ⊤, which is true since the set is nonempty
      have hmem : (↑(1:ℝ) : EReal) ∈ {x | ∃ m ≥ (0:ℤ), x = ↑(if m ≥ 0 then 1 / ((m.toNat:ℝ) + 1) else 0)} := by
        simp; use 0; simp
      exact lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hmem) (EReal.coe_lt_top 1)
    | coe r =>
      simp only [EReal.coe_pos] at hc
      -- r > 0, find n with 1/(n+1) < r
      set n := ⌈1/r⌉₊
      have hmem : (↑(1 / ((n:ℝ) + 1)) : EReal) ∈ {x | ∃ m ≥ (0:ℤ), x = ↑(if m ≥ 0 then 1 / ((m.toNat:ℝ) + 1) else 0)} := by
        simp; use n; simp
      have hlt : (↑(1 / ((n:ℝ) + 1)) : EReal) < ↑r := by
        apply EReal.coe_lt_coe_iff.mpr
        rw [one_div, inv_lt_comm₀ (by positivity : (0:ℝ) < (n:ℝ) + 1) hc]
        have h1 : 1/r ≤ n := Nat.le_ceil (1/r)
        have h2 : (n:ℝ) < n + 1 := by linarith
        calc r⁻¹ = 1/r := by ring
          _ ≤ n := h1
          _ < n + 1 := h2
      exact csInf_lt_of_lt (OrderBot.bddBelow _) hmem hlt
  . -- show 0 ≤ inf: 0 is a lower bound
    apply le_csInf
    . simp; use 1; use 0; simp
    . simp
      intro h x hx h2
      simp [hx] at h2
      rw [h2]
      apply EReal.coe_le_coe_iff.mpr
      positivity

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  rw [Sequence.sup]
  -- Show sup = ⊤ by showing the set is unbounded above
  apply le_antisymm
  . exact le_top
  . -- show ⊤ ≤ sup: for any M < ⊤, there exists n with n+1 > M
    apply le_of_forall_lt
    intro c hc
    cases c with
    | bot =>
      have hmem : (↑(1:ℝ) : EReal) ∈ {x | ∃ m ≥ (0:ℤ), x = ↑(if m ≥ 0 then ((m.toNat:ℝ) + 1) else 0)} := by
        simp; use 0; simp
      exact lt_of_eq_of_lt rfl (lt_of_lt_of_le (EReal.bot_lt_coe 1) (le_csSup (OrderTop.bddAbove _) hmem))
    | top => exact absurd hc (lt_irrefl _)
    | coe r =>
      -- Find n with n+1 > r
      have hmem : (↑((⌈r⌉₊ + 1 : ℕ) : ℝ) : EReal) ∈ {x | ∃ m ≥ (0:ℤ), x = ↑(if m ≥ 0 then ((m.toNat:ℝ) + 1) else 0)} := by
        simp; use ⌈r⌉₊; simp
      apply lt_of_lt_of_le _ (le_csSup (OrderTop.bddAbove _) hmem)
      apply EReal.coe_lt_coe_iff.mpr
      calc r ≤ ⌈r⌉₊ := Nat.le_ceil r
        _ < (⌈r⌉₊:ℝ) + 1 := by linarith
        _ = ((⌈r⌉₊ + 1 : ℕ) : ℝ) := by simp [Nat.cast_add]

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  rw [Sequence.inf]
  apply le_antisymm
  . -- show inf ≤ 1: 1 is in the set (at n=0)
    apply csInf_le (OrderBot.bddBelow _)
    simp; use 0; simp
  . -- show 1 ≤ inf: 1 is a lower bound (n+1 ≥ 1 for all n ≥ 0)
    apply le_csInf
    . simp; use 1; use 0; simp
    . simp
      intro h x hx h2
      simp [hx] at h2
      rw [h2]
      apply EReal.coe_le_coe_iff.mpr
      have : (0:ℝ) ≤ x.toNat := Nat.cast_nonneg _
      linarith

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  constructor
  · -- IsBounded → BddAbove ∧ BddBelow
    intro ⟨M, _, hM⟩
    exact ⟨⟨M, fun n _ => le_of_abs_le (hM n)⟩,
           ⟨-M, fun n _ => neg_le_of_abs_le (hM n)⟩⟩
  · -- BddAbove ∧ BddBelow → IsBounded
    intro ⟨⟨U, hU⟩, ⟨L, hL⟩⟩
    use max (|U|) (|L|), le_max_of_le_left (abs_nonneg U)
    intro n
    by_cases hn : n ≥ a.m
    · rw [abs_le]
      exact ⟨le_trans (neg_le_neg (le_max_right _ _)) (le_trans (neg_abs_le L) (hL n hn)),
             le_trans (hU n hn) (le_trans (le_abs_self U) (le_max_left _ _))⟩
    · simp [a.vanish n (by omega)]

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
  obtain ⟨U, hU⟩ := (a.bounded_iff.mp h).1
  have hsup_le : a.sup ≤ ↑U := by
    apply sSup_le; rintro x ⟨n, hn, rfl⟩; exact_mod_cast hU n hn
  have hsup_ge : ↑(a a.m) ≤ a.sup :=
    le_sSup ⟨a.m, le_refl _, rfl⟩
  rcases EReal.def a.sup with ⟨y, hy⟩ | htop | hbot
  · exact ⟨y, hy⟩
  · rw [htop] at hsup_le; exact absurd hsup_le (not_le.mpr (EReal.coe_lt_top _))
  · rw [hbot] at hsup_ge; exact absurd hsup_ge (not_le.mpr (EReal.bot_lt_coe _))

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  obtain ⟨L, hL⟩ := (a.bounded_iff.mp h).2
  have hinf_ge : ↑L ≤ a.inf := by
    apply le_sInf; rintro x ⟨n, hn, rfl⟩; exact_mod_cast hL n hn
  have hinf_le : a.inf ≤ ↑(a a.m) :=
    sInf_le ⟨a.m, le_refl _, rfl⟩
  rcases EReal.def a.inf with ⟨y, hy⟩ | htop | hbot
  · exact ⟨y, hy⟩
  · rw [htop] at hinf_le; exact absurd hinf_le (not_le.mpr (EReal.coe_lt_top _))
  · rw [hbot] at hinf_ge; exact absurd hinf_ge (not_le.mpr (EReal.bot_lt_coe _))

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by
  rw [Sequence.sup]
  apply le_sSup
  use n

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  rw [Sequence.sup]
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  exact h n hn

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
  by_contra h'
  push_neg at h'
  -- h' : ∀ n ≥ a.m, y < a n → a.sup < a n
  -- Since a.le_sup gives a n ≤ a.sup, the premise y < a n must be false.
  -- So a n ≤ y for all n ≥ a.m, making y an upper bound.
  have hle : a.sup ≤ y := a.sup_le_upper fun n hn => by
    by_contra hlt; push_neg at hlt
    exact absurd (a.le_sup hn) (not_le.mpr (h' n hn hlt))
  exact absurd hle (not_le.mpr h)

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by
  rw [Sequence.inf]
  apply sInf_le
  exact ⟨n, hn, rfl⟩

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  rw [Sequence.inf]
  apply le_sInf
  rintro x ⟨n, hn, rfl⟩
  exact h n hn

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
  by_contra h'
  push_neg at h'
  exact (not_le.mpr h) (a.inf_ge_lower fun n hn => by
    by_contra hgt; push_neg at hgt
    exact absurd (a.ge_inf hn) (not_le.mpr (h' n hn hgt)))

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Monotone sequences are increasing: a n ≥ a N when n ≥ N ≥ a.m -/
private theorem Sequence.monotone_le {a:Sequence} (hmono: a.IsMonotone)
    {N n : ℤ} (hN : N ≥ a.m) (hn : n ≥ N) : a n ≥ a N := by
  suffices h : ∀ k : ℕ, a (N + k) ≥ a N by
    obtain ⟨k, hk⟩ := Int.le.dest hn
    have : a n = a (N + ↑k) := by congr; omega
    rw [this]; exact h k
  intro k; induction k with
  | zero => simp
  | succ k ih =>
    have h2 := hmono (N + k) (by omega : N + ↑k ≥ a.m)
    have : a (N + ↑(k + 1)) = a (N + ↑k + 1) := by congr 1; omega
    rw [this]; exact le_trans ih h2

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by
  have hbdd : a.IsBounded := by
    rw [a.bounded_iff]
    exact ⟨hbound, ⟨a a.m, fun n hn => a.monotone_le hmono le_rfl hn⟩⟩
  obtain ⟨S, hS⟩ := a.sup_of_bounded hbdd
  rw [convergent_def]; use S; rw [tendsTo_iff]
  intro ε hε
  have hlt : (↑(S - ε) : EReal) < a.sup := by
    rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨N, hN, haN, _⟩ := a.exists_between_lt_sup hlt
  use N; intro n hn
  rw [abs_le]
  constructor
  · have hmn : (↑(a n) : EReal) ≥ a N :=
      EReal.coe_le_coe_iff.mpr (a.monotone_le hmono hN hn)
    linarith [EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le haN hmn)]
  · have : (a n : EReal) ≤ a.sup := a.le_sup (by omega)
    rw [← hS] at this
    linarith [EReal.coe_le_coe_iff.mp this]

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by
  have hconv := a.convergent_of_monotone hbound hmono
  obtain ⟨S, hS⟩ := a.sup_of_bounded (bounded_of_convergent hconv)
  suffices h : a.TendsTo S by rw [(lim_eq.mp h).2, hS]
  rw [tendsTo_iff]; intro ε hε
  have hlt : (↑(S - ε) : EReal) < a.sup := by
    rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨N, hN, haN, _⟩ := a.exists_between_lt_sup hlt
  use N; intro n hn; rw [abs_le]
  exact ⟨by linarith [EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le haN
      (EReal.coe_le_coe_iff.mpr (a.monotone_le hmono hN hn)))],
    by have : (a n : EReal) ≤ a.sup := a.le_sup (by omega)
       rw [← hS] at this; linarith [EReal.coe_le_coe_iff.mp this]⟩

private theorem Sequence.antitone_le {a:Sequence} (hmono: a.IsAntitone)
    {N n : ℤ} (hN : N ≥ a.m) (hn : n ≥ N) : a n ≤ a N := by
  suffices h : ∀ k : ℕ, a (N + k) ≤ a N by
    obtain ⟨k, hk⟩ := Int.le.dest hn
    have : a n = a (N + ↑k) := by congr; omega
    rw [this]; exact h k
  intro k; induction k with
  | zero => simp
  | succ k ih =>
    have h2 := hmono (N + k) (by omega : N + ↑k ≥ a.m)
    have : a (N + ↑(k + 1)) = a (N + ↑k + 1) := by congr 1; omega
    rw [this]; exact le_trans h2 ih

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by
  have hbdd : a.IsBounded := by
    rw [a.bounded_iff]
    exact ⟨⟨a a.m, fun n hn => a.antitone_le hmono le_rfl hn⟩, hbound⟩
  obtain ⟨S, hS⟩ := a.inf_of_bounded hbdd
  rw [convergent_def]; use S
  rw [tendsTo_iff]
  intro ε hε
  have hgt : a.inf < (↑(S + ε) : EReal) := by
    rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨N, hN, haN, _⟩ := a.exists_between_gt_inf hgt
  use N; intro n hn
  rw [abs_le]
  constructor
  · have : (a n : EReal) ≥ a.inf := a.ge_inf (by omega)
    rw [← hS] at this; linarith [EReal.coe_le_coe_iff.mp this]
  · have hmn : (↑(a n) : EReal) ≤ a N :=
      EReal.coe_le_coe_iff.mpr (a.antitone_le hmono hN hn)
    linarith [EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt hmn haN)]

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
  have hconv := a.convergent_of_antitone hbound hmono
  obtain ⟨S, hS⟩ := a.inf_of_bounded (bounded_of_convergent hconv)
  suffices h : a.TendsTo S by rw [(lim_eq.mp h).2, hS]
  rw [tendsTo_iff]; intro ε hε
  have hgt : a.inf < (↑(S + ε) : EReal) := by
    rw [← hS]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨N, hN, haN, _⟩ := a.exists_between_gt_inf hgt
  use N; intro n hn; rw [abs_le]
  exact ⟨by have : (a n : EReal) ≥ a.inf := a.ge_inf (by omega)
            rw [← hS] at this; linarith [EReal.coe_le_coe_iff.mp this],
    by linarith [EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt
      (EReal.coe_le_coe_iff.mpr (a.antitone_le hmono hN hn)) haN)]⟩

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by
  constructor
  · exact bounded_of_convergent
  · intro hb; exact a.convergent_of_monotone (a.bounded_iff.mp hb).1 ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by
  constructor
  · exact bounded_of_convergent
  · intro hb; exact a.convergent_of_antitone (a.bounded_iff.mp hb).2 ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

private lemma example_6_3_9_monotone : (Example_6_3_9:Sequence).IsMonotone := by
  intro n hn
  have hn0 : (0:ℤ) ≤ n := by linarith
  simp only [hn0, show (0:ℤ) ≤ n + 1 from by linarith, ite_true, ge_iff_le]
  rw [show (n + 1).toNat = n.toNat + 1 from by omega]
  set m := n.toNat
  have h10m : (0:ℝ) < 10^m := by positivity
  rw [div_le_div_iff₀ h10m (by positivity : (0:ℝ) < 10^(m+1))]
  have hpow : (10:ℝ)^(m+1) = 10 * 10^m := pow_succ' 10 m
  have hkey : (10:ℝ) * ↑⌊Real.pi * (10:ℝ)^m⌋ ≤ ↑⌊Real.pi * (10:ℝ)^(m+1)⌋ := by
    exact_mod_cast show (10:ℤ) * ⌊Real.pi * (10:ℝ)^m⌋ ≤ ⌊Real.pi * (10:ℝ)^(m+1)⌋ from by
      rw [Int.le_floor]; push_cast; rw [hpow]
      nlinarith [Int.floor_le (Real.pi * (10:ℝ)^m)]
  calc ↑⌊Real.pi * (10:ℝ)^m⌋ * (10:ℝ)^(m+1)
      = ↑⌊Real.pi * (10:ℝ)^m⌋ * (10 * 10^m) := by rw [hpow]
    _ = (10 * ↑⌊Real.pi * (10:ℝ)^m⌋) * 10^m := by ring
    _ ≤ ↑⌊Real.pi * (10:ℝ)^(m+1)⌋ * 10^m := by nlinarith

private lemma example_6_3_9_bddAbove : (Example_6_3_9:Sequence).BddAboveBy 4 := by
  intro n hn
  have hn0 : (0:ℤ) ≤ n := by linarith
  simp only [hn0, ite_true]
  set m := n.toNat
  have : (↑⌊Real.pi * (10:ℝ)^m⌋ : ℝ) / 10^m ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 10^m)]
    linarith [Int.floor_le (Real.pi * (10:ℝ)^m)]
  linarith [Real.pi_lt_d6]

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := example_6_3_9_monotone

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := example_6_3_9_bddAbove

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent :=
  Sequence.convergent_of_monotone ⟨4, example_6_3_9_bddAbove⟩ example_6_3_9_monotone

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by
  set a := (Example_6_3_9:Sequence)
  have hlim := a.lim_of_monotone ⟨4, example_6_3_9_bddAbove⟩ example_6_3_9_monotone
  have hsup : a.sup ≤ (4 : EReal) :=
    a.sup_le_upper fun n hn => EReal.coe_le_coe_iff.mpr (example_6_3_9_bddAbove n hn)
  rw [← hlim] at hsup
  exact EReal.coe_le_coe_iff.mp hsup


/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := by
    rw [Sequence.IsAntitone]
    intro n hn
    unfold a
    simp only [ge_iff_le]
    have hn : 0 ≤ n := by linarith
    have : 0 ≤ n + 1 := by linarith
    simp [this, hn]
    apply (pow_le_pow_iff_right_of_lt_one₀ hpos hbound).mpr
    simp
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by
    suffices h : ((fun (n:ℕ) ↦ x^(n+1)):Sequence).TendsTo L by
      exact (Sequence.lim_eq.mp h).2
    rw [Sequence.tendsTo_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Sequence.tendsTo_iff a L).mp (a.lim_def hconv) ε hε
    use max N 0
    intro n hn
    have hn0 : (0:ℤ) ≤ n := le_trans (le_max_right N 0) hn
    specialize hN (n + 1) (by linarith [show N ≤ n from le_trans (le_max_left N 0) hn])
    suffices heq : ((fun n:ℕ ↦ x^(n+1)):Sequence).seq n = a.seq (n + 1) by rw [heq]; exact hN
    simp only [a, hn0, show (0 : ℤ) ≤ n + 1 from by linarith, ite_true]
    congr 1; omega
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
  rw [Sequence.convergent_iff_bounded_of_monotone]
  · rw [Sequence.bounded_iff]
    push_neg
    intro ⟨M, hM⟩
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hbound
    have := hM ↑n (by positivity)
    simp at this; linarith
  · intro n hn
    simp [show (0:ℤ) ≤ n from by linarith, show (0:ℤ) ≤ n + 1 from by linarith]
    exact pow_le_pow_right₀ (le_of_lt hbound) (by omega)

end Chapter6
