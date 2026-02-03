import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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
      have h1 : r ≤ ⌈r⌉₊ := Nat.le_ceil r
      have h2 : (⌈r⌉₊:ℝ) < (⌈r⌉₊:ℝ) + 1 := by linarith
      calc r ≤ ⌈r⌉₊ := h1
        _ < (⌈r⌉₊:ℝ) + 1 := h2
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

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by sorry

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by sorry

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by sorry

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by sorry

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by sorry

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by sorry

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by sorry

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by sorry

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by sorry

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by sorry

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by sorry

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := sorry
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by sorry
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by sorry

end Chapter6
