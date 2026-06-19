import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_9_6


/-!
# Analysis I, Section 9.7: The intermediate value theorem

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The intermediate value theorem.
-/

namespace Chapter9

/-- Theorem 9.7.1 (Intermediate value theorem) -/
theorem intermediate_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ} (hy: y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) :
  ∃ c ∈ Set.Icc a b, f c = y := by
  -- This proof is written to follow the structure of the original text.
  obtain hy_left | hy_right := hy
  . by_cases hya : y = f a; use a; grind
    by_cases hyb : y = f b; use b; grind
    simp at hy_left
    replace hya : f a < y := by grind
    replace hyb : y < f b := by grind
    set E := {x | x ∈ Set.Icc a b ∧ f x < y}
    have hE : E ⊆ .Icc a b := fun x ⟨hx₁, hx₂⟩ ↦ hx₁
    have hE_bdd : BddAbove E := bddAbove_Icc.mono hE
    have hEa : a ∈ E := by simp [E, hya, le_of_lt hab]
    have hE_nonempty : E.Nonempty := by use a
    set c := sSup E
    have hc : c ∈ Set.Icc a b := by
      simp; split_ands
      . solve_by_elim [le_csSup]
      convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
      grind [csSup_Icc]
    use c, hc
    have hfc_upper : f c ≤ y := by
      have hxe (n:ℕ) : ∃ x ∈ E, c - 1/(n+1:ℝ) < x := by
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c - 1/(n+1:ℝ) < sSup E := by linarith
        solve_by_elim [exists_lt_of_lt_csSup]
      set x := fun n ↦ (hxe n).choose
      have hx1 (n:ℕ) : x n ∈ E := (hxe n).choose_spec.1
      have hx2 (n:ℕ) : c - 1/(n+1:ℝ) < x n := (hxe n).choose_spec.2
      have : Filter.atTop.Tendsto x (nhds c) := by
        apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1:ℝ)) (h := fun j ↦ c) (f := x)
        . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub c;simp
        . exact tendsto_const_nhds
        . exact fun n ↦ le_of_lt (hx2 n)
        exact fun n ↦ le_csSup hE_bdd (hx1 n)
      replace := this.comp_of_continuous (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n))
      have hfxny (n:ℕ) : f (x n) ≤ y := by specialize hx1 n; simp [E] at hx1; grind
      exact le_of_tendsto' this hfxny
    have hne : c < b := by grind
    have hfc_lower : y ≤ f c := by
      have : ∃ N:ℕ, ∀ n ≥ N, (c+1/(n+1:ℝ)) < b := by
        choose N hN using exists_nat_gt (1/(b-c))
        use N; intro n hn
        have hpos : 0 < b-c := by linarith
        have : 1/(n+1:ℝ) < b-c := by rw [one_div_lt] <;> (try positivity); apply hN.trans; norm_cast; linarith
        linarith
      choose N hN using this
      have hmem : ∀ n ≥ N, (c + 1/(n+1:ℝ)) ∈ Set.Icc a b := by
        intro n hn
        simp [-one_div, le_of_lt (hN n hn)]
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        grind
      have : ∀ n ≥ N, c + 1/(n+1:ℝ) ∉ E := by
        intro n _
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        solve_by_elim [notMem_of_csSup_lt]
      replace : ∀ n ≥ N, f (c + 1/(n+1:ℝ)) ≥ y := by
        intro n hn; specialize this n hn; contrapose! this
        simp [E]
        have := hmem n hn
        simp_all
      have hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (nhds c) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add c; simp
      replace hf := (hf.continuousWithinAt hc).tendsto
      rw [nhdsWithin.eq_1] at hf
      have hconv' : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (.principal (.Icc a b)) := by
        simp [-one_div, -Set.mem_Icc]; use N
      replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
      apply ge_of_tendsto (hf.comp hconv') _
      simp [-one_div]; use N
    linarith
  . by_cases hya : y = f a; use a; grind
    by_cases hyb : y = f b; use b; grind
    simp at hy_right
    replace hya : y < f a := by grind
    replace hyb : f b < y := by grind
    set E := {x | x ∈ Set.Icc a b ∧ f x > y}
    have hE : E ⊆ .Icc a b := fun x ⟨hx₁, hx₂⟩ ↦ hx₁
    have hE_bdd : BddAbove E := bddAbove_Icc.mono hE
    have hEa : a ∈ E := by simp [E, hya, le_of_lt hab]
    have hE_nonempty : E.Nonempty := by use a
    set c := sSup E
    have hc : c ∈ Set.Icc a b := by
      simp; split_ands
      . solve_by_elim [le_csSup]
      convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
      grind [csSup_Icc]
    use c, hc
    have hfc_lower : f c ≥ y := by
      have hxe (n:ℕ) : ∃ x ∈ E, c - 1/(n+1:ℝ) < x := by
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c - 1/(n+1:ℝ) < sSup E := by linarith
        solve_by_elim [exists_lt_of_lt_csSup]
      set x := fun n ↦ (hxe n).choose
      have hx1 (n:ℕ) : x n ∈ E := (hxe n).choose_spec.1
      have hx2 (n:ℕ) : c - 1/(n+1:ℝ) < x n := (hxe n).choose_spec.2
      have : Filter.atTop.Tendsto x (nhds c) := by
        apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1:ℝ)) (h := fun j ↦ c) (f := x)
        . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub c;simp
        . exact tendsto_const_nhds
        . exact fun n ↦ le_of_lt (hx2 n)
        exact fun n ↦ le_csSup hE_bdd (hx1 n)
      replace := this.comp_of_continuous (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n))
      have hfxny (n:ℕ) : f (x n) ≥ y := by specialize hx1 n; simp [E] at hx1; grind
      exact ge_of_tendsto' this hfxny
    have hne : c < b := by grind
    have hfc_upper : y ≥ f c := by
      have : ∃ N:ℕ, ∀ n ≥ N, (c+1/(n+1:ℝ)) < b := by
        choose N hN using exists_nat_gt (1/(b-c))
        use N; intro n hn
        have hpos : 0 < b-c := by linarith
        have : 1/(n+1:ℝ) < b-c := by rw [one_div_lt] <;> (try positivity); apply hN.trans; norm_cast; linarith
        linarith
      choose N hN using this
      have hmem : ∀ n ≥ N, (c + 1/(n+1:ℝ)) ∈ Set.Icc a b := by
        intro n hn
        simp [-one_div, le_of_lt (hN n hn)]
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        grind
      have : ∀ n ≥ N, c + 1/(n+1:ℝ) ∉ E := by
        intro n _
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        solve_by_elim [notMem_of_csSup_lt]
      replace : ∀ n ≥ N, f (c + 1/(n+1:ℝ)) ≤ y := by
        intro n hn; specialize this n hn; contrapose! this
        simp [E]
        have := hmem n hn
        simp_all
      have hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (nhds c) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add c; simp
      replace hf := (hf.continuousWithinAt hc).tendsto
      rw [nhdsWithin.eq_1] at hf
      have hconv' : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (.principal (.Icc a b)) := by
        simp [-one_div, -Set.mem_Icc]; use N
      replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
      apply le_of_tendsto (hf.comp hconv') _
      simp [-one_div]; use N
    linarith

open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

example : 0 ∈ Set.Icc (f_9_7_1 (-1)) (f_9_7_1 1) ∧ ¬ ∃ x ∈ Set.Icc (-1) 1, f_9_7_1 x = 0 := by
  constructor
  . simp [f_9_7_1]
    norm_num
  . simp [f_9_7_1]
    intro x hx hx'
    push_neg
    by_cases h : x ≤ 0 <;> simp [h]

/-- Remark 9.7.2 -/
abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

example : f_9_7_2 (-2) = -6 := by norm_num
example : f_9_7_2 2 = 6 := by norm_num
example : f_9_7_2 (-1) = 0 := by norm_num
example : f_9_7_2 0 = 0 := by norm_num
example : f_9_7_2 1 = 0 := by norm_num

/-- Remark 9.7.3 -/
example : ∃ x:ℝ, 0 ≤ x ∧ x ≤ 2 ∧ x^2 = 2 := by
  have h : (2:ℝ) ∈ Set.Icc (0^2) (2^2) := by norm_num
  have hlt : 0 < (2:ℝ) := by norm_num
  obtain ⟨x, hx⟩ := intermediate_value hlt (continuousOn_id.pow 2) (Or.inl h)
  use x
  simp at hx
  simp [hx]

/-- Corollary 9.7.4 (Images of continuous functions) / Exercise 9.7.1 -/
theorem continuous_image_Icc {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ}
    (hy: sInf (f '' .Icc a b) ≤ y ∧ y ≤ sSup (f '' .Icc a b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨xmin, hxmin, hm⟩ := sInf.of_continuous_on_compact hab f hf
  obtain ⟨xmax, hxmax, hM⟩ := sSup.of_continuous_on_compact hab f hf
  obtain ⟨hym, hyM⟩ := hy
  rw [hm] at hym; rw [hM] at hyM
  by_cases heq : xmin = xmax
  · use xmin, hxmin; rw [← heq] at hyM; linarith
  · set p := min xmin xmax
    set q := max xmin xmax
    have hpq : p < q := lt_of_le_of_ne min_le_max (by simp [p, q, heq])
    have hsub : Set.Icc p q ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc (le_min hxmin.1 hxmax.1) (max_le hxmin.2 hxmax.2)
    have hf' : ContinuousOn f (Set.Icc p q) := hf.mono hsub
    have hy' : y ∈ Set.Icc (f p) (f q) ∨ y ∈ Set.Icc (f q) (f p) := by
      rcases le_or_gt xmin xmax with h | h
      · left;  simp [p, q, min_eq_left h, max_eq_right h]; exact ⟨hym, hyM⟩
      · right; simp [p, q, min_eq_right h.le, max_eq_left h.le]; exact ⟨hym, hyM⟩
    obtain ⟨c, hc, hfc⟩ := intermediate_value hpq hf' hy'
    exact ⟨c, hsub hc, hfc⟩

theorem continuous_image_Icc' {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b))
    : f '' .Icc a b = .Icc (sInf (f '' .Icc a b)) (sSup (f '' .Icc a b)) := by
  have hbd : Bornology.IsBounded (f '' .Icc a b) :=
    (BddOn.iff' f (.Icc a b)).mp (BddOn.of_continuous_on_compact hab hf)
  ext x
  constructor
  . intro h
    constructor
    . apply csInf_le
      . exact hbd.bddBelow
      . exact h
    . apply le_csSup
      . exact hbd.bddAbove
      . exact h
  . intro h
    obtain ⟨y, hy⟩ := continuous_image_Icc hab hf h
    use y

/-- Exercise 9.7.2 -/
theorem exists_fixed_pt {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc 0 1)) (hmap: f '' .Icc 0 1 ⊆ .Icc 0 1) : ∃ x ∈ Set.Icc 0 1, f x = x := by
  let g := fun x ↦ f x - x
  have hg : ContinuousOn g (.Icc 0 1) := by
    apply ContinuousOn.sub
    . exact hf
    . exact continuousOn_id
  have ha : g 0 ≥ 0 := by
    simp [g]
    simp only [Set.image_subset_iff] at hmap
    have : (0:ℝ) ∈ Set.Icc 0 1 := by simp
    have := hmap this
    simp only [Set.mem_preimage, Set.mem_Icc] at this
    exact this.1
  have hb : g 1 ≤ 0 := by
    simp [g]
    simp only [Set.image_subset_iff] at hmap
    have : (1:ℝ) ∈ Set.Icc 0 1 := by simp
    have := hmap this
    simp only [Set.mem_preimage, Set.mem_Icc] at this
    exact this.2
  have := intermediate_value (show 0 < 1 by norm_num) hg (y:=0) (Or.inr ⟨hb, ha⟩)
  obtain ⟨x, hx, hgx⟩ := this
  use x, hx
  unfold g at hgx
  linarith
end Chapter9
