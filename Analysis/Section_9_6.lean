import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.6: The maximum principle

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded.
- Continuous functions on closed and bounded intervals attain their maximum and minimum.
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f:ℝ → ℝ) (X:Set ℝ) : BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  constructor
  . intro h
    choose M hM using h
    constructor
    . use M
      intro x hx
      specialize hM x hx
      rw [abs_le] at hM
      exact hM.2
    . use M
      intro x hx
      specialize hM x hx
      rw [abs_le] at hM
      exact hM.1
  . rintro ⟨⟨M₁, hM₁⟩, ⟨M₂, hM₂⟩⟩
    use max M₁ M₂
    intro x hx
    specialize hM₁ x hx
    specialize hM₂ x hx
    rw [abs_le]
    grind

theorem BddOn.iff' (f:ℝ → ℝ) (X:Set ℝ) :  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  constructor
  case mp =>
    rintro ⟨M, hM⟩
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨M, ?_⟩; rintro _ ⟨x, hx, rfl⟩; simp [Metric.mem_closedBall]; exact hM x hx
  case mpr =>
    intro h
    rw [Metric.isBounded_iff_subset_closedBall 0] at h
    obtain ⟨r, hr⟩ := h
    exact ⟨r, fun x hx => by have := hr ⟨x, hx, rfl⟩; simp at this; exact this⟩


theorem BddOn.of_bounded {f :ℝ → ℝ} {X: Set ℝ} {M:ℝ} (h: ∀ x ∈ X, |f x| ≤ M) : BddOn f X := by use M

example : Continuous (fun x:ℝ ↦ x) := continuous_id

example : ¬ BddOn (fun x:ℝ ↦ x) .univ := by
  rintro ⟨M, hM⟩
  have := hM (|M| + 1) trivial
  simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ |M| + 1)] at this
  linarith [le_abs_self M]

example : BddOn (fun x:ℝ ↦ x) (.Icc 1 2) := by
  use 2
  intro x ⟨h1, h2⟩
  simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]
  linarith

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro x hx
  exact ne_of_gt hx.1

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  rintro ⟨M, hM⟩
  have hM' : (1:ℝ) < max M 2 + 1 := by linarith [le_max_right M 2]
  set x := 1 / (max M 2 + 1)
  have hx_pos : 0 < x := by positivity
  have hx_lt : x < 1 := by rw [div_lt_one (by linarith : (0:ℝ) < max M 2 + 1)]; linarith
  have := hM x ⟨hx_pos, hx_lt⟩
  simp [x, abs_of_pos (by positivity : (0 : ℝ) < max M 2 + 1)] at this
  linarith [le_max_left M 2]

theorem why_7_6_3 {n: ℕ → ℕ} (hn: StrictMono n) (j:ℕ) : n j ≥ j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have : n (j + 1) > n j := hn (show j < j + 1 by simp)
    linarith

/-- Lemma 9.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (_h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b) ) :
  BddOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound; simp at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hunbound n).choose_spec; exact ⟨h1, h2, h3⟩
  set X := Set.Icc a b
  observe hXclosed : IsClosed X
  observe hXbounded : Bornology.IsBounded X
  have haX (n:ℕ): x n ∈ X := by simp [X]; specialize hx n; grind
  have ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := hf.continuousWithinAt hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := hf.comp (fun j ↦ haX (n j)) hconv
  apply Metric.isBounded_range_of_tendsto at hf
  rw [isBounded_def] at hf; choose M hpos hM using hf
  choose j hj using exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by grind
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

/- Definition 9.6.5.  Use the Mathlib `IsMaxOn` type. -/
#check isMaxOn_iff
#check isMinOn_iff

/-- Remark 9.6.6 -/
theorem BddAboveOn.isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMaxOn f X x₀): BddAboveOn f X := by
  rw [isMaxOn_iff] at h
  use f x₀

theorem BddBelowOn.isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMinOn f X x₀): BddBelowOn f X := by
  rw [isMinOn_iff] at h
  use -(f x₀)
  simp
  exact h

/-- Proposition 9.6.7 (Maximum principle) -/
theorem IsMaxOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  -- This proof is written to follow the structure of the original text.
  choose M hM using BddOn.of_continuous_on_compact h hf
  set E := f '' (.Icc a b)
  have hE : E ⊆ .Icc (-M) M := by rintro _ ⟨ x, hx, rfl ⟩; simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by simp [E]; contrapose! h; grind [Set.Icc_eq_empty_iff]
  set m := sSup E
  have claim1 {y:ℝ} (hy: y ∈ E) : y ≤ m := le_csSup (BddAbove.mono hE bddAbove_Icc) hy
  suffices h : ∃ xmax, xmax ∈ Set.Icc a b ∧ f xmax = m
  . obtain ⟨xmax, hmax, hmax'⟩ := h
    use xmax, hmax
    rw [isMaxOn_iff]
    intro x hx
    rw [hmax']
    specialize claim1 (Set.mem_image_of_mem f hx)
    exact claim1
  have claim2 (n:ℕ) : ∃ x ∈ Set.Icc a b, m - 1/(n+1:ℝ) < f x := by
    have : 1/(n+1:ℝ) > 0 := by positivity
    replace : m - 1/(n+1:ℝ) < sSup E := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    apply exists_lt_of_lt_csSup hnon at this
    grind
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n:ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n:ℕ) : m - 1/(n+1:ℝ) < f (x n) := (claim2 n).choose_spec.2
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ n, hn, ⟨ xmax, hmax, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨hclosed, hbounded⟩ x hx
  use xmax, hmax
  have hn_lower (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds (f xmax)) :=
    hconv.comp_of_continuous (hf.continuousWithinAt hmax) (fun j ↦ hx (n j))
  have hlower (j:ℕ) : m - 1/(j+1:ℝ) < f (x (n j)) := by
    apply lt_of_le_of_lt _ (hfx (n j)); gcongr; grind
  have hupper (j:ℕ) : f (x (n j)) ≤ m := by apply claim1; simp [Set.mem_image, E]; use x (n j), hx (n j)
  have hconvm : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds m) := by
    apply Filter.Tendsto.squeeze (g := fun j ↦ m - 1/(j+1:ℝ)) (h := fun _ ↦ m) (f := fun j ↦ f (x (n j)))
    . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub m (c:=0); simp
    . exact tendsto_const_nhds
    . intro _; grind
    exact hupper
  exact tendsto_nhds_unique hconv' hconvm

theorem IsMinOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmin ∈ Set.Icc a b, IsMinOn f (.Icc a b) xmin := by
  have ⟨xmin, hmin, hmax_neg⟩ := IsMaxOn.of_continuous_on_compact h (hf.neg)
  use xmin, hmin
  intro x hx
  have := hmax_neg hx
  simp at this
  exact this

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) 2 := by
  intro x hx
  simp at hx ⊢
  nlinarith [sq_nonneg (2 - x), sq_nonneg (2 + x)]

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) (-2) := by
  intro x hx
  simp at hx ⊢
  nlinarith [sq_nonneg (2 - x), sq_nonneg (2 + x)]

theorem sSup.of_isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMaxOn f X x₀) :
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMinOn f X x₀) :
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax := by
  choose x hx h' using IsMaxOn.of_continuous_on_compact h hf
  grind [sSup.of_isMaxOn]

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin := by
  choose x hx h' using IsMinOn.of_continuous_on_compact h hf
  grind [sInf.of_isMinOn]

/-- Exercise 9.6.1 a) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ioo 1 2) ∧ BddOn f (.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, IsMinOn f (.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀
  := by
  use fun x ↦ |x - 1.5|
  constructor
  . apply Continuous.continuousOn; continuity
  . constructor
    . use 2
      intro x hx
      simp at hx
      rw [abs_le]
      constructor
      · linarith [abs_nonneg (x - 1.5)]
      · rw [abs_le]; constructor <;> linarith
    . use 1.5
      constructor
      . norm_num
      . constructor
        . rw [isMinOn_iff]
          intro x hx
          simp at hx
          rw [abs_le]
          simp
        . push_neg
          intro x hx
          rw [isMaxOn_iff]
          push_neg
          -- is x is > 1.5, get a bigger value by moving left; if x is < 1.5, get a bigger value by moving right
          by_cases h : x < 1.5
          . use (x + 1) / 2
            constructor
            · constructor <;> [linarith [hx.1]; linarith]
            · rw [abs_of_neg (by linarith), abs_of_neg (by linarith : (x + 1) / 2 - 1.5 < 0)]
              linarith [hx.1]
          . use (x + 2) / 2
            constructor
            · constructor <;> [linarith; linarith [hx.2]]
            · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : (x + 2) / 2 - 1.5 ≥ 0)]
              linarith [hx.2]

/-- Exercise 9.6.1 b) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ici 0) ∧ BddOn f (.Ici 0) ∧
  ∃ x₀ ∈ Set.Ici 0, IsMaxOn f (.Ici 0) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀
  := by
  use fun x ↦ 1 / (x + 1)
  constructor
  . apply continuousOn_const.div (continuousOn_id.add continuousOn_const)
    intro x hx
    simp at hx ⊢
    linarith
  . constructor
    . use 1
      intro x hx
      simp at hx
      rw [abs_le]
      simp
      constructor
      . field_simp
        linarith
      . field_simp
        linarith
    . use 0
      constructor
      . simp
      . constructor
        . rw [isMaxOn_iff]
          intro x hx
          simp at hx ⊢
          field_simp
          linarith
        . push_neg
          intro x hx
          rw [isMinOn_iff]
          push_neg
          use x + 1
          constructor
          . simp at hx ⊢
            linarith
          . simp at hx
            apply div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- Exercise 9.6.1 c) -/
example : ∃ f: ℝ → ℝ, BddOn f (.Icc (-1) 1) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMinOn f (.Icc (-1) 1) x₀) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMaxOn f (.Icc (-1) 1) x₀)
  := by
  use fun x ↦ if x = -1 ∨ x = 1 then 0 else x
  constructor
  . use 1
    intro x hx
    simp
    by_cases h : x = -1 ∨ x = 1
    . by_cases h' : x = -1
      . simp [h']
      . simp [h]
    . simp [h]
      rw [abs_le]
      exact hx
  . constructor
    . push_neg
      intro x hx
      rw [isMinOn_iff]
      push_neg
      by_cases h : x = -1 ∨ x = 1
      . use -0.5
        simp [h]
        norm_num
      . use (x - 1) / 2
        simp only [Set.mem_Icc] at hx
        have hne1 : x ≠ -1 := fun e => h (Or.inl e)
        have hne2 : x ≠ 1 := fun e => h (Or.inr e)
        have hl : -1 < x := lt_of_le_of_ne hx.1 (Ne.symm hne1)
        have hr : x < 1 := lt_of_le_of_ne hx.2 hne2
        have hne : ¬((x - 1) / 2 = -1 ∨ (x - 1) / 2 = 1) := by
          rintro (e | e) <;> linarith
        constructor
        · simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
        · simp only [if_neg hne, if_neg h]; linarith
    . push_neg
      intro x hx
      rw [isMaxOn_iff]
      push_neg
      by_cases h : x = -1 ∨ x = 1
      . use 0.5
        simp [h]
        norm_num
      . use (x + 1) / 2
        simp only [Set.mem_Icc] at hx
        have hne1 : x ≠ -1 := fun e => h (Or.inl e)
        have hne2 : x ≠ 1 := fun e => h (Or.inr e)
        have hl : -1 < x := lt_of_le_of_ne hx.1 (Ne.symm hne1)
        have hr : x < 1 := lt_of_le_of_ne hx.2 hne2
        have hne : ¬((x + 1) / 2 = -1 ∨ (x + 1) / 2 = 1) := by
          rintro (e | e) <;> linarith
        constructor
        · simp only [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
        · simp only [if_neg hne, if_neg h]; linarith

/-- Exercise 9.6.1 d) -/
example : ∃ f: ℝ → ℝ, ¬ BddAboveOn f (.Icc (-1) 1) ∧ ¬ BddBelowOn f (.Icc (-1) 1) := by
  use fun x ↦ 1 / x
  push_neg
  refine ⟨fun M ↦ ?_, fun M ↦ ?_⟩
  . use 1 / (max M 2 + 1)
    have hpos : (0:ℝ) < max M 2 + 1 := by linarith [le_max_right M 2]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
      { field_simp [ne_of_gt hpos]; nlinarith [le_max_left M 2, le_max_right M 2] }
  . use -1 / (max M 2 + 1)
    have hpos : (0:ℝ) < max M 2 + 1 := by linarith [le_max_right M 2]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
      { field_simp [ne_of_gt hpos]; nlinarith [le_max_left M 2, le_max_right M 2] }

/-- Exercise 9.6.2 -/

theorem BddOn.add (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f + g) X := by sorry

theorem BddOn.sub (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f - g) X := by sorry

theorem BddOn.mul (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f * g) X := by sorry

def BddOn.div (f g : ℝ → ℝ) (X : Set ℝ) (h : ∀ x ∈ X, g x ≠ 0) (hf : BddOn f X)
    (hg: BddOn g X) : Decidable (BddOn (f / g) X) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  sorry

end Chapter9
