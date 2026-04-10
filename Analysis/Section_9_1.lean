import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Analysis.Section_6_4
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/

variable (I : Type*)

/- Definition 9.1.1 (Intervals) -/
#check Set.Icc_def
#check Set.Ico_def
#check Set.Ioc_def
#check Set.Ioo_def
#check Set.Ici_def
#check Set.Ioi_def
#check Set.Iic_def
#check Set.Iio_def

#check EReal.image_coe_Icc
#check EReal.image_coe_Ico
#check EReal.image_coe_Ioc
#check EReal.image_coe_Ioo
#check EReal.image_coe_Ici
#check EReal.image_coe_Ioi
#check EReal.image_coe_Iic
#check EReal.image_coe_Iio

/-- Example 9.1.4 -/
example {a b: EReal} (h: a > b) : Set.Icc a b = ∅ := by
  rw [Set.Icc_eq_empty]
  simp only [not_le]
  exact h

example {a b: EReal} (h: a ≥ b) : Set.Ico a b = ∅ := by
  rw [Set.Ico_eq_empty]
  simp only [not_lt]
  exact h

example {a b: EReal} (h: a ≥ b) : Set.Ioc a b = ∅ := by
  rw [Set.Ioc_eq_empty]
  simp only [not_lt]
  exact h

example {a b: EReal} (h: a ≥ b) : Set.Ioo a b = ∅ := by
  rw [Set.Ioo_eq_empty]
  simp only [not_lt]
  exact h

example {a b: EReal} (_: a = b) : Set.Icc a b = {a} := by
  subst a
  simp only [Set.Icc_self]

/-- Definition 9.1.5.  Note that a slightly different `Real.adherent` was defined in Chapter 6.4 -/
abbrev Real.adherent' (ε:ℝ) (x:ℝ) (X: Set ℝ) := ∃ y ∈ X, |x - y| ≤ ε

/-- Example 9.1.7 -/
example : (0.5:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  rw [Real.adherent']
  simp only [Set.mem_Ioo]
  use 0.9; norm_num

example : ¬ (0.1:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  rw [Real.adherent']
  simp only [Set.mem_Ioo]
  push_neg
  intro y hy
  obtain ⟨h1, h2⟩ := hy
  rw [abs_of_pos (by linarith)]
  linarith

example : (0.5:ℝ).adherent' 1.1 {1,2,3} := by
  rw [Real.adherent']
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  use 1
  norm_num

namespace Chapter9

/-- Definition 9.1.-/
abbrev AdherentPt (x:ℝ) (X:Set ℝ) := ∀ ε > (0:ℝ), ε.adherent' x X

example : AdherentPt 1 (.Ioo 0 1) := by
  intro ε hε
  rw [Real.adherent']
  simp only [Set.mem_Ioo]
  by_cases hε' : ε < 1
  . use 1 - ε
    simp
    constructor
    . constructor
      . exact hε'
      . exact hε
    . rw [le_iff_lt_or_eq]
      right
      exact abs_of_pos hε
  . simp at hε'
    use 0.5
    norm_num
    linarith

example : ¬ AdherentPt 2 (.Ioo 0 1) := by
  intro h
  obtain ⟨y, hy, hxy⟩ := h 0.5 (by norm_num)
  simp [Set.mem_Ioo] at hy
  rw [abs_of_pos (by linarith)] at hxy
  linarith

/-- Definition 9.1.10 (Closure).  Here we identify this definition with the Mathilb version. -/
theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext; simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor <;> intro h ε hε
  all_goals choose y hy hxy using h _ (half_pos hε); exact ⟨ _, hy, by rw [abs_sub_comm]; linarith ⟩

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of {name}`AdherentPt` with Mathlib's {name}`ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem subset_closure (X:Set ℝ): X ⊆ closure X := by
  intro x hx
  rw [closure_def]
  intro ε hε
  use x; simp [hx]; linarith

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_union (X Y:Set ℝ): closure (X ∪ Y) = closure X ∪ closure Y := by
  ext x
  rw [closure_def', Set.mem_union, closure_def', closure_def']
  repeat rw [AdherentPt]
  constructor
  . intro h
    by_contra
    push_neg at this
    obtain ⟨hX, hY⟩ := this
    obtain ⟨εX, hεX, h1⟩ := hX
    obtain ⟨εY, hεY, h2⟩ := hY
    have h1' := h ((min εX εY) / 2)
    rw [Real.adherent'] at h1'
    have : (min εX εY) / 2 > 0 := by positivity
    specialize h1' this
    obtain ⟨z, hz, hz'⟩ := h1'
    by_cases hzX : z ∈ X
    . specialize h1 z hzX
      rw [abs_sub_comm] at hz'
      have : (min εX εY) / 2 < εX := by
        have : min εX εY ≤ εX := by apply min_le_left
        linarith
      rw [abs_sub_comm] at h1
      linarith
    . have hzY : z ∈ Y := by
        simp only [Set.mem_union] at hz
        tauto
      specialize h2 z hzY
      have : (min εX εY) / 2 < εY := by
        have : min εX εY ≤ εY := by apply min_le_right
        linarith
      linarith
  . intro h ε hε
    rw [Real.adherent']
    rcases h with (hX | hY)
    . specialize hX ε hε
      obtain ⟨y, hy, hxy⟩ := hX
      use y; simp [hy]; linarith
    . specialize hY ε hε
      obtain ⟨y, hy, hxy⟩ := hY
      use y; simp [hy]; linarith

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_inter (X Y:Set ℝ): closure (X ∩ Y) ⊆ closure X ∩ closure Y := by
  intro x hx
  rw [closure_def', AdherentPt] at hx
  rw [Set.mem_inter_iff, closure_def', closure_def']
  constructor
  . intro ε hε
    specialize hx ε hε
    rw [Real.adherent'] at hx
    obtain ⟨z, hz, h⟩ := hx
    rw [Real.adherent']
    use z
    constructor
    . exact Set.mem_of_mem_inter_left hz
    . exact h
  . intro ε hε
    specialize hx ε hε
    rw [Real.adherent'] at hx
    obtain ⟨z, hz, h⟩ := hx
    rw [Real.adherent']
    use z
    constructor
    . exact Set.mem_of_mem_inter_right hz
    . exact h

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_subset {X Y:Set ℝ} (h: X ⊆ Y): closure X ⊆ closure Y := by
  intro x hx
  rw [closure_def', AdherentPt] at hx ⊢
  intro ε hε
  specialize hx ε hε
  rw [Real.adherent'] at hx
  obtain ⟨z, hz, h'⟩ := hx
  rw [Real.adherent']
  use z
  constructor
  . exact h hz
  . exact h'

/-- Lemma 9.1.12 -/
theorem closure_of_Ioo {a b:ℝ} (h:a < b) : closure (.Ioo a b) = .Icc a b := by
  -- This proof is written to follow the structure of the original text.
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  . intro h; contrapose! h
    obtain h' | h' := le_or_gt a x
    . specialize h h'
      use x-b, by linarith
      intro y ⟨ _, _ ⟩; observe : x-y ≤ |x-y|; linarith
    use a-x, by linarith
    intro y ⟨ _, _ ⟩; observe : -(x-y) ≤ |x-y|; linarith
  intro ⟨ h1, h2 ⟩
  by_cases ha : x = a
  . subst x
    intro ε hε
    use a + min ε (b-a)/2
    grind
  by_cases hb : x = b
  . subst x
    intro ε hε
    use b - min ε (b-a)/2
    grind
  intro ε _; use x, (by exact ⟨lt_of_le_of_ne h1 (Ne.symm ha), lt_of_le_of_ne h2 hb⟩); simp; order


/-- Exercise 9.1.5 -/
theorem closure_closed (X:Set ℝ) : IsClosed (closure X) := by
  rw [← closure_eq_iff_isClosed]
  ext x
  constructor
  . intro h
    rw [closure_def] at h
    rw [closure_def]
    intro ε hε
    specialize h (ε / 2) (by positivity)
    rw [Real.adherent'] at h ⊢
    obtain ⟨y, hy, hxy⟩ := h
    rw [closure_def] at hy
    simp at hy
    obtain ⟨z, hz, hz'⟩ := hy (ε / 2) (by positivity)
    use z; simp [hz]
    grind
  . intro h
    exact subset_closure (closure X) h

/-- Exercise 9.1.5 -/
example {X Y:Set ℝ} (hY: IsClosed Y) (hXY: X ⊆ Y) : closure X ⊆ Y := by
  intro x hx
  rw [← closure_eq_iff_isClosed] at hY
  rw [← hY]
  exact closure_subset hXY hx

/-- Exercise 9.1.6 -/
theorem closure_of_subset_closure {X Y:Set ℝ} (h: X ⊆ Y) (h' : Y ⊆ closure X): closure Y = closure X := by
  have h1 := closure_subset h
  have h2 := closure_subset h'
  have hc := closure_closed X
  rw [← closure_eq_iff_isClosed] at hc
  rw [hc] at h2
  apply subset_antisymm
  . exact h2
  . exact h1

theorem closure_of_Ioc {a b:ℝ} (h:a < b) : closure (.Ioc a b) = .Icc a b := by
  have : closure (.Ioc a b) = closure (.Ioo a b) := by
    apply closure_of_subset_closure Set.Ioo_subset_Ioc_self
    intro x ⟨hxa, hxb⟩
    rw [closure_of_Ioo h]
    exact ⟨hxa.le, hxb⟩
  rw [this, closure_of_Ioo h]

theorem closure_of_Ico {a b:ℝ} (h:a < b) : closure (.Ico a b) = .Icc a b := by
  have : closure (.Ico a b) = closure (.Ioo a b) := by
    apply closure_of_subset_closure Set.Ioo_subset_Ico_self
    intro x ⟨hxa, hxb⟩
    rw [closure_of_Ioo h]
    exact ⟨hxa, hxb.le⟩
  rw [this, closure_of_Ioo h]

theorem closure_of_Icc {a b:ℝ} (_:a ≤ b) : closure (.Icc a b) = .Icc a b := by
  ext x; constructor
  · intro hx
    rw [closure_def', AdherentPt] at hx
    simp [Set.mem_Icc]
    constructor
    · by_contra ha; push_neg at ha
      obtain ⟨y, hy, hxy⟩ := hx ((a - x) / 2) (by linarith)
      simp [Set.mem_Icc] at hy
      observe : -(x - y) ≤ |x - y|; linarith
    · by_contra hb; push_neg at hb
      obtain ⟨y, hy, hxy⟩ := hx ((x - b) / 2) (by linarith)
      simp [Set.mem_Icc] at hy
      observe : x - y ≤ |x - y|; linarith
  · intro hx; exact subset_closure _ hx

theorem closure_of_Ioi {a:ℝ} : closure (.Ioi a) = .Ici a := by
  ext x; constructor
  · intro hx
    rw [closure_def', AdherentPt] at hx
    simp [Set.mem_Ici]
    by_contra hxa; push_neg at hxa
    obtain ⟨y, hy, hxy⟩ := hx ((a - x) / 2) (by linarith)
    simp [Set.mem_Ioi] at hy
    observe : -(x - y) ≤ |x - y|; linarith
  · intro hx
    simp [Set.mem_Ici] at hx
    rw [closure_def', AdherentPt]
    intro ε hε
    rw [Real.adherent']
    by_cases hxa' : x = a
    · subst x; use a + ε / 2
      simp [Set.mem_Ioi]
      constructor
      · linarith
      · rw [abs_of_pos (by linarith)]; linarith
    · use x
      simp [Set.mem_Ioi]
      exact ⟨lt_of_le_of_ne hx (Ne.symm hxa'), by linarith⟩

theorem closure_of_Ici {a:ℝ} : closure (.Ici a) = .Ici a := by
  ext x; constructor
  · intro hx
    rw [closure_def', AdherentPt] at hx
    simp [Set.mem_Ici]
    by_contra ha; push_neg at ha
    obtain ⟨y, hy, hxy⟩ := hx ((a - x) / 2) (by linarith)
    simp [Set.mem_Ici] at hy
    observe : -(x - y) ≤ |x - y|; linarith
  · intro hx; exact subset_closure _ hx

theorem closure_of_Iio {a:ℝ} : closure (.Iio a) = .Iic a := by
  ext x; constructor
  · intro hx
    rw [closure_def', AdherentPt] at hx
    simp [Set.mem_Iic]
    by_contra hxa; push_neg at hxa
    obtain ⟨y, hy, hxy⟩ := hx ((x - a) / 2) (by linarith)
    simp [Set.mem_Iio] at hy
    observe : x - y ≤ |x - y|; linarith
  · intro hx
    simp [Set.mem_Iic] at hx
    rw [closure_def', AdherentPt]
    intro ε hε
    rw [Real.adherent']
    by_cases hxa' : x = a
    · subst x; use a - ε / 2
      simp [Set.mem_Iio]
      constructor
      · linarith
      · rw [abs_of_pos (by linarith)]; linarith
    · use x
      simp [Set.mem_Iio]
      exact ⟨lt_of_le_of_ne hx hxa', by linarith⟩

theorem closure_of_Iic {a:ℝ} : closure (.Iic a) = .Iic a := by
  ext x; constructor
  · intro hx
    rw [closure_def', AdherentPt] at hx
    simp [Set.mem_Iic]
    by_contra ha; push_neg at ha
    obtain ⟨y, hy, hxy⟩ := hx ((x - a) / 2) (by linarith)
    simp [Set.mem_Iic] at hy
    observe : x - y ≤ |x - y|; linarith
  · intro hx; exact subset_closure _ hx

theorem closure_of_R : closure (.univ: Set ℝ) = .univ := by
  have h1 := subset_closure (.univ: Set ℝ)
  have h2 : closure (.univ : Set ℝ) ⊆ .univ := Set.subset_univ _
  ext x
  constructor
  . intro h
    exact h2 h
  . intro h
    exact h1 h

/-- Helper: a set where distinct elements are ≥ 1 apart is closed. -/
private theorem closure_of_discrete {S : Set ℝ}
    (hdist : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ |a - b|) :
    closure S = S := by
  ext x
  constructor
  · intro h
    rw [closure_def'] at h
    rw [AdherentPt] at h
    have h' := h
    specialize h 0.5 (by norm_num)
    rw [Real.adherent'] at h
    obtain ⟨a, ha_mem, ha⟩ := h
    suffices x = a by subst this; exact ha_mem
    by_contra hxa
    have hpos : |x - a| > 0 := abs_pos.mpr (sub_ne_zero.mpr hxa)
    specialize h' (|x - a| / 2) (by positivity)
    rw [Real.adherent'] at h'
    obtain ⟨b, hb_mem, hb⟩ := h'
    by_cases hab : a = b
    · subst hab; linarith
    · have tri : |a - b| ≤ |x - a| + |x - b| := by
        calc |a - b| = |(x - b) - (x - a)| := by ring_nf
        _ ≤ |x - b| + |x - a| := abs_sub _ _
        _ = |x - a| + |x - b| := by ring
      linarith [hdist a ha_mem b hb_mem hab]
  · intro h; exact subset_closure S h

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_N :
  closure ((fun n:ℕ ↦ (n:ℝ)) '' .univ) = ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  apply closure_of_discrete
  simp only [Set.mem_image, Set.mem_univ, true_and]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have hne : (a:ℤ) ≠ b := by exact_mod_cast hab
  have : |(↑a:ℤ) - ↑b| ≥ 1 := Int.one_le_abs (sub_ne_zero.mpr hne)
  exact_mod_cast this

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Z :
  closure ((fun n:ℤ ↦ (n:ℝ)) '' .univ) = ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  apply closure_of_discrete
  simp only [Set.mem_image, Set.mem_univ, true_and]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have hne : (a:ℤ) = b → False := by exact_mod_cast hab
  have : |(a:ℤ) - b| ≥ 1 := Int.one_le_abs (sub_ne_zero.mpr (fun h => hne h))
  exact_mod_cast this

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Q :
  closure ((fun n:ℚ ↦ (n:ℝ)) '' .univ) = .univ := by
  ext x
  constructor
  . intro h
    simp only [Set.mem_univ]
  . intro _
    rw [closure_def']
    rw [AdherentPt]
    intro ε hε
    rw [Real.adherent']
    simp
    obtain ⟨q, hq⟩ := exists_rat_near x hε
    exact ⟨q, le_of_lt hq⟩

/-- Lemma 9.1.14 / Exercise 9.1.4-/
theorem limit_of_AdherentPt (X: Set ℝ) (x:ℝ) :
  AdherentPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X) ∧ Filter.atTop.Tendsto a (nhds x) := by
  constructor
  . intro h
    simp [AdherentPt] at h
    let a: ℕ → X := fun (a : ℕ) => by
      specialize h (1 / (a + 1)) (by positivity)
      rw [Real.adherent'] at h
      exact ⟨h.choose, h.choose_spec.1⟩
    have ha : ∀ n, |x - ↑(a n)| ≤ 1 / (↑n + 1) := by
      intro n
      have := (h (1 / (↑n + 1)) (by positivity))
      rw [Real.adherent'] at this
      exact this.choose_spec.2
    use fun n => ↑(a n)
    refine ⟨fun n => (a n).2, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    use N
    intro n hn
    specialize ha n
    rw [Real.dist_eq, abs_sub_comm]
    calc |x - ↑(a n)| ≤ 1 / (↑n + 1) := ha
    _ ≤ 1 / (↑N + 1) := by
        apply div_le_div_of_nonneg_left one_pos.le (by positivity)
        exact_mod_cast Nat.add_le_add_right hn 1
    _ < ε := hN
  . intro ⟨a, ha_mem, ha_tend⟩
    simp [AdherentPt]
    intro ε hε
    rw [Real.adherent']
    rw [Metric.tendsto_atTop] at ha_tend
    obtain ⟨N, hN⟩ := ha_tend ε hε
    use a N, ha_mem N
    specialize hN N (by linarith)
    rw [Real.dist_eq] at hN
    rw [abs_sub_comm]
    exact hN.le

theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]; use fun _ ↦ x; simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]; simp [closure_def]; rfl

/-- Examples 9.1.16 -/
theorem Icc_closed {a b:ℝ} : IsClosed (.Icc a b) := by
  rw [isClosed_def]; by_cases h : a ≤ b
  · exact closure_of_Icc h
  · push_neg at h; simp [Set.Icc_eq_empty (not_le.mpr h)]

/-- Examples 9.1.16 -/
theorem Ici_closed (a:ℝ) : IsClosed (.Ici a) := by
  rw [isClosed_def]; exact closure_of_Ici

/-- Examples 9.1.16 -/
theorem Iic_closed (a:ℝ) : IsClosed (.Iic a) := by
  rw [isClosed_def]; exact closure_of_Iic

/-- Examples 9.1.16 -/
theorem R_closed : IsClosed (.univ : Set ℝ) := by
  rw [isClosed_def]; exact closure_of_R

/-- Examples 9.1.16 -/
theorem Ico_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ico a b) := by
  rw [isClosed_def, closure_of_Ico h]
  intro h'; have : b ∈ Set.Ico a b := h' ▸ Set.right_mem_Icc.mpr h.le; simp at this

/-- Examples 9.1.16 -/
theorem Ioc_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioc a b) := by
  rw [isClosed_def, closure_of_Ioc h]
  intro h'; have : a ∈ Set.Ioc a b := h' ▸ Set.left_mem_Icc.mpr h.le; simp at this

/-- Examples 9.1.16 -/
theorem Ioo_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioo a b) := by
  rw [isClosed_def, closure_of_Ioo h]
  intro h'; have : b ∈ Set.Ioo a b := h' ▸ Set.right_mem_Icc.mpr h.le; simp at this

/-- Examples 9.1.16 -/
theorem Ioi_not_closed (a:ℝ) : ¬ IsClosed (.Ioi a) := by
  rw [isClosed_def, closure_of_Ioi]
  intro h'; have : a ∈ Set.Ioi a := h' ▸ Set.self_mem_Ici; simp at this

/-- Examples 9.1.16 -/
theorem Iio_not_closed (a:ℝ) : ¬ IsClosed (.Iio a) := by
  rw [isClosed_def, closure_of_Iio]
  intro h'; have : a ∈ Set.Iio a := h' ▸ Set.self_mem_Iic; simp at this

/-- Examples 9.1.16 -/
theorem N_closed : IsClosed ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def]; exact closure_of_N

/-- Examples 9.1.16 -/
theorem Z_closed : IsClosed ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def]; exact closure_of_Z

/-- Examples 9.1.16 -/
theorem Q_not_closed : ¬ IsClosed ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def, closure_of_Q]
  intro h; have : Real.sqrt 2 ∈ (fun n:ℚ ↦ (n:ℝ)) '' Set.univ := h ▸ Set.mem_univ _
  simp at this; exact irrational_sqrt_two this

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h _ L _ _; apply h L; rw [limit_of_AdherentPt]; solve_by_elim
  intro _ _ hx; rw [limit_of_AdherentPt] at hx; grind

/-- Definition 9.1.18 (Limit points) -/
abbrev LimitPt (x:ℝ) (X: Set ℝ) := AdherentPt x (X \ {x})

/-- Identification with Mathlib's {name}`AccPt`-/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

/-- Definition 9.1.18 (Isolated points) -/
abbrev IsolatedPt (x:ℝ) (X: Set ℝ) := x ∈ X ∧ ∃ ε>0, ∀ y ∈ X \ {x}, |x-y| > ε

/-- Example 9.1.19 -/
example : AdherentPt 3 ((.Ioo 1 2) ∪ {3}) := by
  have : 3 ∈ (Set.Ioo (1:ℝ) 2 ∪ {3}) := by simp
  exact AdherentPt.of_mem this

example : ¬ LimitPt 3 ((.Ioo 1 2) ∪ {3}) := by
  set X : Set ℝ := (Set.Ioo (1:ℝ) 2) ∪ {3} with hX
  have : closure (X \ {3}) = (.Icc 1 2) := by
    have : X \ {3} = Set.Ioo 1 2 := by
      simp only [hX, Set.union_diff_right]
      ext x; simp [Set.mem_Ioo]; intro h1 h2; linarith
    rw [this, closure_of_Ioo (by norm_num : (1:ℝ) < 2)]
  by_contra h
  rw [LimitPt] at h
  rw [← closure_def'] at h
  rw [this] at h
  rw [Set.mem_Icc] at h
  norm_num at h

example : IsolatedPt 3 ((.Ioo 1 2) ∪ {3}) := by
  rw [IsolatedPt]
  simp
  use 0.5
  norm_num
  intro y hy1 hy2 hy3
  have : |3 - y| > 1 := by grind
  linarith

/-- Remark 9.1.20 -/
theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) := by
  simp [limit_of_AdherentPt]

/-- Lemma 9.1.21 -/
theorem mem_Icc_isLimit {a b x:ℝ} (h: a < b) (hx: x ∈ Set.Icc a b) : LimitPt x (.Icc a b) := by
  -- This proof is written to follow the structure of the original text, with some slight simplifications.
  simp at hx
  rw [LimitPt.iff_limit]
  obtain hxb | hxb := le_iff_lt_or_eq.1 hx.2
  . use (fun n:ℕ ↦ (x + 1/(n+(b-x)⁻¹)))
    constructor
    . intro n; simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : n + (b - x)⁻¹ > 0 := by linarith
      have : (n+(b - x)⁻¹)⁻¹ > 0 := by positivity
      have : (b-x)⁻¹ ≤ n + (b - x)⁻¹ := by linarith
      have : (n + (b - x)⁻¹)⁻¹ ≤ b-x := by rwa [inv_le_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 (b - x)⁻¹ (by norm_num) using 2 with n; simp
  . subst x
    use (fun n:ℕ ↦ (b - 1/(n+(b-a)⁻¹)))
    constructor
    . intro n; simp
      have hba : b - a > 0 := by linarith
      have hinv : (b - a)⁻¹ > 0 := by positivity
      have hden : n + (b - a)⁻¹ > 0 := by linarith
      have hfrac : (n + (b - a)⁻¹)⁻¹ > 0 := by positivity
      have hle : (b - a)⁻¹ ≤ n + (b - a)⁻¹ := by linarith
      have hfrac_le : (n + (b - a)⁻¹)⁻¹ ≤ b - a := by rwa [inv_le_comm₀ ?_ ?_] <;> positivity
      grind
    have hlim : Filter.Tendsto (fun n:ℕ ↦ 1/((n:ℝ)+(b-a)⁻¹)) Filter.atTop (nhds 0) := by
      convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(b-a)⁻¹)) ?_ tendsto_natCast_atTop_atTop
      convert tendsto_mul_add_inv_atTop_nhds_zero 1 (b - a)⁻¹ (by norm_num) using 2 with n; simp
    have : Filter.Tendsto (fun n:ℕ ↦ b + (-(1/((n:ℝ)+(b-a)⁻¹)))) Filter.atTop (nhds (b + (-0))) :=
      hlim.neg.const_add b
    simp only [neg_zero, add_zero] at this
    exact this.congr (fun n => by ring)


private theorem LimitPt.of_subset {x:ℝ} {X Y: Set ℝ} (h: X ⊆ Y) (hx: LimitPt x X) : LimitPt x Y := by
  intro ε hε; obtain ⟨y, hy, hxy⟩ := hx ε hε
  exact ⟨y, ⟨h hy.1, hy.2⟩, hxy⟩

theorem mem_Ioo_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioo a b) : LimitPt x (.Ioo a b) := by
  rw [LimitPt.iff_limit]
  use (fun n:ℕ ↦ (x + 1/(n + 1 + (b-x)⁻¹)))
  have hbx : b - x > 0 := by linarith [hx.2]
  constructor
  . intro n; simp
    have hinv : (b - x)⁻¹ > 0 := by positivity
    have hden : (n:ℝ) + 1 + (b - x)⁻¹ > 0 := by positivity
    have hfrac : ((n:ℝ) + 1 + (b - x)⁻¹)⁻¹ > 0 := by positivity
    have : (b-x)⁻¹ < (n:ℝ) + 1 + (b - x)⁻¹ := by linarith [Nat.cast_nonneg' (α := ℝ) n]
    have : ((n:ℝ) + 1 + (b - x)⁻¹)⁻¹ < b - x := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    refine ⟨⟨by linarith [hx.1], by linarith⟩, by linarith⟩
  convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k + 1 + (b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 (1 + (b - x)⁻¹) (by norm_num) using 2 with n; simp; ring

private theorem LimitPt_Ioo_left {a b : ℝ} (h : a < b) : LimitPt a (.Ioo a b) := by
  intro ε hε
  have hm : min ε (b - a) > 0 := lt_min hε (by linarith)
  use a + (min ε (b - a)) / 2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ⟨by linarith, by linarith [min_le_right ε (b - a)]⟩
  · simp; linarith
  · rw [show a - (a + (min ε (b - a)) / 2) = -((min ε (b - a)) / 2) from by ring]
    rw [abs_neg, abs_of_pos (by linarith)]
    linarith [min_le_left ε (b - a)]

private theorem LimitPt_Ioo_right {a b : ℝ} (h : a < b) : LimitPt b (.Ioo a b) := by
  intro ε hε
  have hm : min ε (b - a) > 0 := lt_min hε (by linarith)
  use b - (min ε (b - a)) / 2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact ⟨by linarith [min_le_right ε (b - a)], by linarith⟩
  · simp; linarith
  · rw [show b - (b - (min ε (b - a)) / 2) = (min ε (b - a)) / 2 from by ring]
    rw [abs_of_pos (by linarith)]
    linarith [min_le_left ε (b - a)]

theorem mem_Ico_isLimit {a b x:ℝ} (hx: x ∈ Set.Ico a b) : LimitPt x (.Ico a b) := by
  obtain ha | rfl := lt_or_eq_of_le hx.1
  · exact LimitPt.of_subset Set.Ioo_subset_Ico_self (mem_Ioo_isLimit ⟨ha, hx.2⟩)
  · exact LimitPt.of_subset Set.Ioo_subset_Ico_self (LimitPt_Ioo_left hx.2)

theorem mem_Ioc_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioc a b) : LimitPt x (.Ioc a b) := by
  obtain hb | rfl := lt_or_eq_of_le hx.2
  · exact LimitPt.of_subset Set.Ioo_subset_Ioc_self (mem_Ioo_isLimit ⟨hx.1, hb⟩)
  · exact LimitPt.of_subset Set.Ioo_subset_Ioc_self (LimitPt_Ioo_right hx.1)

theorem mem_Ici_isLimit {a x:ℝ} (hx: x ∈ Set.Ici a) : LimitPt x (.Ici a) := by
  obtain ha | rfl := lt_or_eq_of_le (Set.mem_Ici.mp hx)
  · exact LimitPt.of_subset (Set.Ioo_subset_Ico_self.trans Set.Ico_subset_Ici_self)
      (mem_Ioo_isLimit ⟨ha, lt_add_one x⟩)
  · exact LimitPt.of_subset (Set.Ioo_subset_Ico_self.trans Set.Ico_subset_Ici_self)
      (LimitPt_Ioo_left (lt_add_one a))

theorem mem_Ioi_isLimit {a x:ℝ} (hx: x ∈ Set.Ioi a) : LimitPt x (.Ioi a) := by
  exact LimitPt.of_subset (fun y hy => Set.mem_Ioi.mpr hy.1)
    (mem_Ioo_isLimit ⟨Set.mem_Ioi.mp hx, lt_add_one x⟩)

theorem mem_Iic_isLimit {a x:ℝ} (hx: x ∈ Set.Iic a) : LimitPt x (.Iic a) := by
  obtain ha | rfl := lt_or_eq_of_le (Set.mem_Iic.mp hx)
  · exact LimitPt.of_subset (Set.Ioo_subset_Ioc_self.trans Set.Ioc_subset_Iic_self)
      (mem_Ioo_isLimit ⟨sub_one_lt x, ha⟩)
  · exact LimitPt.of_subset (Set.Ioo_subset_Ioc_self.trans Set.Ioc_subset_Iic_self)
      (LimitPt_Ioo_right (sub_one_lt x))

theorem mem_Iio_isLimit {a x:ℝ} (hx: x ∈ Set.Iio a) : LimitPt x (.Iio a) := by
  exact LimitPt.of_subset (fun y hy => Set.mem_Iio.mpr hy.2)
    (mem_Ioo_isLimit ⟨sub_one_lt x, Set.mem_Iio.mp hx⟩)

theorem mem_R_isLimit {x:ℝ} : LimitPt x (.univ) := by
  exact LimitPt.of_subset (Set.subset_univ _) (mem_Ici_isLimit (Set.mem_Ici.mpr le_rfl))

/-- Definition 9.1.22.  We use here Mathlib's {name}`Bornology.IsBounded`-/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro ⟨ C, hC ⟩; use (max C 1)
    refine ⟨ lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_ ⟩
    peel hC with x hx hC; rw [abs_le'] at hC; simp [hC.1]; linarith [le_max_left C 1]
  intro ⟨ M, hM, hXM ⟩; use M; intro x hx; specialize hXM hx; simp_all [abs_le']; linarith [hXM.1]

/-- Example 9.1.23 -/
theorem Icc_bounded (a b:ℝ) : Bornology.IsBounded (.Icc a b) := by
  rw [isBounded_def]
  use max (|a| + 1) (|b| + 1)
  constructor
  . positivity
  . intro x hx
    simp [Set.mem_Icc] at hx ⊢
    grind

/-- Example 9.1.23 -/
theorem Ici_unbounded (a: ℝ) : ¬ Bornology.IsBounded (.Ici a) := by
  rw [isBounded_def]
  intro h
  obtain ⟨M, hM, hXM⟩ := h
  have h : max a M + 1 ∈ Set.Ici a := by simp [Set.mem_Ici]; grind
  have h' := hXM h
  have : M + 1 ≤ M := by grind
  linarith

/-- Example 9.1.23 -/
theorem N_unbounded : ¬ Bornology.IsBounded ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]
  intro h
  obtain ⟨M, hM, hXM⟩ := h
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have h : (n:ℝ) ∈ (fun n:ℕ ↦ (n:ℝ)) '' .univ := by simp
  have h' := hXM h
  have : M > n := by grind
  linarith

/-- Example 9.1.23 -/
theorem Z_unbounded : ¬ Bornology.IsBounded ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  have hsub : (fun n:ℕ ↦ (n:ℝ)) '' .univ ⊆ (fun n:ℤ ↦ (n:ℝ)) '' .univ := by
    intro x ⟨n, _, hn⟩; exact ⟨↑n, trivial, hn⟩
  intro h; exact N_unbounded (h.subset hsub)

/-- Example 9.1.23 -/
theorem Q_unbounded : ¬ Bornology.IsBounded ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  have hsub : (fun n:ℤ ↦ (n:ℝ)) '' .univ ⊆ (fun n:ℚ ↦ (n:ℝ)) '' .univ := by
    intro x ⟨n, _, hn⟩; exact ⟨↑n, trivial, by simp [hn]⟩
  intro h; exact Z_unbounded (h.subset hsub)

/-- Example 9.1.23 -/
theorem R_unbounded : ¬ Bornology.IsBounded (.univ: Set ℝ) := by
  have hsub : (fun n:ℚ ↦ (n:ℝ)) '' .univ ⊆ .univ := Set.subset_univ _
  intro h; exact Q_unbounded (h.subset hsub)

/-- Theorem 9.1.24 / Exercise 9.1.13 (Heine-Borel theorem for the line)-/
theorem Heine_Borel (X: Set ℝ) :
  IsClosed X ∧ Bornology.IsBounded X ↔ ∀ a : ℕ → ℝ, (∀ n, a n ∈ X) →
  (∃ n : ℕ → ℕ, StrictMono n
    ∧ ∃ L ∈ X, Filter.atTop.Tendsto (fun j ↦ a (n j)) (nhds L)) := by
  constructor
  . intro ⟨hclosed, hbounded⟩ a ha
    have hcompact : IsCompact X := Metric.isCompact_of_isClosed_isBounded hclosed hbounded
    have hseqcompact := hcompact.isSeqCompact
    obtain ⟨L, hL, φ, hφ, hφt⟩ :=
      hseqcompact.subseq_of_frequently_in (Filter.Frequently.of_forall (fun n => ha n))
    exact ⟨φ, hφ, L, hL, hφt⟩
  . intro h1
    by_contra h2
    push_neg at h2
    by_cases hclosed : IsClosed X
    . have hbounded := h2 hclosed
      rw [isBounded_def] at hbounded; push_neg at hbounded
      have hseq : ∀ n:ℕ, ∃ x ∈ X, (n:ℝ) < |x| := by
        intro n
        have := Set.not_subset.mp (hbounded ((n:ℝ) + 1) (by positivity))
        obtain ⟨x, hx, hx'⟩ := this
        simp only [Set.mem_Icc, not_and_or, not_le] at hx'
        exact ⟨x, hx, by cases hx' with
          | inl h => linarith [neg_abs_le x]
          | inr h => linarith [le_abs_self x]⟩
      choose a ha_mem ha_big using hseq
      specialize h1 a ha_mem
      obtain ⟨m, hm_mono, L, _, hL_tend⟩ := h1
      rw [Metric.tendsto_atTop] at hL_tend
      obtain ⟨N, hN⟩ := hL_tend 1 one_pos
      set k := N + Nat.ceil (|L| + 1)
      specialize hN k (by omega)
      rw [Real.dist_eq] at hN
      have h1 : |a (m k)| ≤ |L| + 1 := by
        linarith [abs_sub_abs_le_abs_sub (a (m k)) L]
      have h2 : (m k : ℝ) < |L| + 1 := lt_of_lt_of_le (ha_big (m k)) h1
      have h3 : (k : ℝ) ≤ m k := by exact_mod_cast hm_mono.id_le k
      have h4 : (Nat.ceil (|L| + 1) : ℝ) ≥ |L| + 1 := Nat.le_ceil _
      have h5 : (N : ℝ) ≥ 0 := Nat.cast_nonneg N
      have h6 : (k : ℝ) = N + Nat.ceil (|L| + 1) := by simp [k]
      linarith
    . rw [isClosed_iff_limits_mem] at hclosed
      push_neg at hclosed
      obtain ⟨a, L, ha, hL⟩ := hclosed
      specialize h1 a ha
      obtain ⟨n, hn_mono, L', hL'_mem, hL'_tend⟩ := h1
      obtain ⟨hL_tend, hL_not⟩ := hL
      have hsub_tend : Filter.Tendsto (fun j ↦ a (n j)) Filter.atTop (nhds L) :=
        hL_tend.comp hn_mono.tendsto_atTop
      have : L' = L := tendsto_nhds_unique hL'_tend hsub_tend
      subst this; exact hL_not hL'_mem

/-- Exercise 9.1.3 -/
example : ∃ (X Y:Set ℝ), closure (X ∩ Y) ≠ closure X ∩ closure Y := by
  use Set.Ioo 0 1, Set.Ioo 1 2
  have hc1 : closure (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := by simp
  have hc2 : closure (Set.Ioo (1:ℝ) 2) = Set.Icc 1 2 := by simp
  have hi : Set.Ioo (0:ℝ) 1 ∩ Set.Ioo 1 2 = ∅ := by
    ext x
    simp
    intro h1 h2 h3
    linarith
  rw [hi, hc1, hc2]
  simp

/-- Exercise 9.1.7 -/

lemma closed_union(X Y: Set ℝ) (hX: IsClosed X) (hY: IsClosed Y) : IsClosed (X ∪ Y) := by
  rw [isClosed_def] at hX hY ⊢
  rw [closure_union, hX, hY]

example {n:ℕ} (X: Fin n → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋃ i, X i) := by
  induction' n with n ih
  . simp
  . have h := hX (⟨n, by omega⟩)
    have h' := ih (fun i => X ⟨i.1, by omega⟩) (fun i => hX ⟨i.1, by omega⟩)
    have hu : ⋃ i, X i = (⋃ i:Fin n, X ⟨i.1, by omega⟩) ∪ X ⟨n, by omega⟩ := by
      rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]; congr
    rw [hu]
    exact closed_union _ _ h' h

/-- Exercise 9.1.8 -/
example {I:Type} (X: I → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋂ i, X i) := by
  rw [isClosed_def]
  ext x
  constructor
  . intro h
    rw [Set.mem_iInter]
    intro i
    specialize hX i
    rw [closure_def'] at h
    rw [AdherentPt] at h
    simp [Real.adherent'] at h
    have h' : AdherentPt x (X i) := by
      intro ε hε
      specialize h ε hε
      obtain ⟨y, hy, hxy⟩ := h
      use y, hy i, hxy
    rw [isClosed_def] at hX
    rw [← closure_def'] at h'
    rwa [hX] at h'
  . intro h
    exact subset_closure _ h

/-- Exercise 9.1.9 -/
theorem adherent_limit_or_iso {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  by_cases h : x ∈ X
  . by_contra h'
    push_neg at h'
    obtain ⟨h1, h2⟩ := h'
    rw [LimitPt, AdherentPt] at h1
    rw [IsolatedPt] at h2
    push_neg at h1 h2
    specialize h2 h
    obtain ⟨ε, hε, h1⟩ := h1
    specialize h2 ε hε
    obtain ⟨y, hy, hy'⟩ := h2
    specialize h1 y hy
    linarith
  . left
    rw [LimitPt]
    have : X \ {x} = X := by simp [h]
    rwa [this]

/-- Exercise 9.1.9 -/
theorem adherent_not_limit_and_isolated {X:Set ℝ} {x:ℝ} : ¬ (LimitPt x X ∧ IsolatedPt x X) := by
  push_neg
  intro h
  rw [LimitPt, AdherentPt] at h
  rw [IsolatedPt]
  push_neg
  intro y ε hε
  specialize h ε hε
  exact h

/-- Exercise 9.1.10 -/
example {X:Set ℝ} (hX: X ≠ ∅) : Bornology.IsBounded X ↔
  sSup ((fun x:ℝ ↦ (x:EReal)) '' X) < ⊤ ∧
  sInf ((fun x:ℝ ↦ (x:EReal)) '' X) > ⊥ := by
  constructor
  . intro h
    rw [isBounded_def] at h
    obtain ⟨M, hM, hXM⟩ := h
    have h1 : sSup ((fun x:ℝ ↦ (x:EReal)) '' X) ≤ (M:EReal) := by
      apply sSup_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      specialize hXM hx
      simp [Set.mem_Icc] at hXM
      have : (x:EReal) ≤ (M:EReal) := by simp [hXM]
      exact this
    have h2 : sInf ((fun x:ℝ ↦ (x:EReal)) '' X) ≥ (-M:EReal) := by
      apply le_sInf
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      specialize hXM hx
      simp [Set.mem_Icc] at hXM
      have : (-M:EReal) ≤ (x:EReal) := by exact_mod_cast hXM.1
      exact this
    constructor
    . have : (M:EReal) < ⊤ := by simp only [EReal.coe_lt_top]
      exact lt_of_le_of_lt h1 this
    . have : ⊥ < (-M:EReal) := by exact_mod_cast EReal.bot_lt_coe (x := -M)
      exact lt_of_lt_of_le this h2
  . intro ⟨h1, h2⟩
    rw [isBounded_def]
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hX
    have hStop : sSup ((fun x : ℝ ↦ (x : EReal)) '' X) ≠ ⊤ := ne_of_lt h1
    have hIbot : sInf ((fun x : ℝ ↦ (x : EReal)) '' X) ≠ ⊥ := ne_of_gt h2
    have hSbot : sSup ((fun x : ℝ ↦ (x : EReal)) '' X) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe x₀) (le_sSup ⟨x₀, hx₀, rfl⟩))
    have hItop : sInf ((fun x : ℝ ↦ (x : EReal)) '' X) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (sInf_le ⟨x₀, hx₀, rfl⟩) (EReal.coe_lt_top x₀))
    set s := (sSup ((fun x : ℝ ↦ (x : EReal)) '' X)).toReal
    set i := (sInf ((fun x : ℝ ↦ (x : EReal)) '' X)).toReal
    use max |s| |i| + 1
    refine ⟨by positivity, fun x hxX ↦ ?_⟩
    have hxS : (x : EReal) ≤ ↑s := by
      rw [EReal.coe_toReal hStop hSbot]
      exact le_sSup ⟨x, hxX, rfl⟩
    have hIx : (↑i : EReal) ≤ (x : EReal) := by
      rw [EReal.coe_toReal hItop hIbot]
      exact sInf_le ⟨x, hxX, rfl⟩
    rw [EReal.coe_le_coe_iff] at hxS hIx
    rw [Set.mem_Icc]
    constructor
    · linarith [neg_abs_le i, le_max_right |s| |i|]
    · linarith [le_abs_self s, le_max_left |s| |i|]

/-- Exercise 9.1.11 -/
example {X:Set ℝ} (hX: Bornology.IsBounded X) : Bornology.IsBounded (closure X) := by
  rw [isBounded_def] at hX ⊢
  obtain ⟨M, hM, hXM⟩ := hX
  use (M + 1), by linarith
  intro x hx
  rw [closure_def'] at hx
  rw [AdherentPt] at hx
  specialize hx 0.5 (by norm_num)
  rw [Real.adherent'] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hyM := hXM hy
  rw [Set.mem_Icc] at hyM ⊢
  rw [abs_le] at hxy
  constructor <;> linarith

/-- Exercise 9.1.12.  As a followup: prove or disprove this exercise with {lean}`[Fintype I]` removed. -/
lemma bounded_union (X Y: Set ℝ) (hX: Bornology.IsBounded X) (hY: Bornology.IsBounded Y) : Bornology.IsBounded (X ∪ Y) := by
  rw [isBounded_def] at hX hY ⊢
  obtain ⟨MX, hMX, hXMX⟩ := hX
  obtain ⟨MY, hMY, hYMY⟩ := hY
  use max MX MY + 1
  constructor
  . positivity
  . intro x hx
    simp only [Set.mem_union] at hx
    cases hx with
    | inl hx =>
      specialize hXMX hx
      simp [Set.mem_Icc] at hXMX
      grind
    | inr hy =>
      specialize hYMY hy
      simp [Set.mem_Icc] at hYMY
      grind

example {I:Type} [Fintype I] (X: I → Set ℝ) (hX: ∀ i, Bornology.IsBounded (X i)) :
  Bornology.IsBounded (⋃ i, X i) := by
  classical
  suffices h : ∀ (S : Finset I), Bornology.IsBounded (⋃ i ∈ S, X i) by
    convert h Finset.univ using 1; simp
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.set_biUnion_insert]
    exact bounded_union _ _ (hX a) ih

example : ∃ (I:Type) (X: I → Set ℝ), (∀ i, Bornology.IsBounded (X i)) ∧ ¬ Bornology.IsBounded (⋃ i, X i) := by
  use ℕ, fun (a: ℕ) ↦ Set.Icc (-a:ℝ)  a
  constructor
  . intro i
    exact Icc_bounded (-i) i
  . intro h
    have hall: (⋃ (i:ℕ), Set.Icc (-i:ℝ) i) = .univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      use n
      constructor
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]
    rw [hall] at h
    exact R_unbounded h

/-- Exercise 9.1.14 -/
example (I: Finset ℝ) : IsClosed (I:Set ℝ) ∧ Bornology.IsBounded (I:Set ℝ) := by
  constructor
  . rw [isClosed_def]
    ext x
    constructor
    . intro h
      rw [closure_def'] at h
      have := adherent_limit_or_iso h
      suffices hlim : ¬ LimitPt x I by tauto
      by_contra hl
      rw [LimitPt] at hl
      rw [AdherentPt] at hl
      by_cases hempty : (I \ {x}).Nonempty
      · set d := (I \ {x}).inf' hempty (fun y ↦ |x - y|)
        have hd_pos : 0 < d := by
          rw [Finset.lt_inf'_iff hempty]
          intro y hy
          have hne := (Finset.mem_sdiff.mp hy).2
          simp at hne
          exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
        obtain ⟨y, hy, hxy⟩ := hl (d / 2) (by linarith)
        have hym : y ∈ I \ {x} := by
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hy ⊢
          exact hy
        linarith [Finset.inf'_le (fun y ↦ |x - y|) hym]
      · rw [Finset.not_nonempty_iff_eq_empty] at hempty
        obtain ⟨y, hy, _⟩ := hl 1 one_pos
        have hym : y ∈ I \ {x} := by
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hy ⊢
          exact hy
        simp [hempty] at hym
    . intro h
      exact subset_closure _ h
  . rw [isBounded_def]
    by_cases hempty : I.Nonempty
    · use I.sup' hempty (fun y ↦ |y|) + 1
      constructor
      · linarith [Finset.le_sup' (fun y : ℝ ↦ |y|) hempty.choose_spec, abs_nonneg hempty.choose]
      · intro y hy
        rw [Set.mem_Icc]
        have hle := Finset.le_sup' (fun y : ℝ ↦ |y|) hy
        constructor <;> linarith [neg_abs_le y, le_abs_self y]
    · rw [Finset.not_nonempty_iff_eq_empty] at hempty
      use 1, one_pos
      simp [hempty]

/-- Exercise 9.1.15 -/
example {E:Set ℝ} (hE: Bornology.IsBounded E) (hnon: E.Nonempty): AdherentPt (sSup E) E ∧ AdherentPt (sSup E) Eᶜ := by
  constructor
  . rw [AdherentPt]
    intro ε hε
    rw [Real.adherent']
    by_contra h
    push_neg at h
    have h1 : ∀ x ∈ E, x ≤ sSup E - ε := by
      intro x hx
      specialize h x hx
      have hle : x ≤ sSup E := le_csSup hE.bddAbove hx
      have hab : |sSup E - x| = sSup E - x := abs_of_nonneg (by linarith)
      linarith
    linarith [csSup_le hnon h1]
  . rw [AdherentPt]
    intro ε hε
    rw [Real.adherent']
    by_contra h
    push_neg at h
    have hnotin : sSup E + ε / 2 ∉ Eᶜ := by
      intro hmem
      have h1 := h _ hmem
      have : |sSup E - (sSup E + ε / 2)| = ε / 2 := by
        rw [show sSup E - (sSup E + ε / 2) = -(ε / 2) from by ring]
        rw [abs_neg, abs_of_pos (by linarith)]
      linarith
    have hin : sSup E + ε / 2 ∈ E := by
      by_contra hmem
      exact hnotin (Set.mem_compl hmem)
    linarith [le_csSup hE.bddAbove hin]

end Chapter9
