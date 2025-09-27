import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases h: x = 0
  . left; exact h
  right
  obtain ⟨a , ha, rfl⟩ := eq_lim x
  rw [← Real.LIM.zero] at h
  rw [LIM_eq_LIM ha (Sequence.IsCauchy.const 0)] at h
  rw [Sequence.equiv_def] at h
  simp [Rat.eventuallyClose_iff] at h
  obtain ⟨ε, hε, h⟩ := h
  have ha_copy := ha
  rw [Sequence.IsCauchy.coe] at ha
  specialize ha (ε / 2) (by positivity)
  obtain ⟨N, ha⟩ := ha
  simp [Section_4_3.dist] at ha
  specialize h N
  obtain ⟨j, hj, h⟩ := h
  by_cases hj': 0 ≤ a j
  . simp [abs_of_nonneg hj'] at h
    left
    rw [isPos_def]

    let a' := (fun n ↦ if n < N then ε / 2 else a n)
    have ha'_equiv : Sequence.Equiv a a' := by
      rw [Sequence.equiv_def]
      intro ε' hε'
      rw [Rat.eventuallyClose_iff]
      use N
      intro n hn
      have hn': ¬ n < N := by linarith
      unfold a'
      simp [hn']
      exact le_of_lt hε'
    have ha' : (a':Sequence).IsCauchy := by
      rw [← Sequence.isCauchy_of_equiv ha'_equiv]
      exact ha_copy
    specialize ha j hj

    use a'
    constructor
    . rw [boundedAwayPos_def]
      use (ε / 2), (by positivity)
      intro n
      by_cases hn: n < N
      . unfold a'
        simp [hn]
      . simp at hn
        specialize ha n hn
        simp
        calc
          (ε / 2) = ε - (ε / 2) := by ring
          _ ≤ ε - |a j - a n| := by gcongr
          _ ≤ a j - |a j - a n| := by gcongr
          _ = |a j| - |a j - a n| := by
            simp
            rw [abs_of_nonneg hj']
          _ ≤ |(|a j| - |a j - a n|)| := by
            exact le_abs_self _
          _ ≤ |a j - (a j - a n)| := by
            exact abs_abs_sub_abs_le _ _
          _ = |a n| := by ring_nf
        have : a' n = a n := by
          unfold a'
          simp [hn]
        rw [this]
        by_cases han: 0 ≤ a n
        . rw [abs_of_nonneg han]
        . have : a j - a n > 0 := by linarith
          rw [abs_of_nonneg (le_of_lt this)] at ha
          linarith
    . constructor
      . exact ha'
      . apply (Real.LIM_eq_LIM ha_copy ha').mpr
        exact ha'_equiv
  -- some copy/paste by inequality proofs reworked
  . simp at hj'
    have h': a j < -ε := by
      rw [abs_of_neg hj'] at h
      linarith
    right
    rw [isNeg_def]
    -- refactor with a theorem generalizing this construction
    let a' := (fun n ↦ if n < N then -(ε / 2) else a n)
    have ha'_equiv : Sequence.Equiv a a' := by
      rw [Sequence.equiv_def]
      intro ε' hε'
      rw [Rat.eventuallyClose_iff]
      use N
      intro n hn
      have hn': ¬ n < N := by linarith
      unfold a'
      simp [hn']
      exact le_of_lt hε'
    have ha' : (a':Sequence).IsCauchy := by
      rw [← Sequence.isCauchy_of_equiv ha'_equiv]
      exact ha_copy
    specialize ha j hj

    use a'
    constructor
    . rw [boundedAwayNeg_def]
      use (ε / 2), (by positivity)
      intro n
      by_cases hn: n < N
      . unfold a'
        simp [hn]
      . simp at hn
        specialize ha n hn
        suffices - (ε / 2) ≥ a n by
          unfold a'
          have : ¬ n < N := by linarith
          simp [this]
          linarith
        by_cases hnj: a j ≤ a n
        . have : |a j - a n| = a n - a j := by
            rw [abs_sub_comm]
            rw [abs_of_nonneg (by linarith)]
          rw [this] at ha
          calc
            _ = -ε + (ε / 2) := by ring_nf
            _ ≥ a j + (ε / 2) := by linarith
            _ ≥ a j + a n - a j := by linarith
            _ ≥ a n := by linarith
        . apply le_of_lt
          calc
            - (ε / 2) ≥ - ε := by linarith
            _ ≥ a j := by linarith
            _ > a n := by
              simp at hnj
              exact hnj
    . constructor
      . exact ha'
      . apply (Real.LIM_eq_LIM ha_copy ha').mpr
        exact ha'_equiv

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  push_neg
  intro h
  rw [isPos_def]
  subst x
  push_neg
  intro a hb hc
  symm
  apply lim_of_boundedAwayZero
  . exact BoundedAwayZero.boundedAwayPos hb
  . exact hc

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  push_neg
  intro h
  rw [isNeg_def]
  subst x
  push_neg
  intro a hb hc
  symm
  apply lim_of_boundedAwayZero
  . exact BoundedAwayZero.boundedAwayNeg hb
  . exact hc

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rw [isNeg_def, isPos_def]
  push_neg
  intro h
  obtain ⟨ a, ha_pos, ha_cauchy, rfl ⟩ := h
  intro a' ha' ha'c
  intro hl
  rw [LIM_eq_LIM ha_cauchy ha'c] at hl
  rw [Sequence.equiv_def] at hl
  rw [boundedAwayPos_def] at ha_pos
  rw [boundedAwayNeg_def] at ha'
  obtain ⟨ε, hε, hn⟩ := ha_pos
  obtain ⟨ε', hε', hn'⟩ := ha'
  specialize hl ε hε
  rw [Rat.eventuallyClose_iff] at hl
  obtain ⟨N, hl⟩ := hl
  specialize hn N
  specialize hn' N
  specialize hl N (by rfl)
  have : a N - a' N ≥ 0 := by
    simp
    apply le_of_lt
    calc
      _ ≤ -ε' := hn'
      _ < 0 := by linarith
      _ < ε := by linarith
      _ ≤ a N := by linarith
  rw [abs_of_nonneg this] at hl
  linarith

lemma BoundedAwayZero.boundedAwayNeg_of_neg_pos {a:ℕ → ℚ} (ha: BoundedAwayPos a) :
  BoundedAwayNeg (fun n ↦ - a n) := by
  rw [boundedAwayPos_def] at ha
  rw [boundedAwayNeg_def]
  obtain ⟨ c, hc, h ⟩ := ha
  use c, hc
  intro n
  specialize h n
  linarith


lemma BoundedAwayZero.boundedAwayPos_of_neg_neg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) :
  BoundedAwayPos (fun n ↦ - a n) := by
  -- same proof as above, how can it be refactored?
  rw [boundedAwayNeg_def] at ha
  rw [boundedAwayPos_def]
  obtain ⟨ c, hc, h ⟩ := ha
  use c, hc
  intro n
  specialize h n
  linarith

lemma Sequence.IsCauchy_neg {a : ℕ → ℚ} (ha : IsCauchy a) : IsCauchy (fun n ↦ - a n) := by
  rw [Sequence.IsCauchy.coe] at ha ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro j hj k hk
  specialize hN j hj k hk
  rw [Section_4_3.dist] at hN ⊢
  rw [abs_sub_comm]
  simp
  rw [add_comm]
  rw [_root_.sub_eq_add_neg] at hN
  exact hN

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  . intro h
    rw [isNeg_def] at h
    rw [isPos_def]
    obtain ⟨a, ha, ha', hlim⟩ := h
    use fun n ↦ - a n
    constructor
    . exact BoundedAwayZero.boundedAwayPos_of_neg_neg ha
    . constructor
      . exact Sequence.IsCauchy_neg ha'
      . subst x
        rw [neg_LIM a ha']
        rfl
  . intro h
    rw [isPos_def] at h
    rw [isNeg_def]
    obtain ⟨a, ha, ha', hlim⟩ := h
    use fun n ↦ - a n
    constructor
    . exact BoundedAwayZero.boundedAwayNeg_of_neg_pos ha
    . constructor
      . exact Sequence.IsCauchy_neg ha'
      . have : x = - LIM a := by
          rw [← hlim]
          ring
        subst x
        rw [neg_LIM a ha']
        rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨a, ha, ha', hlim⟩ := hx
  obtain ⟨b, hb, hb', hlim'⟩ := hy
  use fun n ↦ a n + b n
  constructor
  . rw [boundedAwayPos_def] at ha hb ⊢
    obtain ⟨c, hc, ha⟩ := ha
    obtain ⟨d, hd, hb⟩ := hb
    use c + d, by linarith
    intro n
    specialize ha n
    specialize hb n
    linarith
  . constructor
    . exact Sequence.IsCauchy.add  ha' hb'
    . subst x
      subst y
      rw [LIM_add ha' hb']
      rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨a, ha, ha', hlim⟩ := hx
  obtain ⟨b, hb, hb', hlim'⟩ := hy
  use fun n ↦ a n * b n
  constructor
  . rw [boundedAwayPos_def] at ha hb ⊢
    obtain ⟨c, hc, ha⟩ := ha
    obtain ⟨d, hd, hb⟩ := hb
    use c * d, by positivity
    intro n
    specialize ha n
    specialize hb n
    exact mul_le_mul ha hb (by linarith) (by linarith)
  . constructor
    . exact Sequence.IsCauchy.mul ha' hb'
    . subst x
      subst y
      rw [LIM_mul ha' hb']
      rfl

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  . intro h
    rw [isPos_def] at h
    obtain ⟨a, ha, ha', hlim⟩ := h
    rw [ratCast_def] at hlim
    rw [LIM_eq_LIM (Sequence.IsCauchy.const q) ha'] at hlim
    rw [boundedAwayPos_def] at ha
    rw [Sequence.equiv_def] at hlim
    obtain ⟨c, hc, ha⟩ := ha
    specialize hlim (c / 2) (by positivity)
    rw [Rat.eventuallyClose_iff] at hlim
    obtain ⟨N, hlim⟩ := hlim
    specialize hlim N (by linarith)
    specialize ha N
    have := sub_le_of_abs_sub_le_left hlim
    linarith
  . intro h
    rw [isPos_def]
    use (fun _:ℕ ↦ q)
    constructor
    . rw [boundedAwayPos_def]
      use q, h
      intro n
      rfl
    . constructor
      . exact Sequence.IsCauchy.const q
      . rw [ratCast_def]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  constructor
  . intro h
    rw [isNeg_def] at h
    obtain ⟨a, ha, ha', hlim⟩ := h
    rw [ratCast_def] at hlim
    rw [LIM_eq_LIM (Sequence.IsCauchy.const q) ha'] at hlim
    rw [boundedAwayNeg_def] at ha
    rw [Sequence.equiv_def] at hlim
    obtain ⟨c, hc, ha⟩ := ha
    specialize hlim (c / 2) (by positivity)
    rw [Rat.eventuallyClose_iff] at hlim
    obtain ⟨N, hlim⟩ := hlim
    specialize hlim N (by linarith)
    specialize ha N
    have := sub_le_of_abs_sub_le_right hlim
    linarith
  . intro h
    rw [isNeg_def]
    use (fun _:ℕ ↦ q)
    constructor
    . rw [boundedAwayNeg_def]
      use -q, (by linarith)
      intro n
      simp
    . constructor
      . exact Sequence.IsCauchy.const q
      . rw [ratCast_def]

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

theorem Real.abs_nonneg (x:Real): (abs x).IsPos ∨ (abs x) = 0 := by
  by_cases hx: x.IsPos
  . rw [abs_of_pos x hx]
    left
    exact hx
  . have := trichotomous x
    simp [hx] at this
    rcases this with (h | h)
    . subst x
      right
      simp
    . left
      rw [← neg_iff_pos_of_neg] at h
      rw [abs_of_neg x h]
      rw [← neg_iff_pos_of_neg]
      exact h

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  simp only [gt_iff_lt]
  rw [lt_iff]
  rw [neg_iff_pos_of_neg]
  simp only [neg_sub]

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp only [ge_iff_le, gt_iff_lt]
  rw [Real.le_iff]
  tauto

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [lt_iff]
  have : q < q' ↔ q - q' < 0 := by exact Iff.symm sub_neg
  rw [this]
  have : (q:Real) - (q':Real) = (((q - q') : ℚ): Real) := by exact ratCast_sub q q'
  rw [this]
  exact Iff.symm (neg_of_coe (q - q'))

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  rw [gt_iff, sub_zero]

theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  rw [lt_iff, sub_zero]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  have := trichotomous (x - y)
  rcases this with (h | h | h)
  . right
    right
    have : x - y = 0 ↔ x = y := by exact sub_eq_zero
    rwa [← this]
  . left
    rwa [gt_iff]
  . right
    left
    rwa [lt_iff]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]
  exact not_pos_neg (x - y)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, ← sub_eq_zero]
  have := not_zero_pos (x - y)
  contrapose! this
  exact this.symm

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, ← sub_eq_zero]
  have := not_zero_neg (x - y)
  contrapose! this
  exact this.symm

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ (y - x).IsPos := by
  rw [lt_iff]
  rw [neg_iff_pos_of_neg]
  simp only [neg_sub]

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [antisymm] at hxy hyz ⊢
  have := pos_add hxy hyz
  simp only [sub_add_sub_cancel'] at this
  exact this

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [antisymm] at hxy ⊢
  simp only [add_sub_add_right_eq_sub]
  exact hxy

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [le_iff] at hxy ⊢
  cases' hxy with hxy hxy
  . left
    have := mul_lt_mul_right hxy hz
    rw [mul_comm, mul_comm y] at this
    exact this
  . right
    subst x
    rfl

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  rw [neg_iff_pos_of_neg] at hy ⊢
  have := pos_mul hx hy
  simp only [mul_neg] at this
  exact this

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by
    intro x
    right
    rfl

  le_trans := by
    intro a b c hab hac
    rw [le_iff] at hab hac ⊢
    cases' hab with hab hab
    . cases' hac with hac hac
      . left
        exact lt_trans hab hac
      . subst c
        left
        exact hab
    . subst b
      exact hac

  lt_iff_le_not_ge := by
    intro a b
    simp [le_iff]
    push_neg
    constructor
    . intro h
      constructor
      . left; exact h
      . constructor
        . have := not_gt_and_lt a b
          tauto
        . have := not_lt_and_eq a b
          tauto
    . intro h
      have := trichotomous' a b
      tauto

  le_antisymm := by
    intro a b hab hba
    rw [le_iff] at hab hba
    cases' hab with hab hab
    . cases' hba with hba hba
      . have := lt_trans hab hba
        exfalso
        rw [lt_iff] at this
        simp only [sub_self, neg_iff_pos_of_neg, neg_zero] at this
        exact not_zero_pos 0 ⟨rfl, this⟩
      . exact hba.symm
    . exact hab

  le_total := by
    intro a b
    rw [le_iff] at ⊢
    have := trichotomous' a b
    tauto

  toDecidableLE := Classical.decRel _

#check |(3:Real)|

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [show (x/y) = x * y⁻¹ from rfl]
  exact pos_mul hx (inv_of_pos hy)

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b hab c
    rw [le_iff] at hab ⊢
    cases' hab with hab hab
    . left
      rw [antisymm] at hab ⊢
      simpa only [add_sub_add_left_eq_sub]
    . subst a
      right
      rfl

  add_le_add_right := by
    intro a b hab c
    rw [le_iff] at hab ⊢
    cases' hab with hab hab
    . left
      rw [antisymm] at hab ⊢
      simpa only [add_sub_add_right_eq_sub]
    . subst a
      right
      rfl

  mul_lt_mul_of_pos_left := by
    intro a b c hab hc
    rw [antisymm] at hab ⊢
    rw [show (c * b - c * a) = c * (b - a) by ring]
    have : c > 0 := hc
    rw [← (isPos_iff c)] at this
    exact pos_mul this hab

  mul_lt_mul_of_pos_right := by
    intro a b c hab hc
    rw [antisymm] at hab ⊢
    rw [show (b * c - a * c) = (b - a) * c by ring]
    have : c > 0 := hc
    rw [← (isPos_iff c)] at this
    exact pos_mul hab this

  le_of_add_le_add_left := by
    intro a b c hab
    rw [le_iff] at hab ⊢
    cases' hab with hab hab
    . left
      rw [antisymm] at hab ⊢
      simp only [add_sub_add_left_eq_sub] at hab
      exact hab
    . simp only [add_right_inj] at hab
      subst b
      right
      rfl

  zero_le_one := by
    left
    rw [lt_iff]
    simp only [zero_sub, neg_iff_pos_of_neg, neg_neg]
    exact (pos_of_coe ↑1).mpr rfl

lemma Real.abs_eq_abs (x: Real): |x| = x.abs := by
  rcases trichotomous x with h | h | h
  . subst x
    simp only [abs_zero, abs_of_zero]
  . have : 0 < x := by exact (isPos_iff x).mp h
    simp only [h, abs_of_pos, abs_eq_self, ge_iff_le]
    exact le_of_lt this
  . have : x < 0 := by exact (isNeg_iff x).mp h
    simp only [h, abs_of_neg, abs_eq_neg_self, ge_iff_le]
    exact le_of_lt this

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

lemma add_inv_le_ε{ε: ℚ} (hε: 0 < ε) {k N: ℕ} (hn: N ≤ k) (hnε: (N:ℚ) > 2 / ε) : ((k:ℚ) + 1)⁻¹ < ε / 2 := by
  calc
    _ ≤ ((N:ℚ) + 1)⁻¹ := by gcongr
    _ < (2 / ε + 1)⁻¹ := by gcongr
    _ ≤ _ := by
      field_simp
      rw [div_le_div_iff₀]
      . gcongr
        linarith
      . positivity
      . norm_num

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n < b n)
    ∧ ¬ LIM a < LIM b := by
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  have hc1 : ((fun (n:ℕ) ↦ 1 - 1/(n + 1:ℚ)) : Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    obtain ⟨ N, hN : N > 2/ε ⟩ := exists_nat_gt (2 / ε)
    use N
    intro j hj k hk
    rw [Section_4_3.dist]
    simp
    have hk : ((k:ℚ) + 1)⁻¹ < ε / 2 := add_inv_le_ε hε hk hN
    have hk' : 0 ≤ ((k:ℚ) + 1)⁻¹ := by positivity
    have hj : ((j:ℚ) + 1)⁻¹ < ε / 2 := add_inv_le_ε hε hj hN
    have hj' : 0 ≤ ((j:ℚ) + 1)⁻¹ := by positivity
    calc
      _ ≤ |((k:ℚ) + 1)⁻¹| + |((j:ℚ) + 1)⁻¹| := by
        exact abs_sub _ _
      _ = ((k:ℚ) + 1)⁻¹ + ((j:ℚ) + 1)⁻¹ := by
        rw [abs_of_nonneg hk', abs_of_nonneg hj']
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  -- copy/paste from hc1 with one rw [abs_sub_comm injected
  have hc2 : ((fun (n:ℕ) ↦ 1 + 1/(n + 1:ℚ)) : Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    obtain ⟨ N, hN : N > 2/ε ⟩ := exists_nat_gt (2 / ε)
    use N
    intro j hj k hk
    rw [Section_4_3.dist]
    simp
    have hk : ((k:ℚ) + 1)⁻¹ < ε / 2 := add_inv_le_ε hε hk hN
    have hk' : 0 ≤ ((k:ℚ) + 1)⁻¹ := by positivity
    have hj : ((j:ℚ) + 1)⁻¹ < ε / 2 := add_inv_le_ε hε hj hN
    have hj' : 0 ≤ ((j:ℚ) + 1)⁻¹ := by positivity
    rw [abs_sub_comm]
    calc
      _ ≤ |((k:ℚ) + 1)⁻¹| + |((j:ℚ) + 1)⁻¹| := by
        exact abs_sub _ _
      _ = ((k:ℚ) + 1)⁻¹ + ((j:ℚ) + 1)⁻¹ := by
        rw [abs_of_nonneg hk', abs_of_nonneg hj']
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

  constructor
  . exact hc1
  . constructor
    . exact hc2
    . constructor
      . intro n
        have : 1 - 1/(n + 1:ℚ) < 1 := by
          simp
          exact Nat.cast_add_one_pos n
        have : 1 < 1 + 1/(n + 1:ℚ) := by
          simp
          exact Nat.cast_add_one_pos n
        linarith
      . rw [not_lt]
        right
        rw [LIM_eq_LIM hc2 hc1]
        rw [Sequence.equiv_def]
        intro ε hε
        rw [Rat.eventuallyClose_iff]
        obtain ⟨ N, hN : N > 2/ε ⟩ := exists_nat_gt (2 / ε)
        use N
        intro n hn
        field_simp
        ring_nf
        rw [abs_of_nonneg (by positivity)]
        calc
          _ ≤ 1 / (1 + (N:ℚ)) * 2 := by
            gcongr
            field_simp
            norm_cast
            apply one_div_le_one_div_of_le
            . positivity
            . simp
              exact hn
          _ ≤ 1 / (1 + (2 / ε)) * 2 := by
            gcongr
          _ ≤ _ := by
            have : ε + 2 > 0 := by positivity
            field_simp [this, hε]
            -- what tactic can close this?
            rw [div_le_iff₀]
            . field_simp
              exact le_of_lt hε
            . positivity

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_ge {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_ge (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  . wlog hx : x > 0
    . simp at hx
      by_cases h': x = 0
      . subst x
        use 0
        simp
      . have h: x < 0 := by grind
        specialize this (-x) (by linarith)
        obtain ⟨N, hN, hN'⟩ := this
        by_cases hx: (N:Real) = -x
        . use -N
          observe : x = -(N: Real)
          subst x
          simp
        use -N-1
        simp
        grind
    obtain ⟨M, hM, h⟩ := le_mul (ε := 1) (by exact (pos_of_coe ↑1).mpr rfl) x
    simp at h
    induction' M with M ih
    . contradiction
    . by_cases hM': (M:Real) ≤ x
      . use M
        simp [hM']
        norm_cast
      . simp at hM'
        by_cases hz: M = 0
        . subst M
          norm_cast at hM'
          linarith
        . have : M > 0 := by
            have : 0 ≤  M := by exact Nat.zero_le M
            rw [le_iff_lt_or_eq] at this
            aesop
          specialize ih this hM'
          exact ih
  . intro N N' hN hN'
    have h1 := lt_of_le_of_lt hN.1 hN'.2
    have h2 := lt_of_le_of_lt hN'.1 hN.2
    norm_cast at h1 h2
    have h1': N ≤ N' := by exact (Int.add_le_add_iff_right 1).mp h1
    have h2': N' ≤ N := by exact (Int.add_le_add_iff_right 1).mp h2
    exact Int.le_antisymm h1' h2'

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  obtain ⟨N, hN, h⟩ := (Real.floor_exist (1/x)).exists
  rw [isPos_iff] at hx
  use N + 1
  have hN1: 0 < (N: Real) + 1 :=
    calc
      0 < 1 / x := by exact one_div_pos.mpr hx
      _ < _ := h
  constructor
  . norm_cast at hN1
  . rw [inv_eq_one_div]
    field_simp
    rw [div_lt_iff₀ hN1]
    rw [div_lt_iff₀ hx] at h
    rw [mul_comm]
    exact h

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  obtain ⟨N, hN, h⟩ := exist_inv_nat_le (x:= y - x) (by exact (antisymm x y).mp hxy)
  obtain ⟨M, hM, hM'⟩ := (floor_exist (N * x)).exists
  use (M + 1) / N
  field_simp at h
  constructor
  . simp
    rw [lt_div_iff₀ (by norm_cast)]
    rw [mul_comm]
    exact hM'
  . simp
    calc
      _ = (M: Real) / (N: Real) + 1 / (N: Real) := by ring
      _ < (M: Real) / (N: Real) + y - x := by linarith
      _ ≤ x + y - x := by
        gcongr
        rw [div_le_iff₀ (by norm_cast)]
        rw [mul_comm]
        exact hM
      _ = y := by ring

theorem Real.abs_of_nonneg (x:Real) (hx: 0 ≤ x) : abs x = x := by
  rw [le_iff] at hx
  cases' hx with hx hx
  . rw [antisymm] at hx
    simp at hx
    rw [abs_of_pos x hx]
  . subst x
    simp

theorem Real.abs_nonneg' (x:Real): x.abs ≥ 0 := by
  simp
  rw [le_iff]
  have := abs_nonneg x
  rw [antisymm]
  aesop

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rw [abs_eq_abs]
  by_cases h: 0 ≤ x - y
  . rw [abs_of_nonneg (x - y) h]
    constructor
    . intro hlt
      constructor <;> linarith
    . intro hlt
      linarith
  . rw [abs_of_neg (x - y) (by simp at h; exact h)]
    constructor
    . intro hlt
      constructor <;> linarith
    . intro hlt
      linarith

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  rw [abs_eq_abs]
  constructor
  . intro h
    cases' h with h h
    . rw [← abs_eq_abs] at h
      rw [dist_lt_iff] at h
      exact ⟨h.1.le, h.2.le⟩
    . subst ε
      by_cases h: 0 ≤ x - y
      . simp [abs_of_nonneg _ h]
        linarith
      . simp at h
        simp [abs_of_neg (x - y) (by exact h)]
        linarith
  . intro ⟨h1, h2⟩
    cases' h1 with h1 h1
    . cases' h2 with h2 h2
      . have := (dist_lt_iff _ _ _).mpr ⟨h1, h2⟩
        rw [abs_eq_abs] at this
        exact le_of_lt this
      . subst x
        simp
        by_cases hε: 0 < ε
        . rw [abs_of_nonneg _ (le_of_lt hε)]
        . simp at hε
          linarith
    . subst x
      simp
      by_cases hε: 0 < ε
      . have : -ε < 0 := by
          linarith
        rw [abs_of_neg _ (by exact (isNeg_iff (-ε)).mpr this)]
        simp
      . simp at hε
        have : 0 ≤ -ε := by linarith
        rw [abs_of_nonneg _ this]
        linarith

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor
  . intro h
    by_contra! hxy
    specialize h ((x - y) / 2) (by linarith)
    linarith
  . intro h
    intro ε hε
    linarith

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor
  . intro h
    by_contra! hxy
    wlog h': x > y
    . simp at h'
      specialize this y x
      apply this
      . rw [abs_sub_comm]
        exact h
      . exact hxy.symm
      . exact lt_of_le_of_ne h' hxy
    have := _root_.abs_of_pos (a:=x - y) (by linarith)
    simp [this] at h
    simp [add_comm] at h
    rw [le_add_eps_iff] at h
    linarith
  . intro h
    subst x
    simp
    intro ε
    exact le_of_lt

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by
  by_contra h'
  simp at h'
  obtain ⟨q, hq1, hq2⟩ := rat_between h'
  rw [ratCast_def] at hq2
  have : ∀ n, a n ≤ q := by
    intro n
    specialize h n
    apply le_of_lt
    have := lt_of_le_of_lt h hq1
    norm_cast at this
  have := LIM_mono hcauchy (Sequence.IsCauchy.const q) this
  linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
  by_contra h'
  simp at h'
  obtain ⟨q, hq1, hq2⟩ := rat_between h'
  rw [ratCast_def] at hq1
  have : ∀ n, a n ≥ q := by
    intro n
    specialize h n
    apply le_of_lt
    have := lt_of_lt_of_le hq2 h
    norm_cast at this
  have := LIM_mono (Sequence.IsCauchy.const q) hcauchy this
  linarith

theorem Real.max_eq (x y:Real) : max x y = (if x ≥ y then x else y) := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  rw [max_eq, min_eq]
  by_cases h: x ≥ y <;> simp [h]

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  rw [neg_max]
  simp

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  rw [max_eq, max_eq]
  by_cases h: x ≥ y
  . simp [h]
    intro h
    linarith
  . simp [h]
    intro h
    linarith

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  rw [max_def]
  simp

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  rw [max_eq, max_eq]
  by_cases h: x ≥ y
  . have : x + z ≥ y + z := by linarith
    simp [this]
    intro h
    linarith
  . simp at h
    have : ¬ x + z ≥ y + z := by linarith
    simp [this]
    intro h
    linarith

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  rw [max_eq, max_eq]
  have hz': 0 < z := by exact (isPos_iff z).mp hz
  by_cases h: x ≥ y
  . have : x * z ≥ y * z := by exact (mul_le_mul_iff_of_pos_right hz').mpr h
    simp [this]
    intro h
    linarith
  . simp at h
    have : ¬ x * z ≥ y * z := by simp; exact mul_lt_mul_right h hz
    simp [this]
    intro h
    linarith

theorem Real.max_mul_neg (x y :Real) {z:Real} (hz: z.IsNeg) : max (x * z) (y * z) = min x y * z := by
  have : (-z).IsPos := by exact (neg_iff_pos_of_neg z).mp hz
  have := max_mul (x:=-x) (y:=-y) this
  simp at this
  rw [this]
  rw [neg_min]
  ring

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  rw [min_eq, min_eq]
  by_cases h: x ≤ y
  . simp [h]
    intro h
    linarith
  . simp [h]
    intro h
    linarith

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [min_eq]
  simp

/- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  rw [min_eq, min_eq]
  by_cases h: x + z ≤ y + z
  . simp [h]
    intro h
    linarith
  . simp [h]
    intro h
    linarith

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  rw [min_eq, min_eq]
  have hz': 0 < z := by exact (isPos_iff z).mp hz
  by_cases h: x ≤ y
  . have : x * z ≤ y * z := by exact (mul_le_mul_iff_of_pos_right hz').mpr h
    simp [this]
    intro h
    linarith
  . simp at h
    have : ¬ x * z ≤ y * z := by simp; exact mul_lt_mul_right h hz
    simp [this]
    intro h
    linarith

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  rw [max_eq, min_eq]
  have hx': 0 < x := by exact (isPos_iff x).mp hx
  have hy': 0 < y := by exact (isPos_iff y).mp hy
  by_cases h: x < y
  . have : ¬ x ≥ y := by linarith
    simp [this]
    have : y⁻¹ < x⁻¹ := by rwa [inv_lt_inv₀ hy' hx']
    simp [this]
  . simp at h
    simp [h]
    rw [inv_lt_inv₀ hy' hx']
    intro h
    linarith

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  rw [min_eq, max_eq]
  have hx': 0 < x := by exact (isPos_iff x).mp hx
  have hy': 0 < y := by exact (isPos_iff y).mp hy
  by_cases h: x ≤ y
  . simp [h]
    rw [inv_lt_inv₀ hx' hy']
    intro h
    linarith
  . simp [h]
    rw [inv_le_inv₀ hy' hx']
    intro h
    linarith

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by
    simp
    intro x y h
    simp [ratCast_def]
    apply LIM_mono (Sequence.IsCauchy.const x) (Sequence.IsCauchy.const y)
    intro n
    exact h

end Chapter5
