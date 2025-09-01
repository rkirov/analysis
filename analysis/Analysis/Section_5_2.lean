import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.closeSeq_def]
  intro n ha hb
  rw [Rat.Close]
  simp_all
  lift n to ℕ using ha
  simp
  cases' Nat.even_or_odd n with heven hodd
  . have : (-(1:ℚ)) ^ n = 1 := by
      norm_cast
      exact Even.neg_one_pow heven
    rw [this]
    norm_num
    refine (le_of_eq (abs_of_nonneg (by norm_num)))
  . have : (-(1:ℚ)) ^ n = -1 := by
      norm_cast
      exact Odd.neg_one_pow hodd
    rw [this]
    norm_num
    refine (le_of_eq (abs_of_nonneg (by norm_num)))

/-- Example 5.2.2 (same proof as in 5.1)-/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence)
:= by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h
  have : |(11:ℚ) / 5| = 11 / 5 := abs_of_nonneg (by norm_num)
  rw [this] at h
  linarith

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Rat.eventuallyClose_def]
  constructor
  . rintro ⟨N, hN⟩
    by_cases hn: N < 0
    . use 0
      intro n
      rw [Rat.closeSeq_def] at hN
      specialize hN n
      simp at hN
      have : N ≤ (n:ℤ) := by linarith
      simp [this] at hN
      intro h'
      exact hN
    simp at hn
    lift N to ℕ using hn
    rw [Rat.closeSeq_def] at hN
    simp at hN
    use N
    intro n hn
    specialize hN n
    simp [hn] at hN
    exact hN
  . intro ⟨N, hN⟩
    use N
    rw [Rat.closeSeq_def]
    intro n ha hb
    rw [Rat.Close]
    simp at ha hb
    have : 0 ≤ n := by linarith
    lift n to ℕ using this
    simp [ha]
    simp at ha
    specialize hN n ha
    exact hN

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.closeSeq_def]
  push_neg
  use 0
  simp
  rw [Rat.Close]
  norm_num
  have : |(1:ℚ) / 5| = 1 / 5 := by apply abs_of_nonneg; norm_num
  rw [this]
  norm_num

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_def]
  use 1
  intro n hn
  simp_all
  rw [Rat.Close]
  have hn': 0 ≤ n := by linarith
  simp [hn']
  calc
    _ = |2 * (10:ℚ) ^ (-n - 1)| := by ring_nf
    _ = |2 * (10:ℚ) ^ (- (n + 1))| := by ring_nf
    _ = 2 * (10:ℚ) ^ (-(n + 1)) := by
      apply abs_of_nonneg
      positivity
    _ ≤ 2 * (10:ℚ) ^ (-(2:ℤ)) := by
      gcongr
      . norm_num
      . linarith
    _ ≤ 0.1 := by norm_num

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_def]
  use 2
  intro n hn
  simp_all
  rw [Rat.Close]
  have hn': 0 ≤ n := by linarith
  simp [hn']
  calc
    _ = |2 * (10:ℚ) ^ (-n - 1)| := by ring_nf
    _ = |2 * (10:ℚ) ^ (- (n + 1))| := by ring_nf
    _ = 2 * (10:ℚ) ^ (-(n + 1)) := by
      apply abs_of_nonneg
      positivity
    _ ≤ 2 * (10:ℚ) ^ (-(3:ℤ)) := by
      gcongr
      . norm_num
      . linarith
    _ ≤ 0.01 := by norm_num

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  simp only [Sequence.equiv_def, Rat.eventuallyClose_iff]

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]



/-- Exercise 5.2.1 -/
lemma Sequence.close_seq_symm (ε: ℚ) (a b: Sequence) : ε.CloseSeq a b ↔ ε.CloseSeq b a := by
  repeat rw [Rat.closeSeq_def]
  constructor
  . intro h
    intro n hb ha
    specialize h n ha hb
    rw [Rat.Close] at h ⊢
    rw [abs_sub_comm]
    exact h
  . intro h
    intro n hb ha
    specialize h n ha hb
    rw [Rat.Close] at h ⊢
    rw [abs_sub_comm]
    exact h

lemma Sequence.eventuallyClose_symm (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ε.EventuallyClose b a := by
  repeat rw [Rat.eventuallyClose_def]
  constructor
  . rintro ⟨N, hN⟩
    use N
    rw [Sequence.close_seq_symm]
    exact hN
  . rintro ⟨N, hN⟩
    use N
    rw [Sequence.close_seq_symm]
    exact hN

lemma Sequence.equiv_symm {a b: ℕ → ℚ}: Equiv a b ↔ Equiv b a := by
  constructor
  . intro hab ε hε
    rw [equiv_def] at hab
    specialize hab ε hε
    rw [Sequence.eventuallyClose_symm]
    exact hab
  . intro hab ε hε
    rw [equiv_def] at hab
    specialize hab ε hε
    rw [Sequence.eventuallyClose_symm]
    exact hab

theorem Sequence.isCauchy_of_equiv_one_d {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy → (b:Sequence).IsCauchy := by
  rw [equiv_iff] at hab
  repeat rw [Sequence.IsCauchy.coe]
  intro h
  intro ε hε
  specialize h (ε / 3) (by linarith)
  specialize hab (ε / 3) (by linarith)
  obtain ⟨N, hN⟩ := hab
  obtain ⟨M, hM⟩ := h
  use max M N
  intro j hj k hk
  simp [Section_4_3.dist_eq] at ⊢ hN hM
  simp_all
  specialize hM j hj.1 k hk.1
  have hNk := hN k hk.2
  have hNj := hN j hj.2
  calc
    |b j - b k| = |b j - a j + a j - a k + a k - b k| := by ring_nf
    _ = |(b j - a j) + (a j - a k + a k - b k)| := by ring_nf
    _ ≤ |b j - a j| + |a j - a k + a k - b k| := abs_add _ _
    _ = |b j - a j| + |(a j - a k) + (a k - b k)| := by ring_nf
    _ ≤ |b j - a j| + (|a j - a k| + |a k - b k|) := by
      gcongr
      exact abs_add _ _
    _ ≤ (ε / 3) + (|a j - a k| + |a k - b k|) := by gcongr; rw [abs_sub_comm]; exact hNj
    _ ≤ (ε / 3) + (ε / 3 + |a k - b k|) := by gcongr
    _ ≤ (ε / 3) + (ε / 3 + (ε / 3)) := by gcongr
    _ = ε := by linarith

theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  constructor
  . exact isCauchy_of_equiv_one_d hab
  . rw [equiv_symm] at hab
    exact isCauchy_of_equiv_one_d hab

theorem Sequence.isBounded_of_eventuallyClose_one_dir {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded → (b:Sequence).IsBounded := by
  intro h
  rw [Sequence.isBounded_def] at h ⊢
  rw [Rat.eventuallyClose_iff] at hab
  obtain ⟨N, hN⟩ := hab
  obtain ⟨M, hMp, hM⟩ := h
  simp [boundedBy_def] at ⊢ hN
  obtain ⟨M', hM'p, hM'⟩ := IsBounded.finite (fun n ↦ b n : Fin N → ℚ)
  use (max M' M) + |ε|
  constructor
  . positivity
  . intro n
    by_cases hn: n < N
    . by_cases hn': n < 0
      . have : ¬ 0 ≤ n := by exact not_le_of_gt hn'
        simp [this]
        positivity
      have : 0 ≤ n := by linarith
      lift n to ℕ using this
      norm_cast at hn
      lift n to Fin N using hn
      simp
      rw [Chapter5.BoundedBy] at hM'
      specialize hM' n
      calc
        |b n| ≤ M' := hM'
        _ ≤ max M' M := by apply le_max_left
        _ ≤ (max M' M) + |ε| := by simp
    simp at hn
    have : 0 ≤ n := by linarith
    lift n to ℕ using this
    simp
    norm_cast at hn
    calc
      |b n| = |b n - a n + a n| := by ring_nf
      _ = |(b n - a n) + a n| := by ring_nf
      _ ≤ |b n - a n| + |a n| := abs_add _ _
      _ ≤ ε + |a n| := by gcongr; rw [abs_sub_comm]; exact hN n hn
      _ ≤ |ε| + |a n| := by gcongr; exact le_abs_self ε
      _ ≤ |ε| + M := by gcongr; exact hM n
      _ ≤ |ε| + max M' M := by gcongr; exact le_max_right M' M
      _ = _ := by ring_nf

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  constructor
  . exact isBounded_of_eventuallyClose_one_dir hab
  . rw [Sequence.eventuallyClose_symm] at hab
    exact isBounded_of_eventuallyClose_one_dir hab

end Chapter5
