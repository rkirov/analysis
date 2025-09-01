import Mathlib.Tactic
import Analysis.Section_4_3
import Analysis.Section_4_4

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point `n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from ℕ to ℚ can be thought of as sequences starting from 0; `ofNatFun` performs this conversion.

The `coe` attribute allows the delaborator to print `Sequence.ofNatFun f` as `↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (a : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
If `a : ℕ → ℚ` is used in a context where a `Sequence` is expected, automatically coerce `a` to `Sequence.ofNatFun a` (which will be pretty-printed as `↑a`)
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of Definition 5.1.3 - definition of ε-steadiness for a sequence with an
arbitrary starting point n₀
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Definition 5.1.3 - definition of ε-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 3, 3 ... is 1-steady
Intended as a demonstration of `Rat.Steady.coe`
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
Compare: if you need to work with `Rat.Steady` on the coercion directly, there will be side
conditions `hn : n ≥ 0` and `hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into four cases based on whether n and m are even or odd
  -- In each case, we know the exact value of a n and a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h
  specialize h 0 1
  simp [Rat.Close] at h
  norm_num at h
  have : |(9:ℚ) / (100:ℚ)| = 9 / 100 := by norm_num
  rw [this] at h
  linarith

lemma two_pow_gt (n: ℕ) : 2 ^ (n + 1) ≥ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := by ring
    rw [this]
    calc
      2 ^ (n + 1) * 2 ≥ (n + 1) * 2 := by simp [ih]
      _ > 2 * n + 1 := by linarith
      _ ≥ n + 1 := by linarith

/-- Example 5.1.5: The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
-/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h
  let n := (Nat.exists_gt ε).choose
  have hn := (Nat.exists_gt ε).choose_spec
  specialize h (n + 1) n
  rw [Rat.Close] at h
  -- not only norm_cast proves it? norm_num fails
  rw [show (2:ℚ) ^ (n + 1 + 1) = (2:ℚ) ^ (n + 1) * (2:ℚ) by ring] at h
  rw [show |(2:ℚ) ^ (n + 1) * 2 - (2:ℚ) ^ (n + 1)| = |(2:ℚ) ^ (n + 1)| by ring_nf] at h
  rw [show |(2:ℚ) ^ (n + 1)| = (2:ℚ) ^ (n + 1) by exact IsAbsoluteValue.abv_pow abs 2 (n + 1)] at h
  change ε < n at hn
  have : (2:ℚ) ^ (n + 1) < n := by exact lt_of_le_of_lt h hn
  norm_cast at this
  have := two_pow_gt n
  linarith

/-- Example 5.1.5:The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Split into 4 cases based on whether n and m are 0 or not
  split_ifs <;> simp [Rat.Close]

/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

namespace Chapter5

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is not 0.1-steady
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h
  rw [abs_of_nonneg] at h <;> grind

/--
Example 5.1.7: The sequence a_10, a_11, a_12, ... is 0.1-steady
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is eventually 0.1-steady
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by
  use 1
  simp
  rw [Rat.Steady]
  intro n hn m hm
  simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  have hne: n ≠ 0 := by omega
  have hme : m ≠ 0 := by omega
  simp [hne, hme]
  exact le_of_lt hε

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Definition of Cauchy sequences, for a sequence starting at 0 -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h'; specialize h' j _ k _ <;> try omega
    simp_all; exact h'
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := ?_
  have mpos : 0 ≤ m := ?_
  lift n to ℕ using npos
  lift m to ℕ using mpos
  simp [hn, hm]; specialize h' n _ m _
  all_goals try omega
  norm_cast

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

lemma floor_abs (r: ℝ) : |r - ⌊r⌋| < 1 := by
  have : ⌊r⌋ ≤ r := Int.floor_le r
  have : r < ⌊r⌋ + 1 := Int.lt_floor_add_one _
  have : |r - ⌊r⌋| = r - ⌊r⌋ := by
    apply abs_of_nonneg (by linarith)
  rw [this]
  linarith

lemma sqrt_approx (n: ℕ): |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2| < 1 / 10 ^ n := by
   have := floor_abs (√2 * 10 ^ n)
   -- divide both sides of this by 10 ^n
   calc |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2|
    = |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2 * 10 ^ n / 10 ^ n| := by simp
  _ = |(↑⌊√2 * 10 ^ n⌋ - √2 * 10 ^ n) / 10 ^ n| := by rw [sub_div]
  _ = |↑⌊√2 * 10 ^ n⌋ - √2 * 10 ^ n| / 10 ^ n := by
      rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 10) n)]
  _ = |√2 * 10 ^ n - ↑⌊√2 * 10 ^ n⌋| / 10 ^ n := by
      rw [abs_sub_comm]
  _ < 1 / 10 ^ n := by
    apply div_lt_div₀ this <;> norm_num


lemma pow_te_lt (n: ℕ) (h: n > 0): 1 / (10:ℝ) ^ n ≤ 1 / 10 := by
  calc
    1 / (10:ℝ) ^ n ≤ 1 / 10 ^ 1 := by
      apply div_le_div_of_nonneg_left (a:=1)
      . linarith
      · norm_num
      · norm_cast
        exact Nat.le_pow h
    _ = 1 / 10 := by norm_num


lemma int_frac_sqrt : √2 - ⌊√2⌋ < 0.9 := by
  norm_num
  sorry

lemma int_frac_sqrt': √2 - ⌊√2 * 10⌋ / 10  < 0.09 := by
  norm_num
  sorry

lemma sqrt_two_floor : |√2 - ↑⌊√2⌋| < 0.9 := by
  calc
     _ = √2 - ↑⌊√2⌋ := by simp
    _ < 0.9 := int_frac_sqrt

lemma sqrt_two_floor' : |√2 - ↑⌊√2 * 10⌋ / 10| < 0.09 := by
  calc
    _ = √2 - ↑⌊√2 * 10⌋ / 10 := by
      apply abs_of_nonneg
      simp
      conv =>
        rhs
        rw [show √2 = √2 * 10 / 10 by ring_nf]
      suffices ⌊√2 * 10⌋ ≤ √2 * 10 by
        gcongr
      exact Int.floor_le _
    _ < 0.09 := int_frac_sqrt'

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by
  rw [Rat.Steady, sqrt_two]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp [Rat.Close]
  -- later proof doesn't work for m or n = 0 so we treat those separately here
  by_cases hmn : m = n
  . simp [hmn]
  wlog hmn': m < n
  . specialize this m n (by exact fun a ↦ hmn (id (Eq.symm a)))
    simp at hmn'
    rw [le_iff_lt_or_eq] at hmn'
    cases' hmn' with hmn' hmn'
    . specialize this hmn'
      rw [abs_sub_comm]
      exact this
    . symm at hmn'
      contradiction
  by_cases hm: m = 0
  . subst m
    simp
    have h1 := sqrt_approx n
    have h2 := sqrt_two_floor
    have hn : n > 0 := by omega
    have h3 := pow_te_lt n (by omega)
    have h12 := add_lt_add h1 h2
    qify at h12 h3 ⊢
    have := calc
      |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - (⌊√2⌋:ℝ)| = |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - √2 + (√2 - (⌊√2⌋:ℝ))| := by ring_nf
      _ ≤ |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - √2| + |√2 - (⌊√2⌋:ℝ)| := by exact abs_add _ _
      _ < 1 / 10 ^ n + 0.9 := h12
      _ ≤ 1 / 10 + 0.9 := by exact add_le_add_right h3 0.9
      _ = 1 := by norm_num
    exact_mod_cast (le_of_lt this)
  have hn : n ≠ 0 := by linarith
  have := calc
    |(⌊√2 * 10 ^ n⌋:ℚ) / 10 ^ n - (⌊√2 * 10 ^ m⌋:ℚ) / 10 ^ m| =
      |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - (⌊√2 * 10 ^ m⌋:ℝ) / 10 ^ m| := by simp
    _ = |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - √2 - ((⌊√2 * 10 ^ m⌋:ℝ) / 10 ^ m - √2)| := by ring_nf
    _ ≤ |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - √2| + |(⌊√2 * 10 ^ m⌋:ℝ) / 10 ^ m - √2| := by exact abs_sub _ _
    _ ≤ 1 / 10 ^ n + 1 / 10 ^ m := by
      have := sqrt_approx n
      have := sqrt_approx m
      linarith
    _ ≤ 1 := by
      have hm := pow_te_lt m (by exact Nat.zero_lt_of_ne_zero hm)
      have hn := pow_te_lt n (by exact Nat.zero_lt_of_ne_zero hn)
      linarith
  exact_mod_cast this

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by
  rw [Rat.Steady, sqrt_two]
  simp only [n0_coe, zero_le_one, sup_of_le_right, ge_iff_le, eval_coe_at_int, dite_eq_ite]
  intro n hn m hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  rw [Rat.Close] at ⊢
  by_cases hmn: m = n
  . simp [hmn]
    norm_num
  wlog hmn': m < n
  . specialize this m hm n hn (by exact fun a ↦ hmn (id (Eq.symm a)))
    have hmn'' : n < m := by
      simp at hmn'
      rw [le_iff_lt_or_eq] at hmn'
      aesop
    specialize this hmn''
    rwa [abs_sub_comm]
  simp [hm, hn]
  norm_cast at hn hm
  by_cases hn': m = 1
  . subst m
    simp
    have hten: 1 / (10:ℝ) ^ n ≤ 0.01 := by
      norm_num
      field_simp
      suffices (10:ℝ) ^ n ≥ (100:ℝ) by
        field_simp
        apply div_le_div_of_nonneg_left
        . norm_num
        . norm_num
        . exact this
      norm_cast
      rw [show 100 = 10^2 by rfl]
      apply Nat.pow_le_pow_right
      . omega
      . omega
    have := calc
      |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - ↑⌊√2 * 10⌋ / 10| = |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2 + (√2 - ↑⌊√2 * 10⌋ / 10)| := by ring_nf
      _ ≤ |↑⌊√2 * 10 ^ n⌋ / 10 ^ n - √2| + |√2 - ↑⌊√2 * 10⌋ / 10| := by exact abs_add _ _
      _ ≤ 1 / 10 ^ n + |√2 - ↑⌊√2 * 10⌋ / 10| := by
        gcongr
        linarith [sqrt_approx n]
      _ ≤ 1 / 10 ^ n + 0.09 := by
        gcongr
        linarith [sqrt_two_floor']
      _ ≤ 0.01 + 0.09 := by
        gcongr
      _ = 0.1 := by norm_num
    rw [show (0.1:ℝ) = (0.1:ℚ) by norm_cast] at this
    norm_cast at this ⊢

  -- same as above
  have := calc
    |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - (⌊√2 * 10 ^ m⌋:ℝ) / 10 ^ m| = |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - √2 - ((⌊√2 * 10 ^ m⌋:ℝ) / 10 ^ m - √2)| := by ring_nf
    _ ≤ |(⌊√2 * 10 ^ n⌋:ℝ) / 10 ^ n - √2| + |(⌊√2 * 10 ^ m⌋:ℝ) / 10 ^ m - √2| := by exact abs_sub _ _
    _ ≤ 1 / 10 ^ n + 1 / 10 ^ m := by
      have := sqrt_approx n
      have := sqrt_approx m
      linarith
    _ ≤ 1 / 10 ^ 2 + 1 / 10 ^ 2 := by
      gcongr <;> try norm_num <;> omega
    _ ≤ 1 / 10 := by norm_num
  suffices h: (|↑⌊√2 * 10 ^ n⌋ / 10 ^ n - ↑⌊√2 * 10 ^ m⌋ / 10 ^ m| : ℝ) ≤ (0.1 : ℝ) by
    rw [show (0.1:ℝ) = (0.1:ℚ) by norm_cast] at h
    norm_cast at h ⊢
  calc
    _ ≤ 1 / 10 := by exact this
    _ = (0.1 : ℝ) := by norm_num


/-- Proposition 5.1.11. The harmonic sequence, defined as a₁ = 1, a₂ = 1/2, ... is a Cauchy sequence. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    observe : (N:ℚ) > 0
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    We establish the following bounds:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    These imply that the distance between 1/j and 1/k is at most 1/N - when they are as "far apart" as possible.
    -/
    have : 1/j ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/j
    have : 1/k ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/k
    grind
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from 0 rather than 1 to align
  better with Mathlib conventions.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]
  push_neg
  intro M hM
  rw [Sequence.boundedBy_def]
  push_neg
  simp
  obtain ⟨ N, hN⟩ := exists_nat_gt M
  by_cases h: (-1) ^ N = 1
  . use N
    qify at h
    simp [h]
    have : (N:ℚ) + 1 ≥ 0 := by linarith
    have : |(N:ℚ) + 1| = (N:ℚ) + 1 := by simp [this]
    rw [this]
    exact lt_add_of_lt_of_pos hN rfl
  .
    have : (-1) ^ N = -1 := by
      cases' Nat.even_or_odd N with heven hodd
      · have : (-1) ^ N = 1 := Even.neg_one_pow heven
        contradiction
      · rw [Odd.neg_one_pow hodd]
    have h': (-1) ^ (N + 1) = 1 := by
      calc (-1) ^ (N + 1) = (-1) ^ N * (-1) := by ring
        _ = -1 * (-1) := by rw [this]
        _ = 1 := by ring
    use (N + 1)
    -- repeat above
    have h'pos : 0 ≤ (N:ℤ) + 1 := by linarith
    qify at h'
    simp [h'pos, h']
    ring_nf
    have : 2 + (N:ℚ) ≥ 0 := by linarith
    have : |2 + (N:ℚ)| = 2 + (N:ℚ) := by simp [this]
    rw [this]
    exact lt_add_of_pos_of_lt rfl hN

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Section_4_3.dist] at h
    norm_num at h
  observe h₁: Odd N
  observe h₂: Even (N+1)
  simp [h₁.neg_one_pow, h₂.neg_one_pow, Section_4_3.dist] at h
  norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0, BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  rw [Sequence.isCauchy_def] at h
  rw [Sequence.isBounded_def]
  specialize h 1 (by norm_num)
  simp [Rat.eventuallySteady_def] at h
  obtain ⟨N, hN, h⟩ := h
  have := IsBounded.finite (n:= (N - a.n₀).toNat) (fun n ↦ a (a.n₀ + n))
  obtain ⟨M, hM, h'⟩ := this
  use max M (|(a N)| + 1)
  constructor
  . exact le_sup_of_le_left hM
  . rw [Sequence.boundedBy_def]
    intro n
    by_cases hn: n < N
    . rw [Chapter5.BoundedBy] at h'
      by_cases hnn : n ≥ a.n₀
      .
        simp only [le_sup_iff]
        left
        let n': Fin (N - a.n₀).toNat := ⟨(n - a.n₀).toNat, by omega⟩
        specialize h' n'
        unfold n' at h'
        have : (n - a.n₀).toNat + a.n₀ = n := by omega
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
      rw [Rat.steady_def] at h
      simp at h
      specialize h n (by linarith) hn N hN (by rfl)
      rw [Rat.Close] at h
      have hn': a.n₀ ≤ n := by linarith
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

-- todo generalize further
lemma op_add {a b: ℕ → ℚ} (n: ℤ): (a: Sequence).seq n + (b: Sequence).seq n = ((a + b): Sequence).seq n := by
  by_cases hn: 0 ≤ n <;> simp [hn]

lemma op_sub {a b: ℕ → ℚ} (n: ℤ): (a: Sequence).seq n - (b: Sequence).seq n = ((a - b): Sequence).seq n := by
  by_cases hn: 0 ≤ n <;> simp [hn]

lemma op_mul {a b: ℕ → ℚ} (n: ℤ): (a: Sequence).seq n * (b: Sequence).seq n = ((a * b): Sequence).seq n := by
  by_cases hn: 0 ≤ n <;> simp [hn]

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by
  rw [Sequence.isBounded_def] at ha hb ⊢
  obtain ⟨Ma, ha0, ha'⟩ := ha
  obtain ⟨Mb, hb0, hb'⟩ := hb
  use Ma + Mb
  constructor
  . positivity
  . rw [Sequence.boundedBy_def] at ha' hb' ⊢
    intro n
    specialize ha' n
    specialize hb' n
    have := add_le_add ha' hb'
    have := le_trans (abs_add _ _) this
    rwa [op_add n] at this

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by
  -- same proof as above, except last 3 lines
  -- todo - refactor
  rw [Sequence.isBounded_def] at ha hb ⊢
  obtain ⟨Ma, ha0, ha'⟩ := ha
  obtain ⟨Mb, hb0, hb'⟩ := hb
  use Ma + Mb
  constructor
  . positivity
  . rw [Sequence.boundedBy_def] at ha' hb' ⊢
    intro n
    specialize ha' n
    specialize hb' n
    rw [← op_sub n]
    exact le_trans (abs_sub _ _) (add_le_add ha' hb')

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by
  -- same proof as above, except last 3 lines
  -- todo - refactor
  rw [Sequence.isBounded_def] at ha hb ⊢
  obtain ⟨Ma, ha0, ha'⟩ := ha
  obtain ⟨Mb, hb0, hb'⟩ := hb
  use Ma * Mb
  constructor
  . positivity
  . rw [Sequence.boundedBy_def] at ha' hb' ⊢
    intro n
    specialize ha' n
    specialize hb' n
    have := mul_le_mul ha' hb' (by exact abs_nonneg _) (by exact ha0)
    rw [← abs_mul] at this
    rwa [op_mul n] at this

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by sorry

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by sorry

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by sorry

end Chapter5
