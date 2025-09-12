import Mathlib.Tactic
import Analysis.Section_5_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [Real.upperBound_def]
  simp only [Set.mem_Icc, and_imp, ge_iff_le]
  constructor
  . intro h
    specialize h 1 (by norm_num) (by rfl)
    exact h
  . intro h x hx1 hx2
    exact le_trans hx2 h

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M, M ∈ upperBounds (.Ioi (0:Real)) := by
  push_neg
  intro M h
  rw [Real.upperBound_def] at h
  rw [Real.Ioi_def] at h
  by_cases hM: 0 < M
  . specialize h (M + 1)
    simp at h
    specialize h (by positivity)
    linarith
  . simp at hM
    specialize h 1
    simp at h
    linarith

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M
  rw [Real.upperBound_def]
  intro h he
  contradiction

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  rw [mem_upperBounds] at hb ⊢
  intros x hx
  exact le_trans (hb x hx) h

/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1:Real) := by
  rw [Real.isLUB_def]
  constructor
  . rw [Real.upperBound_def]
    rintro x ⟨hx1, hx2⟩
    exact hx2
  . intros M' hM'
    rw [Real.upperBound_def] at hM'
    specialize hM' 1 (by norm_num)
    exact hM'

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  push_neg
  intro M h
  rw [Real.isLUB_def] at h
  obtain ⟨h1, h2⟩ := h
  specialize h2 (M-1)
  simp at h2
  linarith

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by grind [Real.isLUB_def]

/-- definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

set_option maxHeartbeats 1500000 in
/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  -- clean up toNat, I don't know how to use it properly
  let k:ℕ := (K - 1 - L).toNat
  have hkToNat: (K - 1 - L).toNat = K - 1 - L := by
    simp
    linarith
  induction' hk: k with k' ih generalizing K
  . subst k
    simp at hk
    have : K = L + 1 := by linarith
    use K, hLK, (by rfl), hK
    rw [this]
    simp_all
  . by_cases h: ((K - 1):ℤ) * ((1/(n+1):ℚ):Real) ∈ upperBounds E
    . have : L < K - 1 := by linarith
      specialize ih this h
      have h': L ≤ K - 1 - 1 := by linarith
      have h'': (K - 1 - 1 - L).toNat = k' := by
        have ht: (K - 1 - 1 - L).toNat = (K - 1 - 1 - L) := by simp [h']
        have : k' = k - 1 := by omega
        rw [this]
        unfold k
        linarith
      simp at ih
      specialize ih h'
      simp [h''] at ih
      obtain ⟨M, hM, hM', hM'', hM'''⟩ := ih
      use M
      . constructor
        . exact hM
        . constructor
          . linarith
          . constructor
            . simp [hM'']
            . simp [hM''']
    . use K
      simp_all

theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at ha ⊢
  intro ε hε
  specialize ha ε hε
  obtain ⟨M, hM⟩ := ha
  use M
  intro n hn n' hn'
  specialize hM n hn n' hn'
  rw [Section_4_3.dist] at hM ⊢
  simp_all
  calc
    _ ≤ |a n - a n'| := by exact abs_abs_sub_abs_le (a n) (a n')
    _ ≤ _ := hM

theorem Real.LIM.abs_eq {a b:ℕ → ℚ}
    (ha: (a: Sequence).IsCauchy) (hb: (b: Sequence).IsCauchy)
    (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  rw [LIM_eq_LIM ha hb] at h
  rw [LIM_eq_LIM (Sequence.IsCauchy.abs ha) (Sequence.IsCauchy.abs hb)]
  rw [Sequence.equiv_def] at h ⊢
  intro ε hε
  specialize h ε hε
  rw [Rat.eventuallyClose_iff] at h ⊢
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n hn
  simp_all
  calc
    _ ≤ |a n - b n| := abs_abs_sub_abs_le (a n) (b n)
    _ ≤ _ := hN

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy)
    : LIM a = LIM |a| := by
  rw [← isPos_iff] at h
  rw [isPos_def] at h
  obtain ⟨b, hb, hbc, h⟩ := h
  rw [h]
  rw [Real.LIM.abs_eq ha hbc h]
  congr
  funext n
  simp only [Pi.abs_apply]
  rw [boundedAwayPos_def] at hb
  obtain ⟨c, hc, hb⟩ := hb
  specialize hb n
  symm
  apply _root_.abs_of_nonneg
  linarith

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  rcases trichotomous' (LIM a) 0 with (h | h | h)
  . rw [_root_.abs_of_nonneg (le_of_lt h)]
    exact Real.LIM.abs_eq_pos h ha
  . rw [_root_.abs_of_neg h]
    rw [neg_LIM _ ha]
    have hneg: (((-a): ℕ → ℚ): Sequence).IsCauchy := Sequence.IsCauchy_neg ha
    conv_rhs => rw [show |a| = |(- a)| by funext x; simp]
    have : LIM (-a) > 0 := by
      rw [← isPos_iff]
      rw [← isNeg_iff] at h
      rw [neg_iff_pos_of_neg] at h
      rw [neg_LIM _ ha] at h
      exact h
    exact Real.LIM.abs_eq_pos this hneg
  . rw [h]
    rw [← Real.LIM.zero] at h
    apply Real.LIM.abs_eq ha (Sequence.IsCauchy.const 0) at h
    rw [h]
    have : |fun (x:ℕ) ↦ (0:ℚ)| = 0 := by funext x; simp
    rw [this]
    simp
    symm
    exact Real.LIM.zero

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∃ N, ∀ n ≥ N, a n ≤ x) :
    LIM a ≤ x := by
  obtain ⟨N, hN⟩ := h
  let a' := fun n ↦ if n < N then a N else a n
  have ha'_def: ∀ n, a' n = if n < N then a N else a n := by
    unfold a'
    simp
  have ha': (a':Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe] at hcauchy ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hcauchy ε hε
    use max M N
    intro n hn n' hn'
    simp [ha'_def]
    have h1: ¬ n < N := by
      simp
      exact le_of_max_le_right hn
    have h2: ¬ n' < N := by
      simp
      exact le_of_max_le_right hn'
    simp [h1, h2]
    specialize hM n (by exact le_of_max_le_left hn) n' (by exact le_of_max_le_left hn')
    exact hM
  have ha'eq: Sequence.Equiv a a' := by
    rw [Sequence.equiv_def]
    intro ε hε
    rw [Rat.eventuallyClose_iff]
    use N
    intro n hn
    simp [ha'_def]
    have : ¬ n < N := by simp; exact hn
    simp [this]
    exact le_of_lt hε
  have ha'a: LIM a = LIM a' := (LIM_eq_LIM (hcauchy) (ha')).mpr ha'eq
  rw [ha'a]
  have : ∀ n, a' n ≤ x := by
    intro n
    by_cases hn: n < N
    . rw [ha'_def n]
      simp [hn]
      specialize hN N (by rfl)
      exact hN
    . rw [ha'_def n]
      simp [hn]
      simp at hn
      specialize hN n hn
      exact hN
  exact LIM_of_le ha' this

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by
  wlog h: m < m'
  . simp at h
    rw [le_iff_lt_or_eq] at h
    cases' h with h h
    . specialize this hm'1 hm'2 hm1 hm2 h
      exact this.symm
    . exact h.symm
  have : m ≤ m' - 1 := by linarith
  have : (((m:ℚ) / (n+1):ℚ):Real) ≤ (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) := by
    field_simp
    rw [div_le_div_iff_of_pos_right (by positivity)]
    norm_cast
  have := upperBound_upper this hm1
  contradiction

set_option pp.coercions.types true in
/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by sorry

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by sorry

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by sorry

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by sorry

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by sorry

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by
  have hqCauchy: (q:Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_ge (1 / ε)
    use M
    intro j hj k hk
    rw [Section_4_3.dist]
    specialize hq M j hj k hk
    have hMp : 0 < M := by
      by_contra h'
      simp at h'
      subst M
      norm_cast at hM
      simp at hε
      rw [<- one_div_pos] at hε
      linarith
    calc
      _ = |q j - q k| := by ring
      _ ≤ 1 / (M+1) := hq
      _ ≤ 1 / M := by
        gcongr
        norm_cast
        exact Nat.le_add_right M 1
      _ ≤ ε := by
        rw [one_div_le]
        . exact hM
        . norm_cast
        . exact hε
  constructor
  . exact hqCauchy
  . intro M
    specialize hq M M (by rfl)
    rw [ratCast_def]
    rw [LIM_sub (Sequence.IsCauchy.const _) hqCauchy]
    have hsub := Sequence.IsCauchy.sub (Sequence.IsCauchy.const (q M)) hqCauchy
    rw [LIM_abs hsub]
    apply LIM_of_le' (Sequence.IsCauchy.abs hsub)
    use M
    intro n hn
    specialize hq n hn
    simp_all
    rw [show (M:Real) = ((M:ℚ):Real) by rfl]
    norm_cast at ⊢ hq

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  . intros; apply LIM_of_ge claim3; grind [upperBound_def]
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers ⊤ to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers ⊥ to denote the -∞ element.-/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y := by
      simp [E] at hy
      have : (x - ε) ^ 2 ≥ y^2 := by linarith
      refine (sq_le_sq₀ hy.1 ?_).mp this
      linarith
    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  have hr := exist_sqrt_two
  have hq := Rat.not_exist_sqrt_two
  obtain ⟨x, hx⟩ := hr
  use x
  contrapose! hq
  obtain ⟨q, hq⟩ := hq
  use q
  subst x
  norm_cast at hx

lemma hLowerBound_of_UpperBound {E : Set Real} (M:Real)
    (hbound: M ∈ lowerBounds E) : -M ∈ upperBounds (-E) := by
  rw [mem_upperBounds]
  rw [mem_lowerBounds] at hbound
  intro x h
  specialize hbound (-x) h
  linarith

lemma hUpperBound_of_LowerBound {E: Set Real} (M:Real)
    (hbound: M ∈ upperBounds E) : -M ∈ lowerBounds (-E) := by
  rw [mem_upperBounds] at hbound
  rw [mem_lowerBounds]
  intro x h
  specialize hbound (-x) h
  linarith

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  rw [isGLB_def]
  rw [isLUB_def] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  . have := hUpperBound_of_LowerBound _ h1
    simp at this
    exact this
  . intro y hy
    apply hLowerBound_of_UpperBound y at hy
    simp at hy
    specialize h2 (-y) hy
    linarith

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by sorry

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  have hE': (-E).Nonempty := by
    obtain ⟨x, hx⟩ := hE
    use -x
    simpa
  have hE'bound: BddAbove (-E) := by
    rw [Real.bddAbove_def]
    rw [Real.bddBelow_def] at hbound
    obtain ⟨M, hM⟩ := hbound
    use -M
    exact hLowerBound_of_UpperBound M hM
  obtain ⟨S, hS⟩ := Real.LUB_exist hE' hE'bound
  use -S
  exact isLUB_neg.mp hS

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
  obtain ⟨sq2, hsq2⟩ := exist_sqrt_two
  wlog h: 0 < sq2
  . simp at h
    rw [le_iff_lt_or_eq] at h
    cases' h with h h
    . specialize this hxy (-sq2) (by simpa) (by simpa)
      exact this
    . subst sq2
      norm_num at hsq2
  have := Real.rat_between (x := x - sq2) (y := y - sq2) (by linarith)
  obtain ⟨q, h1, h2⟩ := this
  use q + sq2
  constructor
  . linarith
  . constructor
    . linarith
    . rintro ⟨r, hr⟩
      have := Rat.not_exist_sqrt_two
      push_neg at this
      specialize this (r - q)
      have h: (r - q) = (sq2:Real) := by linarith
      apply congrArg (. ^ 2) at h
      rw [hsq2] at h
      norm_cast at h

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the `sSup` operation to build a conditionally complete lattice structure on `Real`-/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
