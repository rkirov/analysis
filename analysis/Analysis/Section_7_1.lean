import Mathlib.Tactic

/-!
# Analysis I, Section 7.1: Finite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be
functions on the entire integers.

Main constructions and results of this section:
-/

-- This makes available the convenient notation `∑ n ∈ A, f n` to denote summation of `f n` for
-- `n` ranging over a finite set `A`.
open BigOperators

/-!
- API for summation over finite sets (encoded using Mathlib's `Finset` type), using the
  `Finset.sum` method and the `∑ n ∈ A, f n` notation.
- Fubini's theorem for finite series

We do not attempt to replicate the full API for `Finset.sum` here, but in subsequent sections we
shall make liberal use of this API.

-/

-- This is a technical device to avoid Mathlib's insistence on decidable equality for finite sets.
open Classical

namespace Finset

-- We use `Finset.Icc` to describe finite intervals in the integers. `Finset.mem_Icc` is the
-- standard Mathlib tool for checking membership in such intervals.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. This is similar to Mathlib's `Finset.sum_Icc_succ_top` except that the
  latter involves summation over the natural numbers rather than integers.
-/
theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := sum_of_empty (by omega) a

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := sum_of_empty (by omega) a

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by simp [Icc_self]

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  have : Icc m (m+1) = {m, m + 1} := by
    ext x; simp [mem_Icc]; omega
  simp [this]

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have : Icc m (m+2) = {m, m + 1, m + 2} := by
    ext x; simp [mem_Icc]; omega
  simp [this]
  ring

/-- Remark 7.1.3 -/
example (a: ℤ → ℝ) (m n:ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, p = n + ↑d := ⟨(p - n).toNat, by omega⟩
  induction d with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    have := sum_of_empty (n := n) (m := n + 1) (by omega) a
    rw [this, add_zero]
  | succ d ih =>
    rw [show n + ↑(d + 1) = (n + ↑d) + 1 from by push_cast; ring,
        sum_of_nonempty (by omega) a, sum_of_nonempty (by omega) a,
        ← add_assoc, ih (by omega)]

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero =>
      simp only [Nat.cast_zero, add_zero, Icc_self]; simp
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          sum_of_nonempty (by omega) a,
          show (m + ↑d) + 1 + k = (m + ↑d + k) + 1 from by ring,
          sum_of_nonempty (by omega) (fun i ↦ a (i - k)), ih (by omega)]
      congr 1; show a (m + ↑d + 1) = a (m + ↑d + k + 1 - k); congr 1; ring
  · push_neg at hmn
    rw [sum_of_empty (by omega), sum_of_empty (by omega)]

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          sum_of_nonempty (by omega), sum_of_nonempty (by omega),
          sum_of_nonempty (by omega), ih (by omega)]
      ring
  · push_neg at hmn
    simp [sum_of_empty (by omega)]

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n:ℤ}  (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          sum_of_nonempty (by omega), sum_of_nonempty (by omega), ih (by omega)]
      ring
  · push_neg at hmn
    simp [sum_of_empty (by omega)]

/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n:ℤ}   (a: ℤ → ℝ) (c:ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          sum_of_nonempty (by omega), sum_of_nonempty (by omega)]
      exact le_trans (abs_add _ _) (add_le_add_right (ih (by omega)) _)
  · push_neg at hmn
    simp [sum_of_empty (by omega)]

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero =>
      simp only [Nat.cast_zero, add_zero, Icc_self]; simp
      exact h m (by omega) (by omega)
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          sum_of_nonempty (by omega) a, sum_of_nonempty (by omega) b]
      apply add_le_add
      · exact ih (fun i hi1 hi2 ↦ h i hi1 (by push_cast at hi2 ⊢; omega)) (by omega)
      · exact h _ (by omega) (by push_cast; omega)
  · push_neg at hmn
    rw [sum_of_empty (by omega), sum_of_empty (by omega)]

#check sum_congr

/--
  Proposition 7.1.8.
-/
theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x := calc
    _ = ∑ i ∈ Icc (1:ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert shift_finite_series _; simp
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j:ℤ) n, f (h' i) + f x := by
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]
      simp [show ¬ i < j by linarith]
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, Subtype.val_inj, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, Subtype.val_inj, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have why : Function.Bijective gtil := by sorry
  have why2 : Function.Bijective htil := by sorry
  calc
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind

/--
  This fact ensures that Definition 7.1.6 would be well-defined even if we did not appeal to the
  existing `Finset.sum` method.
-/
theorem exist_bijection {n:ℕ} {Y:Type*} (X: Finset Y) (hcard: X.card = n) :
    ∃ g: Icc (1:ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1:ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  have hempty : Icc (1:ℤ) (0:ℕ) = ∅ := Icc_eq_empty_of_lt (by norm_num)
  have g : Icc (1:ℤ) (0:ℕ) → (∅ : Finset X') :=
    fun ⟨_, hx⟩ => absurd (hempty ▸ hx) (notMem_empty _)
  rw [finite_series_eq ∅ f g
    ⟨fun ⟨_, a⟩ => absurd (hempty ▸ a) (notMem_empty _),
     fun ⟨_, a⟩ => absurd a (notMem_empty _)⟩]
  simp

/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  let g : Icc (1:ℤ) (1:ℕ) → ({x₀} : Finset X') := fun _ => ⟨x₀, mem_singleton_self x₀⟩
  have hg : Function.Bijective g := by
    constructor
    · intro ⟨a, ha⟩ ⟨b, hb⟩ _
      have ha' : a = 1 := by simp at ha; omega
      have hb' : b = 1 := by simp at hb; omega
      exact Subtype.ext (show a = b by omega)
    · intro ⟨val, hy⟩
      exact ⟨⟨1, by simp⟩, Subtype.ext (by show x₀ = val; exact (mem_singleton.mp hy).symm)⟩
  rw [finite_series_eq {x₀} f g hg]
  simp [Icc_self, g]

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X Y:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by sorry

-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
  generalize hm : X.card = m
  generalize hk : Y.card = k
  obtain ⟨bX, hbX⟩ := exist_bijection X hm
  obtain ⟨bY, hbY⟩ := exist_bijection Y hk
  set XY := X ∪ Y with hXY_def
  have hcard : XY.card = m + k := by rw [hXY_def, card_union_of_disjoint hdisj, hm, hk]
  -- Glue bijections: first m positions via bX, remaining k via bY
  let bXY : Icc (1:ℤ) ↑(m + k) → XY := fun ⟨i, hi⟩ =>
    if him : i ≤ ↑m then
      ⟨(bX ⟨i, mem_Icc.mpr ⟨by simp [mem_Icc] at hi; omega, him⟩⟩).val,
       show _ ∈ X ∪ Y from mem_union_left _ (bX _).property⟩
    else
      ⟨(bY ⟨i - ↑m, mem_Icc.mpr ⟨by omega, by simp [mem_Icc] at hi; omega⟩⟩).val,
       show _ ∈ X ∪ Y from mem_union_right _ (bY _).property⟩
  have hbXY : Function.Bijective bXY := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      apply Subtype.ext; show i = j
      have hv := congrArg Subtype.val heq
      simp only [bXY] at hv
      simp [mem_Icc] at hi hj
      by_cases him : i ≤ ↑m <;> by_cases hjm : j ≤ ↑m <;> simp [him, hjm] at hv
      · exact congrArg Subtype.val (hbX.injective (Subtype.ext hv))
      · exact absurd (hv ▸ (bX _).property) (fun h => disjoint_left.mp hdisj h (bY _).property)
      · exact absurd (hv.symm ▸ (bX _).property)
          (fun h => disjoint_left.mp hdisj h (bY _).property)
      · have h := hbY.injective (Subtype.ext hv)
        have : i - ↑m = j - ↑m := by simpa using congrArg Subtype.val h
        omega
    · intro ⟨z, hz⟩
      rcases mem_union.mp (show z ∈ X ∪ Y from hz) with hzX | hzY
      · obtain ⟨⟨i, hi⟩, hbi⟩ := hbX.surjective ⟨z, hzX⟩
        simp [mem_Icc] at hi
        exact ⟨⟨i, mem_Icc.mpr ⟨by omega, by push_cast; omega⟩⟩,
          Subtype.ext (by simp [bXY, show i ≤ ↑m from hi.2]; exact congrArg Subtype.val hbi)⟩
      · obtain ⟨⟨j, hj⟩, hbj⟩ := hbY.surjective ⟨z, hzY⟩
        simp [mem_Icc] at hj
        exact ⟨⟨j + ↑m, mem_Icc.mpr ⟨by omega, by push_cast; omega⟩⟩,
          Subtype.ext (by simp [bXY, show ¬(j + ↑m ≤ ↑m) from by omega,
            show j + ↑m - ↑m = j from by omega]; exact congrArg Subtype.val hbj)⟩
  -- Split the Icc sum and match each half
  rw [finite_series_eq XY f bXY hbXY,
      ← concat_finite_series (show (1:ℤ) ≤ ↑m + 1 from by omega)
                             (show (↑m : ℤ) ≤ ↑(m + k) from by push_cast; omega)]
  congr 1
  · -- First half: ∑ Icc 1 m = ∑ X via bX
    rw [finite_series_eq X f bX hbX]
    apply sum_congr rfl; intro i hi; simp [mem_Icc] at hi
    rw [dif_pos (mem_Icc.mpr ⟨hi.1, by push_cast; omega⟩), dif_pos (mem_Icc.mpr hi)]
    congr 1; simp [bXY, show i ≤ ↑m from hi.2]
  · -- Second half: ∑ Icc (m+1) (m+k) = ∑ Y via shift + bY
    conv_rhs => rw [finite_series_eq Y f bY hbY, shift_finite_series (k := ↑m)]
    conv_rhs =>
      rw [show (1:ℤ) + ↑m = ↑m + 1 from by ring,
          show (↑k : ℤ) + ↑m = ↑(m + k) from by push_cast; ring]
    apply sum_congr rfl
    intro i hi; simp [mem_Icc] at hi
    rw [dif_pos (mem_Icc.mpr ⟨by omega, by push_cast; omega⟩),
        dif_pos (mem_Icc.mpr ⟨by omega, by omega⟩)]
    congr 1; simp [bXY, show ¬(i ≤ ↑m) from by omega]

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
  obtain ⟨b, hb⟩ := exist_bijection X rfl
  let φ (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) ↑X.card then h (b ⟨i, hi⟩) else 0
  have to_icc : ∀ h : X' → ℝ, ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) ↑X.card, φ h i :=
    fun h => finite_series_eq X h b hb
  rw [to_icc, to_icc, to_icc]
  have : ∀ i, φ (f + g) i = φ f i + φ g i := by
    intro i; simp only [φ]; split <;> simp [Pi.add_apply]
  simp_rw [this]
  exact finite_series_add (φ f) (φ g)

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
  obtain ⟨b, hb⟩ := exist_bijection X rfl
  let φ (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) ↑X.card then h (b ⟨i, hi⟩) else 0
  have to_icc : ∀ h : X' → ℝ, ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) ↑X.card, φ h i :=
    fun h => finite_series_eq X h b hb
  rw [to_icc, to_icc]
  have : ∀ i, φ (fun x => c * f x) i = c * φ f i := by
    intro i; simp only [φ]; split <;> simp
  simp_rw [this]
  exact finite_series_const_mul (φ f) c

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  obtain ⟨b, hb⟩ := exist_bijection X rfl
  let φ (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) ↑X.card then h (b ⟨i, hi⟩) else 0
  have to_icc : ∀ h : X' → ℝ, ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) ↑X.card, φ h i :=
    fun h => finite_series_eq X h b hb
  rw [to_icc, to_icc]
  exact finite_series_of_le fun i hi1 hi2 => by
    simp only [φ, show i ∈ Icc (1:ℤ) ↑X.card from mem_Icc.mpr ⟨hi1, hi2⟩, dite_true]
    exact h _ (b ⟨i, mem_Icc.mpr ⟨hi1, hi2⟩⟩).property

/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
  obtain ⟨b, hb⟩ := exist_bijection X rfl
  let φ (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) ↑X.card then h (b ⟨i, hi⟩) else 0
  have to_icc : ∀ h : X' → ℝ, ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) ↑X.card, φ h i :=
    fun h => finite_series_eq X h b hb
  rw [to_icc, to_icc]
  have : ∀ i, φ (fun x => |f x|) i = |φ f i| := by
    intro i; simp only [φ]; split <;> simp
  simp_rw [this]
  exact abs_finite_series_le (φ f) 0

/-- Lemma 7.1.13 --/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . sorry
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . sorry
      sorry

/-- Corollary 7.1.14 (Fubini's theorem for finite series)-/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3 : develop as many analogues as you can of the above theory for finite products
-- instead of finite sums.

#check Nat.factorial_zero
#check Nat.factorial_succ

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics `zify`, `norm_cast`, and `omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  sorry

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  sorry



end Finset
