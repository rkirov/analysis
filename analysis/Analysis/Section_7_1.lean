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
theorem finite_series_const_mul {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
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
theorem abs_finite_series_le {m n:ℤ} (a: ℤ → ℝ) :
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

set_option maxHeartbeats 800000 in
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
  have hπ_val {i:ℤ} (hi1 : 1 ≤ i) (hi2 : i ≤ ↑n + 1) : (π i).val = i := by
    simp [π, mem_Icc, hi1, hi2]
  -- Reduce bijectivity to injectivity via cardinality
  have hcard : Nat.card ↑(Icc (1:ℤ) ↑n) = Nat.card ↑(X.erase x.val) := by
    rw [Nat.card_eq_finsetCard, Nat.card_eq_finsetCard, card_erase_of_mem x.2, hX]; simp
  -- Injectivity helper: π is injective on Icc 1 n
  have hπ_inj {a b : ℤ} (ha : a ∈ Icc (1:ℤ) n) (hb : b ∈ Icc (1:ℤ) n)
      (h_eq : π a = π b) : a = b := by
    simp [mem_Icc] at ha hb
    have := congrArg Subtype.val h_eq
    rwa [hπ_val ha.1 (by linarith), hπ_val hb.1 (by linarith)] at this
  have why : Function.Bijective gtil := by
    rw [Nat.bijective_iff_injective_and_card]; exact ⟨fun a b heq ↦ by
      have := hg.injective (Subtype.val_injective (Subtype.mk.inj heq))
      exact Subtype.ext (hπ_inj a.2 b.2 this), hcard⟩
  have why2 : Function.Bijective htil := by
    rw [Nat.bijective_iff_injective_and_card]; refine ⟨fun a b heq ↦ ?_, hcard⟩
    have hval : h' a.val = h' b.val := Subtype.val_injective (Subtype.mk.inj heq)
    obtain ⟨ha1, ha2⟩ := mem_Icc.mp a.2; obtain ⟨hb1, hb2⟩ := mem_Icc.mp b.2
    by_cases ha_lt : (a:ℤ) < j <;> by_cases hb_lt : (b:ℤ) < j
    · simp only [h', ha_lt, hb_lt, ite_true] at hval
      exact Subtype.ext (hπ_inj a.2 b.2 (hh.injective hval))
    · simp only [h', ha_lt, hb_lt, ite_true, ite_false] at hval
      have := congrArg Subtype.val (hh.injective hval)
      rw [hπ_val (by omega) (by omega), hπ_val (by omega) (by omega)] at this; omega
    · simp only [h', ha_lt, hb_lt, ite_false, ite_true] at hval
      have := congrArg Subtype.val (hh.injective hval)
      rw [hπ_val (by omega) (by omega), hπ_val (by omega) (by omega)] at this; omega
    · simp only [h', ha_lt, hb_lt, ite_false] at hval
      have := congrArg Subtype.val (hh.injective hval)
      rw [hπ_val (by omega) (by omega), hπ_val (by omega) (by omega)] at this
      exact Subtype.ext (by omega)
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
    ∑ x, f x = ∑ y, f (g y) := by
  set n := Fintype.card Y
  have hn : (Finset.univ : Finset Y).card = n := Finset.card_univ
  have hm : (Finset.univ : Finset X).card = n := by
    rw [Finset.card_univ]; exact (Fintype.card_of_bijective hg).symm
  obtain ⟨bY, hbY⟩ := exist_bijection Finset.univ hn
  let bX : Icc (1:ℤ) ↑n → (Finset.univ : Finset X) :=
    fun p => ⟨g (bY p).val, Finset.mem_univ _⟩
  have hbX : Function.Bijective bX := by
    constructor
    · intro a b h
      simp only [bX, Subtype.mk.injEq] at h
      exact hbY.injective (Subtype.ext (hg.injective h))
    · intro ⟨x, _⟩
      obtain ⟨y, rfl⟩ := hg.surjective x
      obtain ⟨p, hp⟩ := hbY.surjective ⟨y, Finset.mem_univ _⟩
      exact ⟨p, Subtype.ext (by simp [bX]; exact congrArg g (congrArg Subtype.val hp))⟩
  rw [finite_series_eq Finset.univ f bX hbX,
      finite_series_eq Finset.univ (fun y => f (g y)) bY hbY]

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
  exact abs_finite_series_le (φ f)

/-- Lemma 7.1.13 --/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . intro X hX; simp [Finset.card_eq_zero.mp hX]
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
      . rw [hunion]; ext ⟨a, b⟩; simp [Finset.mem_product, Finset.mem_union]; tauto
      exact disjoint_product.mpr (.inl hdisj)

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

/-- Definition 7.1.1 (product analogue) / Exercise 7.1.3 -/
theorem prod_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∏ i ∈ Icc m n, a i = 1 := by
  rw [prod_eq_one]; intro _; rw [mem_Icc]; grind

/-- Definition 7.1.1 (product analogue) / Exercise 7.1.3 -/
theorem prod_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∏ i ∈ Icc m (n+1), a i = (∏ i ∈ Icc m n, a i) * a (n+1) := by
  rw [mul_comm _ (a (n+1))]
  convert prod_insert _
  · ext; simp; omega
  · infer_instance
  simp

/-- Lemma 7.1.4(a) (product analogue) / Exercise 7.1.3 -/
theorem concat_finite_product {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  (∏ i ∈ Icc m n, a i) * (∏ i ∈ Icc (n+1) p, a i) = ∏ i ∈ Icc m p, a i := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, p = n + ↑d := ⟨(p - n).toNat, by omega⟩
  induction d with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rw [prod_of_empty (n := n) (m := n + 1) (by omega) a, mul_one]
  | succ d ih =>
    rw [show n + ↑(d + 1) = (n + ↑d) + 1 from by push_cast; ring,
        prod_of_nonempty (by omega) a, prod_of_nonempty (by omega) a,
        ← mul_assoc, ih (by omega)]

/-- Lemma 7.1.4(b) (product analogue) / Exercise 7.1.3 -/
theorem shift_finite_product {m n k:ℤ} (a: ℤ → ℝ) :
  ∏ i ∈ Icc m n, a i = ∏ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero =>
      simp only [Nat.cast_zero, add_zero, Icc_self]; simp
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          prod_of_nonempty (by omega) a,
          show (m + ↑d) + 1 + k = (m + ↑d + k) + 1 from by ring,
          prod_of_nonempty (by omega) (fun i ↦ a (i - k)), ih (by omega)]
      congr 1; show a (m + ↑d + 1) = a (m + ↑d + k + 1 - k); congr 1; ring
  · push_neg at hmn
    rw [prod_of_empty (by omega), prod_of_empty (by omega)]

/-- Lemma 7.1.4(c) (product analogue) / Exercise 7.1.3 -/
theorem finite_product_mul {m n:ℤ} (a b: ℤ → ℝ) :
  ∏ i ∈ Icc m n, (a i * b i) = (∏ i ∈ Icc m n, a i) * (∏ i ∈ Icc m n, b i) := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          prod_of_nonempty (by omega), prod_of_nonempty (by omega),
          prod_of_nonempty (by omega), ih (by omega)]
      ring
  · push_neg at hmn
    simp [prod_of_empty (by omega)]

/-- Lemma 7.1.4(d) (product analogue) / Exercise 7.1.3 -/
theorem finite_product_pow {m n:ℤ} (a: ℤ → ℝ) (c:ℕ) :
  ∏ i ∈ Icc m n, (a i) ^ c = (∏ i ∈ Icc m n, a i) ^ c := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          prod_of_nonempty (by omega), prod_of_nonempty (by omega), ih (by omega),
          mul_pow]
  · push_neg at hmn
    simp [prod_of_empty (by omega)]

/-- Lemma 7.1.4(e) (product analogue) / Exercise 7.1.3 -/
theorem abs_finite_product {m n:ℤ} (a: ℤ → ℝ) :
  |∏ i ∈ Icc m n, a i| = ∏ i ∈ Icc m n, |a i| := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          prod_of_nonempty (by omega), prod_of_nonempty (by omega),
          abs_mul, ih (by omega)]
  · push_neg at hmn
    simp [prod_of_empty (by omega)]

theorem finite_product_nonneg {m n:ℤ} {a: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → 0 ≤ a i) :
    0 ≤ ∏ i ∈ Icc m n, a i := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero => simp [Icc_self]; exact h m (by omega) (by omega)
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          prod_of_nonempty (by omega)]
      exact mul_nonneg
        (ih (fun i hi1 hi2 ↦ h i hi1 (by push_cast at hi2 ⊢; omega)) (by omega))
        (h _ (by omega) (by push_cast; omega))
  · push_neg at hmn
    rw [prod_of_empty (by omega)]; norm_num

/-- Lemma 7.1.4(f) (product analogue) / Exercise 7.1.3 -/
theorem finite_product_of_le {m n:ℤ} {a b: ℤ → ℝ}
    (ha: ∀ i, m ≤ i → i ≤ n → 0 ≤ a i) (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
    ∏ i ∈ Icc m n, a i ≤ ∏ i ∈ Icc m n, b i := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + ↑d := ⟨(n - m).toNat, by omega⟩
    induction d with
    | zero =>
      simp only [Nat.cast_zero, add_zero, Icc_self]; simp
      exact h m (by omega) (by omega)
    | succ d ih =>
      rw [show m + ↑(d + 1) = (m + ↑d) + 1 from by push_cast; ring,
          prod_of_nonempty (by omega) a, prod_of_nonempty (by omega) b]
      exact mul_le_mul
        (ih (fun i hi1 hi2 ↦ ha i hi1 (by push_cast at hi2 ⊢; omega))
            (fun i hi1 hi2 ↦ h i hi1 (by push_cast at hi2 ⊢; omega)) (by omega))
        (h _ (by omega) (by push_cast; omega))
        (ha _ (by omega) (by push_cast; omega))
        (finite_product_nonneg fun i hi1 hi2 ↦
          le_trans (ha i hi1 (by push_cast at hi2 ⊢; omega))
                   (h i hi1 (by push_cast at hi2 ⊢; omega)))
  · push_neg at hmn
    rw [prod_of_empty (by omega), prod_of_empty (by omega)]

#check Nat.factorial_zero
#check Nat.factorial_succ

/-- Binomial theorem with `Nat.choose` over `range`, proved by induction (Pascal's rule). -/
private theorem binomial_choose (x y : ℝ) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m) := by
  let t : ℕ → ℕ → ℝ := fun n m ↦ x ^ m * y ^ (n - m) * ↑(n.choose m)
  change (x + y) ^ n = ∑ m ∈ range (n + 1), t n m
  have h_first : ∀ k, t k 0 = y ^ k := fun k => by simp [t]
  have h_last : ∀ k, t k (k + 1) = 0 := fun k => by simp [t, Nat.choose_succ_self]
  have h_middle : ∀ (k i : ℕ), i ∈ range (k + 1) →
      t (k + 1) (i + 1) = x * t k i + y * t k (i + 1) := by
    intro k i hi
    have hle : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [t, Nat.choose_succ_succ, Nat.cast_add, mul_add]
    congr 1
    · rw [pow_succ x, Nat.succ_sub_succ]; ring
    · by_cases heq : i = k
      · simp [heq, Nat.choose_succ_self]
      · rw [Nat.succ_sub (Nat.lt_of_le_of_ne hle heq), pow_succ y]; ring
  induction n with
  | zero => simp [t]
  | succ n ih =>
    rw [sum_range_succ', h_first, sum_congr rfl (h_middle n), sum_add_distrib, add_assoc,
      pow_succ' (x + y), ih, add_mul, mul_sum, mul_sum]
    congr 1
    rw [sum_range_succ', sum_range_succ, h_first, h_last, mul_zero, add_zero, pow_succ' y]

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics `zify`, `norm_cast`, and `omega`
-/
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  rw [binomial_choose]
  have hIcc : Icc (0:ℤ) ↑n = (range (n+1)).map Nat.castEmbedding := by
    ext x; simp [mem_Icc, mem_range, Nat.castEmbedding]; constructor
    · intro ⟨h1, h2⟩; exact ⟨x.toNat, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩; omega
  rw [hIcc, sum_map]
  apply sum_congr rfl
  intro m hm
  simp [mem_range] at hm
  have hm' : m ≤ n := by omega
  rw [Nat.choose_eq_factorial_div_factorial hm']
  simp only [Nat.castEmbedding_apply, Int.toNat_natCast]
  rw [show (↑n - (↑m : ℤ)).toNat = n - m from by omega]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hm') (by positivity)]
  rw [show (↑n : ℤ) - (↑m : ℤ) = ↑(n - m) from by omega]
  simp [zpow_natCast]
  ring

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  suffices hs : ∀ S : Finset X,
      Filter.atTop.Tendsto (fun n ↦ ∑ x ∈ S, a x n) (nhds (∑ x ∈ S, L x)) from hs univ
  intro S
  induction S using Finset.induction_on with
  | empty =>
    simp only [finite_series_of_empty]
    exact tendsto_const_nhds
  | @insert x₀ S hx₀ ih =>
    have hdisj : Disjoint ({x₀} : Finset X) S := disjoint_singleton_left.mpr hx₀
    simp_rw [insert_eq, finite_series_of_disjoint_union hdisj, finite_series_of_singleton]
    exact (h x₀).add ih

/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {X S : Type*} [Fintype X] [Fintype S]
    (E : X → Finset S)
    (disj : ∀ i j : X, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  have huniv : (univ : Finset S) = (univ : Finset X).biUnion E := by
    ext s; simp [mem_biUnion]; exact cover s
  conv_lhs => rw [show ∑ s, f s = ∑ s ∈ (univ : Finset S), f s from rfl, huniv]
  suffices h : ∀ T : Finset X, ∑ s ∈ T.biUnion E, f s = ∑ i ∈ T, ∑ s ∈ E i, f s from
    h Finset.univ
  intro T
  induction T using Finset.induction_on with
  | empty => simp
  | @insert x₀ T hx₀ ih =>
    rw [biUnion_insert, finite_series_of_disjoint_union ?_, sum_insert hx₀, ih]
    exact (disjoint_biUnion_right ..).mpr fun j hj => disj x₀ j (fun h => hx₀ (h ▸ hj))

/-- Exercise 7.1.7. Uses `Fin m` (so `aᵢ < m`) instead of the book's `aᵢ ≤ m`;
  the bound is baked into the type, and `<` replaces `≤` to match the 0-indexed shift. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  simp_rw [Set.toFinset_setOf]
  have h : ∀ i, (a i : ℕ) = (filter (· < a i) univ).card := by
    intro i
    rw [show filter (· < a i) univ = Iio (a i) from by ext; simp [mem_filter, mem_Iio]]
    exact (Fin.card_Iio _).symm
  simp_rw [h, card_eq_sum_ones, sum_filter]
  exact sum_comm

end Finset
