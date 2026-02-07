import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals `EReal`, particularly with regard to the supremum
  operation `sSup` and infimum operation `sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by simp [lt_iff]; exact real_neq_infty 3


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := by simp


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by rfl

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by
  by_cases h : x.IsFinite
  . obtain ⟨ x', rfl ⟩ := h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      simp only [EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff, gt_iff_lt]
      exact lt_trichotomy x' y'
    . rw [← infinite_iff_not_finite] at h'
      obtain rfl | rfl := h' <;> simp
  . rw [← infinite_iff_not_finite] at h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      obtain rfl | rfl := h <;> simp
    . rw [← infinite_iff_not_finite] at h'
      obtain rfl | rfl := h <;> obtain rfl | rfl := h' <;> simp

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by
  push_neg
  by_cases h : x.IsFinite
  . obtain ⟨ x', rfl ⟩ := h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      simp only [EReal.coe_lt_coe_iff, ne_eq, EReal.coe_eq_coe_iff]
      intro h
      exact ne_of_lt h
    . rw [← infinite_iff_not_finite] at h'
      obtain rfl | rfl := h' <;> simp
  . rw [← infinite_iff_not_finite] at h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      obtain rfl | rfl := h <;> simp
    . rw [← infinite_iff_not_finite] at h'
      intro hlt
      obtain rfl | rfl := h <;> obtain rfl | rfl := h' <;> simp at hlt
      exact Ne.symm infty_neq_neg_infty

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by
  push_neg
  by_cases h : x.IsFinite
  . obtain ⟨ x', rfl ⟩ := h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      simp only [EReal.coe_lt_coe_iff, ne_eq, EReal.coe_eq_coe_iff]
      intro h
      exact ne_of_gt h
    . rw [← infinite_iff_not_finite] at h'
      obtain rfl | rfl := h' <;> simp
  . rw [← infinite_iff_not_finite] at h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      obtain rfl | rfl := h <;> simp
    . rw [← infinite_iff_not_finite] at h'
      intro hlt
      obtain rfl | rfl := h <;> obtain rfl | rfl := h' <;> simp at hlt
      exact infty_neq_neg_infty

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by
  push_neg
  by_cases h : x.IsFinite
  . obtain ⟨ x', rfl ⟩ := h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      simp only [EReal.coe_lt_coe_iff, EReal.coe_le_coe_iff]
      intro h
      exact le_of_lt h
    . rw [← infinite_iff_not_finite] at h'
      obtain rfl | rfl := h' <;> simp
  . rw [← infinite_iff_not_finite] at h
    by_cases h' : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := h'
      obtain rfl | rfl := h <;> simp
    . rw [← infinite_iff_not_finite] at h'
      intro hlt
      obtain rfl | rfl := h <;> obtain rfl | rfl := h' <;> simp at hlt
      exact OrderBot.bot_le ⊤

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  by_cases hx : x.IsFinite
  . obtain ⟨ x', rfl ⟩ := hx
    by_cases hy : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := hy
      by_cases hz : z.IsFinite
      . obtain ⟨ z', rfl ⟩ := hz
        simp_all
        exact Std.le_trans hxy hyz
      . rw [← infinite_iff_not_finite] at hz
        obtain rfl | rfl := hz <;> simp at hyz
        exact OrderTop.le_top _
    . rw [← infinite_iff_not_finite] at hy
      obtain rfl | rfl := hy <;> simp at hxy
      have : z = ⊤ := by exact eq_top_iff.mpr hyz
      subst z
      exact OrderTop.le_top _
  . rw [← infinite_iff_not_finite] at hx
    obtain rfl | rfl := hx <;> simp at hxy
    . subst y
      exact hyz
    . exact OrderBot.bot_le z

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  by_cases hx : x.IsFinite
  . obtain ⟨ x', rfl ⟩ := hx
    by_cases hy : y.IsFinite
    . obtain ⟨ y', rfl ⟩ := hy
      simp at hxy ⊢
      exact hxy
    . rw [← infinite_iff_not_finite] at hy
      obtain rfl | rfl := hy <;> simp at hxy
      exact OrderBot.bot_le _
  . rw [← infinite_iff_not_finite] at hx
    obtain rfl | rfl := hx <;> simp at hxy
    . subst y
      rfl
    . simp only [neg_bot, le_top]

/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . simp at hb
  simpa

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]
  constructor
  . intro h a ha; specialize h (-a) (by simp [ha]); grind [neg_le_neg_iff]
  grind [EReal.le_neg_of_le_neg]

theorem EReal.inf_of_infty_mem {E: Set EReal} : sInf E = sInf (E \ {⊤}) := by
  exact Eq.symm (sInf_diff_singleton_top E)

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

abbrev Example_6_2_7' : Set ℝ := { x | ∃ n:ℕ, x = -((n+1):ℝ)}

theorem Example_6_2_7'_bounded : BddAbove Example_6_2_7' := by
  use 0
  intro x hx
  obtain ⟨ n, rfl ⟩ := hx
  simp
  linarith

theorem Example_6_2_7'_nonempty : Example_6_2_7'.Nonempty := by
  use -1
  simp

theorem Example_6_2_7'_sup : sSup Example_6_2_7' = -1 := by
  apply le_antisymm
  . apply csSup_le Example_6_2_7'_nonempty
    intro x hx
    obtain ⟨ n, rfl ⟩ := hx
    linarith
  . apply le_csSup Example_6_2_7'_bounded
    use 0
    simp

theorem Example_6_2_7_eq : Example_6_2_7 \ {⊥} = (fun (x:Real) ↦ (x:EReal)) '' Example_6_2_7' := by
  ext x
  simp [Example_6_2_7, Example_6_2_7']
  constructor
  . intro h
    obtain ⟨ h1, h2 ⟩ := h
    obtain ⟨ n, rfl ⟩ := h1
    simp at h2
    use - n - 1
    simp
    constructor
    . use n
      grind
    . rw [neg_add]
      . right
        norm_cast
      . right
        norm_cast
  . intro h
    obtain ⟨ y, hy1, hy2 ⟩ := h
    obtain ⟨ n, rfl ⟩ := hy1
    constructor
    . use n
      rw [← hy2]
      simp
      rw [neg_add]
      . rw [add_comm]
        rfl
      . right
        norm_cast
      . right
        norm_cast
    . rw [← hy2]
      exact real_neq_neg_infty _

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  rw [show (-1:EReal) = (-1:ℝ) by rfl]
  rw [Example_6_2_7_eq, ← Example_6_2_7'_sup]
  apply EReal.sup_of_bounded_nonempty
  . exact Example_6_2_7'_bounded
  . exact Example_6_2_7'_nonempty

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  rw [show (⊥:EReal) = - ⊤ by rfl]
  simp only [Set.involutiveNeg, Set.union_singleton, Set.neg_insert, neg_bot, sSup_insert, le_top,
    sup_of_le_left, neg_top]

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  apply le_antisymm
  · -- sInf ≤ 0.9: the element at n=0 is 0.9
    exact sInf_le (show ((0.9:ℝ):EReal) ∈ Example_6_2_8 from ⟨0, by norm_num⟩)
  · -- 0.9 ≤ sInf: 0.9 is a lower bound (minimum of the set)
    apply le_sInf
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    -- 0.9 ≤ 1 - 10^(-n-1) because 10^(-n-1) ≤ 10^(-1) = 0.1
    exact_mod_cast show (0.9:ℝ) ≤ 1 - (10:ℝ)^(-(n:ℤ)-1) by
      have : (10:ℝ)^(-(n:ℤ)-1) ≤ (10:ℝ)^(-1:ℤ) := by
        gcongr
        · norm_num
        · omega
      norm_num at this
      linarith

example : sSup Example_6_2_8 = 1 := by
  apply le_antisymm
  · -- sSup ≤ 1: every element < 1 since 10^(-n-1) > 0
    apply sSup_le
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact_mod_cast show 1 - (10:ℝ)^(-(n:ℤ)-1) ≤ (1:ℝ) by
      linarith [zpow_pos (show (0:ℝ) < 10 by norm_num) (-(n:ℤ)-1)]
  · -- 1 ≤ sSup: if sSup < 1, find an element above sSup
    by_contra hlt; push_neg at hlt
    -- sSup ≥ 0.9 (an element), so sSup is a finite real
    have hge : ((0.9:ℝ):EReal) ≤ sSup Example_6_2_8 :=
      le_sSup (show ((0.9:ℝ):EReal) ∈ Example_6_2_8 from ⟨0, by norm_num⟩)
    obtain ⟨m, hm⟩ | htop | hbot := EReal.def (sSup Example_6_2_8)
    · -- sSup = ↑m with m < 1
      rw [← hm] at hlt hge
      norm_cast at hlt hge
      -- Find k with (10⁻¹)^k < 1 - m, then the k-th element exceeds m
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - m by linarith) (show (10:ℝ)⁻¹ < 1 by norm_num)
      have hconv : (10:ℝ)^(-(k:ℤ)-1) = (10⁻¹)^(k+1) := by
        rw [show -(k:ℤ)-1 = -(↑(k+1) : ℤ) from by omega, zpow_neg, zpow_natCast, inv_pow]
      have helem : (10:ℝ)^(-(k:ℤ)-1) < 1 - m := calc
        (10:ℝ)^(-(k:ℤ)-1) = (10⁻¹)^(k+1) := hconv
        _ ≤ (10⁻¹)^k := pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ < 1 - m := hk
      have hmem : (↑(1 - (10:ℝ)^(-(k:ℤ)-1)) : EReal) ∈ Example_6_2_8 := ⟨k, rfl⟩
      have hle : (↑(1 - (10:ℝ)^(-(k:ℤ)-1)) : EReal) ≤ ↑m := by rw [hm]; exact le_sSup hmem
      simp only [EReal.coe_le_coe_iff] at hle
      linarith
    · rw [htop] at hlt; simp at hlt
    · rw [hbot] at hge; exact absurd hge (not_le_of_gt (bot_lt_coe _))

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  apply le_antisymm
  . apply csInf_le
    . use 1
      intro x hx
      obtain ⟨n, rfl⟩ := hx
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      norm_cast
      linarith
    use 0
    norm_cast
  . apply le_csInf
    . use 1
      use 0
      norm_cast
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    norm_cast
    linarith

example : sSup Example_6_2_9 = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp at hb
    obtain ⟨ n, hn ⟩ := hb
    unfold Example_6_2_9
    obtain ⟨ m, hm ⟩ := exists_nat_gt y
    use m + 1
    constructor
    . use m
    . norm_cast
      suffices y < (m:ℝ) + 1 by
        have hmnorm : ((m + 1:ℕ) : ℝ) = (m:ℝ) + 1 := by exact Nat.cast_add_one m
        rwa [hmnorm]
      linarith
  . simp at hb
  . unfold Example_6_2_9
    use 1
    constructor
    . use 0
      simp
    . norm_cast

example : sInf (∅ : Set EReal) = ⊤ := by
  rw [inf_eq_neg_sup]
  simp only [Set.neg_empty, sSup_empty, neg_bot]

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  . intro h
    by_contra hnon
    obtain ⟨ x, hx ⟩ := Set.nonempty_iff_ne_empty.mpr hnon
    have h1: x ≤ sSup E := by exact CompleteLattice.le_sSup E x hx
    have h2: sInf E ≤ x := by exact CompleteSemilatticeInf.sInf_le E x hx
    have : sInf E ≤ sSup E := by exact h2.trans h1
    exact not_lt.mpr this h
  . intro h
    subst h
    simp

-- Helper: when ⊤ ∉ E, the non-⊥ part of E is the image of a real-valued set
private theorem EReal.diff_bot_eq_image (E: Set EReal) (htop: ⊤ ∉ E) :
    E \ {⊥} = (fun y:ℝ => (y:EReal)) '' { y : ℝ | (y:EReal) ∈ E } := by
  ext z
  simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq]
  constructor
  . intro ⟨hz, hbot⟩
    obtain ⟨y, rfl⟩ | rfl | rfl := EReal.def z
    . exact ⟨y, hz, rfl⟩
    . exact absurd hz htop
    . exact absurd rfl hbot
  . rintro ⟨y, hy, rfl⟩
    exact ⟨hy, real_neq_neg_infty y⟩

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := by
  obtain ⟨ r, rfl ⟩ | rfl | rfl := EReal.def x
  . -- x is a real number r
    by_cases htop : ⊤ ∈ E
    . rw [sup_of_infty_mem htop]; exact le_top
    . rw [sup_of_neg_infty_mem, diff_bot_eq_image E htop]
      set E' := { y : ℝ | (y:EReal) ∈ E }
      have hr : r ∈ E' := hx
      by_cases hbdd : BddAbove E'
      . rw [sup_of_bounded_nonempty hbdd ⟨r, hr⟩]
        exact_mod_cast le_csSup hbdd hr
      . rw [sup_of_unbounded_nonempty hbdd ⟨r, hr⟩]
        exact le_top
  . -- x = ⊤
    rw [sup_of_infty_mem hx]
  . -- x = ⊥
    exact bot_le

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : sInf E ≤ x := by
  rw [inf_eq_neg_sup]
  have h1 : -x ∈ -E := Set.neg_mem_neg.mpr hx
  have h2 : -x ≤ sSup (-E) := mem_le_sup (-E) h1
  exact le_of_le_of_eq (neg_of_lt h2) (neg_neg x)

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := by
  obtain ⟨ m, rfl ⟩ | rfl | rfl := EReal.def M
  . -- M = (m : ℝ), so ⊤ ∉ E
    have htop : ⊤ ∉ E := fun h => absurd (hM h) (not_le.mpr (coe_lt_top m))
    rw [sup_of_neg_infty_mem, diff_bot_eq_image E htop]
    set E' := { y : ℝ | (y:EReal) ∈ E }
    by_cases hne : E'.Nonempty
    . have hbdd : BddAbove E' := ⟨m, fun y hy => by exact_mod_cast hM hy⟩
      rw [sup_of_bounded_nonempty hbdd hne]
      exact_mod_cast csSup_le hne (fun y hy => by exact_mod_cast hM hy)
    . rw [Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne), sup_of_empty]
      exact bot_le
  . -- M = ⊤
    exact le_top
  . -- M = ⊥, so E ⊆ {⊥}
    rw [sup_of_neg_infty_mem]
    have : E \ {⊥} = ∅ := by
      ext x; simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hx, hbot⟩; exact hbot (le_bot_iff.mp (hM hx))
    rw [this, sup_of_empty]

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_upper (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M := by
  rw [inf_eq_neg_sup]
  have hM' : -M ∈ upperBounds (-E) := by
    intro y hy
    have hy' : -y ∈ E := by rwa [← Set.neg_mem_neg, neg_neg]
    exact le_of_eq_of_le (neg_neg y).symm (neg_of_lt (hM hy'))
  exact le_of_eq_of_le (neg_neg M).symm (neg_of_lt (sup_le_upper (-E) hM'))

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib extended reals.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  intro x y h
  cases x <;> cases y <;> simp [toEReal] at h ⊢
  . exact Real.equivR.injective h

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by
  intro y
  obtain ⟨ r, hr ⟩ | rfl | rfl := EReal.def y
  . have := Real.equivR.surjective r
    obtain ⟨ x, hx ⟩ := this
    use ExtendedReal.real x
    simp [toEReal, hx]
    exact hr
  . use ExtendedReal.infty
  . use ExtendedReal.neg_infty

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal :=
  Equiv.ofBijective toEReal
    ⟨ Chapter5.ExtendedReal.coe_inj, Chapter5.ExtendedReal.coe_surj ⟩
