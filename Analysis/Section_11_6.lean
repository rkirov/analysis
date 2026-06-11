import Mathlib.Tactic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Analysis.Section_9_8
import Analysis.Section_11_5

/-!
# Analysis I, Section 11.6: Riemann integrability of monotone functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of monotone functions.

-/

namespace Chapter11
open Chapter9 BoundedInterval

set_option maxHeartbeats 300000 in
/-- Proposition 11.6.1 -/
theorem integ_of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is adapted from the structure of the original text.
  by_cases hab : 0 < b-a
  swap
  . apply (integ_on_subsingleton _).1; rw [←BoundedInterval.length_of_subsingleton]; aesop
  have hbound := BddOn.of_monotone hf
  set I := Icc a b
  have hab' : a ≤ b := by linarith
  have (ε:ℝ) (hε: 0 < ε) : upper_integral f I - lower_integral f I ≤ ((f b - f a) * (b-a)) *ε := by
    choose N hN using exists_nat_gt (1/ε)
    have hNpos : 0 < N := by rify; linarith [show 0 < 1/ε by positivity]
    set δ := (b-a)/N
    have hδpos : 0 < δ := by positivity
    have hbeq : b = a + δ*N := by simp [δ]; field_simp; linarith
    set e : ℕ ↪ BoundedInterval := {
      toFun j := Ico (a + δ*j) (a + δ*(j+1))
      inj' j k hjk := by simp at hjk; obtain _ | _ := hjk <;> linarith
    }
    set P : Partition I := {
      intervals := insert (Icc b b) (.map e (.range N))
      exists_unique := by
        intro x hx; simp; by_cases hb: x = b
        . apply ExistsUnique.intro (Icc b b)
          . simp [hb, mem_iff]
          rintro J ⟨ rfl | ⟨ j, hA, rfl ⟩, hJb ⟩; rfl
          simp [e, mem_iff, hb, hbeq] at hJb
          replace hJb := hJb.2
          rw [mul_lt_mul_iff_of_pos_left hδpos] at hJb
          norm_cast at hJb; linarith
        simp [I, mem_iff] at hx
        set j := ⌊ (x-a)/δ ⌋₊
        have hxa : 0 ≤ x-a := by linarith
        have hxaδ : 0 ≤ (x-a)/δ := by positivity
        have hxb : x < b := lt_of_le_of_ne hx.2 hb
        have hxj : x ∈ e j := by
          simp [e, mem_iff, j]; split_ands
          . calc
              _ ≤ a + δ * ((x-a)/δ) := by gcongr; grind [Nat.floor_le]
              _ = x := by grind
          calc
            _ = a + δ * ((x-a)/δ) := by field_simp; linarith
            _ < _ := by gcongr; apply Nat.lt_floor_add_one
        apply ExistsUnique.intro (e j)
        . refine ⟨ ?_, hxj ⟩; right; use j; simp [j, Nat.floor_lt hxaδ, div_lt_iff₀' hδpos]; linarith
        rintro J ⟨ rfl | ⟨ k, hk, rfl ⟩, hxJ ⟩
        . simp [mem_iff] at hxJ; grind
        simp [mem_iff, e] at hxJ hxj
        obtain hjk | rfl | hjk := lt_trichotomy j k
        . replace hjk : δ*((j:ℝ)+1) ≤ δ*(k:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
          linarith
        . rfl
        replace hjk : δ*((k:ℝ)+1) ≤ δ*(j:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
        linarith
      contains J hJ := by
        simp at hJ; obtain rfl | ⟨ j, hj, rfl ⟩ := hJ <;> simp [subset_iff, e, I]
        . linarith
        apply Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc _ _)
        . simp; positivity
        simp [hbeq]; gcongr; norm_cast
    }
    have hup := calc
      upper_integral f I ≤ ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ := upper_integ_le_upper_sum hbound P
      _ = ∑ j ∈ .range N, (sSup (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply csSup_le
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have : a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ (by order) <;> simp [I, hδj1, this]; grind
    have hdown := calc
      lower_integral f I ≥ ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ :=
        lower_integ_ge_lower_sum hbound P
      _ = ∑ j ∈ .range N, (sInf (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≥ ∑ j ∈ .range N, f (a + δ*j) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply le_csInf
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have hajb': a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply_rules [hf] <;> simp [I, hδj] <;> grind
    calc
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ - ∑ j ∈ .range N, f (a + δ*j) * δ := by linarith
      _ = (f b - f a) * δ := by
        rw [←Finset.sum_sub_distrib]
        have := Finset.sum_range_sub (fun n ↦ f (a + δ*n) * δ) N
        simp only [Nat.cast_add, Nat.cast_one] at this
        convert this using 1; simp [hbeq]; ring
      _ ≤ _ := by
        have : 0 ≤ f b - f a := by simp; apply hf <;> simp [I, hab']
        simp [mul_assoc, δ]; gcongr
        rw [div_le_iff₀', mul_comm, mul_assoc]
        nth_rewrite 1 [←mul_one (b-a)]
        gcongr; rw [←div_le_iff₀']; linarith
        all_goals positivity
  refine ⟨ hbound, ?_ ⟩
  observe low_le_up : lower_integral f I ≤ upper_integral f I
  linarith [nonneg_of_le_const_mul_eps this]


/-- Proposition 11.6.1 -/
theorem integ_of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  rw [←neg_neg f]; apply (integ_of_monotone _).neg.1; convert hf.neg using 1

/-- Corollary 11.6.3 / Exercise 11.6.1 -/
theorem integ_of_bdd_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: MonotoneOn f I) : IntegrableOn f I := by
  -- Instead of the ε-of-room argument of Proposition 11.5.3, extend `f` to a monotone
  -- function `g` on all of `[a,b]` (sending any missing endpoint to the inf/sup of the
  -- image), integrate `g` by Proposition 11.6.1, and restrict back to `I`.
  classical
  obtain ⟨M, hM⟩ := hbound
  have habove : BddAbove (f '' I) := ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hM x hx)).2⟩
  have hbelow : BddBelow (f '' I) := ⟨-M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hM x hx)).1⟩
  set g : ℝ → ℝ := fun x ↦ if x ∈ I then f x
    else if x ≤ I.a then sInf (f '' I) else sSup (f '' I) with hg
  have hIoo : Set.Ioo I.a I.b ⊆ (I:Set ℝ) := by
    have h := (subset_iff _ _).mp I.Ioo_subset; rwa [set_Ioo] at h
  have hIcc : (I:Set ℝ) ⊆ Set.Icc I.a I.b := by
    have h := (subset_iff _ _).mp I.subset_Icc; rwa [set_Icc] at h
  have hend : ∀ z ∈ Set.Icc I.a I.b, z ∉ I → z = I.a ∨ z = I.b := by
    intro z hz hzI
    by_contra h
    push_neg at h
    exact hzI (hIoo ⟨lt_of_le_of_ne hz.1 (Ne.symm h.1), lt_of_le_of_ne hz.2 h.2⟩)
  have hg_mono : MonotoneOn g (Set.Icc I.a I.b) := by
    intro x hx y hy hxy
    by_cases hxI : x ∈ I <;> by_cases hyI : y ∈ I
    · simpa [hg, hxI, hyI] using hf hxI hyI hxy
    · obtain rfl | rfl := hend y hy hyI
      · have : x = I.a := le_antisymm hxy hx.1
        exact absurd (this ▸ hxI) hyI
      · have hab : ¬ I.b ≤ I.a := by
          intro h
          have : x = I.b := le_antisymm (hIcc hxI).2 (h.trans hx.1)
          exact absurd (this ▸ hxI) hyI
        simp only [hg, if_pos hxI, if_neg hyI, if_neg hab]
        exact le_csSup habove ⟨x, hxI, rfl⟩
    · obtain rfl | rfl := hend x hx hxI
      · simp only [hg, if_neg hxI, if_pos hyI, if_pos (le_refl I.a)]
        exact csInf_le hbelow ⟨y, hyI, rfl⟩
      · have : y = I.b := le_antisymm (hIcc hyI).2 hxy
        exact absurd (this ▸ hyI) hxI
    · obtain rfl | rfl := hend x hx hxI <;> obtain rfl | rfl := hend y hy hyI
      · exact le_rfl
      · by_cases hab : I.b ≤ I.a
        · simp [hg, hxI, hyI, hab]
        · have hne : (f '' I).Nonempty :=
            ⟨f ((I.a + I.b)/2), (I.a + I.b)/2,
              hIoo ⟨by linarith [lt_of_not_ge hab], by linarith [lt_of_not_ge hab]⟩, rfl⟩
          simp only [hg, if_neg hxI, if_neg hyI, if_pos (le_refl I.a), if_neg hab]
          exact csInf_le_csSup hne hbelow habove
      · simp [hg, hxI, hyI, hxy]
      · exact le_rfl
  have hgI : IntegrableOn g I := (integ_of_monotone hg_mono).mono' I.subset_Icc
  have hEq : Set.EqOn f g I := fun x hx ↦ (if_pos hx).symm
  exact ⟨⟨M, hM⟩, by rw [lower_integral_congr hEq, upper_integral_congr hEq]; exact hgI.2⟩

theorem integ_of_bdd_antitone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: AntitoneOn f I) : IntegrableOn f I := by
  have hbound' : BddOn (-f) I := by
    obtain ⟨M, hM⟩ := hbound
    exact ⟨M, fun x hx ↦ by simpa using hM x hx⟩
  rw [←neg_neg f]
  exact (integ_of_bdd_monotone hbound' hf.neg).neg.1

/-- The unit-interval Riemann sums sandwich the integral of an antitone function on the
interval from 0 to K, by telescoping over the unit pieces via joins and bounding each piece
by constants. -/
lemma sum_sandwich_integ_of_antitone {f:ℝ → ℝ} (hf: AntitoneOn f (.Ici 0)) (K:ℕ) :
    (∑ j ∈ Finset.range K, f ((j:ℝ)+1)) ≤ integ f (Icc 0 (K:ℝ))
    ∧ integ f (Icc 0 (K:ℝ)) ≤ ∑ j ∈ Finset.range K, f (j:ℝ) := by
  have hint : ∀ x:ℝ, IntegrableOn f (Icc 0 x) := fun x ↦
    integ_of_antitone (hf.mono (by rw [set_Icc]; exact Set.Icc_subset_Ici_self))
  have h00 : integ f (Icc 0 (0:ℝ)) = 0 :=
    integ_of_subsingleton (BoundedInterval.length_of_subsingleton.mpr (by simp [length]))
  have key : ∀ K:ℕ, integ f (Icc 0 ((K:ℝ)+1)) = integ f (Icc 0 (K:ℝ)) + integ f (Ioc (K:ℝ) ((K:ℝ)+1))
      ∧ f ((K:ℝ)+1) ≤ integ f (Ioc (K:ℝ) ((K:ℝ)+1)) ∧ integ f (Ioc (K:ℝ) ((K:ℝ)+1)) ≤ f (K:ℝ) := by
    intro K
    have h0K : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    obtain ⟨-, hIoc, heq⟩ :=
      IntegrableOn.join (join_Icc_Ioc h0K (by linarith)) (hint ((K:ℝ)+1))
    have hmaj : MajorizesOn (fun _ ↦ f (K:ℝ)) f (Ioc (K:ℝ) ((K:ℝ)+1)) := by
      intro x hx
      rw [set_Ioc] at hx
      exact hf (Set.mem_Ici.mpr h0K) (Set.mem_Ici.mpr (h0K.trans hx.1.le)) hx.1.le
    have hmin : MajorizesOn f (fun _ ↦ f ((K:ℝ)+1)) (Ioc (K:ℝ) ((K:ℝ)+1)) := by
      intro x hx
      rw [set_Ioc] at hx
      exact hf (Set.mem_Ici.mpr (h0K.trans hx.1.le)) (Set.mem_Ici.mpr (by linarith)) hx.2
    have hub := IntegrableOn.mono hIoc (IntegrableOn.const (f (K:ℝ)) _).1 hmaj
    have hlb := IntegrableOn.mono (IntegrableOn.const (f ((K:ℝ)+1)) _).1 hIoc hmin
    rw [(IntegrableOn.const (f (K:ℝ)) _).2] at hub
    rw [(IntegrableOn.const (f ((K:ℝ)+1)) _).2] at hlb
    have hlen : |Ioc (K:ℝ) ((K:ℝ)+1)|ₗ = 1 := by simp [length]
    rw [hlen, mul_one] at hub hlb
    exact ⟨heq, hlb, hub⟩
  induction K with
  | zero => simp [h00]
  | succ K ih =>
    obtain ⟨heq, hlb, hub⟩ := key K
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    exact ⟨by linarith [ih.1], by linarith [ih.2]⟩

/-- Proposition 11.6.4 (Integral test) -/
theorem summable_iff_integ_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
  (hf: AntitoneOn f (.Ici 0)) :
  Summable (fun n:ℕ ↦ f n) ↔ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  have hint : ∀ x:ℝ, IntegrableOn f (Icc 0 x) := fun x ↦
    integ_of_antitone (hf.mono (by rw [set_Icc]; exact Set.Icc_subset_Ici_self))
  have h00 : integ f (Icc 0 (0:ℝ)) = 0 :=
    integ_of_subsingleton (BoundedInterval.length_of_subsingleton.mpr (by simp [length]))
  have hsandwich := sum_sandwich_integ_of_antitone hf
  constructor
  · intro hsum
    refine ⟨∑' n:ℕ, f n, fun N hN ↦ ?_⟩
    set K := ⌈N⌉₊
    obtain ⟨-, hIoc, heq⟩ :=
      IntegrableOn.join (join_Icc_Ioc hN (Nat.le_ceil N)) (hint (K:ℝ))
    have hIoc_nonneg : 0 ≤ integ f (Ioc N (K:ℝ)) := by
      apply hIoc.nonneg
      intro x hx
      rw [mem_iff, set_Ioc] at hx
      exact hnon x (hN.trans hx.1.le)
    have htail : (∑ j ∈ Finset.range K, f (j:ℝ)) ≤ ∑' n:ℕ, f n :=
      hsum.sum_le_tsum _ (fun i _ ↦ hnon i (Nat.cast_nonneg i))
    linarith [(hsandwich K).2]
  · rintro ⟨M, hM⟩
    have hM0 : 0 ≤ M := by have := hM 0 le_rfl; linarith [h00]
    apply summable_of_sum_range_le (c := f 0 + M) (fun n ↦ hnon n (Nat.cast_nonneg n))
    intro n
    cases n with
    | zero => simpa using add_nonneg (hnon 0 le_rfl) hM0
    | succ n =>
      rw [Finset.sum_range_succ']
      have h2 := hM (n:ℝ) (Nat.cast_nonneg n)
      push_cast
      linarith [(hsandwich n).1]

-- Exercise 11.6.2: Formulate a reasonable notion of a piecewise monotone function, and then
-- show that all bounded piecewise monotone functions are Riemann integrable.
def PiecewiseMonotoneOn (f:ℝ → ℝ) (I:BoundedInterval) : Prop :=
  ∃ (P : Partition I), ∀ J ∈ P.intervals, MonotoneOn f J

theorem integ_of_piecewise_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: PiecewiseMonotoneOn f I) : IntegrableOn f I := by
  -- Same structure as Proposition 11.5.6: `f` agrees on `I` with the sum over the partition
  -- of the extensions by zero of its restrictions, and each summand is integrable.
  obtain ⟨P, hP⟩ := hf
  classical
  let g : BoundedInterval → (ℝ → ℝ) := fun J ↦ fun x ↦ if x ∈ J then f x else 0
  have hfsum : Set.EqOn f (fun x ↦ ∑ J ∈ P.intervals, g J x) I := by
    intro x hx
    obtain ⟨J₀, ⟨hJ₀, hxJ₀⟩, huniq⟩ := P.exists_unique x hx
    show f x = ∑ J ∈ P.intervals, g J x
    rw [Finset.sum_eq_single J₀]
    · exact (if_pos hxJ₀).symm
    · exact fun J hJ hne ↦ if_neg (fun h ↦ hne (huniq J ⟨hJ, h⟩))
    · exact fun h ↦ absurd hJ₀ h
  have hfint : ∀ J ∈ P.intervals, IntegrableOn f J := by
    intro J hJ
    obtain ⟨M, hM⟩ := hbound
    exact integ_of_bdd_monotone ⟨M, fun x hx ↦ hM x (P.contains J hJ x hx)⟩ (hP J hJ)
  have hgint : ∀ J ∈ P.intervals, IntegrableOn (g J) I :=
    fun J hJ ↦ IntegrableOn.of_extend (P.contains J hJ) (hfint J hJ)
  have hsum : ∀ s : Finset BoundedInterval, (∀ J ∈ s, IntegrableOn (g J) I) →
      IntegrableOn (fun x ↦ ∑ J ∈ s, g J x) I := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simpa using (IntegrableOn.const 0 I).1
    | insert J s hJs ih =>
      intro hmem
      have h1 := hmem J (Finset.mem_insert_self J s)
      have h2 := ih fun K hK ↦ hmem K (Finset.mem_insert_of_mem hK)
      simp only [Finset.sum_insert hJs]
      exact (IntegrableOn.add h1 h2).1
  exact ⟨hbound, by
    rw [lower_integral_congr hfsum, upper_integral_congr hfsum]
    exact (hsum P.intervals hgint).2⟩

/-- Integrability transfers along agreement on the interval. -/
theorem IntegrableOn.congr' {I: BoundedInterval} {f g:ℝ → ℝ} (h: Set.EqOn f g I)
  (hg: IntegrableOn g I) : IntegrableOn f I ∧ integ f I = integ g I := by
  obtain ⟨⟨M, hM⟩, heq⟩ := hg
  exact ⟨⟨⟨M, fun x hx ↦ by rw [h hx]; exact hM x hx⟩,
    by rw [lower_integral_congr h, upper_integral_congr h]; exact heq⟩, integ_congr h⟩

/-- Combining integrability across a join: the converse direction of Theorem 11.4.1(h). -/
theorem IntegrableOn.of_join {I J K: BoundedInterval} (hIJK: K.joins I J) {f: ℝ → ℝ}
  (hI: IntegrableOn f I) (hJ: IntegrableOn f J) :
  IntegrableOn f K ∧ integ f K = integ f I + integ f J := by
  classical
  have hIK : I ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by rw [BoundedInterval.subset_iff, hIJK.2.1]; exact Set.subset_union_right
  have key := (IntegrableOn.of_extend hIK hI).add (IntegrableOn.of_extend hJK hJ)
  rw [IntegrableOn.of_extend' hIK hI, IntegrableOn.of_extend' hJK hJ] at key
  have hEqOn : Set.EqOn f
      ((fun x ↦ if x ∈ I then f x else 0) + (fun x ↦ if x ∈ J then f x else 0)) K := by
    intro x hx
    have hxIJ : x ∈ (I:Set ℝ) ∪ (J:Set ℝ) := by rw [←hIJK.2.1]; exact hx
    simp only [Pi.add_apply]
    rcases hxIJ with hxI | hxJ
    · have hmI : x ∈ I := hxI
      have hxnJ : x ∉ J := fun hJ' ↦
        (Set.mem_empty_iff_false x).mp (hIJK.1 ▸ Set.mem_inter hxI hJ')
      rw [if_pos hmI, if_neg hxnJ, add_zero]
    · have hmJ : x ∈ J := hxJ
      have hxnI : x ∉ I := fun hI' ↦
        (Set.mem_empty_iff_false x).mp (hIJK.1 ▸ Set.mem_inter hI' hxJ)
      rw [if_neg hxnI, if_pos hmJ, zero_add]
  obtain ⟨hint, hcongr⟩ := IntegrableOn.congr' hEqOn key.1
  exact ⟨hint, by rw [hcongr, key.2]⟩

/-- The indicator of the integers is integrable on the interval from 0 to K with vanishing
integral: it is zero off the integer singletons, which carry no length. -/
lemma integ_int_indicator (K:ℕ) :
    IntegrableOn (fun (x:ℝ) ↦ if ⌊x⌋ = x then 1 else 0) (Icc 0 (K:ℝ)) ∧
    integ (fun (x:ℝ) ↦ if ⌊x⌋ = x then 1 else 0) (Icc 0 (K:ℝ)) = 0 := by
  set g : ℝ → ℝ := fun x ↦ if ⌊x⌋ = x then 1 else 0 with hg
  induction K with
  | zero => exact integ_on_subsingleton (by simp [length])
  | succ K ih =>
    push_cast
    have hkk1 : (K:ℝ) < (K:ℝ)+1 := by linarith
    have hIoo : Set.EqOn g (fun _ ↦ 0) (Ioo (K:ℝ) ((K:ℝ)+1)) := by
      intro x hx
      rw [set_Ioo] at hx
      have hfl : ⌊x⌋ = (K:ℤ) := by
        rw [Int.floor_eq_iff]
        push_cast
        exact ⟨hx.1.le, hx.2⟩
      have hne : (⌊x⌋:ℝ) ≠ x := by rw [hfl]; push_cast; exact ne_of_lt hx.1
      show (if (⌊x⌋:ℝ) = x then (1:ℝ) else 0) = 0
      rw [if_neg hne]
    have hIooInt := IntegrableOn.congr' hIoo (IntegrableOn.const 0 _).1
    have hIooEq : integ g (Ioo (K:ℝ) ((K:ℝ)+1)) = 0 := by
      rw [hIooInt.2, (IntegrableOn.const 0 _).2, zero_mul]
    have hsing := integ_on_subsingleton (f := g) (I := Icc ((K:ℝ)+1) ((K:ℝ)+1)) (by simp [length])
    have hpiece := IntegrableOn.of_join (join_Ioo_Icc hkk1 le_rfl) hIooInt.1 hsing.1
    have hstep := IntegrableOn.of_join (join_Icc_Ioc (Nat.cast_nonneg K) hkk1.le) ih.1 hpiece.1
    refine ⟨hstep.1, ?_⟩
    rw [hstep.2, hpiece.2, ih.2, hIooEq, hsing.2]
    norm_num

/-- Exercise 11.6.4 -/
example : ∃ (f:ℝ → ℝ), (∀ x ≥ 0, f x ≥ 0) ∧ Summable (fun n:ℕ ↦ f n) ∧ ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  use (fun (x:ℝ) ↦ if ⌊x⌋ = x then 0 else 1)
  refine ⟨fun x _ ↦ by by_cases h : (⌊x⌋:ℝ) = x <;> simp [h], ?_, ?_⟩
  · exact summable_zero.congr fun n ↦ by simp
  · rintro ⟨M, hM⟩
    -- the function is `1` minus the integer indicator, so its integral over `[0,K]` is `K`
    have heq : (fun (x:ℝ) ↦ if ⌊x⌋ = x then 0 else 1)
        = (fun _ ↦ (1:ℝ)) - (fun (x:ℝ) ↦ if ⌊x⌋ = x then 1 else 0) := by
      funext x; by_cases h : (⌊x⌋:ℝ) = x <;> simp [h]
    have hind := integ_int_indicator (⌈M⌉₊ + 1)
    have hconst := IntegrableOn.const 1 (Icc 0 ((⌈M⌉₊ + 1 : ℕ):ℝ))
    have hsub := hconst.1.sub hind.1
    have hlen : |Icc 0 ((⌈M⌉₊ + 1:ℕ):ℝ)|ₗ = ((⌈M⌉₊ + 1:ℕ):ℝ) := by
      simp [length, a, b]
      positivity
    specialize hM ((⌈M⌉₊ + 1 : ℕ):ℝ) (Nat.cast_nonneg _)
    rw [heq, hsub.2, hconst.2, hind.2, one_mul, sub_zero, hlen] at hM
    have := Nat.le_ceil M
    push_cast at hM
    linarith

example : ∃ (f:ℝ → ℝ), (∀ x ≥ 0, f x ≥ 0) ∧ ¬ Summable (fun n:ℕ ↦ f n) ∧ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  use (fun (x:ℝ) ↦ if ⌊x⌋ = x then 1 else 0)
  refine ⟨fun x _ ↦ by by_cases h : (⌊x⌋:ℝ) = x <;> simp [h], ?_, 0, fun N hN ↦ ?_⟩
  · intro h
    replace h : Summable (fun _:ℕ ↦ (1:ℝ)) := h.congr fun n ↦ by simp
    obtain ⟨n, hn⟩ := exists_nat_gt (∑' _:ℕ, (1:ℝ))
    have hsum := h.sum_le_tsum (Finset.range n) (fun _ _ ↦ zero_le_one)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
    linarith
  · -- the integral over `[0,N]` is squeezed between `0` and the vanishing integral over `[0,⌈N⌉]`
    have hind := integ_int_indicator ⌈N⌉₊
    obtain ⟨-, hIoc, heq⟩ := IntegrableOn.join (join_Icc_Ioc hN (Nat.le_ceil N)) hind.1
    have h0 : 0 ≤ integ (fun (x:ℝ) ↦ if ⌊x⌋ = x then 1 else 0) (Ioc N (⌈N⌉₊:ℝ)) :=
      hIoc.nonneg fun x _ ↦ by by_cases h : (⌊x⌋:ℝ) = x <;> simp [h]
    linarith [hind.2]

/-- Mathlib's interval integral over the interval from 1 to K+1 bounds the chapter integral
over the interval from 0 to K from below, by comparing both with the lower Riemann sum. -/
lemma intervalIntegral_le_integ_of_antitone {f:ℝ → ℝ} (hf: AntitoneOn f (.Ici 0)) (K:ℕ) :
    (∫ x in (1:ℝ)..(1+(K:ℕ)), f x) ≤ integ f (Icc 0 (K:ℝ)) := by
  have hanti : AntitoneOn f (Set.Icc (1:ℝ) (1+(K:ℕ))) :=
    hf.mono fun x hx ↦ Set.mem_Ici.mpr (by linarith [hx.1])
  refine hanti.integral_le_sum.trans
    (le_trans (le_of_eq ?_) (sum_sandwich_integ_of_antitone hf K).1)
  exact Finset.sum_congr rfl fun i _ ↦ by rw [add_comm]

/-- The chapter integral of a nonnegative antitone function over the interval from 0 to N is
bounded by {lit}`f 0` plus Mathlib's interval integral over the interval from 0 to K, whenever
N ≤ K+1, by comparing both with the upper Riemann sum. -/
lemma integ_le_intervalIntegral_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
    (hf: AntitoneOn f (.Ici 0)) {N:ℝ} (hN: N ≥ 0) (K:ℕ) (hNK: N ≤ (K:ℝ)+1) :
    integ f (Icc 0 N) ≤ f 0 + ∫ x in (0:ℝ)..(K:ℕ), f x := by
  have hint : IntegrableOn f (Icc 0 ((K:ℝ)+1)) :=
    integ_of_antitone (hf.mono (by rw [set_Icc]; exact Set.Icc_subset_Ici_self))
  obtain ⟨-, hIoc, heq⟩ := IntegrableOn.join (join_Icc_Ioc hN hNK) hint
  have hpc : 0 ≤ integ f (Ioc N ((K:ℝ)+1)) := by
    apply hIoc.nonneg
    intro x hx
    rw [mem_iff, set_Ioc] at hx
    exact hnon x (by linarith [hx.1])
  have hsand := (sum_sandwich_integ_of_antitone hf (K+1)).2
  rw [Finset.sum_range_succ'] at hsand
  have hanti : AntitoneOn f (Set.Icc (0:ℝ) (0+(K:ℕ))) :=
    hf.mono fun x hx ↦ Set.mem_Ici.mpr hx.1
  have hcomp := hanti.sum_le_integral
  simp only [zero_add] at hcomp
  push_cast at hsand hcomp
  linarith

/-- Exercise 11.6.5.  Decided by the integral test (Proposition 11.6.4) applied to the shifted
function {lit}`(x+1)^(-p)`.  The chapter's {lit}`integ` has no fundamental theorem of calculus
yet, so it is compared against Mathlib's interval integrals ({lit}`integral_rpow`,
{lit}`integral_one_div`) through the Riemann-sum bridge lemmas above. -/
example (p: ℝ) : Summable (fun n:ℕ ↦ 1 / (n : ℝ) ^ p) ↔ 1 < p := by
  set g : ℝ → ℝ := fun x ↦ (x+1)^(-p) with hgdef
  have hshift : Summable (fun n:ℕ ↦ g (n:ℝ)) ↔ Summable (fun n:ℕ ↦ 1/(n:ℝ)^p) := by
    rw [← summable_nat_add_iff (f := fun n:ℕ ↦ 1/(n:ℝ)^p) 1]
    apply summable_congr
    intro n
    simp only [hgdef]
    rw [Real.rpow_neg (by positivity), one_div]
    push_cast
    ring_nf
  have hg_nonneg : ∀ x ≥ (0:ℝ), g x ≥ 0 := by
    intro x hx
    simp only [hgdef]
    exact Real.rpow_nonneg (by linarith) _
  have hg_anti : 0 ≤ p → AntitoneOn g (Set.Ici 0) := by
    intro hp0 x hx y hy hxy
    have hx' := Set.mem_Ici.mp hx
    simp only [hgdef]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  constructor
  · intro hsum
    by_contra hp1
    push_neg at hp1
    rcases le_or_gt p 0 with hp0 | hp0
    · -- p ≤ 0: the terms are at least 1 for n ≥ 1, so they cannot tend to zero
      have h2 : ∀ n:ℕ, 1 ≤ n → (1:ℝ) ≤ 1/(n:ℝ)^p := by
        intro n hn
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        have hppos : (0:ℝ) < (n:ℝ)^p := Real.rpow_pos_of_pos (by linarith) _
        rw [le_div_iff₀ hppos, one_mul]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 hp0
      obtain ⟨n, hn1, hn2⟩ := ((hsum.tendsto_atTop_zero.eventually_lt_const one_pos).and
        (Filter.eventually_ge_atTop 1)).exists
      exact absurd (h2 n hn2) (not_le.2 hn1)
    · -- 0 < p ≤ 1: `integ g` dominates `integ (1/(x+1))`, hence `∫ 1/(x+1) = log`, unbounded
      obtain ⟨M, hM⟩ := (summable_iff_integ_of_antitone hg_nonneg (hg_anti hp0.le)).mp
        (hshift.mpr hsum)
      obtain ⟨K, hK⟩ := exists_nat_gt (2 * Real.exp M)
      set h : ℝ → ℝ := fun x ↦ 1/(x+1) with hhdef
      have hh_anti : AntitoneOn h (Set.Ici 0) := by
        intro x hx y hy hxy
        have hx' := Set.mem_Ici.mp hx
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have hIcc : ∀ {F:ℝ → ℝ}, AntitoneOn F (Set.Ici 0) → IntegrableOn F (Icc 0 (K:ℝ)) :=
        fun hF ↦ integ_of_antitone (hF.mono (by rw [set_Icc]; exact Set.Icc_subset_Ici_self))
      have hcmp : integ h (Icc 0 (K:ℝ)) ≤ integ g (Icc 0 (K:ℝ)) := by
        apply IntegrableOn.mono (hIcc hh_anti) (hIcc (hg_anti hp0.le))
        intro x hx
        rw [set_Icc] at hx
        simp only [hgdef, hhdef]
        calc (1:ℝ)/(x+1) = (x+1)^(-1:ℝ) := by rw [Real.rpow_neg_one, one_div]
          _ ≤ (x+1)^(-p) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [hx.1]) (by linarith)
      have hbr := intervalIntegral_le_integ_of_antitone hh_anti K
      have hval : (∫ x in (1:ℝ)..(1+(K:ℕ)), h x) = Real.log (((1+(K:ℕ))+1)/(1+1)) := by
        rw [show (∫ x in (1:ℝ)..(1+(K:ℕ)), h x)
            = ∫ x in (1+1:ℝ)..((1+(K:ℕ))+1), 1/x from
          intervalIntegral.integral_comp_add_right (fun x ↦ 1/x) 1]
        apply integral_one_div
        rw [Set.uIcc_of_le (by linarith)]
        simp only [Set.mem_Icc, not_and, not_le]
        intro hcontra
        linarith
      have hlog : M < Real.log (((1+(K:ℕ))+1)/(1+1)) := by
        rw [Real.lt_log_iff_exp_lt (by positivity), lt_div_iff₀ (by norm_num : (0:ℝ) < 1+1)]
        linarith
      linarith [hM (K:ℝ) (Nat.cast_nonneg K), hcmp, hbr, hval, hlog]
  · intro hp1
    have hp0 : (0:ℝ) ≤ p := by linarith
    have hp1' : (0:ℝ) < p - 1 := by linarith
    refine hshift.mp ((summable_iff_integ_of_antitone hg_nonneg (hg_anti hp0)).mpr
      ⟨g 0 + 1/(p-1), fun N hN ↦ ?_⟩)
    obtain ⟨K, hK⟩ := exists_nat_gt N
    refine (integ_le_intervalIntegral_of_antitone hg_nonneg (hg_anti hp0) hN K
      (by linarith)).trans ?_
    gcongr
    -- ∫ x^(-p) over the shifted interval evaluates by Mathlib's FTC to at most 1/(p-1)
    simp only [hgdef]
    rw [show (∫ x in (0:ℝ)..(K:ℕ), (x+1)^(-p)) = ∫ x in (0+1:ℝ)..((K:ℕ)+1), x^(-p) from
        intervalIntegral.integral_comp_add_right (fun x ↦ x^(-p)) 1,
      show (0+1:ℝ) = 1 by norm_num,
      integral_rpow (Or.inr ⟨by linarith, by
        rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) K] : (1:ℝ) ≤ (K:ℕ)+1)]
        simp only [Set.mem_Icc, not_and, not_le]
        intro hcontra
        linarith⟩),
      Real.one_rpow, show (-p+1) = -(p-1) by ring, div_neg, ← neg_div, neg_sub]
    have hX : (0:ℝ) ≤ ((K:ℕ)+1:ℝ)^(-(p-1)) := Real.rpow_nonneg (by positivity) _
    gcongr
    linarith

end Chapter11
