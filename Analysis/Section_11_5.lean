import Mathlib.Tactic
import Analysis.Section_9_9
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.5: Riemann integrability of continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of uniformly continuous functions.
- Riemann integrability of bounded continuous functions.

-/

namespace Chapter11
open BoundedInterval
open Chapter9

/-- Split an interval {lit}`I` at an interior point {lit}`c` into a left piece {lit}`L`
(right-open) and a right piece {lit}`R` (left-closed), recording the endpoints. -/
theorem exists_split (I : BoundedInterval) {c : ℝ} (hac : I.a < c) (hcb : c < I.b) :
    ∃ L R : BoundedInterval, I.joins L R ∧ L.a = I.a ∧ L.b = c ∧ R.a = c ∧ R.b = I.b := by
  cases I with
  | Icc a b => exact ⟨Ico a c, Icc c b, join_Ico_Icc hac.le hcb.le, rfl, rfl, rfl, rfl⟩
  | Ico a b => exact ⟨Ico a c, Ico c b, join_Ico_Ico hac.le hcb.le, rfl, rfl, rfl, rfl⟩
  | Ioc a b => exact ⟨Ioo a c, Icc c b, join_Ioo_Icc hac hcb.le, rfl, rfl, rfl, rfl⟩
  | Ioo a b => exact ⟨Ioo a c, Ico c b, join_Ioo_Ico hac hcb.le, rfl, rfl, rfl, rfl⟩

/-- For {lit}`a < b` and {lit}`N ≥ 1`, {lit}`I` admits a partition into {lit}`N` subintervals
each of length {lit}`(b - a)/N`, using the equally-spaced endpoints {lit}`a + i·(b-a)/N`.  Proved
by peeling the leftmost piece and recursing on the (uniformly shorter) remainder. -/
theorem exists_uniform_partition {I : BoundedInterval} {N : ℕ} (hN : 0 < N)
    (hab : I.a < I.b) :
    ∃ P : Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (I.b - I.a) / N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  clear hN
  induction n generalizing I with
  | zero =>
    refine ⟨⊥, by simp, ?_⟩
    intro J hJ
    rw [Partition.intervals_of_bot, Finset.mem_singleton] at hJ
    subst hJ
    rw [show ((0 + 1 : ℕ):ℝ) = 1 by norm_num, div_one]
    show max (J.b - J.a) 0 = J.b - J.a
    exact max_eq_left (by linarith)
  | succ n ih =>
    have hsub_pos : 0 < I.b - I.a := by linarith
    have hw : 0 < (I.b - I.a) / ((n:ℝ) + 1 + 1) := div_pos hsub_pos (by positivity)
    have hwlt : (I.b - I.a) / ((n:ℝ) + 1 + 1) < I.b - I.a := by
      rw [div_lt_iff₀ (show (0:ℝ) < (n:ℝ) + 1 + 1 by positivity)]
      nlinarith [hsub_pos, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
    set c := I.a + (I.b - I.a) / ((n:ℝ) + 1 + 1) with hc
    have hac : I.a < c := by rw [hc]; linarith
    have hcb : c < I.b := by rw [hc]; linarith
    obtain ⟨L, R, hjoin, hLa, hLb, hRa, hRb⟩ := exists_split I hac hcb
    obtain ⟨P, hPcard, hPlen⟩ := ih (I := R) (by rw [hRa, hRb]; exact hcb)
    have hmid : (I.a + c) / 2 ∈ L := by
      apply L.Ioo_subset
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo, hLa, hLb, Set.mem_Ioo]
      exact ⟨by linarith, by linarith⟩
    have hLne : (L:Set ℝ).Nonempty := ⟨_, hmid⟩
    have hLnotmem : L ∉ P.intervals := by
      intro hmem
      obtain ⟨x, hx⟩ := hLne
      have : x ∈ (L:Set ℝ) ∩ (R:Set ℝ) := ⟨hx, (BoundedInterval.subset_iff _ _).mp (P.contains _ hmem) hx⟩
      rw [hjoin.1] at this; exact this
    refine ⟨(⊥ : Partition L).join P hjoin, ?_, ?_⟩
    · rw [Partition.intervals_of_join, Partition.intervals_of_bot, ← Finset.insert_eq,
          Finset.card_insert_of_notMem hLnotmem, hPcard]
    · intro J hJ
      rw [Partition.intervals_of_join, Partition.intervals_of_bot] at hJ
      simp only [Finset.mem_union, Finset.mem_singleton] at hJ
      rcases hJ with rfl | hJ
      · show max (J.b - J.a) 0 = _
        rw [hLa, hLb, max_eq_left (by linarith : (0:ℝ) ≤ c - I.a), hc]
        push_cast; ring
      · rw [hPlen J hJ, hRa, hRb, hc]
        have h1 : ((n:ℝ) + 1) ≠ 0 := by positivity
        have h2 : ((n:ℝ) + 1 + 1) ≠ 0 := by positivity
        push_cast; field_simp; ring

/-- Theorem 11.5.1 -/
theorem integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I) :
  IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨ hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1.2
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ ε * (b-a) := by
    rw [UniformContinuousOn.iff] at hf
    choose δ hδ hf using hf ε hε; simp [Real.Close, Real.dist_eq] at hf
    choose N hN using exists_nat_gt ((b-a)/δ)
    have hNpos : 0 < N := by
      have : 0 < (b-a)/δ := by positivity
      rify; order
    have hN' : (b-a)/N < δ := by rwa [div_lt_comm₀] <;> positivity
    have : ∃ P: Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (b-a) / N :=
      exists_uniform_partition hNpos hsing
    choose P hcard hlength using this
    calc
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * |J|ₗ := by
        have h1 := upper_integ_le_upper_sum hfbound P
        have h2 := lower_integ_ge_lower_sum hfbound P
        simp [sub_mul, upper_riemann_sum, lower_riemann_sum] at *
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε * |J|ₗ := by
        apply Finset.sum_le_sum; intro J hJ; gcongr
        have {x y:ℝ} (hx: x ∈ J) (hy: y ∈ J) : f x ≤ f y + ε := by
          have : J ⊆ I := P.contains _ hJ
          have : |f x - f y| ≤ ε := by
            apply hf y _ x _ _ <;> try solve_by_elim
            apply (BoundedInterval.dist_le_length hx hy).trans; grind
          grind [abs_le']
        have hJnon : (f '' J).Nonempty := by
          simp; by_contra! h
          replace h : Subsingleton (J:Set ℝ) := by simp [h]
          simp only [length_of_subsingleton, hlength J hJ] at h
          linarith [show 0 < (b-a) / N by positivity]
        replace (y:ℝ) (hy:y ∈ J) : sSup (f '' J) ≤ f y + ε := by
          apply csSup_le hJnon; rintro _ ⟨z, hz, rfl⟩; exact this hz hy
        replace : sSup (f '' J) - ε ≤ sInf (f '' J) := by
          apply le_csInf hJnon; grind [mem_iff]
        linarith
      _ = ∑ J ∈ P.intervals, ε * (b-a)/N := by grind [Finset.sum_congr]
      _ = _ := by simp [hcard]; field_simp
  have lower_le_upper : 0 ≤ upper_integral f I - lower_integral f I := by linarith [lower_integral_le_upper hfbound]
  obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
  . set ε := (upper_integral f I - lower_integral f I)/(2*(b-a))
    replace : upper_integral f I - lower_integral f I ≤ (upper_integral f I - lower_integral f I)/2 := by
      convert this ε (by positivity) using 1; grind
    linarith
  linarith

/-- Corollary 11.5.2 -/
theorem integ_of_cts {a b:ℝ} {f:ℝ → ℝ} (hf: ContinuousOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := integ_of_uniform_cts (UniformContinuousOn.of_continuousOn hf)

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Ioc 0 1) := by
  intro x hx
  rw [BoundedInterval.set_Ioc, Set.mem_Ioc] at hx
  exact ((continuousAt_const (y := (1:ℝ))).div continuousAt_id (ne_of_gt hx.1)).continuousWithinAt

example : ¬ IntegrableOn (fun x:ℝ ↦ 1/x) (Ioc 0 1) := by
  rintro ⟨⟨M, hM⟩, -⟩
  have hx : 1 / (|M| + 1) ∈ (Ioc 0 1 : Set ℝ) := by
    rw [BoundedInterval.set_Ioc, Set.mem_Ioc]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]; linarith [abs_nonneg M]
  have := hM _ hx
  simp only [one_div_one_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ |M| + 1)] at this
  linarith [le_abs_self M]

open PiecewiseConstantOn ConstantOn in
set_option maxHeartbeats 300000 in
/-- Proposition 11.5.3-/
theorem integ_of_bdd_cts {I: BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: ContinuousOn f I) : IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1
  have hI : (I:Set ℝ).Nonempty := by by_contra!; rw [←BoundedInterval.length_of_subsingleton] at hsing; simp_all
  simp at hsing
  set a := I.a
  set b := I.b
  have lower_le_upper := lower_integral_le_upper hbound
  have ⟨ M, hM ⟩ := hbound
  have hMpos : 0 ≤ M := (abs_nonneg _).trans (hM hI.some hI.some_mem)
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ (4*M+2) * ε := by
    wlog hε' : ε < (b-a)/2
    . specialize this _ _ _ _ _ _ hM _ ((b-a)/3) _ _
        <;> first | assumption | linarith | apply this.trans; gcongr; linarith
    set I' := Icc (a+ε) (b-ε)
    set Ileft : BoundedInterval := match I with
    | Icc _ _ => Ico a (a + ε)
    | Ico _ _ => Ico a (a + ε)
    | Ioc _ _ => Ioo a (a + ε)
    | Ioo _ _ => Ioo a (a + ε)
    set Iright : BoundedInterval := match I with
    | Icc _ _ => Ioc (b - ε) b
    | Ico _ _ => Ioo (b - ε) b
    | Ioc _ _ => Ioc (b - ε) b
    | Ioo _ _ => Ioo (b - ε) b
    set Ileft' : BoundedInterval := match I with
    | Icc _ _ => Icc a (b - ε)
    | Ico _ _ => Icc a (b - ε)
    | Ioc _ _ => Ioc a (b - ε)
    | Ioo _ _ => Ioc a (b - ε)
    have Ileftlen : |Ileft|ₗ = ε := by cases I <;> simp [Ileft, length, le_of_lt hε]
    have Irightlen : |Iright|ₗ = ε := by cases I <;> simp [Iright, length, le_of_lt hε]
    have hjoin1 : Ileft'.joins Ileft I' := by
      cases I
      case Icc _ _ => apply join_Ico_Icc <;> linarith
      case Ico _ _ => apply join_Ico_Icc <;> linarith
      case Ioc _ _ => apply join_Ioo_Icc <;> linarith
      case Ioo _ _ => apply join_Ioo_Icc <;> linarith
    have hjoin2: I.joins Ileft' Iright := by
      cases I
      case Icc _ _ => apply join_Icc_Ioc <;> linarith
      case Ico _ _ => apply join_Icc_Ioo <;> linarith
      case Ioc _ _ => apply join_Ioc_Ioc <;> linarith
      case Ioo _ _ => apply join_Ioc_Ioo <;> linarith
    have hf' : IntegrableOn f I' := by
      apply integ_of_cts $ ContinuousOn.mono hf $ subset_trans _ $ (subset_iff _ _).mp $ Ioo_subset I
      intro _; simp; grind
    choose h hhmin hhconst hhint using lt_of_gt_upper_integral hf'.1 (show upper_integral f I' < integ f I' + ε by linarith [hf'.2])
    classical
    set h' : ℝ → ℝ := fun x ↦ if x ∈ I' then h x else M
    have h'const_left (x:ℝ) (hx: x ∈ Ileft) : h' x = M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [h',mem_iff]
    have h'const_right (x:ℝ) (hx: x ∈ Iright) : h' x = M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [h',mem_iff]
    have h'const : PiecewiseConstantOn h' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hhconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have h'maj : MajorizesOn h' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [h', hxI']; solve_by_elim; grind [abs_le']
    observe h'maj : upper_integral f I ≤ h'const.integ'
    have h'integ1 := h'const.integ_of_join hjoin2
    have h'integ2 := ((of_join hjoin2 _).mp h'const).1.integ_of_join hjoin1
    have h'integ3 : PiecewiseConstantOn.integ h' Ileft = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_left, integ_const, Ileftlen]
    have h'integ4 : PiecewiseConstantOn.integ h' Iright = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_right, integ_const, Irightlen]
    have h'integ5 : PiecewiseConstantOn.integ h' I' = PiecewiseConstantOn.integ h I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    choose g hgmin hgconst hgint using gt_of_lt_lower_integral hf'.1 (show integ f I' - ε < lower_integral f I' by linarith [hf'.2])
    set g' : ℝ → ℝ := fun x ↦ if x ∈ I' then g x else -M
    have g'const_left (x:ℝ) (hx: x ∈ Ileft) : g' x = -M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [g', mem_iff]
    have g'const_right (x:ℝ) (hx: x ∈ Iright) : g' x = -M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [g', mem_iff]
    have g'const : PiecewiseConstantOn g' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, of_const]
      . apply hgconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, of_const]
    have g'maj : MinorizesOn g' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [g', hxI']; solve_by_elim; grind [abs_le']
    observe g'maj : g'const.integ' ≤ lower_integral f I
    have g'integ1 := g'const.integ_of_join hjoin2
    have g'integ2 := ((of_join hjoin2 _).mp g'const).1.integ_of_join hjoin1
    have g'integ3 : PiecewiseConstantOn.integ g' Ileft = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_left, integ_const, Ileftlen]
    have g'integ4 : PiecewiseConstantOn.integ g' Iright = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_right, integ_const, Irightlen]
    have g'integ5 : PiecewiseConstantOn.integ g' I' = PiecewiseConstantOn.integ g I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    grind
  exact ⟨ hbound, by linarith [nonneg_of_le_const_mul_eps this] ⟩

/-- Definition 11.5.4 -/
abbrev PiecewiseContinuousOn (f:ℝ → ℝ) (I:BoundedInterval) : Prop :=
  ∃ P: Partition I, ∀ J ∈ P.intervals, ContinuousOn f J

/-- Example 11.5.5 -/
noncomputable abbrev f_11_5_5 : ℝ → ℝ := fun x ↦
  if x < 2 then x^2
  else if x = 2 then 7
  else x^3

open Topology in
example : ¬ ContinuousOn f_11_5_5 (Icc 1 3) := by
  intro h
  have hmem : (2:ℝ) ∈ (Icc (1:ℝ) 3 : Set ℝ) := by
    rw [BoundedInterval.set_Icc, Set.mem_Icc]; norm_num
  have hc := (h 2 hmem).tendsto
  rw [show f_11_5_5 2 = 7 by norm_num [f_11_5_5]] at hc
  have hle : 𝓝[<] (2:ℝ) ≤ 𝓝[(Icc (1:ℝ) 3 : Set ℝ)] 2 := by
    rw [BoundedInterval.set_Icc, nhdsWithin_le_iff]
    exact nhdsWithin_le_nhds (Icc_mem_nhds (by norm_num) (by norm_num))
  have hc2 : Filter.Tendsto f_11_5_5 (𝓝[<] (2:ℝ)) (𝓝 7) := hc.mono_left hle
  have heq : f_11_5_5 =ᶠ[𝓝[<] (2:ℝ)] (fun x => x^2) :=
    eventually_nhdsWithin_of_forall (fun x hx => by simp [f_11_5_5, show x < 2 from hx])
  rw [Filter.tendsto_congr' heq] at hc2
  have hc3 : Filter.Tendsto (fun x:ℝ => x^2) (𝓝[<] (2:ℝ)) (𝓝 ((2:ℝ)^2)) :=
    ((continuous_pow 2).tendsto 2).mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique hc2 hc3
  norm_num at this

example : ContinuousOn f_11_5_5 (Ico 1 2) := by
  have heq : Set.EqOn f_11_5_5 (fun x => x^2) (Ico (1:ℝ) 2 : Set ℝ) := by
    intro x hx
    rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx
    simp [f_11_5_5, hx.2]
  exact ((continuous_pow 2).continuousOn).congr heq

example : ContinuousOn f_11_5_5 (Icc 2 2) := by
  rw [BoundedInterval.set_Icc, Set.Icc_self]
  exact continuousOn_singleton f_11_5_5 2

example : ContinuousOn f_11_5_5 (Ioc 2 3) := by
  have heq : Set.EqOn f_11_5_5 (fun x => x^3) (Ioc (2:ℝ) 3 : Set ℝ) := by
    intro x hx
    rw [BoundedInterval.set_Ioc, Set.mem_Ioc] at hx
    have h1 : ¬ x < 2 := by linarith [hx.1]
    have h2 : x ≠ 2 := ne_of_gt hx.1
    simp [f_11_5_5, h1, h2]
  exact ((continuous_pow 3).continuousOn).congr heq

example : PiecewiseContinuousOn f_11_5_5 (Icc 1 3) := by
  have c1 : ContinuousOn f_11_5_5 (Ico 1 2) := by
    have heq : Set.EqOn f_11_5_5 (fun x => x^2) (Ico (1:ℝ) 2 : Set ℝ) := by
      intro x hx
      rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx
      simp [f_11_5_5, hx.2]
    exact ((continuous_pow 2).continuousOn).congr heq
  have c2 : ContinuousOn f_11_5_5 (Icc 2 2) := by
    rw [BoundedInterval.set_Icc, Set.Icc_self]
    exact continuousOn_singleton f_11_5_5 2
  have c3 : ContinuousOn f_11_5_5 (Ioc 2 3) := by
    have heq : Set.EqOn f_11_5_5 (fun x => x^3) (Ioc (2:ℝ) 3 : Set ℝ) := by
      intro x hx
      rw [BoundedInterval.set_Ioc, Set.mem_Ioc] at hx
      have h1 : ¬ x < 2 := by linarith [hx.1]
      have h2 : x ≠ 2 := ne_of_gt hx.1
      simp [f_11_5_5, h1, h2]
    exact ((continuous_pow 3).continuousOn).congr heq
  set P1 : Partition (Icc 1 2) :=
    (⊥ : Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 2)) (join_Ico_Icc (by norm_num) (by norm_num))
  set P2 : Partition (Icc 1 3) :=
    P1.join (⊥ : Partition (Ioc 2 3)) (join_Icc_Ioc (by norm_num) (by norm_num))
  refine ⟨P2, ?_⟩
  intro J hJ
  simp only [P2, P1, Partition.intervals_of_bot,
    Finset.mem_union, Finset.mem_singleton] at hJ
  rcases hJ with (rfl | rfl) | rfl <;> assumption

/-- Proposition 11.5.6 / Exercise 11.5.1 -/
theorem integ_of_bdd_piecewise_cts {I: BoundedInterval} {f:ℝ → ℝ}
  (hbound: BddOn f I) (hf: PiecewiseContinuousOn f I) : IntegrableOn f I := by
  rw [PiecewiseContinuousOn] at hf
  obtain ⟨P, hP⟩ := hf
  classical
  let g : BoundedInterval → (ℝ → ℝ) := fun J ↦ fun x ↦ if x ∈ J then f x else 0
  let G : ℝ → ℝ := fun x ↦ if h : x ∈ I then g (P.exists_unique x h).choose x else 0
  have hfG (x : ℝ) (hx : x ∈ I) : f x = G x := by
    have hxJ : x ∈ (P.exists_unique x hx).choose := ((P.exists_unique x hx).choose_spec).1.2
    show f x = if h : x ∈ I then g (P.exists_unique x h).choose x else 0
    rw [dif_pos hx]
    show f x = if x ∈ (P.exists_unique x hx).choose then f x else 0
    rw [if_pos hxJ]
  have hgG (x : ℝ) (hx : x ∈ I) : G x = ∑ J ∈ P.intervals, g J x := by
    have hspec := (P.exists_unique x hx).choose_spec
    rw [Finset.sum_eq_single (P.exists_unique x hx).choose]
    · show (if h : x ∈ I then g (P.exists_unique x h).choose x else 0)
        = g (P.exists_unique x hx).choose x
      rw [dif_pos hx]
    · intro J hJmem hJne
      have hxJ : x ∉ J := fun h ↦ hJne (hspec.2 J ⟨hJmem, h⟩)
      show (if x ∈ J then f x else 0) = 0
      rw [if_neg hxJ]
    · intro hnotmem; exact absurd hspec.1.1 hnotmem
  -- On each piece `f` is bounded and continuous, hence integrable on `J` (Prop 11.5.3).
  have hfint : ∀ J ∈ P.intervals, IntegrableOn f J := by
    intro J hJ
    refine integ_of_bdd_cts ?_ (hP J hJ)
    obtain ⟨M, hM⟩ := hbound
    exact ⟨M, fun x hx ↦ hM x (P.contains J hJ x hx)⟩
  -- `g J` is the extension by zero of `f|J` to `I`, hence integrable on `I` (Thm 11.4.1(g)).
  have hgint : ∀ J ∈ P.intervals, IntegrableOn (g J) I :=
    fun J hJ ↦ IntegrableOn.of_extend (P.contains J hJ) (hfint J hJ)
  -- A finite sum of integrable functions is integrable (Thm 11.4.1(a)).
  have hsum : ∀ s : Finset BoundedInterval, (∀ J ∈ s, IntegrableOn (g J) I) →
      IntegrableOn (fun x ↦ ∑ J ∈ s, g J x) I := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simpa using (IntegrableOn.const 0 I).1
    | insert J s hJs ih =>
      intro hmem
      have h1 := hmem J (Finset.mem_insert_self J s)
      have h2 := ih (fun K hK ↦ hmem K (Finset.mem_insert_of_mem hK))
      simp only [Finset.sum_insert hJs]
      exact (IntegrableOn.add h1 h2).1
  -- `f` agrees on `I` with the integrable sum, so `f` is integrable too.
  have integrable_congr : ∀ {p q : ℝ → ℝ}, Set.EqOn p q I → IntegrableOn q I → IntegrableOn p I := by
    intro p q hpq hq
    obtain ⟨⟨M, hM⟩, heq⟩ := hq
    exact ⟨⟨M, fun x hx ↦ by rw [hpq hx]; exact hM x hx⟩,
      by rw [lower_integral_congr hpq, upper_integral_congr hpq]; exact heq⟩
  exact integrable_congr (fun x hx ↦ (hfG x hx).trans (hgG x hx)) (hsum P.intervals hgint)

/-- Exercise 11.5.2 -/
theorem integ_zero {a b:ℝ} (hab: a < b) (f: ℝ → ℝ) (hf: ContinuousOn f (Icc a b))
  (hnonneg: MajorizesOn f (fun _ ↦ 0) (Icc a b)) (hinteg : integ f (Icc a b) = 0) :
  ∀ x ∈ Icc a b, f x = 0 := by
  by_contra! h
  obtain ⟨x, hx, hfx⟩ := h
  have ⟨hxa, hxb⟩ := hx
  have hfx' : 0 < f x := lt_of_le_of_ne (hnonneg x hx) (Ne.symm hfx)
  -- Continuity at `x` pins down a radius `δ` on which `f > f x / 2`.
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.continuousWithinAt_iff.mp (hf x hx)) (f x / 2) (half_pos hfx')
  -- A nondegenerate closed subinterval `[c,d] ⊆ [a,b] ∩ (x-δ, x+δ)`.
  set c := max a (x - δ / 2) with hc_def
  set d := min b (x + δ / 2) with hd_def
  have hac : a ≤ c := le_max_left _ _
  have hc_lb : x - δ / 2 ≤ c := le_max_right _ _
  have hcx : c ≤ x := max_le hxa (by linarith)
  have hxd : x ≤ d := le_min hxb (by linarith)
  have hd_ub : d ≤ x + δ / 2 := min_le_right _ _
  have hdb : d ≤ b := min_le_left _ _
  have hcb : c ≤ b := le_trans hcx hxb
  have hcd : c < d := by
    show max a (x - δ / 2) < min b (x + δ / 2)
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨hab, ?_⟩, ?_, ?_⟩ <;> linarith
  -- Split `[a,b] = [a,c) ⊔ [c,d] ⊔ (d,b]` and integrate piecewise.
  have hf_int : IntegrableOn f (Icc a b) := integ_of_cts hf
  obtain ⟨hI_left, hI_cb, hsplit1⟩ := IntegrableOn.join (join_Ico_Icc hac hcb) hf_int
  obtain ⟨hI_cd, hI_right, hsplit2⟩ := IntegrableOn.join (join_Icc_Ioc hcd.le hdb) hI_cb
  -- The two flanks contribute nonnegatively since `f ≥ 0`.
  have hnn_left : 0 ≤ integ f (Ico a c) :=
    IntegrableOn.nonneg hI_left fun y hy ↦ hnonneg y (by
      simp only [BoundedInterval.mem_iff, BoundedInterval.set_Ico, Set.mem_Ico] at hy
      rw [BoundedInterval.set_Icc, Set.mem_Icc]
      exact ⟨hy.1, by linarith [hy.2]⟩)
  have hnn_right : 0 ≤ integ f (Ioc d b) :=
    IntegrableOn.nonneg hI_right fun y hy ↦ hnonneg y (by
      simp only [BoundedInterval.mem_iff, BoundedInterval.set_Ioc, Set.mem_Ioc] at hy
      rw [BoundedInterval.set_Icc, Set.mem_Icc]
      exact ⟨by linarith [hy.1], hy.2⟩)
  -- On `[c,d]`, `f ≥ f x / 2`, so its integral is at least `(f x / 2)·(d - c) > 0`.
  have hmaj : MajorizesOn f (fun _ ↦ f x / 2) (Icc c d) := by
    intro y hy
    simp only [BoundedInterval.set_Icc, Set.mem_Icc] at hy
    have hyab : y ∈ (Icc a b : Set ℝ) := by
      rw [BoundedInterval.set_Icc, Set.mem_Icc]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hydist : dist y x < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hcont := hδ' hyab hydist
    rw [Real.dist_eq, abs_lt] at hcont
    show f x / 2 ≤ f y
    linarith [hcont.1]
  have hpos : 0 < integ f (Icc c d) := by
    have hle := IntegrableOn.mono (IntegrableOn.const (f x / 2) (Icc c d)).1 hI_cd hmaj
    rw [(IntegrableOn.const (f x / 2) (Icc c d)).2] at hle
    have hlen : |Icc c d|ₗ = d - c := by
      show max (d - c) 0 = d - c
      exact max_eq_left (by linarith [hcd.le])
    rw [hlen] at hle
    have hp : 0 < (f x / 2) * (d - c) := mul_pos (by linarith) (by linarith)
    linarith
  rw [hsplit1, hsplit2] at hinteg
  linarith [hnn_left, hnn_right, hpos]

end Chapter11
