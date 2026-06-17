import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_3
import Analysis.Section_11_9


/-!
# Analysis I, Section 11.10: Consequences of the fundamental theorems

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- Integration by parts

-/

namespace Chapter11

open BoundedInterval Chapter9 Chapter10

/-- Proposition 11.10.1 (Integration by parts formula) / Exercise 11.10.1 -/
theorem integ_of_mul_deriv {a b:ℝ} (hab: a ≤ b) {F G: ℝ → ℝ}
  (hF: DifferentiableOn ℝ F (Icc a b)) (hG : DifferentiableOn ℝ G (Icc a b))
  (hF': IntegrableOn (derivWithin F (Icc a b)) (Icc a b))
  (hG': IntegrableOn (derivWithin G (Icc a b)) (Icc a b)) :
  integ (F * derivWithin G (Icc a b)) (Icc a b) = F b * G b - F a * G a -
    integ (G * derivWithin F (Icc a b)) (Icc a b) := by
  have hFinteg : IntegrableOn F (Icc a b) := by exact integ_of_cts (hF.continuousOn)
  have hGinteg : IntegrableOn G (Icc a b) := by exact integ_of_cts (hG.continuousOn)
  have hFGdiff : IntegrableOn (F * (derivWithin G (Icc a b))) (Icc a b) := by
    exact integ_of_mul hFinteg hG'
  have hGFdiff : IntegrableOn (G * (derivWithin F (Icc a b))) (Icc a b) := by
    exact integ_of_mul hGinteg hF'
  have hinteg := hFGdiff.add hGFdiff
  have hFGantidiff : AntiderivOn (F * G)
      (F * (derivWithin G (Icc a b)) + G * (derivWithin F (Icc a b))) (Icc a b) := by
    refine ⟨hF.mul hG, fun x hx => ?_⟩
    have hFx := (hF x hx).hasDerivWithinAt
    have hGx := (hG x hx).hasDerivWithinAt
    convert hFx.mul hGx using 1
    simp only [Pi.add_apply, Pi.mul_apply]; ring
  have hFTC := integ_eq_antideriv_sub hab hinteg.1 hFGantidiff
  rw [hinteg.2] at hFTC
  simp only [Pi.mul_apply] at hFTC
  linarith [hFTC]

/-- Theorem 11.10.2.  Need to add continuity of α due to our conventions on {name}`α_length` -/
theorem PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} {α f:ℝ → ℝ}
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  Chapter11.integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hf_integ: IntegrableOn f (Icc a b) := (integ_of_piecewise_const hf).1
  observe hfα'_integ: IntegrableOn (f * α') (Icc a b)
  refine ⟨ hfα'_integ, ?_ ⟩
  choose P hP using hf
  rw [PiecewiseConstantOn.RS_integ_def hP α, hfα'_integ.split P]
  apply Finset.sum_congr rfl; intro J hJ
  calc
    _ = Chapter11.integ ((constant_value_on f (J:Set ℝ)) • α') J := by
      apply Chapter11.integ_congr; intro x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; congr
      exact (hP J hJ).eq hx
    _ = constant_value_on f (J:Set ℝ) * Chapter11.integ α' J := ((hα'.mono' (P.contains _ hJ)).smul _).2
    _ = _ := by
      congr
      have hJsub (hJab : J.a ≤ J.b) : J ⊆ Ioo (J.a - 1) (J.b + 1) :=
        (subset_Icc J).trans (by simp [subset_iff, Set.Icc_subset_Ioo_iff hJab])
      obtain hJab | hJab := le_iff_eq_or_lt.mp (length_nonneg J)
      . rw [(integ_on_subsingleton hJab.symm).2]
        simp [le_iff_lt_or_eq] at hJab; obtain hJab | hJab := hJab
        . rw [α_length_of_empty _ (empty_of_lt hJab)]
        rw [α_length_of_cts _ _ _ (hJsub _) hαcont.continuousOn] <;> grind
      simp [length] at hJab
      rw [α_length_of_cts ?_ ?_ ?_ (hJsub ?_) hαcont.continuousOn ]
      . have : Icc J.a J.b ⊆ Icc a b := by
          have := closure_mono $ (subset_iff _ _).mp $ (Ioo_subset J).trans $ P.contains _ hJ
          simpa [closure_Ioo (show J.a ≠ J.b by linarith), subset_iff] using this
        calc
          _ = Chapter11.integ α' (Icc J.a J.b) := (hα'.mono' this).eq (subset_Icc J) rfl rfl
          _ = _ := by
            convert integ_eq_antideriv_sub (by order) (hα'.mono' this) _
            apply AntiderivOn.mono ⟨ hα_diff, _ ⟩ this
            intros; solve_by_elim [DifferentiableWithinAt.hasDerivWithinAt]
      all_goals linarith

lemma lower_integral_mono {p q:ℝ → ℝ} {I: BoundedInterval} (hq: BddOn q I)
    (hp: BddOn p I) (hpq: MinorizesOn p q I) : lower_integral p I ≤ lower_integral q I := by
  apply csSup_le (integral_bound_lower_nonempty hp)
  rintro _ ⟨g, ⟨hgp, hgc⟩, rfl⟩
  exact integ_le_lower_integral hq (fun x hx ↦ (hgp x hx).trans (hpq x hx)) hgc

lemma upper_integral_mono {p q:ℝ → ℝ} {I: BoundedInterval} (hp: BddOn p I)
    (hq: BddOn q I) (hpq: MajorizesOn q p I) : upper_integral p I ≤ upper_integral q I := by
  apply le_csInf (integral_bound_upper_nonempty hq)
  rintro _ ⟨g, ⟨hgp, hgc⟩, rfl⟩
  exact upper_integral_le_integ hp (fun x hx ↦ (hpq x hx).trans (hgp x hx)) hgc

/-- Corollary 11.10.3 -/
theorem RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} (hab: a < b) {α f:ℝ → ℝ} (hα: Monotone α)
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: RS_IntegrableOn f (Icc a b) α) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hfα'_bound: BddOn (f * α') (Icc a b) := by
    have ⟨ M, hM ⟩ := hf.1; have ⟨ N, hN ⟩ := hα'.1
    use M * N; intro x hx; specialize hM _ hx; specialize hN _ hx
    simp [abs_mul]; gcongr; linarith [abs_nonneg (f x)]
  have hα'_nonneg : MajorizesOn α' 0 (Icc a b) := by
    intro x hx
    convert ge_iff_le.mp (derivative_of_monotone _ _ hα (hα_diff x hx))
    rw [←mem_closure_iff_clusterPt]
    simp at hx
    obtain h | h := le_iff_lt_or_eq.mp hx.1
    . apply closure_mono (s := .Ico a x) _
      . simp [closure_Ico (show a ≠ x by linarith), hx.1]
      intro _ _; simp_all; grind
    apply closure_mono (s := .Ioc x b) _
    . simp [closure_Ioc (show x ≠ b by linarith), hx.2]
    intro _ _; simp_all
  have h0 := hf.2
  have h1 : RS_integ f (Icc a b) α ≤ lower_integral (f * α') (Icc a b) := by
    apply le_of_forall_sub_le; intro ε hε
    have ⟨ h, hhminor, hhconst, hh ⟩ :=
      gt_of_lt_lower_RS_integral hf.1 hα (show RS_integ f (Icc a b) α - ε < lower_RS_integral f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    replace : lower_integral (h * α') (Icc a b) = integ (h * α') (Icc a b) := this.1.2
    have why : lower_integral (h * α') (Icc a b) ≤ lower_integral (f * α') (Icc a b) := by
      apply lower_integral_mono hfα'_bound
        (BddOn.mul h α' _ (bounded_of_piecewise_constant hhconst) hα'.1)
      intro x hx
      simp only [Pi.mul_apply]
      exact mul_le_mul_of_nonneg_right (hhminor x hx) (hα'_nonneg x hx)
    linarith
  have h2 : upper_integral (f * α') (Icc a b) ≤ RS_integ f (Icc a b) α := by
    apply le_of_forall_pos_le_add; intro ε hε
    have ⟨ h, hhmajor, hhconst, hh ⟩ :=
      lt_of_gt_upper_RS_integral hf.1 hα (show upper_RS_integral f (Icc a b) α + ε > RS_integ f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    have why : upper_integral (f * α') (Icc a b) ≤ upper_integral (h * α') (Icc a b) := by
      apply upper_integral_mono hfα'_bound
        (BddOn.mul h α' _ (bounded_of_piecewise_constant hhconst) hα'.1)
      intro x hx
      simp only [Pi.mul_apply]
      exact mul_le_mul_of_nonneg_right (hhmajor x hx) (hα'_nonneg x hx)
    linarith
  have h3 : lower_integral (f * α') (Icc a b) ≤
    upper_integral (f * α') (Icc a b) := lower_integral_le_upper hfα'_bound
  refine ⟨ ⟨ hfα'_bound, ?_ ⟩, ?_ ⟩ <;> linarith

/- For a continuous monotone φ, the endpoints of the preimage interval K of J
(taken inside [a,b]) map under φ to the endpoints of J. -/
lemma preimage_endpoints {φ:ℝ → ℝ} (hcont: Continuous φ) (hmono: Monotone φ)
    {a b:ℝ} (hab: a ≤ b) {J K: BoundedInterval}
    (hKset : (K:Set ℝ) = {x | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ)})
    (hKne : (K:Set ℝ).Nonempty)
    (hJsub : (J:Set ℝ) ⊆ Set.Icc (φ a) (φ b)) :
    φ K.a = J.a ∧ φ K.b = J.b := by
  obtain ⟨z, hz⟩ := hKne
  have hzIcc := K.subset_Icc z hz
  rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at hzIcc
  have hKa_le_Kb : K.a ≤ K.b := le_trans hzIcc.1 hzIcc.2
  have hzJ : φ z ∈ (J:Set ℝ) := by rw [hKset] at hz; exact hz.2
  have hJ_Icc := J.subset_Icc (φ z) hzJ
  rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at hJ_Icc
  have hJa_le_Jb : J.a ≤ J.b := le_trans hJ_Icc.1 hJ_Icc.2
  have hbd : ∀ x ∈ (K:Set ℝ), J.a ≤ φ x ∧ φ x ≤ J.b := by
    intro x hx
    rw [hKset] at hx
    have := J.subset_Icc (φ x) hx.2
    rwa [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at this
  have hcl : ∀ p, K.a ≤ p → p ≤ K.b → p ∈ closure (K:Set ℝ) := by
    intro p hpa hpb
    rcases eq_or_lt_of_le hKa_le_Kb with h | h
    · have hp : p = K.b := le_antisymm hpb (h ▸ hpa)
      have hzb : z = K.b := le_antisymm hzIcc.2 (h ▸ hzIcc.1)
      rw [hp, ←hzb]; exact subset_closure hz
    · have hsub : Set.Icc K.a K.b ⊆ closure (K:Set ℝ) := by
        rw [←closure_Ioo (ne_of_lt h)]
        apply closure_mono
        rw [←BoundedInterval.set_Ioo]
        exact (subset_iff _ _).mp K.Ioo_subset
      exact hsub (Set.mem_Icc.mpr ⟨hpa, hpb⟩)
  have hKa_cl : K.a ∈ closure (K:Set ℝ) := hcl K.a le_rfl hKa_le_Kb
  have hKb_cl : K.b ∈ closure (K:Set ℝ) := hcl K.b hKa_le_Kb le_rfl
  have hubb : φ K.b ≤ J.b :=
    closure_minimal (fun x hx => (hbd x hx).2) (isClosed_le hcont continuous_const) hKb_cl
  have hlbb : J.a ≤ φ K.b :=
    closure_minimal (fun x hx => (hbd x hx).1) (isClosed_le continuous_const hcont) hKb_cl
  have huba : φ K.a ≤ J.b :=
    closure_minimal (fun x hx => (hbd x hx).2) (isClosed_le hcont continuous_const) hKa_cl
  have hlba : J.a ≤ φ K.a :=
    closure_minimal (fun x hx => (hbd x hx).1) (isClosed_le continuous_const hcont) hKa_cl
  constructor
  · refine le_antisymm ?_ hlba
    rcases eq_or_lt_of_le hJa_le_Jb with hJ | hJ
    · linarith
    · by_contra hcon
      push_neg at hcon
      obtain ⟨y, hy1, hy2⟩ := exists_between hcon
      have hyJ : y ∈ (J:Set ℝ) :=
        (subset_iff _ _).mp J.Ioo_subset
          (by rw [BoundedInterval.set_Ioo]; exact ⟨hy1, by linarith⟩)
      obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab hcont.continuousOn (hJsub hyJ)
      have hxK : x ∈ (K:Set ℝ) := by rw [hKset]; exact ⟨hx, by rw [hxy]; exact hyJ⟩
      have hxKa : K.a ≤ x := by
        have := K.subset_Icc x hxK; rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at this; exact this.1
      have := hmono hxKa
      rw [hxy] at this
      linarith
  · refine le_antisymm hubb ?_
    rcases eq_or_lt_of_le hJa_le_Jb with hJ | hJ
    · linarith
    · by_contra hcon
      push_neg at hcon
      obtain ⟨y, hy1, hy2⟩ := exists_between hcon
      have hyJ : y ∈ (J:Set ℝ) :=
        (subset_iff _ _).mp J.Ioo_subset
          (by rw [BoundedInterval.set_Ioo]; exact ⟨by linarith, hy2⟩)
      obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab hcont.continuousOn (hJsub hyJ)
      have hxK : x ∈ (K:Set ℝ) := by rw [hKset]; exact ⟨hx, by rw [hxy]; exact hyJ⟩
      have hxKb : x ≤ K.b := by
        have := K.subset_Icc x hxK; rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at this; exact this.2
      have := hmono hxKb
      rw [hxy] at this
      linarith

/-- Lemma 11.10.5 / Exercise 11.10.2-/
theorem PiecewiseConstantOn.RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f:ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: PiecewiseConstantOn f (Icc (φ a) (φ b))) :
  PiecewiseConstantOn (f ∘ φ) (Icc a b) ∧ RS_integ (f ∘ φ) (Icc a b) φ =
    integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  choose P' hf using hf
  set P := P'.remove_empty
  have hP (J: P.intervals) : (J:Set ℝ).Nonempty := by
    have hJ := J.property
    simp only [P, Partition.remove_empty, Finset.mem_filter] at hJ
    exact hJ.2
  replace hf : PiecewiseConstantWith f P := by
    intro J hJ; simp [P, (· ∈ ·)] at hJ; exact hf J hJ.1
  rw [integ_def hf]
  unfold PiecewiseConstantWith.integ
  set φ_inv : P.intervals → Set ℝ := fun J ↦ { x:ℝ | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ) }
  have hφ_inv_bounded (J: P.intervals) : Bornology.IsBounded (φ_inv J) := by
    apply Bornology.IsBounded.subset (Icc_bounded a b); intro _; aesop
  have hφ_inv_connected (J: P.intervals) : (φ_inv J).OrdConnected := by
    have hJ : (J:Set ℝ).OrdConnected := ((BoundedInterval.ordConnected_iff (J:Set ℝ)).mpr ⟨J, rfl⟩).2
    refine ⟨fun x hx y hy z hz => ?_⟩
    simp only [φ_inv, Set.mem_setOf_eq, Set.mem_Icc] at hx hy hz ⊢
    refine ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_⟩
    exact hJ.out hx.2 hy.2 (Set.mem_Icc.mpr ⟨hφ_mono hz.1, hφ_mono hz.2⟩)
  set φ_inv' : P.intervals → BoundedInterval := fun J ↦ ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose
  have hφ_inv' (J:P.intervals) : φ_inv J = φ_inv' J :=
    ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose_spec
  have hφ_inv_nonempty (J:P.intervals) : (φ_inv J).Nonempty := by
    obtain ⟨y, hy⟩ := hP J
    obtain ⟨x, hx, rfl⟩ := intermediate_value_Icc hab.le hφ_cont.continuousOn
      ((subset_iff _ _).mp (P.contains _ J.property) hy)
    exact ⟨x, hx, hy⟩
  have hφ_inv_const {J:P.intervals} : ConstantOn (f ∘ φ) (φ_inv' J) ∧ constant_value_on (f ∘ φ) (φ_inv' J) = constant_value_on f J := by
    have hfJ : ConstantOn f (J:Set ℝ) := hf J J.property
    have hmem : ∀ x ∈ (φ_inv' J : Set ℝ), φ x ∈ (J:Set ℝ) := by
      intro x hx
      rw [←hφ_inv' J] at hx
      simp only [φ_inv, Set.mem_setOf_eq] at hx
      exact hx.2
    have hconst : ConstantOn (f ∘ φ) (φ_inv' J) :=
      ⟨constant_value_on f J, fun x => ConstantOn.eq hfJ (hmem x x.property)⟩
    refine ⟨hconst, ?_⟩
    obtain ⟨x₀, hx₀⟩ := hφ_inv' J ▸ hφ_inv_nonempty J
    rw [←ConstantOn.eq hconst hx₀, ←ConstantOn.eq hfJ (hmem x₀ hx₀)]
    rfl
  have hmemset : ∀ (J : P.intervals) (y:ℝ),
      y ∈ (φ_inv' J : Set ℝ) ↔ y ∈ Set.Icc a b ∧ φ y ∈ (J:Set ℝ) := by
    intro J y; rw [←hφ_inv' J]; simp only [φ_inv, Set.mem_setOf_eq]
  have hQ_contains : ∀ K ∈ Finset.image φ_inv' Finset.univ, K ⊆ Icc a b := by
    intro K hK
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK
    obtain ⟨J, rfl⟩ := hK
    rw [subset_iff]
    intro x hx
    exact ((hmemset J x).mp hx).1
  have hQ_unique : ∀ x ∈ Icc a b, ∃! K, K ∈ Finset.image φ_inv' Finset.univ ∧ x ∈ K := by
    intro x hx
    have hxset : x ∈ Set.Icc a b := by simpa [mem_iff] using hx
    have hφx : φ x ∈ Icc (φ a) (φ b) := by
      simp only [mem_iff] at hx ⊢; exact ⟨hφ_mono hx.1, hφ_mono hx.2⟩
    obtain ⟨J', ⟨hJ'mem, hJ'x⟩, hJ'uniq⟩ := P.exists_unique (φ x) hφx
    refine ⟨φ_inv' ⟨J', hJ'mem⟩, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · exact (hmemset ⟨J', hJ'mem⟩ x).mpr ⟨hxset, hJ'x⟩
    · rintro K ⟨hKmem, hKx⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hKmem
      obtain ⟨J'', rfl⟩ := hKmem
      have : J'' = ⟨J', hJ'mem⟩ :=
        Subtype.ext (hJ'uniq _ ⟨J''.property, ((hmemset J'' x).mp hKx).2⟩)
      rw [this]
  set Q : Partition (Icc a b) := {
    intervals := .image φ_inv' .univ
    exists_unique x hx := hQ_unique x hx
    contains K hK := hQ_contains K hK
  }
  have hfφ_piecewise : PiecewiseConstantWith (f ∘ φ) Q := by
    intro K hK
    simp only [Q, Partition.mem_intervals_iff, Finset.mem_image, Finset.mem_univ, true_and] at hK
    obtain ⟨J, rfl⟩ := hK
    exact hφ_inv_const.1
  have hfφ_piecewise' : PiecewiseConstantOn (f ∘ φ) (Icc a b) := ⟨ Q, hfφ_piecewise ⟩
  refine ⟨ hfφ_piecewise' , ?_ ⟩
  rw [RS_integ_def hfφ_piecewise]
  unfold PiecewiseConstantWith.RS_integ
  rw [Finset.sum_image, ←Finset.sum_coe_sort (s := P.intervals)]
  . apply Finset.sum_congr rfl
    intro J _
    congr 1
    . exact hφ_inv_const.2
    have hne : ((φ_inv' J : BoundedInterval):Set ℝ).Nonempty := hφ_inv' J ▸ hφ_inv_nonempty J
    have hKset : ((φ_inv' J : BoundedInterval):Set ℝ)
        = {x | x ∈ Set.Icc a b ∧ φ x ∈ ((J:BoundedInterval):Set ℝ)} := (hφ_inv' J).symm
    have hJsub : ((J:BoundedInterval):Set ℝ) ⊆ Set.Icc (φ a) (φ b) := by
      have := P.contains _ J.property
      rwa [subset_iff, BoundedInterval.set_Icc] at this
    obtain ⟨hKa, hKb⟩ := preimage_endpoints hφ_cont hφ_mono hab.le hKset hne hJsub
    have hKa_le_Kb : (φ_inv' J).a ≤ (φ_inv' J).b := by
      obtain ⟨z, hz⟩ := hne
      have := (φ_inv' J).subset_Icc z hz
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at this
      exact le_trans this.1 this.2
    have hJa_le_Jb : (J:BoundedInterval).a ≤ (J:BoundedInterval).b := by
      obtain ⟨w, hw⟩ := hP J
      have := (J:BoundedInterval).subset_Icc w hw
      rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc, Set.mem_Icc] at this
      exact le_trans this.1 this.2
    have hAlen : α_length φ (φ_inv' J) = φ (φ_inv' J).b - φ (φ_inv' J).a :=
      α_length_of_cts (a := (φ_inv' J).a - 1) (b := (φ_inv' J).b + 1)
        (by linarith) hKa_le_Kb (by linarith)
        ((subset_Icc _).trans (by simp [subset_iff, Set.Icc_subset_Ioo_iff hKa_le_Kb]))
        hφ_cont.continuousOn
    rw [hAlen, hKa, hKb, BoundedInterval.length, max_eq_left (by linarith)]
  intro J _ K _ hJK
  set x := (hφ_inv_nonempty J).some
  have h1 : x ∈ φ_inv J := (hφ_inv_nonempty J).some_mem
  have h2 : x ∈ φ_inv K := by rwa [hφ_inv' J, hJK, ←hφ_inv' K] at h1
  simp [φ_inv] at h1 h2
  have h3 : φ x ∈ Icc (φ a) (φ b) := by
    have := P.contains _ J.property
    simp only [subset_iff, mem_iff] at this ⊢
    exact this h1.2
  ext; apply (P.exists_unique _ h3).unique <;> simp [J.property, K.property, mem_iff, h1, h2]

/-- Proposition 11.10.6 (Change of variables formula II)-/
theorem RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  RS_IntegrableOn (f ∘ φ) (Icc a b) φ ∧
  RS_integ (f ∘ φ) (Icc a b) φ = integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  have hf_bdd := hf.1
  have hfφ_bdd : BddOn (f ∘ φ) (Icc a b) := by
    obtain ⟨M, hM⟩ := hf_bdd
    use M
    intro x hx
    apply hM
    simp at hx ⊢
    exact ⟨hφ_mono hx.1, hφ_mono hx.2⟩
  have heq : lower_integral f (Icc (φ a) (φ b)) = upper_integral f (Icc (φ a) (φ b)) := hf.2
  have hupper : upper_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_integral f (Icc (φ a) (φ b)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    choose f_up hf_upmajor hf_upconst hf_up using lt_of_gt_upper_integral hf.1 (show upper_integral f (Icc (φ a) (φ b)) + ε > integ f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_upconst
    rw [←hpc.2] at hf_up
    have : MajorizesOn (f_up ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_upmajor; aesop
    linarith [upper_RS_integral_le_integ hfφ_bdd this hpc.1 hφ_mono]
  have hlower : lower_integral f (Icc (φ a) (φ b)) ≤ lower_RS_integral (f ∘ φ) (Icc a b) φ := by
    apply le_of_forall_sub_le
    intro ε hε
    choose f_low hf_lowminor hf_lowconst hf_low using gt_of_lt_lower_integral hf.1 (show lower_integral f (Icc (φ a) (φ b)) - ε < lower_integral f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_lowconst
    rw [←hpc.2] at hf_low
    have : MinorizesOn (f_low ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_lowminor; aesop
    linarith [integ_le_lower_RS_integral hfφ_bdd this hpc.1 hφ_mono]
  have hle : lower_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_RS_integral (f ∘ φ) (Icc a b) φ :=
    lower_RS_integral_le_upper hfφ_bdd hφ_mono
  refine ⟨ ⟨ hfφ_bdd, ?_ ⟩, ?_ ⟩ <;> linarith

/-- Proposition 11.10.7 (Change of variables formula III)-/
theorem integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    integ f (Icc (φ a) (φ b)) := by
 have h1 := RS_integ_of_comp hab hφ_cont hφ_mono hf
 have h2 := RS_integ_eq_integ_of_mul_deriv hab hφ_mono hφ_diff hφ_cont hφ' h1.1
 refine ⟨ h2.1, by aesop ⟩

/-- Reflection of a bounded interval about the origin. -/
def BoundedInterval.neg : BoundedInterval → BoundedInterval
  | Ioo a b => Ioo (-b) (-a)
  | Icc a b => Icc (-b) (-a)
  | Ioc a b => Ico (-b) (-a)
  | Ico a b => Ioc (-b) (-a)

theorem BoundedInterval.mem_neg {I : BoundedInterval} {x : ℝ} : x ∈ I.neg ↔ -x ∈ I := by
  cases I <;>
    simp only [neg, mem_iff, set_Ioo, set_Icc, set_Ioc, set_Ico,
      Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioc, Set.mem_Ico] <;>
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

@[simp] theorem BoundedInterval.neg_a {I : BoundedInterval} : I.neg.a = -I.b := by cases I <;> rfl
@[simp] theorem BoundedInterval.neg_b {I : BoundedInterval} : I.neg.b = -I.a := by cases I <;> rfl

@[simp] theorem BoundedInterval.neg_neg_self {I : BoundedInterval} : I.neg.neg = I := by
  cases I <;> simp [neg]

theorem BoundedInterval.neg_injective : Function.Injective BoundedInterval.neg :=
  Function.LeftInverse.injective (fun _ => neg_neg_self)

theorem BoundedInterval.length_neg {I : BoundedInterval} : |I.neg|ₗ = |I|ₗ := by
  simp only [length, neg_a, neg_b]; congr 1; ring

/-- Reflection of a partition about the origin. -/
noncomputable def Partition.neg {I : BoundedInterval} (P : Partition I) : Partition I.neg where
  intervals := P.intervals.image BoundedInterval.neg
  exists_unique x hx := by
    rw [BoundedInterval.mem_neg] at hx
    obtain ⟨J, ⟨hJmem, hJx⟩, hJuniq⟩ := P.exists_unique (-x) hx
    refine ⟨J.neg, ⟨Finset.mem_image_of_mem _ hJmem, BoundedInterval.mem_neg.mpr hJx⟩, ?_⟩
    rintro K ⟨hKmem, hKx⟩
    simp only [Finset.mem_image] at hKmem
    obtain ⟨K', hK'mem, rfl⟩ := hKmem
    rw [BoundedInterval.mem_neg] at hKx
    rw [hJuniq K' ⟨hK'mem, hKx⟩]
  contains K hK := by
    simp only [Finset.mem_image] at hK
    obtain ⟨J, hJmem, rfl⟩ := hK
    intro x hx
    rw [BoundedInterval.mem_neg] at hx ⊢
    exact P.contains J hJmem _ hx

@[simp] theorem Partition.neg_intervals {I : BoundedInterval} (P : Partition I) :
    (P.neg).intervals = P.intervals.image BoundedInterval.neg := rfl

theorem BddOn.comp_neg {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) :
    BddOn (fun x ↦ f (-x)) I.neg := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun x hx => hM (-x) (BoundedInterval.mem_neg.mp hx)⟩

theorem MajorizesOn.comp_neg {h f : ℝ → ℝ} {I : BoundedInterval} (hm : MajorizesOn h f I) :
    MajorizesOn (fun x ↦ h (-x)) (fun x ↦ f (-x)) I.neg :=
  fun x hx => hm (-x) (BoundedInterval.mem_neg.mp hx)

theorem MinorizesOn.comp_neg {h f : ℝ → ℝ} {I : BoundedInterval} (hm : MinorizesOn h f I) :
    MinorizesOn (fun x ↦ h (-x)) (fun x ↦ f (-x)) I.neg :=
  fun x hx => hm (-x) (BoundedInterval.mem_neg.mp hx)

theorem ConstantOn.comp_neg {h : ℝ → ℝ} {J : BoundedInterval} (hc : ConstantOn h (J:Set ℝ)) :
    ConstantOn (fun x ↦ h (-x)) (J.neg : Set ℝ) :=
  ⟨constant_value_on h (J:Set ℝ), fun x => ConstantOn.eq hc (BoundedInterval.mem_neg.mp x.property)⟩

theorem constant_value_length_neg {h : ℝ → ℝ} {J : BoundedInterval} (hc : ConstantOn h (J:Set ℝ)) :
    constant_value_on (fun x ↦ h (-x)) (J.neg : Set ℝ) * |J.neg|ₗ
      = constant_value_on h (J:Set ℝ) * |J|ₗ := by
  rw [BoundedInterval.length_neg]
  rcases eq_or_ne (|J|ₗ) 0 with hJ | hJ
  · rw [hJ, mul_zero, mul_zero]
  · have hJne : (J:Set ℝ).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; exact fun he => hJ (BoundedInterval.length_of_empty he)
    have hJnegne : (J.neg : Set ℝ).Nonempty :=
      ⟨-hJne.some, BoundedInterval.mem_neg.mpr (by simpa using hJne.some_mem)⟩
    congr 1
    exact ConstantOn.const_eq hJnegne (fun x hx => ConstantOn.eq hc (BoundedInterval.mem_neg.mp hx))

theorem PiecewiseConstantWith.integ_comp_neg {h : ℝ → ℝ} {I : BoundedInterval} {P : Partition I}
    (hP : PiecewiseConstantWith h P) :
    PiecewiseConstantWith.integ (fun x ↦ h (-x)) P.neg = PiecewiseConstantWith.integ h P := by
  simp only [PiecewiseConstantWith.integ, Partition.neg_intervals]
  rw [Finset.sum_image (fun x _ y _ hxy => BoundedInterval.neg_injective hxy)]
  exact Finset.sum_congr rfl (fun J hJ => constant_value_length_neg (hP J hJ))

theorem PiecewiseConstantOn.comp_neg {h : ℝ → ℝ} {I : BoundedInterval}
    (hh : PiecewiseConstantOn h I) : PiecewiseConstantOn (fun x ↦ h (-x)) I.neg := by
  obtain ⟨P, hP⟩ := hh
  refine ⟨P.neg, ?_⟩
  intro J' hJ'
  rw [Partition.mem_intervals_iff] at hJ'
  simp only [Partition.neg_intervals, Finset.mem_image] at hJ'
  obtain ⟨J, hJmem, rfl⟩ := hJ'
  exact (hP J hJmem).comp_neg

theorem PiecewiseConstantOn.integ_comp_neg {h : ℝ → ℝ} {I : BoundedInterval}
    (hh : PiecewiseConstantOn h I) :
    PiecewiseConstantOn.integ (fun x ↦ h (-x)) I.neg = PiecewiseConstantOn.integ h I := by
  obtain ⟨P, hP⟩ := hh
  have hP' : PiecewiseConstantWith (fun x ↦ h (-x)) P.neg := by
    intro J' hJ'
    rw [Partition.mem_intervals_iff] at hJ'
    simp only [Partition.neg_intervals, Finset.mem_image] at hJ'
    obtain ⟨J, hJmem, rfl⟩ := hJ'
    exact (hP J hJmem).comp_neg
  rw [PiecewiseConstantOn.integ_def hP', PiecewiseConstantOn.integ_def hP,
    PiecewiseConstantWith.integ_comp_neg hP]

theorem upper_integral_comp_neg_le {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) :
    upper_integral (fun x ↦ f (-x)) I.neg ≤ upper_integral f I := by
  apply csInf_le_csInf (integral_bound_below (BddOn.comp_neg hf)) (integral_bound_upper_nonempty hf)
  rintro y ⟨h, ⟨hhm, hhc⟩, rfl⟩
  exact ⟨fun x ↦ h (-x), ⟨hhm.comp_neg, hhc.comp_neg⟩, PiecewiseConstantOn.integ_comp_neg hhc⟩

theorem upper_integral_comp_neg {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) :
    upper_integral (fun x ↦ f (-x)) I.neg = upper_integral f I := by
  refine le_antisymm (upper_integral_comp_neg_le hf) ?_
  simpa using upper_integral_comp_neg_le (f := fun x ↦ f (-x)) (I := I.neg) (BddOn.comp_neg hf)

theorem lower_integral_comp_neg_le {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) :
    lower_integral f I ≤ lower_integral (fun x ↦ f (-x)) I.neg := by
  apply csSup_le_csSup (integral_bound_above (BddOn.comp_neg hf)) (integral_bound_lower_nonempty hf)
  rintro y ⟨h, ⟨hhm, hhc⟩, rfl⟩
  exact ⟨fun x ↦ h (-x), ⟨hhm.comp_neg, hhc.comp_neg⟩, PiecewiseConstantOn.integ_comp_neg hhc⟩

theorem lower_integral_comp_neg {f : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) :
    lower_integral (fun x ↦ f (-x)) I.neg = lower_integral f I := by
  refine le_antisymm ?_ (lower_integral_comp_neg_le hf)
  simpa using lower_integral_comp_neg_le (f := fun x ↦ f (-x)) (I := I.neg) (BddOn.comp_neg hf)

theorem integ_comp_neg {f : ℝ → ℝ} {I : BoundedInterval} (hf : IntegrableOn f I) :
    IntegrableOn (fun x ↦ f (-x)) I.neg ∧ integ (fun x ↦ f (-x)) I.neg = integ f I := by
  obtain ⟨hbd, heq⟩ := hf
  refine ⟨⟨BddOn.comp_neg hbd, ?_⟩, upper_integral_comp_neg hbd⟩
  rw [lower_integral_comp_neg hbd, upper_integral_comp_neg hbd]; exact heq

/- Exercise 11.10.4: state and prove a version of `integ_of_comp` in which `φ` is `Antitone` rather than `Monotone`. -/
theorem integ_of_comp_anti {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_anti: Antitone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ b) (φ a))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    -integ f (Icc (φ b) (φ a)) := by
  set ψ : ℝ → ℝ := fun x ↦ -φ x with hψ
  have hψ_mono : Monotone ψ := fun x y h => by simp only [hψ]; exact neg_le_neg (hφ_anti h)
  have hψ_cont : Continuous ψ := by rw [hψ]; exact hφ_cont.neg
  have hψ_diff : DifferentiableOn ℝ ψ (Icc a b) := by rw [hψ]; exact hφ_diff.neg
  have hIcc : Icc (ψ a) (ψ b) = (Icc (φ b) (φ a)).neg := rfl
  have hderiv_psi : ∀ x ∈ ((Icc a b : BoundedInterval) : Set ℝ),
      derivWithin ψ (Icc a b) x = -derivWithin φ (Icc a b) x := by
    intro x hx
    have huniq : UniqueDiffWithinAt ℝ ((Icc a b : BoundedInterval) : Set ℝ) x := by
      rw [BoundedInterval.set_Icc] at hx ⊢; exact uniqueDiffOn_Icc hab x hx
    rw [hψ]
    exact (((hφ_diff x hx).hasDerivWithinAt).neg).derivWithin huniq
  have hψ' : IntegrableOn (derivWithin ψ (Icc a b)) (Icc a b) :=
    (IntegrableOn.congr' (fun x hx => hderiv_psi x hx) (IntegrableOn.neg hφ').1).1
  have hf_tilde : IntegrableOn (fun y ↦ f (-y)) (Icc (ψ a) (ψ b)) := by
    rw [hIcc]; exact (integ_comp_neg hf).1
  obtain ⟨hint_psi, heq_psi⟩ := integ_of_comp hab hψ_diff hψ_cont hψ_mono hψ' hf_tilde
  have hEqOn : Set.EqOn ((fun y ↦ f (-y)) ∘ ψ * derivWithin ψ (Icc a b))
      (-(f ∘ φ * derivWithin φ (Icc a b))) ((Icc a b : BoundedInterval) : Set ℝ) := by
    intro x hx
    simp only [Pi.mul_apply, Function.comp_apply, Pi.neg_apply]
    rw [hderiv_psi x hx, hψ]
    simp only [neg_neg]
    ring
  obtain ⟨hng_int, hng_eq⟩ := IntegrableOn.congr' hEqOn.symm hint_psi
  have hg_int : IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) := by
    simpa using (IntegrableOn.neg hng_int).1
  refine ⟨hg_int, ?_⟩
  have key : integ ((fun y ↦ f (-y)) ∘ ψ * derivWithin ψ (Icc a b)) (Icc a b)
      = integ f (Icc (φ b) (φ a)) := by
    rw [heq_psi, hIcc]; exact (integ_comp_neg hf).2
  have hval : integ ((fun y ↦ f (-y)) ∘ ψ * derivWithin ψ (Icc a b)) (Icc a b)
      = -integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) := by
    rw [← hng_eq]; exact (IntegrableOn.neg hg_int).2
  linarith [key, hval]

/-- Exercise 11.10.3-/
example {a b:ℝ} (hab: a < b) {f: ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) ∧
  integ (fun x ↦ f (-x)) (Icc (-b) (-a)) = integ f (Icc a b) := by
  have hab' : (-b:ℝ) < -a := by linarith
  set φ : ℝ → ℝ := fun x ↦ -x with hφ
  have hval1 : φ (-a) = a := by simp [hφ]
  have hval2 : φ (-b) = b := by simp [hφ]
  have hφ_diff : DifferentiableOn ℝ φ (Icc (-b) (-a)) := by rw [hφ]; fun_prop
  have hφ_cont : Continuous φ := by rw [hφ]; fun_prop
  have hφ_anti : Antitone φ := by intro x y hxy; simp only [hφ]; linarith
  have hderiv : ∀ x ∈ ((Icc (-b) (-a):BoundedInterval):Set ℝ),
      derivWithin φ (Icc (-b) (-a)) x = -1 := by
    intro x hx
    rw [BoundedInterval.set_Icc] at hx
    rw [hφ]
    exact ((hasDerivAt_id x).neg.hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc hab' x hx)
  have hconst : Set.EqOn (derivWithin φ (Icc (-b) (-a))) (fun _ ↦ (-1:ℝ))
      ((Icc (-b) (-a):BoundedInterval):Set ℝ) := fun x hx => hderiv x hx
  have hφ' : IntegrableOn (derivWithin φ (Icc (-b) (-a))) (Icc (-b) (-a)) :=
    (IntegrableOn.congr' hconst (integ_of_cts continuous_const.continuousOn)).1
  obtain ⟨hint, heq⟩ := integ_of_comp_anti (f := -f) (a := -b) (b := -a)
    hab' hφ_diff hφ_cont hφ_anti hφ'
    (show IntegrableOn (-f) (Icc (φ (-a)) (φ (-b))) by rw [hval1, hval2]; exact (IntegrableOn.neg hf).1)
  have hEq : Set.EqOn (fun x ↦ f (-x)) ((-f) ∘ φ * derivWithin φ (Icc (-b) (-a)))
      ((Icc (-b) (-a):BoundedInterval):Set ℝ) := by
    intro x hx
    simp only [Pi.mul_apply]
    rw [hderiv x hx]
    simp only [Function.comp_apply, Pi.neg_apply, hφ]
    ring
  obtain ⟨hg_int, hg_eq⟩ := IntegrableOn.congr' hEq hint
  refine ⟨hg_int, ?_⟩
  rw [hg_eq, heq, hval1, hval2, (IntegrableOn.neg hf).2, neg_neg]

end Chapter11
