import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_2

/-!
# Analysis I, Section 11.3: Upper and lower Riemann integrals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The upper and lower Riemann integral; the Riemann integral.
- Upper and lower Riemann sums.

-/

namespace Chapter11
open BoundedInterval Chapter9

/-- Definition 11.3.1 (Majorization of functions) -/
abbrev MajorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), f x ≤ g x

abbrev MinorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), g x ≤ f x

theorem MinorizesOn.iff (g f:ℝ → ℝ) (I: BoundedInterval) : MinorizesOn g f I ↔ MajorizesOn f g I := by rfl

/-- Definition 11.3.2 (Uppper and lower Riemann integrals )-/
noncomputable abbrev upper_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sInf ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sSup ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

theorem upper_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  upper_integral f I = upper_integral g I := by
  simp [upper_integral]; congr! 2; ext; simp; grind

theorem lower_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  lower_integral f I = lower_integral g I := by
  simp [lower_integral]; congr! 2; ext; simp; grind

lemma integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) : M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine' ⟨ fun _ ↦ M , ⟨ ⟨ _, _ ⟩, PiecewiseConstantOn.integ_const _ _ ⟩ ⟩
  . grind [abs_le']
  apply (ConstantOn.of_const (c := M) _).piecewiseConstantOn; simp

lemma integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) : -M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine' ⟨ fun _ ↦ -M , ⟨ ⟨ _, _ ⟩, by convert PiecewiseConstantOn.integ_const _ _ using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn

lemma integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_upper_of_bounded h.choose_spec ⟩

lemma integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_lower_of_bounded h.choose_spec ⟩

lemma integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  (ha: a ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    obtain ⟨ g, ⟨ ⟨ hmaj, hgp⟩, rfl ⟩ ⟩ := ha
    obtain ⟨ h, ⟨ ⟨ hmin, hhp⟩, rfl ⟩ ⟩ := hb
    apply hhp.integ_mono _ hgp; intro x hx; linarith [hmin _ hx, hmaj _ hx]

lemma integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddBelow ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (integral_bound_lower_nonempty h).some
    intro a ha; exact integral_bound_lower_le_upper ha (integral_bound_lower_nonempty h).some_mem

lemma integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddAbove ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (integral_bound_upper_nonempty h).some
    intro b hb; exact integral_bound_lower_le_upper (integral_bound_upper_nonempty h).some_mem hb

/-- Lemma 11.3.3.  The proof has been reorganized somewhat from the textbook. -/
lemma le_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  -M * |I|ₗ ≤ lower_integral f I :=
  le_csSup (integral_bound_above (BddOn.of_bounded h)) (integral_bound_lower_of_bounded h)

lemma lower_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  lower_integral f I ≤ upper_integral f I := by
  apply csSup_le (integral_bound_lower_nonempty h)
  intros
  apply le_csInf (integral_bound_upper_nonempty h)
  intros
  solve_by_elim [integral_bound_lower_le_upper]

lemma upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  upper_integral f I ≤ M * |I|ₗ :=
  csInf_le (integral_bound_below (BddOn.of_bounded h)) (integral_bound_upper_of_bounded h)

lemma upper_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I) :
  upper_integral f I ≤ hg.integ' := by
  apply csInf_le (integral_bound_below hf) _
  use g; simpa [hg]

lemma integ_le_lower_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I) :
  hg.integ' ≤ lower_integral f I := by
  apply le_csSup (integral_bound_above hf) _
  use h; simpa [hg]

lemma lt_of_gt_upper_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: upper_integral f I < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.integ g I < X := by
  choose Y hY hYX using exists_lt_of_csInf_lt (integral_bound_upper_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto

lemma gt_of_lt_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: X < lower_integral f I) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.integ h I := by
  choose Y hY hYX using exists_lt_of_lt_csSup (integral_bound_lower_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto

/-- Definition 11.3.4 (Riemann integral)
As we permit junk values, the simplest definition for the Riemann integral is the upper integral.-/
noncomputable abbrev integ (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := upper_integral f I

theorem integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  integ f I = integ g I := upper_integral_congr h

noncomputable abbrev IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  BddOn f I ∧ lower_integral f I = upper_integral f I

theorem bounded_of_piecewise_constant {I : BoundedInterval} {f : ℝ → ℝ} (hf: PiecewiseConstantOn f I) : BddOn f I := by
  obtain ⟨ P, hP ⟩ := hf
  refine BddOn.of_bounded (M := ∑ J ∈ P.intervals, |constant_value_on f (J:Set ℝ)|) ?_
  intro x hx
  obtain ⟨ J, ⟨ hJ, hxJ ⟩, _ ⟩ := P.exists_unique x hx
  rw [ConstantOn.eq (hP J hJ) hxJ]
  exact Finset.single_le_sum
    (f := fun J : BoundedInterval => |constant_value_on f (J:Set ℝ)|)
    (fun _ _ => abs_nonneg _) hJ

theorem self_majorizes {I : BoundedInterval} {f : ℝ → ℝ} : MajorizesOn f f I := by
  intro x hx
  rfl

theorem self_minorizes {I : BoundedInterval} {f : ℝ → ℝ} : MinorizesOn f f I := by
  intro x hx
  rfl

/-- Lemma 11.3.7 / Exercise 11.3.3 -/
theorem integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) :
  IntegrableOn f I ∧ integ f I = hf.integ' := by
  have h1 := upper_integral_le_integ (bounded_of_piecewise_constant hf) (self_majorizes) hf
  have h2 := integ_le_lower_integral (bounded_of_piecewise_constant hf) (self_minorizes) hf
  have h3 := lower_integral_le_upper (bounded_of_piecewise_constant hf)
  constructor
  . rw [IntegrableOn]
    constructor
    . exact bounded_of_piecewise_constant hf
    . linarith
  . rw [integ]
    linarith

/-- Remark 11.3.8 -/
theorem integ_on_subsingleton {f:ℝ → ℝ} {I: BoundedInterval} (hI: |I|ₗ = 0) :
  IntegrableOn f I ∧ integ f I = 0 := by
  observe : Subsingleton I.toSet
  observe hconst : ConstantOn f I
  convert integ_of_piecewise_const hconst.piecewiseConstantOn
  simp [PiecewiseConstantOn.integ_const' hconst, hI]

/-- Definition 11.3.9 (Riemann sums).  The restriction to positive length J is not needed thanks to various junk value conventions. -/
noncomputable abbrev upper_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ

noncomputable abbrev lower_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ

/-- Lemma 11.3.11 / Exercise 11.3.4 -/
theorem upper_riemann_sum_le {f g: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
    (hgf: MajorizesOn g f I) (hg: PiecewiseConstantWith g P) :
    upper_riemann_sum f P ≤ integ g I := by
  have hg' : PiecewiseConstantOn g I := ⟨P, hg⟩
  rw [(integ_of_piecewise_const hg').2.trans (PiecewiseConstantOn.integ_def hg)]
  apply Finset.sum_le_sum
  intros J hJ
  rcases Set.eq_empty_or_nonempty (J:Set ℝ) with hJe | hJne
  · rw [BoundedInterval.length_of_empty hJe, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ?_ (BoundedInterval.length_nonneg J)
    refine csSup_le (hJne.image f) ?_
    rintro _ ⟨x, hxJ, rfl⟩
    rw [← ConstantOn.eq (hg J hJ) hxJ]
    exact hgf x (P.contains J hJ x hxJ)

theorem lower_riemann_sum_ge {f h: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
    (hfh: MinorizesOn h f I) (hg: PiecewiseConstantWith h P) :
    integ h I ≤ lower_riemann_sum f P := by
  have hg' : PiecewiseConstantOn h I := ⟨P, hg⟩
  rw [(integ_of_piecewise_const hg').2.trans (PiecewiseConstantOn.integ_def hg)]
  apply Finset.sum_le_sum
  intros J hJ
  rcases Set.eq_empty_or_nonempty (J:Set ℝ) with hJe | hJne
  · rw [BoundedInterval.length_of_empty hJe, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right ?_ (BoundedInterval.length_nonneg J)
    refine le_csInf (hJne.image f) ?_
    rintro _ ⟨x, hxJ, rfl⟩
    rw [← ConstantOn.eq (hg J hJ) hxJ]
    exact hfh x (P.contains J hJ x hxJ)

/-- Proposition 11.3.12 / Exercise 11.3.5 -/
theorem upper_integ_le_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
    (P: Partition I): upper_integral f I ≤ upper_riemann_sum f P := by
  classical
  set f' : ℝ → ℝ :=
    fun x => ∑ J ∈ P.intervals, if x ∈ J then sSup (f '' (J:Set ℝ)) else 0
  have hf'_eq : ∀ J ∈ P.intervals, ∀ x ∈ (J:Set ℝ), f' x = sSup (f '' (J:Set ℝ)) := by
    intros J hJ x hx
    show (∑ K ∈ P.intervals, if x ∈ K then sSup (f '' (K:Set ℝ)) else 0) = sSup (f '' (J:Set ℝ))
    rw [Finset.sum_eq_single J]
    · exact if_pos hx
    · intros K hK hKne
      refine if_neg ?_
      intro hxK
      have hxI : x ∈ (I:Set ℝ) := P.contains J hJ x hx
      exact hKne ((P.exists_unique x hxI).unique ⟨hK, hxK⟩ ⟨hJ, hx⟩)
    · intro h; exact absurd hJ h
  have hf'P : PiecewiseConstantWith f' P := fun J hJ =>
    ConstantOn.of_const (c := sSup (f '' (J:Set ℝ))) (hf'_eq J hJ)
  have hf'C : PiecewiseConstantOn f' I := ⟨P, hf'P⟩
  have hf' : MajorizesOn f' f I := by
    intro x hx
    obtain ⟨ J, ⟨ hJ, hxJ ⟩, _ ⟩ := P.exists_unique x hx
    rw [hf'_eq J hJ x hxJ]
    refine le_csSup ?_ (Set.mem_image_of_mem f hxJ)
    obtain ⟨M, hM⟩ := hf
    exact ⟨M, by rintro _ ⟨z, hz, rfl⟩; exact (abs_le.mp (hM z (P.contains J hJ z hz))).2⟩
  refine (upper_integral_le_integ hf hf' hf'C).trans ?_
  show PiecewiseConstantOn.integ f' I ≤ ∑ J ∈ P.intervals, sSup (f '' (J:Set ℝ)) * |J|ₗ
  rw [PiecewiseConstantOn.integ_def hf'P]
  apply Finset.sum_le_sum
  intros J hJ
  rcases Set.eq_empty_or_nonempty (J:Set ℝ) with hJe | hJne
  · rw [BoundedInterval.length_of_empty hJe, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right
      (ConstantOn.const_eq hJne (hf'_eq J hJ)).le (BoundedInterval.length_nonneg J)

theorem upper_integ_eq_inf_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  upper_integral f I = sInf (.range (fun P : Partition I ↦ upper_riemann_sum f P)) := by
  have hbdd : BddBelow (Set.range (fun P : Partition I ↦ upper_riemann_sum f P)) :=
    ⟨upper_integral f I, by rintro _ ⟨P, rfl⟩; exact upper_integ_le_upper_sum hf P⟩
  apply le_antisymm
  · refine le_csInf ?_ ?_
    · exact ⟨upper_riemann_sum f (⊥ : Partition I), (⊥ : Partition I), rfl⟩
    · rintro _ ⟨P, rfl⟩
      exact upper_integ_le_upper_sum hf P
  · apply le_csInf (integral_bound_upper_nonempty hf)
    rintro _ ⟨g, ⟨hgf, hgC⟩, rfl⟩
    obtain ⟨P, hP⟩ := hgC
    calc sInf _ ≤ upper_riemann_sum f P := csInf_le hbdd ⟨P, rfl⟩
      _ ≤ integ g I := upper_riemann_sum_le P hgf hP
      _ = PiecewiseConstantOn.integ g I := (integ_of_piecewise_const ⟨P, hP⟩).2

theorem lower_integ_ge_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
    (P: Partition I): lower_riemann_sum f P ≤ lower_integral f I := by
  classical
  set h' : ℝ → ℝ :=
    fun x => ∑ J ∈ P.intervals, if x ∈ J then sInf (f '' (J:Set ℝ)) else 0
  have hh'_eq : ∀ J ∈ P.intervals, ∀ x ∈ (J:Set ℝ), h' x = sInf (f '' (J:Set ℝ)) := by
    intros J hJ x hx
    show (∑ K ∈ P.intervals, if x ∈ K then sInf (f '' (K:Set ℝ)) else 0) = sInf (f '' (J:Set ℝ))
    rw [Finset.sum_eq_single J]
    · exact if_pos hx
    · intros K hK hKne
      refine if_neg ?_
      intro hxK
      have hxI : x ∈ (I:Set ℝ) := P.contains J hJ x hx
      exact hKne ((P.exists_unique x hxI).unique ⟨hK, hxK⟩ ⟨hJ, hx⟩)
    · intro h; exact absurd hJ h
  have hh'P : PiecewiseConstantWith h' P := fun J hJ =>
    ConstantOn.of_const (c := sInf (f '' (J:Set ℝ))) (hh'_eq J hJ)
  have hh'C : PiecewiseConstantOn h' I := ⟨P, hh'P⟩
  have hh' : MinorizesOn h' f I := by
    intro x hx
    obtain ⟨ J, ⟨ hJ, hxJ ⟩, _ ⟩ := P.exists_unique x hx
    rw [hh'_eq J hJ x hxJ]
    refine csInf_le ?_ (Set.mem_image_of_mem f hxJ)
    obtain ⟨M, hM⟩ := hf
    exact ⟨-M, by rintro _ ⟨z, hz, rfl⟩; exact (abs_le.mp (hM z (P.contains J hJ z hz))).1⟩
  refine le_trans ?_ (integ_le_lower_integral hf hh' hh'C)
  show ∑ J ∈ P.intervals, sInf (f '' (J:Set ℝ)) * |J|ₗ ≤ PiecewiseConstantOn.integ h' I
  rw [PiecewiseConstantOn.integ_def hh'P]
  apply Finset.sum_le_sum
  intros J hJ
  rcases Set.eq_empty_or_nonempty (J:Set ℝ) with hJe | hJne
  · rw [BoundedInterval.length_of_empty hJe, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right
      (ConstantOn.const_eq hJne (hh'_eq J hJ)).ge (BoundedInterval.length_nonneg J)

theorem lower_integ_eq_sup_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  lower_integral f I = sSup (.range (fun P : Partition I ↦ lower_riemann_sum f P)) := by
  have hbdd : BddAbove (Set.range (fun P : Partition I ↦ lower_riemann_sum f P)) :=
    ⟨lower_integral f I, by rintro _ ⟨P, rfl⟩; exact lower_integ_ge_lower_sum hf P⟩
  apply le_antisymm
  · refine csSup_le (integral_bound_lower_nonempty hf) ?_
    rintro _ ⟨h, ⟨hhf, hhC⟩, rfl⟩
    obtain ⟨P, hP⟩ := hhC
    calc PiecewiseConstantOn.integ h I
        = integ h I := ((integ_of_piecewise_const ⟨P, hP⟩).2).symm
      _ ≤ lower_riemann_sum f P := lower_riemann_sum_ge P hhf hP
      _ ≤ sSup _ := le_csSup hbdd ⟨P, rfl⟩
  · refine csSup_le ?_ ?_
    · exact ⟨lower_riemann_sum f (⊥ : Partition I), (⊥ : Partition I), rfl⟩
    · rintro _ ⟨P, rfl⟩
      exact lower_integ_ge_lower_sum hf P

/-- Exercise 11.3.1 -/
theorem MajorizesOn.trans {f g h: ℝ → ℝ} {I: BoundedInterval}
  (hfg: MajorizesOn f g I) (hgh: MajorizesOn g h I) : MajorizesOn f h I := by
  rw [MajorizesOn] at hfg hgh ⊢
  intro x hx
  specialize hfg x hx
  specialize hgh x hx
  linarith

/-- Exercise 11.3.1 -/
theorem MajorizesOn.anti_symm {f g: ℝ → ℝ} {I: BoundedInterval}:
  (∀ x ∈ (I:Set ℝ), f x = g x) ↔ MajorizesOn f g I ∧ MajorizesOn g f I := by
  constructor
  . intro h
    repeat rw [MajorizesOn]
    constructor
    . intro x hx
      specialize h x hx
      rw [h]
    . intro x hx
      specialize h x hx
      rw [h]
  . rintro ⟨hfg, hgf⟩
    rw [MajorizesOn] at hfg hgf
    intro x hx
    specialize hfg x hx
    specialize hgf x hx
    linarith

/-- Exercise 11.3.2 -/
def MajorizesOn.of_add : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (_: MajorizesOn f g I),
 MajorizesOn (f+h) (g+h) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  intros f g h I hfg x hx
  rw [MajorizesOn] at hfg
  specialize hfg x hx
  simp only [Pi.add_apply, add_le_add_iff_right]
  exact hfg

def MajorizesOn.of_mul : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (_: MajorizesOn f g I),
 MajorizesOn (f*h) (g*h) I) := by
  apply isFalse
  push Not
  use fun _ => 1
  use fun _ => 0
  use fun _ => -1
  use BoundedInterval.Icc 0 1
  simp
  constructor
  . rw [MajorizesOn]
    intro x hx
    norm_num
  . use 0
    simp

def MajorizesOn.of_smul : Decidable ( ∀ (f g:ℝ → ℝ) (c:ℝ) (I:BoundedInterval) (_: MajorizesOn f g I),
 MajorizesOn (c • f) (c • g) I) := by
  apply isFalse
  push Not
  use fun _ => 1
  use fun _ => 0
  use -1
  use BoundedInterval.Icc 0 1
  simp
  constructor
  . rw [MajorizesOn]
    intro x hx
    norm_num
  . use 0
    norm_num

end Chapter11
