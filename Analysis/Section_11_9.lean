import Mathlib.Tactic
import Mathlib.Topology.ContinuousOn
import Analysis.Section_7_3
import Analysis.Section_9_4
import Analysis.Section_9_8
import Analysis.Section_10_1
import Analysis.Section_10_2
import Analysis.Section_10_3
import Analysis.Section_11_6
import Analysis.Section_11_8


/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/

namespace Chapter11
open Chapter9 Chapter10 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus)-/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  choose M hM using hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx.1 (le_of_lt hxy))).2
    simp [F, this.2, abs_le']
    constructor
    . convert this.1.mono (g := fun _ ↦ M) (IntegrableOn.const _ _).1 _
      . simp [IntegrableOn.const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at *; grind
      grind [abs_le']
    rw [neg_le]
    convert (IntegrableOn.const _ _).1.mono (f := fun _ ↦ -M) this.1 _
    . simp [IntegrableOn.const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at *; grind
    grind [abs_le']
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    obtain h | rfl | h := lt_trichotomy x y
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; apply le_max_left
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (_: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (.Icc a b) x₀ := by
  -- This proof is written to follow the structure of the original text.
  rw [HasDerivWithinAt.iff_approx_linear]
  simp [(ContinuousWithinAt.tfae _ f x₀).out 0 2] at hcts
  peel hcts with ε hε δ hδ hconv; intro y hy hyδ
  obtain hx₀y | rfl | hx₀y := lt_trichotomy x₀ y
  . have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx₀.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_pos (show 0 < y - x₀ by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y] at h1 h2
      split_ands
      . convert h1 using 1; ring
      . simp [←sub_nonneg] at *; convert h2 using 1; ring
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith
  . simp
  . have := ((hf.join (join_Icc_Ioc hx₀.1 hx₀.2)).1.join (join_Icc_Ioc hy.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_neg (show y - x₀ < 0 by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y] at h1 h2
      simp only [show (Ioc y x₀).b = x₀ from rfl, show (Ioc y x₀).a = y from rfl] at h1 h2
      constructor <;> linarith
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith

/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) :=
  integ_of_monotone (StrictMonoOn.of_f_9_8_5.mono (by simp)).monotoneOn

noncomputable abbrev F_11_9_2 := fun x ↦ integ f_9_8_5 (Icc 0 x)

theorem ContinuousOn.of_F_11_9_2 : ContinuousOn F_11_9_2 (.Icc 0 1) := cts_of_integ IntegrableOn.of_f_9_8_5

theorem DifferentiableOn.of_F_11_9_2 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) (hx': x ∈ Set.Icc 0 1) :
  DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) x := by
  have := deriv_of_integ (show 0 < 1 by norm_num) .of_f_9_8_5 hx' (ContinuousAt.of_f_9_8_5 hx).continuousWithinAt
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at this
  exact ⟨_, this⟩

/-- If {name}`f` is bounded above by {name}`cl` to the left of {name}`x₀` and below by {name}`cr`
to the right (with {name}`cl` < {name}`cr`), then its integral has separated one-sided difference
quotients at {name}`x₀`, hence is not differentiable there.  This packages the squeeze argument of
Exercise 11.9.1 for an arbitrary (one-sided) jump. -/
private lemma not_diff_of_jump {a b x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b)
    {f : ℝ → ℝ} (hint : IntegrableOn f (Icc a b))
    {cl cr : ℝ} (hgap : cl < cr)
    (hLb : ∀ t ∈ Set.Ioo a x₀, f t ≤ cl)
    (hRb : ∀ t ∈ Set.Ioc x₀ b, cr ≤ f t) :
    ¬ DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ := by
  obtain ⟨hax₀, hx₀b⟩ := hx₀
  intro hdiff
  set F : ℝ → ℝ := fun x => integ f (Icc a x) with hFdef
  -- right of x₀ the average of f is at least cr
  have hright : ∀ y:ℝ, x₀ < y → y ≤ b → cr * (y - x₀) ≤ F y - F x₀ := by
    intro y hx₀y hyb
    have hy0 : a ≤ y := le_of_lt (lt_trans hax₀ hx₀y)
    have hsplit := ((hint.join (join_Icc_Ioc hy0 hyb)).1.join (join_Icc_Ioc hax₀.le hx₀y.le)).2
    have hFF : F y - F x₀ = integ f (Ioc x₀ y) := by
      show integ f (Icc a y) - integ f (Icc a x₀) = integ f (Ioc x₀ y)
      rw [hsplit.2]; ring
    have hmaj : MajorizesOn f (fun _ ↦ cr) (Ioc x₀ y) := by
      intro t ht; rw [set_Ioc] at ht; exact hRb t ⟨ht.1, le_trans ht.2 hyb⟩
    have hmono := IntegrableOn.mono (IntegrableOn.const cr (Ioc x₀ y)).1 hsplit.1 hmaj
    rw [(IntegrableOn.const cr (Ioc x₀ y)).2] at hmono
    have hlen : |Ioc x₀ y|ₗ = y - x₀ := by
      simp only [length, BoundedInterval.a, BoundedInterval.b]; exact max_eq_left (by linarith)
    rw [hlen] at hmono
    rw [hFF]; exact hmono
  -- left of x₀ the average of f is at most cl (the endpoint x₀ is dropped via `Ioo`)
  have hleft : ∀ y:ℝ, a ≤ y → y < x₀ → F x₀ - F y ≤ cl * (x₀ - y) := by
    intro y hay hyx₀
    have hsplit := ((hint.join (join_Icc_Ioc hax₀.le hx₀b.le)).1.join (join_Icc_Ioc hay hyx₀.le)).2
    have hjoin := hsplit.1.join (join_Ioo_Icc hyx₀ (le_refl x₀))
    have hpt : integ f (Icc x₀ x₀) = 0 :=
      (integ_on_subsingleton (by simp [length, BoundedInterval.a, BoundedInterval.b])).2
    have hFF : F x₀ - F y = integ f (Ioo y x₀) := by
      show integ f (Icc a x₀) - integ f (Icc a y) = integ f (Ioo y x₀)
      rw [hsplit.2, hjoin.2.2, hpt]; ring
    have hmaj : MajorizesOn (fun _ ↦ cl) f (Ioo y x₀) := by
      intro t ht; rw [set_Ioo] at ht; exact hLb t ⟨lt_of_le_of_lt hay ht.1, ht.2⟩
    have hmono := IntegrableOn.mono hjoin.1 (IntegrableOn.const cl (Ioo y x₀)).1 hmaj
    rw [(IntegrableOn.const cl (Ioo y x₀)).2] at hmono
    have hlen : |Ioo y x₀|ₗ = x₀ - y := by
      simp only [length, BoundedInterval.a, BoundedInterval.b]; exact max_eq_left (by linarith)
    rw [hlen] at hmono
    rw [hFF]; exact hmono
  -- a derivative would be squeezed between `cl` and `cr`
  have hLder := hdiff.hasDerivWithinAt
  set L := derivWithin F (Icc a b) x₀ with hLdef
  rw [HasDerivWithinAt.iff_approx_linear] at hLder
  obtain ⟨δ, hδ, hball⟩ := hLder ((cr - cl) / 4) (by linarith)
  set yr : ℝ := min b (x₀ + δ/2) with hyr
  have hyr_lt : x₀ < yr := lt_min hx₀b (by linarith)
  have hyr_le : yr ≤ b := min_le_left _ _
  have hyr_mem : yr ∈ Set.Icc a b := ⟨by linarith, hyr_le⟩
  have hposr : (0:ℝ) < yr - x₀ := by linarith
  have hyr_δ : |yr - x₀| < δ := by
    rw [abs_of_pos hposr]
    calc yr - x₀ ≤ (x₀ + δ/2) - x₀ := by rw [hyr]; gcongr; exact min_le_right _ _
      _ < δ := by linarith
  set yl : ℝ := max a (x₀ - δ/2) with hyl
  have hyl_lt : yl < x₀ := max_lt hax₀ (by linarith)
  have hyl_ge : a ≤ yl := le_max_left _ _
  have hyl_mem : yl ∈ Set.Icc a b := ⟨hyl_ge, by linarith⟩
  have hposl : (0:ℝ) < x₀ - yl := by linarith
  have hyl_δ : |yl - x₀| < δ := by
    rw [abs_of_neg (by linarith : yl - x₀ < 0)]
    calc -(yl - x₀) = x₀ - yl := by ring
      _ ≤ x₀ - (x₀ - δ/2) := by rw [hyl]; gcongr; exact le_max_right _ _
      _ < δ := by linarith
  have er := hball yr hyr_mem hyr_δ
  have el := hball yl hyl_mem hyl_δ
  rw [abs_le, abs_of_pos hposr] at er
  rw [abs_le, abs_of_neg (by linarith : yl - x₀ < 0)] at el
  have hb_r := hright yr hyr_lt hyr_le
  have hb_l := hleft yl hyl_ge hyl_lt
  have hA : cr - (cr - cl) / 4 ≤ L := by nlinarith [er.2, hb_r, hposr]
  have hB : L ≤ cl + (cr - cl) / 4 := by nlinarith [el.2, hb_l, hposl]
  linarith [hA, hB, hgap]

/-- Exercise 11.9.1 -/
theorem DifferentiableOn.of_F_11_9_2' {q:ℚ} (hq: (q:ℝ) ∈ Set.Ioo 0 1) :
    ¬ DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) q := by
  have hg : 0 < g_9_8_5 q := by positivity
  -- this is the special case of `not_diff_of_jump` with the jump `g_9_8_5 q` at `q`:
  -- `f_9_8_5` is left-continuous (`≤ f_9_8_5 q` below `q`) and jumps up by `g_9_8_5 q` above `q`.
  exact not_diff_of_jump (cl := f_9_8_5 q) (cr := f_9_8_5 q + g_9_8_5 q) hq
    IntegrableOn.of_f_9_8_5 (by linarith)
    (fun t ht => StrictMonoOn.of_f_9_8_5.monotoneOn (Set.mem_univ t) (Set.mem_univ (q:ℝ)) ht.2.le)
    (fun t ht => f_9_8_5_jump q ht.1)

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

theorem AntiderivOn.mono {F f: ℝ → ℝ} {I J: BoundedInterval}
  (h: AntiderivOn F f I) (hIJ: J ⊆ I) : AntiderivOn F f J :=
  ⟨ h.1.mono hIJ, by intro x hx; rw [subset_iff] at hIJ; exact (h.2 x (hIJ hx)).mono hIJ ⟩

/-- Theorem 11.9.4 (Second Fundamental Theorem of Calculus) -/
theorem integ_eq_antideriv_sub {a b:ℝ} (h:a ≤ b) {f F: ℝ → ℝ}
  (hf: IntegrableOn f (Icc a b)) (hF: AntiderivOn F f (Icc a b)) :
  integ f (Icc a b) = F b - F a := by
  -- This proof is written to follow the structure of the original text.
  obtain h | h := lt_or_eq_of_le h
  . have hF_cts : ContinuousOn F (.Icc a b) := by
      intro x hx; exact ContinuousWithinAt.of_differentiableWithinAt (hF.1 x hx)
    -- for technical reasons we need to extend F by constant outside of Icc a b
    let F' : ℝ → ℝ := fun x ↦ F (max (min x b) a)

    have hFF' {x:ℝ} (hx: x ∈ Set.Icc a b) : F' x = F x := by simp_all [F']

    have hF'_cts : ContinuousOn F' (Ioo (a-1) (b+1)) := by
      convert (hF_cts.comp_continuous (f := fun x ↦ max (min x b) a) (by fun_prop) ?_).continuousOn using 1
      intros; simp [le_of_lt h]

    have hupper (P: Partition (Icc a b)) : upper_riemann_sum f P ≥ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≥ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ = F' d - F' c := rfl
                _ = (d - c) * f e := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
                _ = f e * |J|ₗ := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ ≤ _ := by
                  gcongr; apply le_csSup
                  . rw [bddAbove_def]
                    choose M hM using hf.1; use M
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); tauto
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = _ := by congr 1 <;> apply hFF' <;> grind
    have hlower (P: Partition (Icc a b)) : lower_riemann_sum f P ≤ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≤ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ ≤ f e * |J|ₗ := by
                  gcongr; apply csInf_le
                  . rw [bddBelow_def]
                    choose M hM using hf.1; use -M
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); linarith [hM.2]
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
                _ = (d - c) * f e := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ = F' d - F' c := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
                _ = _ := rfl
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = _ := by congr 1 <;> apply hFF' <;> grind
    replace hupper : upper_integral f (Icc a b) ≥ F b - F a := by
      rw [upper_integ_eq_inf_upper_sum hf.1]; apply le_csInf <;> simp [Set.range_nonempty]
      grind
    replace hlower : lower_integral f (Icc a b) ≤ F b - F a := by
      rw [lower_integ_eq_sup_lower_sum hf.1]; apply csSup_le <;> simp [Set.range_nonempty]
      grind
    linarith [hf.2]
  simp [h]; exact (integ_on_subsingleton (by simp [length])).2


open Real

noncomputable abbrev F_11_9 : ℝ → ℝ := fun x ↦ if x = 0 then 0 else x^2 * sin (1 / x^3)

theorem f_11_9_diff: Differentiable ℝ F_11_9 := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · -- At 0 the derivative is 0: the slope `F_11_9 y / y = y · sin (1/y³)` is squeezed by `|y|`.
    have h0 : HasDerivAt F_11_9 0 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      apply squeeze_zero_norm (a := fun y => |y|)
      · intro y
        rcases eq_or_ne y 0 with rfl | hy
        · simp [slope]
        · have hFy : F_11_9 y = y^2 * sin (1/y^3) := by simp [F_11_9, hy]
          have hF0 : F_11_9 0 = 0 := by simp [F_11_9]
          have hdiv : y^2 * sin (1/y^3) / y = y * sin (1/y^3) := by field_simp
          rw [slope_def_field, hF0, hFy]
          simp only [sub_zero]
          rw [hdiv, Real.norm_eq_abs, abs_mul]
          calc |y| * |sin (1/y^3)| ≤ |y| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
            _ = |y| := mul_one _
      · have habs : Filter.Tendsto (fun y:ℝ => |y|) (nhds 0) (nhds 0) := by
          simpa using (continuous_abs.tendsto (0:ℝ))
        exact habs.mono_left nhdsWithin_le_nhds
    exact h0.differentiableAt
  · -- For `x ≠ 0`, `F_11_9` agrees near `x` with the smooth `y ↦ y² · sin (1/y³)`.
    have heq : F_11_9 =ᶠ[nhds x] fun y => y^2 * sin (1/y^3) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [F_11_9, hy]
    rw [heq.differentiableAt_iff]
    have hx3 : x^3 ≠ 0 := pow_ne_zero 3 hx
    fun_prop (disch := assumption)

example : ¬ BddOn (deriv F_11_9) (.Icc (-1) 1) := by
  -- Away from 0, `F_11_9` is `y²·sin(1/y³)`; its derivative there is the product/chain rule.
  have hderiv : ∀ x:ℝ, x ≠ 0 →
      HasDerivAt F_11_9 (2*x*sin (1/x^3) - 3*cos (1/x^3)/x^2) x := by
    intro x hx
    have hx3 : x^3 ≠ 0 := pow_ne_zero 3 hx
    have heq : F_11_9 =ᶠ[nhds x] fun y => y^2 * sin (1/y^3) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [F_11_9, hy]
    rw [heq.hasDerivAt_iff]
    have h1 : HasDerivAt (fun y:ℝ => y^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
    have hcube : HasDerivAt (fun y:ℝ => y^3) (3*x^2) x := by simpa using hasDerivAt_pow 3 x
    have hinner : HasDerivAt (fun y:ℝ => 1/y^3) (-(3*x^2)/(x^3)^2) x := by
      simpa only [one_div] using hcube.inv hx3
    have hsin : HasDerivAt (fun y:ℝ => sin (1/y^3)) (cos (1/x^3) * (-(3*x^2)/(x^3)^2)) x :=
      hinner.sin
    rw [show (2*x*sin (1/x^3) - 3*cos (1/x^3)/x^2)
        = 2*x * sin (1/x^3) + x^2 * (cos (1/x^3) * (-(3*x^2)/(x^3)^2)) from by field_simp; ring]
    exact h1.mul hsin
  -- Suppose the derivative were bounded by `M` on `[-1,1]`.
  rintro ⟨M, hM⟩
  -- Pick `n` large; the test point `x = (2π(n+1))^(-1/3)` makes `1/x³ = 2π(n+1)`.
  obtain ⟨n, hn⟩ := exists_nat_gt ((|M|/3)^(3/2:ℝ) / (2*π))
  set t : ℝ := 2*π*((n:ℝ)+1) with htdef
  have ht1 : (1:ℝ) ≤ t := by
    rw [htdef]; nlinarith [Real.pi_gt_three, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)]
  have ht0 : 0 < t := by linarith
  set x : ℝ := t ^ (-(1/3):ℝ) with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos ht0 _
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
  have hxmem : x ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith, hx1⟩
  -- `1/x³ = t`, where `t = 2π(n+1)`, so the sine vanishes and the cosine is `1`.
  have hxcube : x^3 = t⁻¹ := by
    rw [hxdef, ← Real.rpow_natCast (t ^ (-(1/3):ℝ)) 3, ← Real.rpow_mul ht0.le,
        show (-(1/3:ℝ)) * (3:ℕ) = -1 by push_cast; ring, Real.rpow_neg ht0.le, Real.rpow_one]
  have hx3 : 1/x^3 = t := by rw [hxcube, one_div, inv_inv]
  have hsin0 : sin (1/x^3) = 0 := by
    rw [hx3, show t = ((2*(n+1):ℕ):ℝ) * π from by rw [htdef]; push_cast; ring]
    exact_mod_cast Real.sin_nat_mul_pi (2*(n+1))
  have hcos1 : cos (1/x^3) = 1 := by
    rw [hx3, show t = ((n+1:ℕ):ℝ) * (2*π) from by rw [htdef]; push_cast; ring]
    exact_mod_cast Real.cos_nat_mul_two_pi (n+1)
  -- Hence `deriv F_11_9 x = -3/x²`, whose magnitude is `3·t^(2/3)`.
  have hdx : deriv F_11_9 x = -3/x^2 := by rw [(hderiv x hxne).deriv, hsin0, hcos1]; ring
  have habs : |deriv F_11_9 x| = 3/x^2 := by
    rw [hdx, show (-3/x^2:ℝ) = -(3/x^2) from by ring, abs_neg, abs_of_pos (by positivity)]
  have hxsq : x^2 = t ^ (-(2/3):ℝ) := by
    rw [hxdef, ← Real.rpow_natCast (t ^ (-(1/3):ℝ)) 2, ← Real.rpow_mul ht0.le,
        show (-(1/3:ℝ)) * (2:ℕ) = -(2/3) by push_cast; ring]
  have hx2inv : 1/x^2 = t ^ (2/3:ℝ) := by rw [hxsq, Real.rpow_neg ht0.le, one_div, inv_inv]
  -- But `3·t^(2/3) > M`, contradicting the bound.
  have hbig : M < 3/x^2 := by
    rw [show (3:ℝ)/x^2 = 3 * (1/x^2) from by ring, hx2inv]
    have hKnn : (0:ℝ) ≤ (|M|/3)^(3/2:ℝ) := Real.rpow_nonneg (by positivity) _
    have htK : (|M|/3)^(3/2:ℝ) < t := by
      have h2pi : (0:ℝ) < 2*π := by positivity
      have hn2 := (div_lt_iff₀ h2pi).mp hn
      rw [htdef]; nlinarith [hn2, Real.pi_pos, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
    have hmono : ((|M|/3)^(3/2:ℝ))^(2/3:ℝ) < t^(2/3:ℝ) := Real.rpow_lt_rpow hKnn htK (by norm_num)
    rw [← Real.rpow_mul (by positivity), show (3/2:ℝ)*(2/3) = 1 by norm_num, Real.rpow_one] at hmono
    linarith [le_abs_self M, hmono]
  have hle := hM x hxmem
  rw [habs] at hle
  linarith

example : AntiderivOn F_11_9 (deriv F_11_9) (Icc (-1) 1) :=
  ⟨f_11_9_diff.differentiableOn,
   fun x _ ↦ (f_11_9_diff x).hasDerivAt.hasDerivWithinAt⟩

/-- Lemma 11.9.5 / Exercise 11.9.2 -/
theorem antideriv_eq_antideriv_add_const {I:BoundedInterval} {f F G : ℝ → ℝ}
  (hfF: AntiderivOn F f I) (hfG: AntiderivOn G f I) :
   ∃ C, ∀ x ∈ (I:Set ℝ), F x = G x + C := by
  have hoc : (↑I : Set ℝ).OrdConnected := ((BoundedInterval.ordConnected_iff ↑I).mpr ⟨I, rfl⟩).2
  -- `H = F - G` has zero derivative on `I`, hence is constant on every sub-segment `[u,v] ⊆ I`.
  have key : ∀ u v : ℝ, u ∈ (I:Set ℝ) → v ∈ (I:Set ℝ) → u ≤ v →
      F u - G u = F v - G v := by
    intro u v hu hv huv
    obtain rfl | hlt := eq_or_lt_of_le huv
    · rfl
    have hsub : Set.Icc u v ⊆ (I:Set ℝ) := hoc.out hu hv
    have hHdiff : DifferentiableOn ℝ (fun z => F z - G z) (Set.Icc u v) :=
      (hfF.1.mono hsub).sub (hfG.1.mono hsub)
    have hzero : ∀ x ∈ Set.Ioo u v, derivWithin (fun z => F z - G z) (Set.Icc u v) x = 0 := by
      intro x hx
      have hxI : x ∈ (I:Set ℝ) := hsub (Set.Ioo_subset_Icc_self hx)
      have hF' : HasDerivWithinAt F (f x) (Set.Icc u v) x := (hfF.2 x hxI).mono hsub
      have hG' : HasDerivWithinAt G (f x) (Set.Icc u v) x := (hfG.2 x hxI).mono hsub
      have hH' : HasDerivWithinAt (fun z => F z - G z) 0 (Set.Icc u v) x := by
        simpa using hF'.sub hG'
      exact hH'.derivWithin (uniqueDiffOn_Icc hlt x (Set.Ioo_subset_Icc_self hx))
    have hconst := const_of_zero_derivative hHdiff hzero
    simpa using hconst ⟨u, Set.left_mem_Icc.mpr huv⟩ ⟨v, Set.right_mem_Icc.mpr huv⟩
  rcases Set.eq_empty_or_nonempty (I:Set ℝ) with hI | ⟨x₀, hx₀⟩
  · exact ⟨0, by rw [hI]; simp⟩
  · refine ⟨F x₀ - G x₀, fun x hx => ?_⟩
    rcases le_total x x₀ with h | h
    · have := key x x₀ hx hx₀ h; linarith
    · have := key x₀ x hx₀ hx h; linarith

/-- The right limit {lit}`f(x₀⁺) := sInf (f '' (Ioc x₀ b))` of a function that is {lit}`≥ f x₀` to the
right of {lit}`x₀`: it is a lower bound for the values on the right, yet stays {lit}`≥ f x₀`. -/
private lemma sided_inf_right {b x₀ : ℝ} (hx₀b : x₀ < b) {f : ℝ → ℝ}
    (hmono_r : ∀ t ∈ Set.Ioc x₀ b, f x₀ ≤ f t) :
    (f '' (Set.Ioc x₀ b)).Nonempty ∧
    (∀ t ∈ Set.Ioc x₀ b, sInf (f '' (Set.Ioc x₀ b)) ≤ f t) ∧
    f x₀ ≤ sInf (f '' (Set.Ioc x₀ b)) := by
  have hne : (f '' (Set.Ioc x₀ b)).Nonempty := ⟨f b, b, ⟨hx₀b, le_refl b⟩, rfl⟩
  have hbdd : BddBelow (f '' (Set.Ioc x₀ b)) := ⟨f x₀, by rintro z ⟨t, ht, rfl⟩; exact hmono_r t ht⟩
  exact ⟨hne, fun t ht => csInf_le hbdd ⟨t, ht, rfl⟩,
    le_csInf hne (by rintro z ⟨t, ht, rfl⟩; exact hmono_r t ht)⟩

/-- The left limit {lit}`f(x₀⁻) := sSup (f '' (Ico a x₀))` of a function that is {lit}`≤ f x₀` to the
left of {lit}`x₀`: it is an upper bound for the values on the left, yet stays {lit}`≤ f x₀`. -/
private lemma sided_sup_left {a x₀ : ℝ} (hax₀ : a < x₀) {f : ℝ → ℝ}
    (hmono_l : ∀ t ∈ Set.Ico a x₀, f t ≤ f x₀) :
    (f '' (Set.Ico a x₀)).Nonempty ∧
    (∀ t ∈ Set.Ico a x₀, f t ≤ sSup (f '' (Set.Ico a x₀))) ∧
    sSup (f '' (Set.Ico a x₀)) ≤ f x₀ := by
  have hne : (f '' (Set.Ico a x₀)).Nonempty := ⟨f a, a, ⟨le_refl a, hax₀⟩, rfl⟩
  have hbdd : BddAbove (f '' (Set.Ico a x₀)) := ⟨f x₀, by rintro z ⟨t, ht, rfl⟩; exact hmono_l t ht⟩
  exact ⟨hne, fun t ht => le_csSup hbdd ⟨t, ht, rfl⟩,
    csSup_le hne (by rintro z ⟨t, ht, rfl⟩; exact hmono_l t ht)⟩

/-- Exercise 11.9.3 -/
example {a b x₀:ℝ} (hab: a < b) (hx₀: x₀ ∈ Ioo a b) {f: ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ ↔
  ContinuousWithinAt f (Icc a b) x₀ := by
  have hint : IntegrableOn f (Icc a b) := integ_of_monotone hf
  obtain ⟨hax₀, hx₀b⟩ := hx₀
  have hx₀I : x₀ ∈ Set.Icc a b := ⟨hax₀.le, hx₀b.le⟩
  -- monotonicity bounds on either side of x₀
  have hmono_r : ∀ t ∈ Set.Ioc x₀ b, f x₀ ≤ f t := fun t ht =>
    hf hx₀I ⟨hax₀.le.trans ht.1.le, ht.2⟩ ht.1.le
  have hmono_l : ∀ t ∈ Set.Ico a x₀, f t ≤ f x₀ := fun t ht =>
    hf ⟨ht.1, ht.2.le.trans hx₀b.le⟩ hx₀I ht.2.le
  -- `R = f(x₀⁺)` and `L = f(x₀⁻)` are the one-sided limits of the monotone `f` at `x₀`.
  obtain ⟨hIocne, hRle, -⟩ := sided_inf_right hx₀b hmono_r
  obtain ⟨hIcone, hLge, -⟩ := sided_sup_left hax₀ hmono_l
  set R := sInf (f '' (Set.Ioc x₀ b)) with hRdef
  set L := sSup (f '' (Set.Ico a x₀)) with hLdef
  constructor
  · -- a jump on either side contradicts differentiability
    intro hdiff
    by_contra hnc
    have hjump : f x₀ < R ∨ L < f x₀ := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hRle', hLge'⟩ := hcon
      apply hnc
      refine ((ContinuousWithinAt.tfae (Icc a b) f x₀).out 0 2).mpr ?_
      intro ε hε
      obtain ⟨zr, hzr, hzrlt⟩ := exists_lt_of_csInf_lt hIocne (show R < f x₀ + ε by linarith)
      obtain ⟨zl, hzl, hzlgt⟩ := exists_lt_of_lt_csSup hIcone (show f x₀ - ε < L by linarith)
      obtain ⟨tr, htr, rfl⟩ := hzr
      obtain ⟨tl, htl, rfl⟩ := hzl
      refine ⟨min (tr - x₀) (x₀ - tl), lt_min (by linarith [htr.1]) (by linarith [htl.2]), ?_⟩
      intro x hx hxδ
      have hδr : |x - x₀| < tr - x₀ := lt_of_lt_of_le hxδ (min_le_left _ _)
      have hδl : |x - x₀| < x₀ - tl := lt_of_lt_of_le hxδ (min_le_right _ _)
      rcases lt_trichotomy x x₀ with hlt | heq | hgt
      · have hxtl : tl < x := by
          rw [abs_of_neg (show x - x₀ < 0 by linarith)] at hδl; linarith
        have h1 : f x ≤ f x₀ := hmono_l x ⟨hx.1, hlt⟩
        have h2 : f tl ≤ f x := hf ⟨htl.1, by linarith [htl.2]⟩ hx hxtl.le
        rw [abs_of_nonpos (show f x - f x₀ ≤ 0 by linarith)]; linarith
      · rw [heq]; simpa using hε
      · have hxtr : x < tr := by
          rw [abs_of_pos (show (0:ℝ) < x - x₀ by linarith)] at hδr; linarith
        have h1 : f x₀ ≤ f x := hmono_r x ⟨hgt, hx.2⟩
        have h2 : f x ≤ f tr := hf hx ⟨by linarith [htr.1], htr.2⟩ hxtr.le
        rw [abs_of_nonneg (show (0:ℝ) ≤ f x - f x₀ by linarith)]; linarith
    rcases hjump with hR | hL
    · exact not_diff_of_jump ⟨hax₀, hx₀b⟩ hint hR
        (fun t ht => hmono_l t ⟨ht.1.le, ht.2⟩) (fun t ht => hRle t ht) hdiff
    · exact not_diff_of_jump ⟨hax₀, hx₀b⟩ hint hL
        (fun t ht => hLge t ⟨ht.1.le, ht.2⟩) (fun t ht => hmono_r t ht) hdiff
  · intro hcts
    exact (deriv_of_integ hab hint hx₀I hcts).differentiableWithinAt

/-- Derivative of the shifted power {lit}`(x+1)^q`; the base {lit}`x+1` stays positive on
{lit}`[0,∞)`. -/
lemma hasDerivAt_rpow_shift (q:ℝ) {x:ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y:ℝ ↦ (y+1)^q) (q*(x+1)^(q-1)) x := by
  have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
  have hbase : HasDerivAt (fun y:ℝ ↦ y+1) 1 x := by simpa using (hasDerivAt_id x).add_const 1
  simpa using (Real.hasDerivAt_rpow_const (x := x+1) (p := q) (Or.inl hx1)).comp x hbase

/-- The chapter integral of {lit}`(x+1)^(-p)` over {lit}`[0,N]`, evaluated by the second
fundamental theorem of calculus with antiderivative {lit}`(x+1)^(1-p)/(1-p)` (valid when
{lit}`p ≠ 1`). -/
lemma integ_rpow_shift {p:ℝ} (hp0 : 0 ≤ p) (hp1 : p ≠ 1) {N:ℝ} (hN : 0 ≤ N) :
    integ (fun x ↦ (x+1)^(-p)) (Icc 0 N) = ((N+1)^(1-p) - 1)/(1-p) := by
  set g : ℝ → ℝ := fun x ↦ (x+1)^(-p) with hgdef
  set G : ℝ → ℝ := fun y ↦ (y+1)^(1-p)/(1-p) with hGdef
  have hsub : (1:ℝ) - p ≠ 0 := fun h ↦ hp1 (by linarith)
  have hg_anti : AntitoneOn g (Set.Ici 0) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by have := Set.mem_Ici.mp hx; linarith)
      (by linarith) (by linarith)
  have hint : IntegrableOn g (Icc 0 N) :=
    integ_of_antitone (hg_anti.mono (by rw [set_Icc]; exact Set.Icc_subset_Ici_self))
  have hGderiv : ∀ x, 0 ≤ x → HasDerivAt G (g x) x := by
    intro x hx
    have hd := (hasDerivAt_rpow_shift (1-p) hx).div_const (1-p)
    have hval : (1 - p) * (x + 1) ^ (1 - p - 1) / (1 - p) = g x := by
      rw [show (1:ℝ) - p - 1 = -p by ring, mul_div_cancel_left₀ _ hsub, hgdef]
    rwa [hval] at hd
  have hmem : ∀ x, x ∈ (Icc 0 N : BoundedInterval) → 0 ≤ x := by
    intro x hx; rw [mem_iff, set_Icc, Set.mem_Icc] at hx; exact hx.1
  have hG : AntiderivOn G g (Icc 0 N) :=
    ⟨fun x hx ↦ (hGderiv x (hmem x hx)).differentiableAt.differentiableWithinAt,
     fun x hx ↦ (hGderiv x (hmem x hx)).hasDerivWithinAt⟩
  rw [integ_eq_antideriv_sub hN hint hG]
  show (N+1)^(1-p)/(1-p) - (0+1)^(1-p)/(1-p) = ((N+1)^(1-p) - 1)/(1-p)
  rw [show (0:ℝ)+1 = 1 by norm_num, Real.one_rpow]
  ring

/-- The chapter integral of {lit}`(x+1)^(-1)` over {lit}`[0,N]`, the borderline {lit}`p = 1`
case, evaluated by the second fundamental theorem of calculus with antiderivative
{lit}`log (x+1)`. -/
lemma integ_inv_shift {N:ℝ} (hN : 0 ≤ N) :
    integ (fun x ↦ (x+1)^(-1:ℝ)) (Icc 0 N) = log (N+1) := by
  set g : ℝ → ℝ := fun x ↦ (x+1)^(-1:ℝ) with hgdef
  set G : ℝ → ℝ := fun y ↦ log (y+1) with hGdef
  have hg_anti : AntitoneOn g (Set.Ici 0) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by have := Set.mem_Ici.mp hx; linarith)
      (by linarith) (by norm_num)
  have hint : IntegrableOn g (Icc 0 N) :=
    integ_of_antitone (hg_anti.mono (by rw [set_Icc]; exact Set.Icc_subset_Ici_self))
  have hGderiv : ∀ x, 0 ≤ x → HasDerivAt G (g x) x := by
    intro x hx
    have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
    have hbase : HasDerivAt (fun y:ℝ ↦ y+1) 1 x := by simpa using (hasDerivAt_id x).add_const 1
    have hd := (Real.hasDerivAt_log hx1).comp x hbase
    have hval : (x+1)⁻¹ * 1 = g x := by
      rw [mul_one]; show (x+1)⁻¹ = (x+1)^(-1:ℝ); rw [Real.rpow_neg_one]
    rwa [hval] at hd
  have hmem : ∀ x, x ∈ (Icc 0 N : BoundedInterval) → 0 ≤ x := by
    intro x hx; rw [mem_iff, set_Icc, Set.mem_Icc] at hx; exact hx.1
  have hG : AntiderivOn G g (Icc 0 N) :=
    ⟨fun x hx ↦ (hGderiv x (hmem x hx)).differentiableAt.differentiableWithinAt,
     fun x hx ↦ (hGderiv x (hmem x hx)).hasDerivWithinAt⟩
  rw [integ_eq_antideriv_sub hN hint hG]
  show log (N+1) - log (0+1) = log (N+1)
  rw [show (0:ℝ)+1 = 1 by norm_num, Real.log_one, sub_zero]

open Chapter7

/-- Partial sums of the q-series match the chapter-7 partial sums, once the vanishing zeroth
term is accounted for. The hypothesis {lit}`p ≠ 0` makes the zeroth term {lit}`1/0^p` vanish. -/
lemma qseries_partial_eq {p:ℝ} (hp : p ≠ 0) (k:ℕ) :
    (∑ n ∈ Finset.range (k+1), 1/(n:ℝ)^p)
      = (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).partial (k:ℤ) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_one, Series.partial_of_lt (by norm_num),
      Nat.cast_zero, Real.zero_rpow hp, div_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih,
      show ((k+1:ℕ):ℤ) = (k:ℤ)+1 by push_cast; ring,
      (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).partial_succ (by norm_num)]
    congr 1
    rw [Series.eval_mk' _ (by norm_num : ((k:ℤ)+1) ≥ 1)]
    push_cast; ring

/-- The q-series converges as a chapter-7 series iff its terms are summable, since the series is
nonnegative. -/
lemma qseries_converges_iff_summable {p:ℝ} (hp : p ≠ 0) :
    (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).converges
      ↔ Summable (fun n:ℕ ↦ 1/(n:ℝ)^p) := by
  have hf_nonneg : ∀ n:ℕ, 0 ≤ 1/(n:ℝ)^p := fun n ↦ by positivity
  have hnonneg : (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).nonneg := by
    intro n
    by_cases h : (1:ℤ) ≤ n <;> simp [h]; positivity
  rw [Series.converges_of_nonneg_iff hnonneg]
  constructor
  · rintro ⟨M, hM⟩
    have hM0 : 0 ≤ M := le_trans (Series.partial_nonneg hnonneg 0) (hM 0)
    apply summable_of_sum_range_le (c := M) hf_nonneg
    intro k
    cases k with
    | zero => simpa using hM0
    | succ j => rw [qseries_partial_eq hp j]; exact hM j
  · intro hsum
    refine ⟨∑' n:ℕ, 1/(n:ℝ)^p, fun N ↦ ?_⟩
    rcases lt_or_ge N 1 with hN | hN
    · rw [Series.partial_of_lt hN]; exact tsum_nonneg hf_nonneg
    · rw [show N = (N.toNat:ℤ) from (Int.toNat_of_nonneg (by linarith)).symm,
        ← qseries_partial_eq hp N.toNat]
      exact hsum.sum_le_tsum _ (fun i _ ↦ hf_nonneg i)

end Chapter11

open Chapter11 BoundedInterval Real

/-- Exercise 11.6.5, moved to Section 11.9.  Decided by the integral test (Proposition 11.6.4)
applied to the shifted function {lit}`(x+1)^(-p)`, whose integral over {lit}`[0,N]` is now
computed directly by the second fundamental theorem of calculus ({name}`Chapter11.integ_rpow_shift`,
{name}`Chapter11.integ_inv_shift`), rather than borrowing Mathlib's interval integrals. -/
theorem Chapter7.Series.converges_qseries' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).converges ↔ (p>1) := by
  rcases le_or_gt p 0 with hp0 | hp0
  · -- For `p ≤ 0` the terms stay `≥ 1`, so the series cannot converge, and `p > 1` is false.
    constructor
    · intro hconv
      exfalso
      have hdecay := Series.decay_of_converges hconv
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdecay 1 (by norm_num)
      have hge : ∀ n:ℤ, 1 ≤ n → (1:ℝ) ≤ (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).seq n := by
        intro n hn1
        rw [Series.eval_mk' _ hn1]
        have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
        have hppos : (0:ℝ) < (n:ℝ)^p := Real.rpow_pos_of_pos (by linarith) _
        rw [le_div_iff₀ hppos, one_mul]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1' hp0
      have h1 := hN (max N 1) (le_max_left _ _)
      have h2 := hge (max N 1) (le_max_right _ _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)] at h1
      linarith
    · intro hp1; linarith
  · -- For `p > 0` the integral test plus the second FTC computation of `∫ (x+1)^(-p)` decides it.
    rw [qseries_converges_iff_summable (ne_of_gt hp0)]
    set g : ℝ → ℝ := fun x ↦ (x+1)^(-p) with hgdef
    have hshift : Summable (fun n:ℕ ↦ g (n:ℝ)) ↔ Summable (fun n:ℕ ↦ 1/(n:ℝ)^p) := by
      rw [← summable_nat_add_iff (f := fun n:ℕ ↦ 1/(n:ℝ)^p) 1]
      apply summable_congr
      intro n
      simp only [hgdef]
      rw [Real.rpow_neg (by positivity), one_div]
      push_cast
      ring_nf
    have hg_nonneg : ∀ x ≥ (0:ℝ), g x ≥ 0 := fun x hx ↦ Real.rpow_nonneg (by linarith) _
    have hg_anti : AntitoneOn g (Set.Ici 0) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by have := Set.mem_Ici.mp hx; linarith)
        (by linarith) (by linarith)
    rw [← hshift, summable_iff_integ_of_antitone hg_nonneg hg_anti]
    constructor
    · rintro ⟨M, hM⟩
      by_contra hp1
      push_neg at hp1
      rcases lt_or_eq_of_le hp1 with hlt | heq
      · set q := 1 - p with hq
        have hq0 : 0 < q := by rw [hq]; linarith
        set T := M * q + 1 with hTdef
        have hbase : (0:ℝ) < |T| + 1 := by positivity
        set N := (|T|+1)^(1/q) - 1 with hNdef
        have hN1 : N + 1 = (|T|+1)^(1/q) := by rw [hNdef]; ring
        have hge1 : (1:ℝ) ≤ (|T|+1)^(1/q) :=
          calc (1:ℝ) = (1:ℝ)^(1/q) := (Real.one_rpow _).symm
            _ ≤ (|T|+1)^(1/q) :=
              Real.rpow_le_rpow (by norm_num) (by linarith [abs_nonneg T]) (by positivity)
        have hN0 : 0 ≤ N := by rw [hNdef]; linarith
        have hpow : (N+1)^q = |T| + 1 := by
          rw [hN1, ← Real.rpow_mul hbase.le, one_div, inv_mul_cancel₀ (ne_of_gt hq0), Real.rpow_one]
        have hint := hM N hN0
        rw [integ_rpow_shift hp0.le (ne_of_lt hlt) hN0,
          ← hq, hpow, add_sub_cancel_right, div_le_iff₀ hq0] at hint
        have := le_abs_self T
        rw [hTdef] at this
        linarith
      · have hint := hM (Real.exp M) (Real.exp_pos M).le
        rw [hgdef, heq, integ_inv_shift (Real.exp_pos M).le] at hint
        have hlt : M < Real.log (Real.exp M + 1) := by
          rw [Real.lt_log_iff_exp_lt (by positivity)]; linarith [Real.exp_pos M]
        linarith
    · intro hp1
      have hp1' : p ≠ 1 := ne_of_gt hp1
      have hpm1 : (0:ℝ) < p - 1 := by linarith
      have h1p : (1:ℝ) - p < 0 := by linarith
      have hpm1' : p - 1 ≠ 0 := ne_of_gt hpm1
      refine ⟨1/(p-1), fun N hN ↦ ?_⟩
      have hN1 : (0:ℝ) ≤ N + 1 := by linarith
      have hpow : (0:ℝ) ≤ (N+1)^(1-p) := Real.rpow_nonneg hN1 _
      rw [integ_rpow_shift hp0.le hp1' hN, div_le_iff_of_neg h1p,
        show (1:ℝ)/(p-1) * (1-p) = -1 by field_simp; ring]
      linarith [hpow]

theorem Chapter7.Series.converges_qseries'' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).absConverges ↔ (p>1) := by
  have hnonneg : (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).nonneg := by
    intro n; by_cases h : (1:ℤ) ≤ n <;> simp [h]; positivity
  have hpart : (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).abs.partial
             = (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).partial := by
    funext N
    unfold Series.partial
    exact Finset.sum_congr rfl fun n _ ↦ by rw [Series.abs_seq, abs_of_nonneg (hnonneg n)]
  have hiff : (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).absConverges
            ↔ (Series.mk' (m := 1) fun n ↦ 1/(n:ℝ)^p).converges := by
    unfold Series.absConverges Series.converges Series.convergesTo
    rw [hpart]
  rw [hiff]; exact Chapter7.Series.converges_qseries' p
