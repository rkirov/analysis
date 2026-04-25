import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_9_7


/-!
# Analysis I, Section 9.8: Monotonic functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Review of Mathlib monotonicity concepts.
-/

namespace Chapter9

/-- Definition 9.8.1 -/
theorem MonotoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : MonotoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≥ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictMono.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictMonoOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y > f x := by
  constructor <;> intros <;> solve_by_elim

theorem AntitoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : AntitoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≤ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictAntitone.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictAntiOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y < f x := by
  constructor <;> intros <;> solve_by_elim

/-- Examples 9.8.2 -/
example : StrictMonoOn (fun x:ℝ ↦ x^2) (.Ici 0) := by
  intro x hx y hy hxy
  simp only [pow_two]
  exact mul_self_lt_mul_self hx hxy

example : StrictAntiOn (fun x:ℝ ↦ x^2) (.Iic 0) := by
  intro x hx y hy hxy
  simp only [pow_two]
  simp at hx hy
  suffices (-y * -y) < (-x * -x) by
    ring_nf at this ⊢
    exact this
  apply mul_self_lt_mul_self (a:= -y) (b:= -x)
  . linarith
  . linarith

theorem pow_not_monotone : ¬ MonotoneOn (fun x:ℝ ↦ x^2) .univ := by
  rw [MonotoneOn.iff]
  push_neg
  use -2, by simp, 1, by norm_num, by norm_num, by norm_num

theorem pow_not_antitone : ¬ AntitoneOn (fun x:ℝ ↦ x^2) .univ := by
  rw [AntitoneOn.iff]
  push_neg
  use -1, by simp, 2, by norm_num, by norm_num, by norm_num

theorem mono_of_strictmono {X:Set ℝ} {f:ℝ → ℝ} (hf: StrictMonoOn f X) : MonotoneOn f X := by
  intro x hx y hy hxy
  rw [StrictMono.iff] at hf
  specialize hf x hx y hy
  by_cases h : x = y
  . subst x; simp
  . rw [le_iff_lt_or_eq] at hxy
    simp [h] at hxy
    specialize hf hxy
    exact hf.le

theorem anti_of_strictanti {X:Set ℝ} {f:ℝ → ℝ} (hf: StrictAntiOn f X) : AntitoneOn f X := by
  intro x hx y hy hxy
  rw [StrictAntitone.iff] at hf
  specialize hf x hx y hy
  by_cases h : x = y
  . subst x; simp
  . rw [le_iff_lt_or_eq] at hxy
    simp [h] at hxy
    specialize hf hxy
    exact hf.le

example (X:Set ℝ) : MonotoneOn (fun _:ℝ ↦ (6:ℝ)) X := by
  rw [MonotoneOn.iff]; intros; rfl

example (X:Set ℝ) : AntitoneOn (fun _:ℝ ↦ (6:ℝ)) X := by
  rw [AntitoneOn.iff]; intros; rfl

#check nontrivial_iff

example {X:Set ℝ} (hX: Nontrivial X) : ¬ StrictMonoOn (fun _:ℝ ↦ (6:ℝ)) X := by
  rw [nontrivial_iff] at hX
  obtain ⟨ x, y, hxy⟩ := hX
  rw [StrictMono.iff]
  push_neg
  wlog hxy' : x < y
  . specialize this y x hxy.symm
    have hxy'' : y < x ∨ y = x ∨ x < y := lt_trichotomy y x
    have h : y < x := by grind
    specialize this h
    exact this
  use x, x.prop, y, y.prop, hxy'

example {X:Set ℝ} (hX: Nontrivial X) : ¬ StrictAntiOn (fun _:ℝ ↦ (6:ℝ)) X := by
  rw [nontrivial_iff] at hX
  obtain ⟨x, y, hxy⟩ := hX
  rw [StrictAntitone.iff]
  push_neg
  wlog hxy' : x < y
  . specialize this y x hxy.symm
    have hxy'' : y < x ∨ y = x ∨ x < y := lt_trichotomy y x
    have h : y < x := by grind
    specialize this h
    exact this
  use x, x.prop, y, y.prop, hxy'

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), ContinuousOn f X ∧ ¬ MonotoneOn f X ∧ ¬ AntitoneOn f X := by
  use .univ, fun x ↦ x^2
  constructor
  . exact continuousOn_pow 2
  . constructor
    . exact pow_not_monotone
    . exact pow_not_antitone

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), MonotoneOn f X ∧ ¬ ContinuousOn f X := by
  use .univ, f_9_4_6
  constructor
  . intro x _ y _ hxy
    by_cases hx : x ≥ 0
    . simp [f_9_4_6, if_pos hx, if_pos (hx.trans hxy)]
    . by_cases hy : y ≥ 0 <;> simp [f_9_4_6, if_neg hx, hy]
  . exact fun hcont => f_9_4_6_not_continuousAt_zero
      (continuousOn_univ.mp hcont).continuousAt

lemma MonotoneCtOn.image {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictMonoOn f (.Icc a b)) :
  f '' (.Icc a b) = .Icc (f a) (f b) := by
  ext x
  constructor
  . intro h
    simp at h
    obtain ⟨y, hy, hxy⟩ := h
    simp
    subst x
    constructor
    . rw [StrictMono.iff] at hmono
      specialize hmono a (by simp;linarith) y hy
      by_cases hy' : y = a
      . subst y
        simp
      . have hy'' : a < y := by grind
        specialize hmono hy''
        simp at hmono
        exact hmono.le
    . rw [StrictMono.iff] at hmono
      specialize hmono y hy b (by simp;linarith)
      by_cases hy' : y = b
      . subst y
        simp
      . have hy'' : y < b := by grind
        specialize hmono hy''
        simp at hmono
        exact hmono.le
  . intro x'
    exact intermediate_value h hcont (Or.inl x')

/-- Proposition 9.8.3 / Exercise 9.8.4 -/
theorem MonotoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictMonoOn f (.Icc a b)) :
  f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y
   := by
  constructor
  . exact MonotoneCtOn.image h f hcont hmono
  . let g : ℝ → ℝ := fun x ↦ if hx : x ∈ Set.Icc (f a) (f b) then
      by
        rw [← MonotoneCtOn.image h f hcont hmono] at hx
        simp at hx
        exact hx.choose
      else 0
    have hfinv' : ∀ y ∈ Set.Icc (f a) (f b), f (g y) = y := by
      intro y hy
      simp at hy
      simp [g, hy]
      generalize_proofs h
      have ⟨hab, hf⟩ := h.choose_spec
      exact hf
    have hgim : ∀ y ∈ Set.Icc (f a) (f b), g y ∈ Set.Icc a b := by
      intro y hy
      simp at hy
      simp [g, hy]
      generalize_proofs ha
      obtain ⟨hab, hf⟩ := ha.choose_spec
      exact hab
    have hfinv : ∀ x ∈ Set.Icc a b, g (f x) = x := by
      intro x hx
      have hfx_mem : f x ∈ Set.Icc (f a) (f b) := by
        rw [← MonotoneCtOn.image h f hcont hmono]
        exact ⟨x, hx, rfl⟩
      exact hmono.injOn (hgim (f x) hfx_mem) hx (hfinv' (f x) hfx_mem)
    -- Helper: g is strictly mono, so we can invert inequalities via f.
    have hg_lt_of_lt : ∀ ⦃x y:ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc (f a) (f b) →
        f x < y → x < g y := by
      intro x z hx hz hlt
      by_contra hge; push_neg at hge
      have : f (g z) ≤ f x := by
        rcases eq_or_lt_of_le hge with h' | h'
        · rw [h']
        · exact (hmono (hgim z hz) hx h').le
      rw [hfinv' z hz] at this
      linarith
    have hg_gt_of_lt : ∀ ⦃x y:ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc (f a) (f b) →
        y < f x → g y < x := by
      intro x z hx hz hlt
      by_contra hge; push_neg at hge
      have : f x ≤ f (g z) := by
        rcases eq_or_lt_of_le hge with h' | h'
        · rw [← h']
        · exact (hmono hx (hgim z hz) h').le
      rw [hfinv' z hz] at this
      linarith
    have hgct : ContinuousOn g (.Icc (f a) (f b)) := by
      intro y hy
      refine (ContinuousWithinAt.tfae (Set.Icc (f a) (f b)) g y).out 0 2 |>.mpr ?_
      intro ε hε
      have hgy_mem : g y ∈ Set.Icc a b := hgim y hy
      have hfgy : f (g y) = y := hfinv' y hy
      obtain ⟨hgya, hgyb⟩ := hgy_mem
      -- Clipped endpoints; δL and δR separately, padded to 1 at the degenerate endpoint.
      set xL := max a (g y - ε)
      set xR := min b (g y + ε)
      have hxL_mem : xL ∈ Set.Icc a b :=
        ⟨le_max_left .., max_le (hgya.trans hgyb) (by linarith)⟩
      have hxR_mem : xR ∈ Set.Icc a b :=
        ⟨le_min (hgya.trans hgyb) (by linarith), min_le_left ..⟩
      have hxL_le : xL ≤ g y := max_le hgya (by linarith)
      have hgy_le : g y ≤ xR := le_min hgyb (by linarith)
      set δL := if xL = g y then (1:ℝ) else y - f xL
      set δR := if xR = g y then (1:ℝ) else f xR - y
      have hδL_pos : 0 < δL := by
        by_cases hL : xL = g y
        · simp [δL, hL]
        · have : f xL < f (g y) := hmono hxL_mem ⟨hgya, hgyb⟩ (lt_of_le_of_ne hxL_le hL)
          simp only [δL, if_neg hL]; linarith [hfgy]
      have hδR_pos : 0 < δR := by
        by_cases hR : xR = g y
        · simp [δR, hR]
        · have : f (g y) < f xR := hmono ⟨hgya, hgyb⟩ hxR_mem (lt_of_le_of_ne hgy_le (Ne.symm hR))
          simp only [δR, if_neg hR]; linarith [hfgy]
      use min δL δR, lt_min hδL_pos hδR_pos
      intro x hx hx_lt
      have ⟨hxy1, hxy2⟩ := abs_lt.mp hx_lt
      have hgx_mem := hgim x hx
      rw [abs_lt]
      constructor
      · by_cases hL : xL = g y
        · have hxLa : xL = a := by
            rcases le_or_gt (g y - ε) a with h' | h'
            · simp [xL, max_eq_left h']
            · have : xL = g y - ε := by simp [xL, max_eq_right h'.le]
              linarith
          have : g y = a := by linarith
          linarith [hgx_mem.1]
        · have hδL : δL = y - f xL := by simp [δL, if_neg hL]
          have hfxL : f xL < x := by
            have : min δL δR ≤ δL := min_le_left _ _
            linarith
          have : xL < g x := hg_lt_of_lt hxL_mem hx hfxL
          linarith [le_max_right a (g y - ε)]
      · by_cases hR : xR = g y
        · have hxRb : xR = b := by
            rcases le_or_gt b (g y + ε) with h' | h'
            · simp [xR, min_eq_left h']
            · have : xR = g y + ε := by simp [xR, min_eq_right h'.le]
              linarith
          have : g y = b := by linarith
          linarith [hgx_mem.2]
        · have hδR : δR = f xR - y := by simp [δR, if_neg hR]
          have hfxR : x < f xR := by
            have : min δL δR ≤ δR := min_le_right _ _
            linarith
          have : g x < xR := hg_gt_of_lt hxR_mem hx hfxR
          linarith [min_le_right b (g y + ε)]

    have hgmono : StrictMonoOn g (.Icc (f a) (f b)) := by
      intro x hx y hy hxy
      apply hg_lt_of_lt (hgim x hx) hy
      rw [hfinv' x hx]; exact hxy
    refine ⟨g, hgct, hgmono, ?_, hfinv, hfinv'⟩
    have hfab : f a < f b :=
      hmono (by simp; linarith) (by simp; linarith) h
    have := MonotoneCtOn.image hfab g hgct hgmono
    rw [hfinv a (by simp; linarith), hfinv b (by simp; linarith)] at this
    exact this

/-- Example 9.8.4-/
example {R :ℝ} (hR: R > 0) {n:ℕ} (hn: n > 0) : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (R^n), (g x)^n = x := by
  set f : ℝ → ℝ := fun x ↦ x^n
  have hcont : ContinuousOn f (.Icc 0 R) := by fun_prop
  have hmono : StrictMonoOn f (.Icc 0 R) := by
    intro _ hx _ _ hxy; simp_all [f]
    apply pow_lt_pow_left₀ hxy <;> grind
  obtain ⟨ g, ⟨ _, _, _, _, hg⟩ ⟩ := (MonotoneOn.exist_inverse (by positivity) f hcont hmono).2
  simp only [f, zero_pow (by positivity)] at hg; use g

/-- Exercise 9.8.1 -/
theorem IsMaxOn.of_monotone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use b
  constructor
  . simp
    exact h.le
  . intro y hy
    simp
    rw [MonotoneOn.iff] at hf
    specialize hf y hy b (by simp;linarith)
    simp at hy
    by_cases hy' : y = b
    . subst y
      simp
    . have hy'' : y < b := by grind
      specialize hf hy''
      exact hf

theorem IsMaxOn.of_strictmono_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictMonoOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use b
  constructor
  . simp
    exact h.le
  . intro y hy
    simp
    rw [StrictMono.iff] at hf
    specialize hf y hy b (by simp;linarith)
    simp at hy
    by_cases hy' : y = b
    . subst y
      simp
    . have hy'' : y < b := by grind
      specialize hf hy''
      simp at hf
      exact hf.le

theorem IsMaxOn.of_antitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use a
  constructor
  . simp
    exact h.le
  . intro y hy
    simp
    rw [AntitoneOn.iff] at hf
    specialize hf a (by simp;linarith) y hy
    simp at hy
    by_cases hy' : y = a
    . subst y
      simp
    . have hy'' : a < y:= by grind
      specialize hf hy''
      exact hf

theorem IsMaxOn.of_strictantitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictAntiOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use a
  constructor
  . simp
    exact h.le
  . intro y hy
    simp
    rw [StrictAntitone.iff] at hf
    specialize hf a (by simp;linarith) y hy
    simp at hy
    by_cases hy' : y = a
    . subst y
      simp
    . have hy'' : a < y:= by grind
      specialize hf hy''
      exact hf.le

theorem BddOn.of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  refine (iff' f (Set.Icc a b)).mpr ?_
  refine (isBounded_def (f '' Set.Icc a b)).mpr ?_
  use max |f a| |f b| + 1
  constructor
  . grind
  . intro x hx
    simp at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    rw [MonotoneOn.iff] at hf
    have := hf y hy.1 b (by simp;linarith)
    by_cases h': y = b
    . subst b
      simp
      grind
    . by_cases h'': y = a
      . subst a
        grind
      have hy' : b > y := by grind
      have hy'' : y > a := by grind
      have hfy' : f a ≤ f y  := by grind
      have hfy'' : f y ≤ f b := by grind
      simp
      constructor
      . grind
      . grind

theorem BddOn.of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  refine (iff' f (Set.Icc a b)).mpr ?_
  refine (isBounded_def (f '' Set.Icc a b)).mpr ?_
  use max |f a| |f b| + 1
  constructor
  . grind
  . intro x hx
    simp at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    rw [AntitoneOn.iff] at hf
    have := hf y hy.1 b (by simp;linarith)
    by_cases h': y = b
    . subst b
      simp
      grind
    . by_cases h'': y = a
      . subst a
        grind
      have hy' : b > y := by grind
      have hy'' : y > a := by grind
      have hfy' : f a ≥ f y  := by grind
      have hfy'' : f y ≥ f b := by grind
      simp
      constructor
      . grind
      . grind

/-- Exercise 9.8.2 -/
theorem no_strictmono_intermediate_value : ∃ (a b:ℝ) (_: a < b) (f:ℝ → ℝ)
    (_: StrictMonoOn f (.Icc a b)),
    ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
         ∀ x ∈ Set.Icc a b, f x ≠ y := by
  let f : ℝ → ℝ := fun x ↦ if x ≤ 0 then 0 else x + 1
  have hf_zero (x : ℝ) (hx : x = 0) : f x = 0 := by grind
  have hf_other (x : ℝ) (hx : x > 0) : f x > 1 := by grind
  use 0, 1, (by norm_num), f
  refine ⟨?_, 1, ?_, ?_⟩
  . intro x hx y hy hxy
    simp at hx hy
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    . rw [hf_zero x hx0.symm]
      have hy0 : y > 0 := by linarith [hx0.symm]
      linarith [hf_other y hy0]
    . have hy0 : y > 0 := by linarith
      simp only [f, if_neg (not_le.mpr hx0), if_neg (not_le.mpr hy0)]
      linarith
  . left
    have hf1 : f 1 = 2 := by simp [f]; norm_num
    simp [hf_zero 0 rfl, hf1]
  . intro x hx hfx
    simp at hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    . rw [hf_zero x hx0.symm] at hfx; linarith
    . exact absurd hfx (ne_of_gt (hf_other x hx0))


theorem no_monotone_intermediate_value : ∃ (a b:ℝ) (_: a < b) (f:ℝ → ℝ)
    (_: MonotoneOn f (.Icc a b)),
    ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
         ∀ x ∈ Set.Icc a b, f x ≠ y := by
  obtain ⟨a, b, hab, f, hf, h⟩ := no_strictmono_intermediate_value
  exact ⟨a, b, hab, f, mono_of_strictmono hf, h⟩

theorem no_strictanti_intermediate_value : ∃ (a b:ℝ) (_: a < b) (f:ℝ → ℝ)
    (_: StrictAntiOn f (.Icc a b)),
    ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
         ∀ x ∈ Set.Icc a b, f x ≠ y := by
  obtain ⟨a, b, hab, f, hf, y, hy, hyim⟩ := no_strictmono_intermediate_value
  refine ⟨a, b, hab, fun x ↦ -f x, ?_, -y, ?_, ?_⟩
  . intro u hu v hv huv
    exact neg_lt_neg (hf hu hv huv)
  . rcases hy with hy | hy
    . right
      simp at hy ⊢
      exact ⟨by linarith, by linarith⟩
    . left
      simp at hy ⊢
      exact ⟨by linarith, by linarith⟩
  . intro x hx hfx
    exact hyim x hx (by linarith)

theorem no_antitone_intermediate_value : ∃ (a b:ℝ) (_: a < b) (f:ℝ → ℝ)
    (_: AntitoneOn f (.Icc a b)),
    ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
         ∀ x ∈ Set.Icc a b, f x ≠ y := by
  obtain ⟨a, b, hab, f, hf, h⟩ := no_strictanti_intermediate_value
  exact ⟨a, b, hab, f, anti_of_strictanti hf, h⟩

private lemma strictMono_of_continuous_inj_of_lt {a b:ℝ} {f:ℝ → ℝ}
  (hf: ContinuousOn f (.Icc a b))
  (hinj: Function.Injective (fun x: Set.Icc a b ↦ f x ))
  (ha: f a < f b) : StrictMonoOn f (.Icc a b) := by
  by_contra
  rw [StrictMono.iff] at this
  push_neg at this
  obtain ⟨x, hx, y, hy, h, h'⟩ := this
  simp at hx hy
  by_cases hx' : f a > f y
  . have hyb : y < b := by
      rcases lt_or_eq_of_le hy.2 with hyb | hyb
      · exact hyb
      · exfalso; rw [hyb] at hx'; linarith
    obtain ⟨z, hz, hfz⟩ := intermediate_value hyb
      (hf.mono (fun u hu ↦ by simp at hu ⊢; exact ⟨by linarith [hy.1], hu.2⟩))
      (y := f a) (Or.inl ⟨by linarith, by linarith⟩)
    simp at hz
    have hza : (⟨z, by simp; exact ⟨by linarith, hz.2⟩⟩ : Set.Icc a b)
             = ⟨a, by simp; linarith⟩ := hinj (by simp [hfz])
    simp at hza
    linarith
  . push_neg at hx'
    have hfyx : f y < f x := by
      rcases lt_or_eq_of_le h' with h' | h'
      · exact h'
      · exfalso
        have : (⟨y, by simp; exact hy⟩ : Set.Icc a b) = ⟨x, by simp; exact hx⟩ :=
          hinj (by simp [h'])
        simp at this; linarith
    have hax : a < x := by
      rcases lt_or_eq_of_le hx.1 with hax | hax
      · exact hax
      · exfalso; rw [← hax] at hfyx; linarith
    obtain ⟨z, hz, hfz⟩ := intermediate_value hax
      (hf.mono (fun u hu ↦ by simp at hu ⊢; exact ⟨hu.1, by linarith [hx.2]⟩))
      (y := f y) (Or.inl ⟨hx', by linarith⟩)
    simp at hz
    have hzy : (⟨z, by simp; exact ⟨hz.1, by linarith [hx.2]⟩⟩ : Set.Icc a b)
             = ⟨y, by simp; exact hy⟩ := hinj (by simp [hfz])
    simp at hzy
    linarith

/-- Exercise 9.8.3 -/
theorem mono_of_continuous_inj {a b:ℝ} (h: a < b) {f:ℝ → ℝ}
  (hf: ContinuousOn f (.Icc a b))
  (hinj: Function.Injective (fun x: Set.Icc a b ↦ f x )) :
  StrictMonoOn f (.Icc a b) ∨ StrictAntiOn f (.Icc a b) := by
  by_cases ha : f a < f b
  . exact Or.inl (strictMono_of_continuous_inj_of_lt hf hinj ha)
  . simp at ha
    rw [le_iff_lt_or_eq] at ha
    cases' ha with ha ha
    . right
      intro u hu v hv huv
      have := strictMono_of_continuous_inj_of_lt hf.neg
        (fun p q hpq ↦ hinj (by simpa using hpq)) (by simpa using ha) hu hv huv
      simp at this; linarith
    . have ha' : (fun x: Set.Icc a b ↦ f x ) ⟨a, by grind only [= Set.mem_Icc]⟩
          = (fun x: Set.Icc a b ↦ f x ) ⟨b, by grind only [= Set.mem_Icc]⟩ := by simp [ha]
      have := hinj ha'
      grind only

/-- Exercise 9.8.4 -/
def MonotoneOn.exist_inverse_without_continuity {a b:ℝ} (h: a < b) {f: ℝ → ℝ} (hmono: StrictMonoOn f (.Icc a b)) :
  Decidable ( f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y )
   := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise 9.8.4 -/
def MonotoneOn.exist_inverse_without_strictmono {a b:ℝ} (h: a < b) (f: ℝ → ℝ)
  (hcont: ContinuousOn f (.Icc a b)) (hmono: MonotoneOn f (.Icc a b)) :
  Decidable ( f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y )
   := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


/- Exercise 9.8.4: state and prove an analogue of `MonotoneOne.exist_inverse` for `Antitone` functions. -/
-- theorem AntitoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictAntiOn f (.Icc a b)) : sorry := by sorry

/-- An equivalence between the natural numbers and the rationals. -/
noncomputable abbrev q_9_8_5 : ℕ ≃ ℚ := nonempty_equiv_of_countable.some

noncomputable abbrev g_9_8_5 : ℚ → ℝ := fun q ↦ (2:ℝ)^(-q_9_8_5.symm q:ℤ)

noncomputable abbrev f_9_8_5 : ℝ → ℝ := fun x ↦ ∑' r : {r:ℚ // (r:ℝ) < x}, g_9_8_5 r

/-- Exercise 9.8.5(a) -/
theorem StrictMonoOn.of_f_9_8_5 : StrictMonoOn f_9_8_5 .univ := by
  sorry

/-- Exercise 9.8.5(b) -/
theorem ContinuousAt.of_f_9_8_5' (r:ℚ) : ¬ ContinuousAt f_9_8_5 r := by
  sorry

/-- Exercise 9.8.5(c) -/
theorem ContinuousAt.of_f_9_8_5 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) : ContinuousAt f_9_8_5 x := by
  sorry

end Chapter9
