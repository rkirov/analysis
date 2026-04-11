import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Instances.EReal.Lemmas
import Analysis.Section_9_1

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 9.3: Limiting values of functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Limits of continuous functions
- Connection with Mathilb's filter convergence concepts
- Limit laws for functions

Technical point: in the text, the functions `f` studied are defined only on subsets `X` of {lean}`ℝ`, and
left undefined elsewhere.  However, in Lean, this then creates some fiddly conversions when trying
to restrict `f` to various subsets of `X` (which, technically, are not precisely subsets of {lean}`ℝ`,
though they can be coerced to such).  To avoid this issue we will deviate from the text by having
our functions defined on all of {lean}`ℝ` (with the understanding that they are assigned "junk" values
outside of the domain `X` of interest).
-/

/-- Definition 9.3.1
Using < instead of ≤, to match mathlib's defintion.
-/
abbrev Real.CloseFn (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Definition 9.3.3 -/
abbrev Real.CloseNear (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∃ δ > 0, ε.CloseFn (X ∩ .Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
example : (5.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  rw [Real.CloseFn]
  intro x hx
  simp at hx
  obtain ⟨h1, h2⟩ := hx; rw [abs_lt, sq x]; constructor <;> nlinarith

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
example : (0.42:ℝ).CloseFn (.Icc 1.9 2.1) (fun x ↦ x^2) 4 := by
  intro x hx; simp [Set.mem_Icc] at hx; obtain ⟨h1, h2⟩ := hx
  show |x ^ 2 - 4| < 0.42
  rw [abs_lt, sq x]
  have h3 : x * x ≤ 2.1 * 2.1 := mul_le_mul h2 h2 (by linarith) (by linarith)
  have h4 : 1.9 * 1.9 ≤ x * x := mul_le_mul h1 h1 (by linarith) (by linarith)
  norm_num at h3 h4; constructor <;> linarith

/-- Example 9.3.4 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  intro h; have := h 1 (by norm_num); simp at this; nlinarith

/-- Example 9.3.4 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  refine ⟨0.02, by norm_num, ?_⟩
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo] at hx
  obtain ⟨⟨_, _⟩, h3, h4⟩ := hx
  show |x ^ 2 - 4| < 0.1
  rw [abs_lt, sq x]; constructor <;> nlinarith

/-- Example 9.3.5 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 9 := by
  intro h; have := h 1 (by norm_num); simp at this; nlinarith

/-- Example 9.3.5 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 9 3 := by
  refine ⟨0.01, by norm_num, ?_⟩
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo] at hx
  obtain ⟨⟨_, _⟩, h3, h4⟩ := hx
  show |x ^ 2 - 9| < 0.1
  rw [abs_lt, sq x]; constructor <;> nlinarith

/-- Definition 9.3.6 (Convergence of functions at a point)-/
abbrev Convergesto (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop := ∀ ε > (0:ℝ), ε.CloseNear X f L x₀

/-- Connection with Mathlib filter convergence concepts -/
theorem Convergesto.iff (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) :
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  unfold Convergesto Real.CloseNear Real.CloseFn nhdsWithin
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . intro ⟨ δ, _, _ ⟩; use x₀-δ, x₀+δ, by grind
    intro _; simp; grind
  intro ⟨ l, u, ⟨ _, _ ⟩, h ⟩
  have h1 : 0 < x₀ - l := by linarith
  have h2 : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  observe hδ1 : δ ≤ x₀ - l
  observe hδ2 : δ ≤ u - x₀
  use δ, (by positivity); intro x hxX _ _
  specialize h (show x ∈ .Ioo l u by simp; grind)
  simpa [hxX] using h

/-- Example 9.3.8 -/
example: Convergesto (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  intro ε hε
  refine ⟨ε / 5, by positivity, ?_⟩
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo] at hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  show |x ^ 2 - 4| < ε
  rw [show x ^ 2 - 4 = (x - 2) * (x + 2) from by ring]
  have hx2 : |x + 2| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have hxd : |x - 2| < ε / 5 := by rw [abs_lt]; constructor <;> linarith
  calc |(x - 2) * (x + 2)| = |x - 2| * |x + 2| := abs_mul _ _
    _ < ε / 5 * 5 := by nlinarith [abs_nonneg (x - 2)]
    _ = ε := by ring

/-- Proposition 9.3.9 / Exercise 9.3.1 -/
theorem Convergesto.iff_conv {E:Set ℝ} (f: ℝ → ℝ) (L:ℝ) {x₀:ℝ} :
  Convergesto E f L x₀ ↔ ∀ a:ℕ → ℝ, (∀ n:ℕ, a n ∈ E) →
  Filter.atTop.Tendsto a (nhds x₀) →
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  constructor
  · intro h' a ha hconv
    rw [Metric.tendsto_nhds] at hconv ⊢
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := h' ε hε
    have hev := hconv δ hδ
    rw [Filter.Eventually, Filter.mem_atTop_sets] at hev ⊢
    obtain ⟨N, hN⟩ := hev
    use N; intro n hn
    simp only [Set.mem_setOf_eq] at hN ⊢
    specialize hN n hn
    rw [Real.dist_eq] at hN; rw [abs_lt] at hN
    rw [Real.dist_eq]
    exact hclose (a n) ⟨ha n, by constructor <;> linarith⟩
  · intro h'
    by_contra hc
    simp only [Convergesto, Real.CloseNear, Real.CloseFn, not_forall, not_exists,
      not_and, not_lt] at hc
    obtain ⟨ε, hε, hc⟩ := hc
    have hc' : ∀ n : ℕ, ∃ x ∈ E ∩ Set.Ioo (x₀ - 1/(n+1:ℝ)) (x₀ + 1/(n+1:ℝ)),
        ε ≤ |f x - L| := by
      intro n; obtain ⟨x, hx, hfx⟩ := hc (1/(n+1:ℝ)) (by positivity); exact ⟨x, hx, hfx⟩
    choose b hb hfb using hc'
    have hbE : ∀ n, b n ∈ E := fun n ↦ (hb n).1
    have hbconv : Filter.atTop.Tendsto b (nhds x₀) := by
      rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have hmem := (hb n).2
      rw [Real.dist_eq]; rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2]
    specialize h' b hbE hbconv
    rw [Metric.tendsto_nhds] at h'
    obtain ⟨N, hN⟩ := (h' ε hε).exists_forall_of_atTop
    simp only [Real.dist_eq] at hN
    linarith [hfb N, hN N le_rfl]

theorem Convergesto.comp {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (hf: Convergesto E f L x₀) {a:ℕ → ℝ} (ha: ∀ n:ℕ, a n ∈ E) (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [iff_conv f L] at hf; solve_by_elim

/-- Corollary 9.3.13 -/
theorem Convergesto.uniq {E:Set ℝ} {f: ℝ → ℝ} {L L':ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hf': Convergesto E f L' x₀) : L = L' := by
  -- This proof is written to follow the structure of the original text.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  exact tendsto_nhds_unique (hf.comp ha hconv) (hf'.comp ha hconv)

/-- Proposition 9.3.14 (Limit laws for functions) -/
theorem Convergesto.add {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f + g) (L + M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.add hg using 1

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.sub {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f - g) (L - M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    exact hf.sub hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.max {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (max f g) (max L M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    exact hf.max hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.min {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (min f g) (min L M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    exact hf.min hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.smul {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (c:ℝ) :
  Convergesto E (c • f) (c * L) x₀ := by
    rw [iff_conv _ _] at hf ⊢
    intro a ha hconv; specialize hf a ha hconv
    exact hf.const_smul c

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.mul {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f * g) (L * M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    exact hf.mul hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2.  The hypothesis in the book that g is non-vanishing on E can be dropped. -/
theorem Convergesto.div {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (hM: M ≠ 0)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f / g) (L / M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    exact hf.div hg hM

theorem Convergesto.const (E:Set ℝ) (x₀:ℝ) (c:ℝ)
  : Convergesto E (fun _ ↦ c) c x₀ := by
  rw [iff_conv _ _]
  intro _ _ _
  exact tendsto_const_nhds

theorem Convergesto.id (E:Set ℝ) (x₀:ℝ)
  : Convergesto E (fun x ↦ x) x₀ x₀ := by
  rw [iff_conv _ _]
  intro _ _ hconv
  exact hconv

theorem Convergesto.sq (E:Set ℝ) (x₀:ℝ)
  : Convergesto E (fun x ↦ x^2) (x₀^2) x₀ := by
  rw [iff_conv _ _]
  intro _ _ hconv
  exact hconv.pow 2

theorem Convergesto.linear (E:Set ℝ) (x₀:ℝ) (c:ℝ)
  : Convergesto E (fun x ↦ c * x) (c * x₀) x₀ := by
  exact (Convergesto.const E x₀ c).mul (Convergesto.id E x₀)

theorem Convergesto.quadratic (E:Set ℝ) (x₀:ℝ) (c d:ℝ)
  : Convergesto E (fun x ↦ x^2 + c * x + d) (x₀^2 + c * x₀ + d) x₀ := by
  have h1 := Convergesto.sq E x₀
  have h2 := Convergesto.linear E x₀ c
  have h3 := Convergesto.const E x₀ d
  have h4 := h1.add h2
  have h5 := h4.add h3
  convert h5 using 1

theorem Convergesto.restrict {X Y:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
    (hf: Convergesto X f L x₀) (hY: Y ⊆ X) : Convergesto Y f L x₀ := by
  rw [Convergesto] at hf ⊢
  intro ε hε
  specialize hf ε hε
  rw [Real.CloseNear] at hf ⊢
  obtain ⟨δ, hδ, hclose⟩ := hf
  use δ, hδ
  rw [Real.CloseFn] at hclose ⊢
  intro x hx
  apply hclose
  obtain ⟨hxY, hcloseX⟩ := hx
  constructor
  . exact hY hxY
  . exact hcloseX

theorem Real.sign_def (x:ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

/-- Example 9.3.16 -/
theorem Convergesto.sign_right : Convergesto (.Ioi 0) Real.sign 1 0 := by
  rw [Convergesto]
  intro ε hε
  rw [Real.CloseNear]
  use 1, by positivity
  rw [Real.CloseFn]
  intro x hx
  simp at hx
  have hpos: x > 0 := by linarith
  have : x.sign = 1 := by simp [Real.sign_def, hpos]; intro h; linarith
  rw [this]
  simp
  exact hε

/-- Example 9.3.16 -/
theorem Convergesto.sign_left : Convergesto (.Iio 0) Real.sign (-1) 0 := by
  rw [Convergesto]
  intro ε hε
  rw [Real.CloseNear]
  use 1, by positivity
  rw [Real.CloseFn]
  intro x hx
  simp at hx
  have hpos: x < 0 := by linarith
  have : x.sign = -1 := by simp [Real.sign_def, hpos]
  rw [this]
  simp
  exact hε

/-- Example 9.3.16 -/
theorem Convergesto.sign_all : ¬ ∃ L, Convergesto (.univ) Real.sign L 0 := by
  push_neg
  intro L h
  rw [Convergesto] at h
  specialize h 1 (by positivity)
  rw [Real.CloseNear] at h
  obtain ⟨δ, hδ, hclose⟩ := h
  rw [Real.CloseFn] at hclose
  have h1 := hclose (-δ/2) (by simp; constructor <;> linarith)
  have h2 := hclose (δ/2) (by simp; constructor <;> linarith)
  rw [Real.sign_def] at h1 h2
  have hn : - δ / 2 < 0 := by
    have : -δ < 0 := by linarith
    simp at this; linarith
  have hn' : ¬ (δ /  2 < 0) := by simp; linarith
  simp [hn, hn', hδ] at h1 h2
  grind

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

theorem Convergesto.f_9_3_17_remove : Convergesto (.univ \ {0}) f_9_3_17 0 0 := by
  rw [Convergesto]
  intro ε hε
  rw [Real.CloseNear]
  use 1, by positivity
  rw [Real.CloseFn]
  intro x hx
  simp at hx
  have hpos: x ≠ 0 := by exact hx.1
  have : f_9_3_17 x = 0 := by simp [f_9_3_17, hpos]
  rw [this]
  simp
  exact hε

theorem Convergesto.f_9_3_17_all : ¬ ∃ L, Convergesto .univ f_9_3_17 L 0 := by
  push_neg
  intro L h
  rw [Convergesto] at h
  specialize h 0.3 (by positivity)
  rw [Real.CloseNear] at h
  obtain ⟨δ, hδ, hclose⟩ := h
  rw [Real.CloseFn] at hclose
  have h1 := hclose (-δ/2) (by simp; constructor <;> linarith)
  have h2 := hclose 0 (by simp; exact hδ)
  simp [f_9_3_17, show ¬ δ = 0 by linarith] at h1 h2
  rw [abs_lt] at h1 h2; linarith

/-- Proposition 9.3.18 / Exercise 9.3.3 -/
theorem Convergesto.local {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} {δ:ℝ} (hδ: δ > 0) :
  Convergesto E f L x₀ ↔ Convergesto (E ∩ .Ioo (x₀-δ) (x₀+δ)) f L x₀ := by
  constructor
  . intro h
    apply restrict h
    exact Set.inter_subset_left
  . intro h
    rw [Convergesto] at h ⊢
    intro ε hε
    specialize h ε hε
    rw [Real.CloseNear] at h ⊢
    obtain ⟨δ', hδ', hclose⟩ := h
    use Min.min δ δ', by positivity
    convert hclose using 1
    ext x
    repeat rw [Set.mem_inter_iff]
    simp only [Set.mem_Ioo]
    constructor
    . rintro ⟨hxE, hδx, hδ'x⟩
      have h1 := min_le_left δ δ'
      have h2 := min_le_right δ δ'
      exact ⟨⟨hxE, by linarith, by linarith⟩, by linarith, by linarith⟩
    . rintro ⟨⟨hxE, h1, h2⟩, hδx, hδ'x⟩
      refine ⟨hxE, ?_, ?_⟩
      . have := lt_min (show x₀ - x < δ by linarith) (show x₀ - x < δ' by linarith)
        linarith
      . have := lt_min (show x - x₀ < δ by linarith) (show x - x₀ < δ' by linarith)
        linarith

/-- Example 9.3.19.  The point of this example is somewhat blunted by the ability to remove the hypothesis that {lit}`g` is non-zero from the relevant part of Proposition 9.3.14 -/
example : Convergesto .univ (fun x ↦ (x+2)/(x+1)) (4/3:ℝ) 2 := by
  apply Convergesto.div (by norm_num)
  . rw [show (4:ℝ) = 2 + 2 by norm_num]
    apply Convergesto.add
    . exact Convergesto.id .univ 2
    . exact Convergesto.const .univ 2 2
  . rw [show (3:ℝ) = 2 + 1 by norm_num]
    apply Convergesto.add
    . exact Convergesto.id .univ 2
    . exact Convergesto.const .univ 2 1

/-- Example 9.3.20 -/
example : Convergesto (.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by
  rw [show (2:ℝ) = 2 / 1 by norm_num]
  suffices h : Convergesto (.univ \ {1}) (fun x ↦ x + 1) (2 / 1) 1 by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx ↦ by
      have hx1 : x ≠ 1 := by
        obtain ⟨_, hx1⟩ := hx.1
        simpa using hx1
      have key : (x ^ 2 - 1) / (x - 1) = x + 1 := by
        have : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
        field_simp
        ring
      simp only [key]
      exact hδ' x hx⟩
  rw [show (2:ℝ) / 1 = 1 + 1 by norm_num]
  apply Convergesto.add
  · exact Convergesto.id _ 1
  · exact Convergesto.const _ 1 1

open Classical in
/-- Example 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ then 1 else 0

theorem f_9_3_21_seq_conv_1 : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 (1/n:ℝ)) (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.Eventually, Filter.mem_atTop_sets]
  use 2; intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  have : (1/n:ℝ) ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ := by
    simp
    use 1 / n
    simp
  rw [f_9_3_21]
  simp only [this, if_true]
  rw [Real.dist_eq]
  simp
  exact hε

theorem f_9_3_21_seq_conv_0 : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.Eventually, Filter.mem_atTop_sets]
  use 2; intro n hn
  simp only [Set.mem_setOf_eq] at hn ⊢
  have : ((Real.sqrt 2)/n:ℝ) ∉ (fun q:ℚ ↦ (q:ℝ)) '' .univ := by
    simp
    intro h
    obtain ⟨q, _, hq⟩ := h
    have hn0 : n ≠ 0 := by omega
    exact Ne.symm ((irrational_sqrt_two.div_natCast hn0).ne_rat _)
  rw [f_9_3_21]
  simp only [this, if_false]
  rw [Real.dist_eq]
  simp
  exact hε

example : ¬ ∃ L, Convergesto .univ f_9_3_21 L 0 := by
  by_contra h
  obtain ⟨L, h⟩ := h
  rw [Convergesto.iff_conv] at h
  have seq1_tendsto : Filter.Tendsto (fun (n:ℕ) => (1:ℝ)/n) Filter.atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have seq2_tendsto : Filter.Tendsto (fun (n:ℕ) => (Real.sqrt 2)/(n:ℝ)) Filter.atTop (nhds 0) := by
    rw [show (0:ℝ) = Real.sqrt 2 * 0 by ring]
    exact tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hL1 := h _ (fun _ => Set.mem_univ _) seq1_tendsto
  have hL0 := h _ (fun _ => Set.mem_univ _) seq2_tendsto
  have h1 := tendsto_nhds_unique hL1 f_9_3_21_seq_conv_1
  have h0 := tendsto_nhds_unique hL0 f_9_3_21_seq_conv_0
  linarith

/- Exercise 9.3.4: State a definition of limit superior and limit inferior for functions, and prove an analogue of Proposition 9.3.9 for those definitions. -/
abbrev puncturedNear (X:Set ℝ) (x₀ ε:ℝ) : Set ℝ :=
  (X ∩ Set.Ioo (x₀-ε) (x₀+ε)) \ {x₀}

abbrev valuesNear (X:Set ℝ) (f: ℝ → ℝ) (x₀ ε:ℝ) : Set EReal :=
  (fun x:ℝ ↦ (f x:EReal)) '' puncturedNear X x₀ ε

noncomputable abbrev upperEnvelope (X:Set ℝ) (f: ℝ → ℝ) (x₀ ε:ℝ) : EReal :=
  sSup (valuesNear X f x₀ ε)

noncomputable abbrev lowerEnvelope (X:Set ℝ) (f: ℝ → ℝ) (x₀ ε:ℝ) : EReal :=
  sInf (valuesNear X f x₀ ε)

abbrev FiniteNearZero (g: ℝ → EReal) : Prop :=
  ∃ δ > (0:ℝ), ∀ ε ∈ Set.Ioo 0 δ, g ε ≠ ⊤ ∧ g ε ≠ ⊥

abbrev DivergesToTop (g: ℝ → EReal) : Prop :=
  ∀ A:ℝ, ∃ δ > (0:ℝ), ∀ ε ∈ Set.Ioo 0 δ, (A:EReal) < g ε

abbrev DivergesToBot (g: ℝ → EReal) : Prop :=
  ∀ A:ℝ, ∃ δ > (0:ℝ), ∀ ε ∈ Set.Ioo 0 δ, g ε < (A:EReal)

noncomputable abbrev limSup (X:Set ℝ) (f: ℝ → ℝ) (L:EReal) (x₀:ℝ) : Prop :=
  match L with
  | ⊤ => DivergesToTop (upperEnvelope X f x₀)
  | ⊥ => DivergesToBot (upperEnvelope X f x₀)
  | (r:ℝ) => FiniteNearZero (upperEnvelope X f x₀) ∧
      Convergesto (.Ioi 0) (fun ε ↦ (upperEnvelope X f x₀ ε).toReal) r 0

noncomputable abbrev limInf (X:Set ℝ) (f: ℝ → ℝ) (L:EReal) (x₀:ℝ) : Prop :=
  match L with
  | ⊤ => DivergesToTop (lowerEnvelope X f x₀)
  | ⊥ => DivergesToBot (lowerEnvelope X f x₀)
  | (r:ℝ) => FiniteNearZero (lowerEnvelope X f x₀) ∧
      Convergesto (.Ioi 0) (fun ε ↦ (lowerEnvelope X f x₀ ε).toReal) r 0

private lemma eventually_nhdsWithin_Ioi_zero_iff {P : ℝ → Prop} :
    (∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), P ε) ↔ ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, P ε := by
  rw [nhdsWithin, Filter.eventually_inf_principal, Filter.Eventually,
    mem_nhds_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨l, u, hlu, hP⟩
    obtain ⟨hl, hu⟩ := Set.mem_Ioo.mp hlu
    refine ⟨min (-l) u, lt_min (by linarith) hu, ?_⟩
    rintro ε ⟨hε1, hε2⟩
    exact hP ⟨by linarith, by linarith [min_le_right (-l) u]⟩ hε1
  · rintro ⟨δ, hδ, hP⟩
    refine ⟨-1, δ, Set.mem_Ioo.mpr ⟨by linarith, hδ⟩, ?_⟩
    intro ε hε hεmem
    exact hP ε ⟨hεmem, hε.2⟩

private lemma ne_top_bot_of_mem_compl {x : EReal} (h : x ∈ ({⊥, ⊤}ᶜ : Set EReal)) :
    x ≠ ⊤ ∧ x ≠ ⊥ := by simpa [not_or, and_comm] using h

private theorem limSup_iff_tendsto {E:Set ℝ} {f: ℝ → ℝ} {L:EReal} {x₀:ℝ} :
    limSup E f L x₀ ↔
      (nhdsWithin 0 (.Ioi 0)).Tendsto (upperEnvelope E f x₀) (nhds L) := by
  cases L using EReal.rec with
  | top =>
      rw [limSup, EReal.tendsto_nhds_top_iff_real]
      simp_rw [eventually_nhdsWithin_Ioi_zero_iff]
  | bot =>
      show DivergesToBot (upperEnvelope E f x₀) ↔ _
      rw [EReal.tendsto_nhds_bot_iff_real]
      simp_rw [eventually_nhdsWithin_Ioi_zero_iff]
  | coe r =>
      show (FiniteNearZero (upperEnvelope E f x₀) ∧
        Convergesto (.Ioi 0) (fun ε ↦ (upperEnvelope E f x₀ ε).toReal) r 0) ↔
        (nhdsWithin 0 (.Ioi 0)).Tendsto (upperEnvelope E f x₀) (nhds ↑r)
      constructor
      · rintro ⟨⟨δ, hδ, hfinδ⟩, hconv⟩
        rw [Convergesto.iff] at hconv
        have hfinite : ∀ᶠ ε in nhdsWithin 0 (.Ioi 0),
            upperEnvelope E f x₀ ε ≠ ⊤ ∧ upperEnvelope E f x₀ ε ≠ ⊥ :=
          eventually_nhdsWithin_Ioi_zero_iff.mpr ⟨δ, hδ, hfinδ⟩
        have heq : upperEnvelope E f x₀ =ᶠ[nhdsWithin 0 (.Ioi 0)]
            (fun ε ↦ (((upperEnvelope E f x₀ ε).toReal : ℝ) : EReal)) := by
          filter_upwards [hfinite] with ε hε
          exact (EReal.coe_toReal hε.1 hε.2).symm
        exact Filter.Tendsto.congr' heq.symm (EReal.tendsto_coe.mpr hconv)
      · intro h
        have hfinite : FiniteNearZero (upperEnvelope E f x₀) := by
          have hmem : ({⊥, ⊤}ᶜ : Set EReal) ∈ nhds ((r:EReal)) :=
            (Set.Finite.isClosed (Set.toFinite _)).isOpen_compl.mem_nhds (by simp)
          obtain ⟨δ, hδ, hP⟩ := eventually_nhdsWithin_Ioi_zero_iff.mp (h hmem)
          exact ⟨δ, hδ, fun ε hε ↦ ne_top_bot_of_mem_compl (hP ε hε)⟩
        exact ⟨hfinite, (Convergesto.iff _ _ _ _).2
          ((EReal.tendsto_toReal (by simp) (by simp)).comp h)⟩

private theorem limInf_iff_tendsto {E:Set ℝ} {f: ℝ → ℝ} {L:EReal} {x₀:ℝ} :
    limInf E f L x₀ ↔
      (nhdsWithin 0 (.Ioi 0)).Tendsto (lowerEnvelope E f x₀) (nhds L) := by
  cases L using EReal.rec with
  | top =>
      rw [limInf, EReal.tendsto_nhds_top_iff_real]
      simp_rw [eventually_nhdsWithin_Ioi_zero_iff]
  | bot =>
      show DivergesToBot (lowerEnvelope E f x₀) ↔ _
      rw [EReal.tendsto_nhds_bot_iff_real]
      simp_rw [eventually_nhdsWithin_Ioi_zero_iff]
  | coe r =>
      show (FiniteNearZero (lowerEnvelope E f x₀) ∧
        Convergesto (.Ioi 0) (fun ε ↦ (lowerEnvelope E f x₀ ε).toReal) r 0) ↔
        (nhdsWithin 0 (.Ioi 0)).Tendsto (lowerEnvelope E f x₀) (nhds ↑r)
      constructor
      · rintro ⟨⟨δ, hδ, hfinδ⟩, hconv⟩
        rw [Convergesto.iff] at hconv
        have hfinite : ∀ᶠ ε in nhdsWithin 0 (.Ioi 0),
            lowerEnvelope E f x₀ ε ≠ ⊤ ∧ lowerEnvelope E f x₀ ε ≠ ⊥ :=
          eventually_nhdsWithin_Ioi_zero_iff.mpr ⟨δ, hδ, hfinδ⟩
        have heq : lowerEnvelope E f x₀ =ᶠ[nhdsWithin 0 (.Ioi 0)]
            (fun ε ↦ (((lowerEnvelope E f x₀ ε).toReal : ℝ) : EReal)) := by
          filter_upwards [hfinite] with ε hε
          exact (EReal.coe_toReal hε.1 hε.2).symm
        exact Filter.Tendsto.congr' heq.symm (EReal.tendsto_coe.mpr hconv)
      · intro h
        have hfinite : FiniteNearZero (lowerEnvelope E f x₀) := by
          have hmem : ({⊥, ⊤}ᶜ : Set EReal) ∈ nhds ((r:EReal)) :=
            (Set.Finite.isClosed (Set.toFinite _)).isOpen_compl.mem_nhds (by simp)
          obtain ⟨δ, hδ, hP⟩ := eventually_nhdsWithin_Ioi_zero_iff.mp (h hmem)
          exact ⟨δ, hδ, fun ε hε ↦ ne_top_bot_of_mem_compl (hP ε hε)⟩
        exact ⟨hfinite, (Convergesto.iff _ _ _ _).2
          ((EReal.tendsto_toReal (by simp) (by simp)).comp h)⟩

private lemma tendsto_of_mem_puncturedNear {E:Set ℝ} {x₀:ℝ} {a:ℕ → ℝ}
    (ha_pn: ∀ n, a n ∈ puncturedNear E x₀ (1 / (↑n + 1))) :
    Filter.Tendsto a Filter.atTop (nhds x₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N; intro n hn
  have hIoo := (ha_pn n).1.2
  rw [Set.mem_Ioo] at hIoo
  rw [Real.dist_eq, abs_lt]
  have : 1 / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) :=
    div_le_div_of_nonneg_left one_pos.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1)
  have : 1 / ((N:ℝ) + 1) < ε := by
    have hN1 : 1 / ε < ↑N + 1 := lt_trans hN (by linarith)
    rwa [div_lt_comm₀ hε (by positivity : (0:ℝ) < ↑N + 1)] at hN1
  constructor <;> linarith

private lemma upperEnvelope_eventually_ge {E:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {a:ℕ → ℝ}
    (ha_mem: ∀ n, a n ∈ E) (ha_neq: ∀ n, a n ≠ x₀)
    (ha_conv: Filter.atTop.Tendsto a (nhds x₀)) (ε:ℝ) (hε: ε > 0) :
    ∀ᶠ n in Filter.atTop, (f (a n) : EReal) ≤ upperEnvelope E f x₀ ε := by
  rw [Metric.tendsto_atTop] at ha_conv
  obtain ⟨N, hN⟩ := ha_conv ε hε
  rw [Filter.eventually_atTop]
  use N
  intro n hn
  apply le_csSup_of_le ⟨⊤, fun x hx ↦ le_top⟩
  · exact ⟨a n, ⟨⟨ha_mem n, by
      specialize hN n hn; rw [Real.dist_eq, abs_lt] at hN; constructor <;> linarith⟩,
      ha_neq n⟩, rfl⟩
  · exact le_rfl

/-- limsup of f∘a ≤ upperEnvelope(ε) for any sequence converging to x₀ -/
private lemma limsup_le_upperEnvelope {E:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {a:ℕ → ℝ}
    (ha_mem: ∀ n, a n ∈ E) (ha_neq: ∀ n, a n ≠ x₀)
    (ha_conv: Filter.atTop.Tendsto a (nhds x₀)) (ε:ℝ) (hε: ε > 0) :
    Filter.limsup (fun n ↦ (f (a n) : EReal)) Filter.atTop ≤ upperEnvelope E f x₀ ε := by
  apply Filter.limsup_le_of_le ⟨⊥, by simp⟩
  exact upperEnvelope_eventually_ge ha_mem ha_neq ha_conv ε hε

/-- The iSup of sequential limsups equals the infimum of upperEnvelope -/
private lemma iSup_limsup_eq_iInf_upperEnvelope {E:Set ℝ} (f: ℝ → ℝ) {x₀:ℝ} :
    ⨆ (a:ℕ → ℝ) (_ : ∀ n, a n ∈ E) (_ : ∀ n, a n ≠ x₀)
      (_ : Filter.atTop.Tendsto a (nhds x₀)),
      Filter.limsup (fun n ↦ (f (a n) : EReal)) Filter.atTop =
    ⨅ (ε : ℝ) (_ : ε > 0), upperEnvelope E f x₀ ε := by
  apply le_antisymm
  · -- iSup of sequential limsups ≤ iInf of upper envelopes
    apply iSup_le; intro a
    apply iSup_le; intro ha_mem
    apply iSup_le; intro ha_neq
    apply iSup_le; intro ha_conv
    apply le_iInf; intro ε
    apply le_iInf; intro hε
    exact limsup_le_upperEnvelope ha_mem ha_neq ha_conv ε hε
  · -- iInf of upper envelopes ≤ iSup of sequential limsups
    set S := ⨆ (a : ℕ → ℝ) (_ : ∀ n, a n ∈ E) (_ : ∀ n, a n ≠ x₀)
      (_ : Filter.atTop.Tendsto a (nhds x₀)),
      Filter.limsup (fun n ↦ (f (a n) : EReal)) Filter.atTop
    apply le_of_forall_lt_imp_le_of_dense
    intro v hv
    -- v < upperEnvelope ε for all ε > 0
    have hv_lt : ∀ ε > 0, v < upperEnvelope E f x₀ ε := by
      intro ε hε
      exact lt_of_lt_of_le hv (iInf_le_of_le ε (iInf_le_of_le hε le_rfl))
    -- For each n, pick a_n ∈ puncturedNear with f(a_n) > v
    have hchoose : ∀ n : ℕ, ∃ x, x ∈ puncturedNear E x₀ (1 / (↑n + 1)) ∧
        v < (f x : EReal) := by
      intro n
      have h1 : v < sSup (valuesNear E f x₀ (1 / (↑n + 1))) := hv_lt _ (by positivity)
      rw [lt_sSup_iff] at h1
      obtain ⟨w, ⟨x, hx, rfl⟩, hw⟩ := h1
      exact ⟨x, hx, hw⟩
    choose a ha_pn ha_fab using hchoose
    have ha_conv := tendsto_of_mem_puncturedNear ha_pn
    calc v ≤ Filter.limsup (fun n ↦ (f (a n) : EReal)) Filter.atTop :=
            Filter.le_limsup_of_frequently_le'
              (Filter.Frequently.of_forall (fun n => le_of_lt (ha_fab n)))
      _ ≤ S := le_iSup₂_of_le a (fun n => (ha_pn n).1.1)
              (le_iSup₂_of_le (fun n => (ha_pn n).2) ha_conv le_rfl)

/-- upperEnvelope is monotone: larger ε gives larger (or equal) sSup -/
private lemma upperEnvelope_monotone {E:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} :
    Monotone (fun ε ↦ upperEnvelope E f x₀ ε) := by
  intro ε₁ ε₂ h
  apply sSup_le_sSup
  intro v ⟨x, hx, hv⟩
  exact ⟨x, ⟨⟨hx.1.1, by constructor <;> linarith [hx.1.2.1, hx.1.2.2]⟩, hx.2⟩, hv⟩

/-- The limit of a monotone EReal-valued function as ε → 0⁺ equals its infimum -/
private lemma tendsto_iInf_of_monotone_nhdsWithin {g : ℝ → EReal}
    (hg : Monotone g) :
    (nhdsWithin 0 (.Ioi 0)).Tendsto g (nhds (⨅ (ε : ℝ) (_ : ε > 0), g ε)) := by
  convert hg.tendsto_nhdsGT 0 using 1
  congr 1
  simp only [sInf_image, Set.mem_Ioi]

/-- Sequential characterization of limSup -/
theorem Convergesto.iff_conv_limSup {E:Set ℝ} (f: ℝ → ℝ) (L:EReal) {x₀:ℝ} :
    limSup E f L x₀ ↔
    L = ⨆ (a:ℕ → ℝ) (_ : ∀ n, a n ∈ E) (_ : ∀ n, a n ≠ x₀)
      (_ : Filter.atTop.Tendsto a (nhds x₀)),
      Filter.limsup (fun n ↦ (f (a n) : EReal)) Filter.atTop := by
  rw [limSup_iff_tendsto]
  rw [iSup_limsup_eq_iInf_upperEnvelope f]
  constructor
  · intro h
    exact tendsto_nhds_unique h (tendsto_iInf_of_monotone_nhdsWithin upperEnvelope_monotone)
  · intro h
    rw [h]
    exact tendsto_iInf_of_monotone_nhdsWithin upperEnvelope_monotone

private lemma lowerEnvelope_eventually_le {E:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {a:ℕ → ℝ}
    (ha_mem: ∀ n, a n ∈ E) (ha_neq: ∀ n, a n ≠ x₀)
    (ha_conv: Filter.atTop.Tendsto a (nhds x₀)) (ε:ℝ) (hε: ε > 0) :
    ∀ᶠ n in Filter.atTop, lowerEnvelope E f x₀ ε ≤ (f (a n) : EReal) := by
  rw [Metric.tendsto_atTop] at ha_conv
  obtain ⟨N, hN⟩ := ha_conv ε hε
  rw [Filter.eventually_atTop]
  use N
  intro n hn
  apply csInf_le_of_le ⟨⊥, fun x hx ↦ bot_le⟩
  · exact ⟨a n, ⟨⟨ha_mem n, by
      specialize hN n hn; rw [Real.dist_eq, abs_lt] at hN; constructor <;> linarith⟩,
      ha_neq n⟩, rfl⟩
  · exact le_rfl

private lemma lowerEnvelope_le_liminf {E:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {a:ℕ → ℝ}
    (ha_mem: ∀ n, a n ∈ E) (ha_neq: ∀ n, a n ≠ x₀)
    (ha_conv: Filter.atTop.Tendsto a (nhds x₀)) (ε:ℝ) (hε: ε > 0) :
    lowerEnvelope E f x₀ ε ≤ Filter.liminf (fun n ↦ (f (a n) : EReal)) Filter.atTop := by
  apply Filter.le_liminf_of_le ⟨⊤, by simp⟩
  exact lowerEnvelope_eventually_le ha_mem ha_neq ha_conv ε hε

private lemma lowerEnvelope_antitone {E:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} :
    Antitone (fun ε ↦ lowerEnvelope E f x₀ ε) := by
  intro ε₁ ε₂ h
  apply sInf_le_sInf
  intro v ⟨x, hx, hv⟩
  exact ⟨x, ⟨⟨hx.1.1, by constructor <;> linarith [hx.1.2.1, hx.1.2.2]⟩, hx.2⟩, hv⟩

private lemma tendsto_iSup_of_antitone_nhdsWithin {g : ℝ → EReal}
    (hg : Antitone g) :
    (nhdsWithin 0 (.Ioi 0)).Tendsto g (nhds (⨆ (ε : ℝ) (_ : ε > 0), g ε)) := by
  convert hg.tendsto_nhdsGT 0 using 1
  congr 1
  simp only [sSup_image, Set.mem_Ioi]

private lemma iInf_liminf_eq_iSup_lowerEnvelope {E:Set ℝ} (f: ℝ → ℝ) {x₀:ℝ} :
    ⨅ (a:ℕ → ℝ) (_ : ∀ n, a n ∈ E) (_ : ∀ n, a n ≠ x₀)
      (_ : Filter.atTop.Tendsto a (nhds x₀)),
      Filter.liminf (fun n ↦ (f (a n) : EReal)) Filter.atTop =
    ⨆ (ε : ℝ) (_ : ε > 0), lowerEnvelope E f x₀ ε := by
  apply le_antisymm
  · -- iInf of sequential liminfs ≤ iSup of lower envelopes
    apply le_of_forall_gt_imp_ge_of_dense
    intro v hv
    have hv_lt : ∀ ε > 0, lowerEnvelope E f x₀ ε < v := by
      intro ε hε
      exact lt_of_le_of_lt (le_iSup₂_of_le ε hε le_rfl) hv
    have hchoose : ∀ n : ℕ, ∃ x, x ∈ puncturedNear E x₀ (1 / (↑n + 1)) ∧
        (f x : EReal) < v := by
      intro n
      have h1 : sInf (valuesNear E f x₀ (1 / (↑n + 1))) < v := hv_lt _ (by positivity)
      rw [sInf_lt_iff] at h1
      obtain ⟨w, ⟨x, hx, rfl⟩, hw⟩ := h1
      exact ⟨x, hx, hw⟩
    choose a ha_pn ha_fab using hchoose
    have ha_conv := tendsto_of_mem_puncturedNear ha_pn
    calc
      _ ≤ Filter.liminf (fun n ↦ (f (a n) : EReal)) Filter.atTop :=
          iInf₂_le_of_le a (fun n => (ha_pn n).1.1)
            (iInf₂_le_of_le (fun n => (ha_pn n).2) ha_conv le_rfl)
      _ ≤ v := Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall (fun n => le_of_lt (ha_fab n)))
  · -- iSup of lower envelopes ≤ iInf of sequential liminfs
    apply iSup_le; intro ε
    apply iSup_le; intro hε
    apply le_iInf; intro a
    apply le_iInf; intro ha_mem
    apply le_iInf; intro ha_neq
    apply le_iInf; intro ha_conv
    exact lowerEnvelope_le_liminf ha_mem ha_neq ha_conv ε hε

/-- Sequential characterization of limInf -/
theorem Convergesto.iff_conv_limInf {E:Set ℝ} (f: ℝ → ℝ) (L:EReal) {x₀:ℝ} :
    limInf E f L x₀ ↔
    L = ⨅ (a:ℕ → ℝ) (_ : ∀ n, a n ∈ E) (_ : ∀ n, a n ≠ x₀)
      (_ : Filter.atTop.Tendsto a (nhds x₀)),
      Filter.liminf (fun n ↦ (f (a n) : EReal)) Filter.atTop := by
  rw [limInf_iff_tendsto]
  rw [iInf_liminf_eq_iSup_lowerEnvelope f]
  constructor
  · intro h
    exact tendsto_nhds_unique h (tendsto_iSup_of_antitone_nhdsWithin lowerEnvelope_antitone)
  · intro h
    rw [h]
    exact tendsto_iSup_of_antitone_nhdsWithin lowerEnvelope_antitone

/-- Exercise 9.3.5 (Continuous version of squeeze test) -/
theorem Convergesto.squeeze {E:Set ℝ} {f g h: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
  (hfg: ∀ x ∈ E, f x ≤ g x) (hgh: ∀ x ∈ E, g x ≤ h x)
  (hf: Convergesto E f L x₀) (hh: Convergesto E h L x₀) :
  Convergesto E g L x₀ := by
    rw [iff_conv _ _] at hf hh ⊢
    intro a ha hconv
    specialize hf a ha hconv
    specialize hh a ha hconv
    have hl : ∀ n , f (a n) ≤ g (a n) := by intro n; exact hfg _ (ha n)
    have hr : ∀ n , g (a n) ≤ h (a n) := by intro n; exact hgh _ (ha n)
    apply hf.squeeze hh hl hr

end Chapter9
