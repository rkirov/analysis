import Mathlib.Tactic
import Mathlib.Data.Real.Sign
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
theorem Convergesto.local {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) {δ:ℝ} (hδ: δ > 0) :
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
example : Convergesto .univ (fun x ↦ (x+2)/(x+1)) (4/3:ℝ) 2 := by sorry

/-- Example 9.3.20 -/
example : Convergesto (.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by sorry

open Classical in
/-- Example 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ then 1 else 0

example : Filter.atTop.Tendsto (fun n ↦ f_9_3_21 (1/n:ℝ)) (nhds 1) := by sorry

example : Filter.atTop.Tendsto (fun n ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) (nhds 0) := by sorry

example : ¬ ∃ L, Convergesto .univ f_9_3_21 L 0 := by sorry

/- Exercise 9.3.4: State a definition of limit superior and limit inferior for functions, and prove an analogue of Proposition 9.3.9 for those definitions. -/

/-- Exercise 9.3.5 (Continuous version of squeeze test) -/
theorem Convergesto.squeeze {E:Set ℝ} {f g h: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (had: AdherentPt x₀ E)
  (hfg: ∀ x ∈ E, f x ≤ g x) (hgh: ∀ x ∈ E, g x ≤ h x)
  (hf: Convergesto E f L x₀) (hh: Convergesto E h L x₀) :
  Convergesto E g L x₀ := by
    sorry


end Chapter9
