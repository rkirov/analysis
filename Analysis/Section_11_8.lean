import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 11.8: The Riemann-Stieltjes integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Definition of `α_length`.
- The piecewise constant Riemann-Stieltjes integral.
- The full Riemann-Stieltjes integral.

{open Set}

Technical notes:
- In Lean it is more convenient to make definitions such as `α_length` and the Riemann-Stieltjes
  integral totally defined, thus assigning "junk" values to the cases where the definition is
  not intended to be applied. For the definition of `α_length`, the definition is intended to be
  applied in contexts where left and right limits exist, and the function is extended by
  constants to the left and right of its intended domain of definition; for instance, if a
  function `x` `f` is defined on {lean}`Icc 0 1`, then it is intended that `f x = f 1` for all `x ≥ 1`
  and `f x = f 0` for all `x ≤ 0`; in particular, at a right endpoint, the value of a function
  is intended to agree with its right limit, and similarly for the left endpoint, although we
  do not enforce this in our definition of `α_length`. (For functions defined on open intervals,
  the extension is immaterial.)
- The notion of `α_length` and piecewise constant Riemann-Stieltjes integral is intended for
  situations where left and right limits exist, such as for monotone functions or continuous
  functions, though technically they make sense without these hypotheses. The full Riemann-Stieltjes
  integral is intended for functions that are of bounded variation, though we shall restrict
  attention to the special case of monotone increasing functions for the most part.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Left and right limits. A junk value is assigned if the limit does not exist. -/
noncomputable abbrev right_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Ioi x₀)).map f)

noncomputable abbrev left_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Iio x₀)).map f)

theorem right_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Ioi x₀) f L x₀) :
  right_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

theorem left_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Iio x₀) f L x₀) :
  left_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Right limits exist for continuous functions -/
theorem right_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  right_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo x₀ (x₀ + ε))).Tendsto f  (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ico_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]; congr 1; simp [Set.Ioo_subset_Ioi_self]

/-- Left limits exist for continuous functions -/
theorem left_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  left_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo (x₀ - ε) x₀)).Tendsto f (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ioc_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1; simp [Set.Ioo_subset_Iio_self]

/-- No jump for continuous functions -/
theorem jump_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : X ∈ nhds x₀) (hf: ContinuousWithinAt f X x₀) :
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  choose l u hx₀ hX using h; simp at hx₀
  have hl : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X :=
    ⟨ x₀-l, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  have hu : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X :=
    ⟨ u-x₀, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Right limits exist for monotone functions -/
theorem right_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Ioi x₀) f (sInf (f '' .Ioi x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsGT
  rw [bddBelow_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem right_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  right_lim f x₀ = sInf (f '' .Ioi x₀) := right_lim_def (right_lim_of_monotone x₀ hf)

/-- Left limits exist for monotone functions -/
theorem left_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Iio x₀) f (sSup (f '' .Iio x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsLT
  rw [bddAbove_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem left_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  left_lim f x₀ = sSup (f '' .Iio x₀) := left_lim_def (left_lim_of_monotone x₀ hf)

theorem jump_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le (by simp); intro a ha
  apply le_csInf (by simp); intro b hb; simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha; obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; grind

theorem right_lim_le_left_lim_of_monotone {f:ℝ → ℝ} {a b:ℝ} (hab: a < b)
  (hf: Monotone f) :
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply csInf_le
      . rw [bddBelow_def]; use f a; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply le_csSup
      . rw [bddAbove_def]; use f b; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith

/-- Definition 11.8.1 -/
noncomputable abbrev α_length (α: ℝ → ℝ) (I: BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

syntax:max term "[" term "]ₗ" : term
macro_rules | `($α[$I]ₗ) => `(α_length $α $I)

theorem α_length_of_empty (α: ℝ → ℝ) {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc _ _ => by simp [Set.Icc_eq_empty_iff] at *; simp [*]
  | Ico a b => by simp [Set.Ico_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioc a b => by simp [Set.Ioc_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioo _ _ => by simp [Set.Ioo_eq_empty_iff] at *; simp [*]

@[simp]
theorem α_length_of_pt {α: ℝ → ℝ} (a:ℝ) : α[Icc a a]ₗ = jump α a := by simp [α_length, jump]

theorem α_length_of_cts {α:ℝ → ℝ} {I: BoundedInterval} {a b: ℝ}
  (haa: a < I.a) (hab: I.a ≤ I.b) (hbb: I.b < b)
  (hI : I ⊆ Ioo a b) (hα: ContinuousOn α (Ioo a b)) :
  α[I]ₗ = α I.b - α I.a := by
  have ha_left : left_lim α I.a = α I.a := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.a - a, by grind, by intro _; simp; grind ⟩
  have ha_right : right_lim α I.a = α I.a := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.a, by grind, by intro _; simp; grind ⟩
  have hb_left : left_lim α I.b = α I.b := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.b - a, by grind, by intro _; simp; grind ⟩
  have hb_right : right_lim α I.b = α I.b := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.b, by grind, by intro _; simp; grind ⟩
  cases I with
  | Icc _ _ => grind
  | Ico _ _ => grind
  | Ioc _ _ => grind
  | Ioo _ _ => simp [α_length, ha_right, hb_left]; intro h; have := le_antisymm h (by linarith); subst this; simp

/-- Example 11.8.2-/
example : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
  rw [α_length_of_cts (I:=Icc 2 3) (a:=1) (b:=4)]
  . grind
  . grind
  . grind
  . grind
  . simp [BoundedInterval.subset_iff]
    grind
  . exact continuousOn_pow 2


example : (fun x ↦ x^2)[Icc 2 2]ₗ = 0 := by
  rw [α_length_of_cts (a:=1) (b:=3) (I:=Icc 2 2)]
  . grind
  . grind
  . grind
  . grind
  . simp [BoundedInterval.subset_iff]
    grind
  . exact continuousOn_pow 2

example : (fun x ↦ x^2)[Ioo 2 2]ₗ = 0 := by
  rw [α_length_of_empty]
  simp

/-- Example 11.8.3-/
@[simp]
theorem α_len_of_id (I: BoundedInterval) : (fun x ↦ x)[I]ₗ = |I|ₗ := by
  by_cases h: I.a ≤ I.b
  . rw [α_length_of_cts (a:=I.a-1) (b:=I.b+1) (I:=I)]
    simp
    . exact h
    . linarith
    . exact h
    . linarith
    . rw [BoundedInterval.subset_iff]
      intro x hx
      simp at h ⊢
      have := (I.subset_iff _).mp I.subset_Icc hx
      simp at this
      constructor <;> linarith
    . exact continuousOn_id
  . simp at h
    have : (I:Set ℝ) = ∅ := by exact empty_of_lt h
    rw [α_length_of_empty]
    . simp
      exact h.le
    . exact this

/-- An improved version of {name}`BoundedInterval.joins` that also controls {name}`α_length`. -/
abbrev BoundedInterval.joins' (K I J: BoundedInterval) : Prop :=  K.joins I J ∧ ∀ α:ℝ → ℝ, α[K]ₗ = α[I]ₗ + α[J]ₗ

theorem BoundedInterval.join_Icc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Icc a b) (Ioc b c) := ⟨ join_Icc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩


theorem BoundedInterval.join_Icc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins' (Icc a b) (Ioo b c) := ⟨ join_Icc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioc a b) (Ioc b c) := ⟨ join_Ioc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins' (Ioc a b) (Ioo b c) := ⟨ join_Ioc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a < c by grind] ⟩

theorem BoundedInterval.join_Ico_Icc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Ico a b) (Icc b c) := ⟨ join_Ico_Icc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ico_Ico' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins' (Ico a b) (Ico b c) := ⟨ join_Ico_Ico hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Icc' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioo a b) (Icc b c) := ⟨ join_Ioo_Icc hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Ico' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins' (Ioo a b) (Ico b c) := ⟨ join_Ioo_Ico hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a < c by grind] ⟩

/-- A bounded interval whose carrier is a single point `{a}` must be `Icc a a`: the half-open and
open shapes cannot be nonempty singletons. -/
theorem BoundedInterval.eq_Icc_of_eq_singleton {K : BoundedInterval} {a : ℝ}
    (hK : (K:Set ℝ) = {a}) : K = Icc a a := by
  rcases K with ⟨c,d⟩|⟨c,d⟩|⟨c,d⟩|⟨c,d⟩
  · rw [show ((Ioo c d:BoundedInterval):Set ℝ) = Set.Ioo c d from rfl,
        Set.eq_singleton_iff_unique_mem] at hK
    obtain ⟨⟨hlt1, hlt2⟩, huniq⟩ := hK
    have := huniq ((c + a)/2) ⟨by linarith, by linarith⟩
    linarith
  · simp at hK; obtain ⟨rfl, rfl⟩ := hK; rfl
  · rw [show ((Ioc c d:BoundedInterval):Set ℝ) = Set.Ioc c d from rfl,
        Set.eq_singleton_iff_unique_mem] at hK
    obtain ⟨⟨hlt1, hle2⟩, huniq⟩ := hK
    have := huniq ((c + a)/2) ⟨by linarith, by linarith⟩
    linarith
  · rw [show ((Ico c d:BoundedInterval):Set ℝ) = Set.Ico c d from rfl,
        Set.eq_singleton_iff_unique_mem] at hK
    obtain ⟨⟨hle1, hlt2⟩, huniq⟩ := hK
    have := huniq ((a + d)/2) ⟨by linarith, by linarith⟩
    linarith

/-- Theorem 11.8.4 / Exercise 11.8.1 -/
theorem Partition.sum_of_α_length  {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  -- Mirrors `Partition.sum_of_length`, but carries the `α`-additivity of a join via
  -- `BoundedInterval.joins'`. The subsingleton base case differs: a one-point interval has
  -- `α`-length `jump α a`, not `0`, so it cannot be handled by "everything is zero".
  generalize hcard: P.intervals.card = n
  induction' n with n hn generalizing I
  . rw [Finset.card_eq_zero] at hcard
    have hIe : (I:Set ℝ) = ∅ := by
      have := P.exists_unique
      by_contra h
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
      obtain ⟨J, ⟨hJP, _⟩, _⟩ := this x hx
      rw [hcard] at hJP
      exact Finset.notMem_empty _ hJP
    rw [hcard, Finset.sum_empty, α_length_of_empty α hIe]
  by_cases h : Subsingleton (I:Set ℝ)
  . have hsub (J: BoundedInterval) (hJ: J ∈ P.intervals) : Subsingleton (J:Set ℝ) := by
      have hJI : J ⊆ I := P.contains _ hJ
      rw [subset_iff] at hJI
      rw [Set.subsingleton_coe] at h ⊢
      exact Set.Subsingleton.anti h hJI
    by_cases hIe : (I:Set ℝ) = ∅
    . rw [α_length_of_empty α hIe]
      apply Finset.sum_eq_zero
      intro J hJ
      apply α_length_of_empty
      have hJI : (J:Set ℝ) ⊆ (I:Set ℝ) := P.contains _ hJ
      rw [hIe] at hJI
      exact Set.subset_eq_empty hJI rfl
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hIe
    have hIa : (I:Set ℝ) = {a} := ((Set.subsingleton_coe _).mp h).eq_singleton_of_mem ha
    obtain ⟨J₀, ⟨hJ₀P, hJ₀a⟩, hJ₀uniq⟩ := P.exists_unique a ha
    rw [Finset.sum_eq_single_of_mem J₀ hJ₀P]
    · have hJ₀carrier : (J₀:Set ℝ) = {a} :=
        ((Set.subsingleton_coe _).mp (hsub J₀ hJ₀P)).eq_singleton_of_mem hJ₀a
      rw [BoundedInterval.eq_Icc_of_eq_singleton hJ₀carrier,
          BoundedInterval.eq_Icc_of_eq_singleton hIa]
    · intro J hJ hne
      apply α_length_of_empty
      have hJI : (J:Set ℝ) ⊆ {a} := by rw [←hIa]; exact P.contains _ hJ
      have hanJ : a ∉ (J:Set ℝ) := by
        intro haJ
        exact hne (hJ₀uniq J ⟨hJ, haJ⟩)
      rcases Set.subset_singleton_iff_eq.mp hJI with he | he
      · exact he
      · exact absurd (he ▸ Set.mem_singleton a) hanJ
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins' L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := BoundedInterval.eq_Icc_of_eq_singleton hbK
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc' <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc' <;> order
        | Ico _ _ => simp at hI'
      simp [length_of_subsingleton, -Set.subsingleton_coe] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]; split_ands
        . apply csSup_le_csSup bddAbove_Icc (by simp [hsub]) at hKI'
          simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
        have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
      have hKA : I.a ≤ K.a := by
        apply csInf_le_csInf bddBelow_Icc (by simp [hsub]) at hKI'
        simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
      cases I with
      | Ioo _ _ => simp [mem_iff] at hI'
      | Icc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp [mem_iff, subset_iff] at *; grind
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc' <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc' <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc']
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc' <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo' <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      grind [join_Ioo_Ico']
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo']
      use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico']
  obtain ⟨ K, L, hK, ⟨ h1, h2, _ ⟩, hα ⟩ := this
  have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    use {
      intervals := P.intervals.erase K
      exists_unique x hx := by
        obtain ⟨M, hM, hM'⟩ := P.exists_unique x (by
          rw [mem_iff, h2]; exact Or.inl hx)
        use M
        constructor
        . constructor
          . rw [Finset.mem_erase]
            refine ⟨?_, hM.1⟩
            intro hMK
            have : x ∈ ((L:Set ℝ) ∩ (K:Set ℝ)) :=
              ⟨hx, hMK ▸ hM.2⟩
            rw [h1] at this
            exact this
          . exact hM.2
        . intro J hJ
          simp at hM'
          specialize hM' J (by grind) hJ.2
          exact hM'
      contains J hJ := by
        rw [Finset.mem_erase] at hJ
        obtain ⟨hJK, hJP⟩ := hJ
        rw [subset_iff]
        intro x hxJ
        have hxI : x ∈ I := (J.subset_iff _).mp (P.contains _ hJP) hxJ
        rw [mem_iff, h2] at hxI
        rcases hxI with hxL | hxK
        · exact hxL
        · exfalso
          have hxI' : x ∈ I := by rw [mem_iff, h2]; exact Or.inr hxK
          obtain ⟨M, _, hMuniq⟩ := P.exists_unique x hxI'
          have hJM : J = M := hMuniq J ⟨hJP, hxJ⟩
          have hKM : K = M := hMuniq K ⟨hK, hxK⟩
          exact hJK (hJM.trans hKM.symm)
    }
  choose P' hP' using this
  rw [hα α, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
  apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.8.5 (Piecewise constant RS integral)-/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ

/-- Example 11.8.6 -/
noncomputable abbrev f_11_8_6 (x:ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥: Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

theorem P_11_8_6_eq : P_11_8_6.intervals = { Ico 1 2, Icc 2 3 } := by simp

theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x^2) = 22 := by
  rw [PiecewiseConstantWith.RS_integ, P_11_8_6_eq, Finset.sum_pair (by simp)]
  have h1: constant_value_on f_11_8_6 (Ico 1 2) = 4 := by
    apply ConstantOn.const_eq ⟨1, by simp⟩
    intro x hx; simp [f_11_8_6] at hx ⊢; exact hx.2
  have h2: constant_value_on f_11_8_6 (Icc 2 3) = 2 := by
    apply ConstantOn.const_eq ⟨2, by norm_num⟩
    intro x hx; simp [f_11_8_6] at hx ⊢; linarith [hx.1]
  have e1: (fun x ↦ x^2)[Ico 1 2]ₗ = 3 := by
    rw [α_length_of_cts (I:=Ico 1 2) (a:=0) (b:=3)]
    · grind
    · grind
    · grind
    · grind
    · simp [BoundedInterval.subset_iff]; grind
    · exact continuousOn_pow 2
  have e2: (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
    rw [α_length_of_cts (I:=Icc 2 3) (a:=1) (b:=4)]
    · grind
    · grind
    · grind
    · grind
    · simp [BoundedInterval.subset_iff]; grind
    · exact continuousOn_pow 2
  rw [h1, h2, e1, e2]
  norm_num

/-- Example 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f:ℝ → ℝ} {I: BoundedInterval} (P: Partition I) :RS_integ f P (fun x ↦ x) = integ f P := by
  simp [RS_integ, integ]

/-- Unlike {name}`BoundedInterval.length_eq_set` (where the length only depends on `sup - inf`),
`α_length` also depends on which endpoints are included. Equal carriers still force equal
`α_length`, because a nonempty carrier determines its infimum, supremum, *and* whether each
endpoint belongs — hence the bracket type. -/
theorem α_length_eq_set {α: ℝ → ℝ} {I J: BoundedInterval} (h: (I:Set ℝ) = (J:Set ℝ)) :
    α[I]ₗ = α[J]ₗ := by
  classical
  rcases eq_or_ne (I:Set ℝ) ∅ with hempty | hne
  · rw [α_length_of_empty α hempty, α_length_of_empty α (h ▸ hempty)]
  by_cases hsub : Subsingleton (I:Set ℝ)
  · obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hIa : (I:Set ℝ) = {a} := ((Set.subsingleton_coe _).mp hsub).eq_singleton_of_mem ha
    have hJa : (J:Set ℝ) = {a} := h ▸ hIa
    rw [BoundedInterval.eq_Icc_of_eq_singleton hIa,
        BoundedInterval.eq_Icc_of_eq_singleton hJa]
  · have hsubJ : ¬ Subsingleton (J:Set ℝ) := by
      rw [Set.subsingleton_coe] at hsub ⊢; rw [← h]; exact hsub
    have hI : I.a < I.b := by
      rw [Set.subsingleton_coe] at hsub
      by_contra hba; push_neg at hba; apply hsub
      cases I with
      | Ioo _ _ => simp [Set.Ioo_eq_empty (not_lt.mpr hba)] at *
      | Ioc _ _ => simp [Set.Ioc_eq_empty (not_lt.mpr hba)] at *
      | Ico _ _ => simp [Set.Ico_eq_empty (not_lt.mpr hba)] at *
      | Icc x y => simp [a, b] at hba; intro u hu v hv; simp at hu hv; linarith
    have hJ : J.a < J.b := by
      rw [Set.subsingleton_coe] at hsubJ
      by_contra hba; push_neg at hba; apply hsubJ
      cases J with
      | Ioo _ _ => simp [a, b, Set.Ioo_eq_empty (not_lt.mpr hba)] at *
      | Ioc _ _ => simp [a, b, Set.Ioc_eq_empty (not_lt.mpr hba)] at *
      | Ico _ _ => simp [a, b, Set.Ico_eq_empty (not_lt.mpr hba)] at *
      | Icc x y => simp [a, b] at hba; intro u hu v hv; simp at hu hv; linarith
    have hSupI : sSup (I:Set ℝ) = I.b := by
      cases I with
      | Ioo a b => simp [csSup_Ioo hI]
      | Icc a b => simp [csSup_Icc hI.le]
      | Ioc a b => simp [csSup_Ioc hI]
      | Ico a b => simp [csSup_Ico hI]
    have hInfI : sInf (I:Set ℝ) = I.a := by
      cases I with
      | Ioo a b => simp [csInf_Ioo hI]
      | Icc a b => simp [csInf_Icc hI.le]
      | Ioc a b => simp [csInf_Ioc hI]
      | Ico a b => simp [csInf_Ico hI]
    have hSupJ : sSup (J:Set ℝ) = J.b := by
      cases J with
      | Ioo a b => simp [csSup_Ioo hJ]
      | Icc a b => simp [csSup_Icc hJ.le]
      | Ioc a b => simp [csSup_Ioc hJ]
      | Ico a b => simp [csSup_Ico hJ]
    have hInfJ : sInf (J:Set ℝ) = J.a := by
      cases J with
      | Ioo a b => simp [csInf_Ioo hJ]
      | Icc a b => simp [csInf_Icc hJ.le]
      | Ioc a b => simp [csInf_Ioc hJ]
      | Ico a b => simp [csInf_Ico hJ]
    have hab : I.a = J.a := by rw [← hInfI, ← hInfJ, h]
    have hbb : I.b = J.b := by rw [← hSupI, ← hSupJ, h]
    have formula : ∀ K : BoundedInterval, K.a < K.b →
        α[K]ₗ = (if K.b ∈ (K:Set ℝ) then right_lim α K.b else left_lim α K.b)
              - (if K.a ∈ (K:Set ℝ) then left_lim α K.a else right_lim α K.a) := by
      intro K hK
      cases K with
      | Ioo a b => simp [α_length, BoundedInterval.set_Ioo, Set.mem_Ioo, hK]
      | Icc a b => simp [α_length, BoundedInterval.set_Icc, Set.mem_Icc, hK.le]
      | Ioc a b => simp [α_length, BoundedInterval.set_Ioc, Set.mem_Ioc, hK, hK.le]
      | Ico a b => simp [α_length, BoundedInterval.set_Ico, Set.mem_Ico, hK, hK.le]
    rw [formula I hI, formula J hJ, hab, hbb]
    have ea : (J.a ∈ (I:Set ℝ)) ↔ (J.a ∈ (J:Set ℝ)) := by rw [h]
    have eb : (J.b ∈ (I:Set ℝ)) ↔ (J.b ∈ (J:Set ℝ)) := by rw [h]
    simp only [ea, eb]

/-- Analogue of {name}`Partition.length_restrict_inter`. -/
theorem Partition.α_length_restrict_inter {I:BoundedInterval} (Q: Partition I)
    (J: BoundedInterval) (hJ: J ⊆ I) (α:ℝ → ℝ) :
    ∑ K ∈ Q.intervals, α[(J ∩ K : BoundedInterval)]ₗ = α[J]ₗ := by
  rw [← Partition.sum_of_α_length (Q.restrict_inter J hJ) α]
  refine (Finset.sum_image_of_pairwise_eq_zero (g := fun L : BoundedInterval ↦ α[L]ₗ) ?_).symm
  intro K₁ hK₁ K₂ hK₂ hne heq
  show α[(J ∩ K₁ : BoundedInterval)]ₗ = 0
  apply α_length_of_empty
  by_contra hne_empty
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne_empty
  rw [BoundedInterval.inter_eq] at hx
  have hx2 : x ∈ ((J ∩ K₂ : BoundedInterval):Set ℝ) := heq ▸ by rw [BoundedInterval.inter_eq]; exact hx
  rw [BoundedInterval.inter_eq] at hx2
  exact hne (Partition.eq_of_mem hK₁ hK₂ hx.2 hx2.2)

/-- Analogue of {name}`PiecewiseConstantWith.integ_max_eq_double_sum`. -/
theorem PiecewiseConstantWith.RS_integ_max_eq_double_sum {f:ℝ → ℝ} {I: BoundedInterval}
    (P P': Partition I) (α:ℝ → ℝ) :
    RS_integ f (max P P') α = ∑ J ∈ P.intervals, ∑ K ∈ P'.intervals,
      constant_value_on f ((J ∩ K : BoundedInterval):Set ℝ) * α[(J ∩ K : BoundedInterval)]ₗ := by
  classical
  have h_max_intervals : (max P P').intervals =
      Finset.image (Function.uncurry fun J K ↦ (J ∩ K : BoundedInterval))
        (P.intervals ×ˢ P'.intervals) := by
    show Finset.image₂ _ _ _ = _
    rw [← Finset.image_uncurry_product]
  rw [show RS_integ f (max P P') α = ∑ L ∈ (max P P').intervals,
        constant_value_on f (L:Set ℝ) * α[L]ₗ from rfl, h_max_intervals]
  rw [Finset.sum_image_of_pairwise_eq_zero
    (g := fun L : BoundedInterval ↦ constant_value_on f (L:Set ℝ) * α[L]ₗ)
    (I := P.intervals ×ˢ P'.intervals)
    (f := Function.uncurry fun J K ↦ (J ∩ K : BoundedInterval))]
  swap
  · intro p₁ hp₁ p₂ hp₂ hne heq
    simp [Function.uncurry] at heq
    show constant_value_on f ((p₁.1 ∩ p₁.2 : BoundedInterval):Set ℝ)
      * α[(p₁.1 ∩ p₁.2 : BoundedInterval)]ₗ = 0
    suffices h : α[(p₁.1 ∩ p₁.2 : BoundedInterval)]ₗ = 0 by rw [h]; ring
    simp at hp₁ hp₂
    exact α_length_of_empty α (Partition.inter_empty_of_dup hp₁.1 hp₁.2 hp₂.1 hp₂.2 hne (by rw [heq]))
  rw [Finset.sum_product]
  rfl

/-- Analogue of {name}`PiecewiseConstantWith.integ_max`. -/
theorem PiecewiseConstantWith.RS_integ_max {f:ℝ → ℝ} {I: BoundedInterval} (P P': Partition I)
  (hP: PiecewiseConstantWith f P) (α:ℝ → ℝ): RS_integ f P α = RS_integ f (max P P') α := by
  rw [RS_integ_max_eq_double_sum P P']
  rw [show RS_integ f P α = ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ from rfl]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJsub : J ⊆ I := P.contains _ hJ
  have hconst : ConstantOn f (J:Set ℝ) := hP J hJ
  have heach : ∀ K ∈ P'.intervals,
      constant_value_on f ((J ∩ K : BoundedInterval):Set ℝ) * α[(J ∩ K : BoundedInterval)]ₗ
        = constant_value_on f (J:Set ℝ) * α[(J ∩ K : BoundedInterval)]ₗ := by
    intro K _
    by_cases hempty : ((J ∩ K : BoundedInterval):Set ℝ) = ∅
    · rw [α_length_of_empty α hempty]; ring
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      rw [BoundedInterval.inter_eq] at hx
      have hcv : constant_value_on f ((J ∩ K : BoundedInterval):Set ℝ) = constant_value_on f (J:Set ℝ) := by
        apply ConstantOn.const_eq (X := ((J ∩ K : BoundedInterval):Set ℝ))
          ⟨x, by rw [BoundedInterval.inter_eq]; exact hx⟩
        intro y hy
        rw [BoundedInterval.inter_eq] at hy
        exact hconst.eq hy.1
      rw [hcv]
  rw [Finset.sum_congr rfl heach, ← Finset.mul_sum,
      Partition.α_length_restrict_inter P' J hJsub]

/-- Analogue of {name}`PiecewiseConstantWith.integ_max_comm`; uses {name}`α_length_eq_set` to match
the two double sums termwise (`J ∩ K` and `K ∩ J` have equal carriers). -/
theorem PiecewiseConstantWith.RS_integ_max_comm {f:ℝ → ℝ} {I: BoundedInterval} (P P': Partition I)
    (α:ℝ → ℝ) : RS_integ f (max P P') α = RS_integ f (max P' P) α := by
  rw [RS_integ_max_eq_double_sum P P', RS_integ_max_eq_double_sum P' P, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro J _
  apply Finset.sum_congr rfl; intro K _
  have hset : ((J ∩ K : BoundedInterval):Set ℝ) = ((K ∩ J : BoundedInterval):Set ℝ) := by
    rw [BoundedInterval.inter_eq, BoundedInterval.inter_eq, Set.inter_comm]
  rw [hset, α_length_eq_set (α := α) hset]

/-- Analogue of Proposition 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') (α:ℝ → ℝ): RS_integ f P α = RS_integ f P' α := by
  rw [RS_integ_max P P' hP, RS_integ_max_comm, ← RS_integ_max P' P hP']

open Classical in
noncomputable abbrev PiecewiseConstantOn.RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ):
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.RS_integ f h.choose α else 0

theorem PiecewiseConstantOn.RS_integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) (α:ℝ → ℝ) : RS_integ f I α = PiecewiseConstantWith.RS_integ f P α := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [RS_integ, h']; exact PiecewiseConstantWith.RS_integ_eq h'.choose_spec h α

/-- {name}`α_length` non-negative when α monotone -/
theorem α_length_nonneg_of_monotone {α:ℝ → ℝ}  (hα: Monotone α) (I: BoundedInterval):
  0 ≤ α[I]ₗ := by
  have hjump (x:ℝ) : left_lim α x ≤ right_lim α x := by
    have : (0:ℝ) ≤ right_lim α x - left_lim α x := jump_of_monotone x hα
    linarith
  have hcross (a b : ℝ) (hab : a < b) : right_lim α a ≤ left_lim α b :=
    right_lim_le_left_lim_of_monotone hab hα
  cases I with
  | Icc a b =>
    simp only [α_length]
    by_cases hab : a ≤ b
    · rcases eq_or_lt_of_le hab with rfl | hlt
      · simp; linarith [hjump a]
      · simp only [hab, if_true]; linarith [hjump a, hjump b, hcross a b hlt]
    · simp [hab]
  | Ico a b =>
    simp only [α_length]
    by_cases hab : a ≤ b
    · rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · simp only [hab, if_true]; linarith [hjump a, hcross a b hlt]
    · simp [hab]
  | Ioc a b =>
    simp only [α_length]
    by_cases hab : a ≤ b
    · rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      · simp only [hab, if_true]; linarith [hjump b, hcross a b hlt]
    · simp [hab]
  | Ioo a b =>
    simp only [α_length]
    by_cases hab : a < b
    · simp only [hab, if_true]; linarith [hcross a b hab]
    · simp [hab]

/-- Analogue of Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) {α:ℝ → ℝ} (_: Monotone α):
  RS_integ (f + g) I α = RS_integ f I α + RS_integ g I α := by
  obtain ⟨P, hPf, hPg⟩ := exists_common hf hg
  have hPfg : PiecewiseConstantWith (f + g) P :=
    PiecewiseConstantWith.binop (· + ·) (fun _ ↦ rfl) hPf hPg
  rw [RS_integ_def hPfg α, RS_integ_def hPf α, RS_integ_def hPg α]
  simp only [PiecewiseConstantWith.RS_integ, ← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  obtain ⟨cf, hcf⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
  obtain ⟨cg, hcg⟩ := (PiecewiseConstantWith.def g).mp hPg J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hJne hcf, ConstantOn.const_eq hJne hcg,
        ConstantOn.const_eq hJne (c := cf + cg) (fun x hx ↦ by simp [hcf x hx, hcg x hx])]
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; ring

/-- If `f` vanishes on `F`, its contribution to a piecewise constant RS integral is zero.
Analogue of {name}`constant_value_on_zero_mul_length`. -/
lemma constant_value_on_zero_mul_α_length {f : ℝ → ℝ} {F : BoundedInterval} {α:ℝ → ℝ}
    (hf : ∀ x ∈ (F : Set ℝ), f x = 0) :
    constant_value_on f (F : Set ℝ) * α[F]ₗ = 0 := by
  by_cases hFne : (F : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hFne hf]; ring
  · rw [Set.not_nonempty_iff_eq_empty] at hFne
    rw [α_length_of_empty α hFne]; ring

/-- Analogue of {name}`PiecewiseConstantWith.integ_congr`. -/
theorem PiecewiseConstantWith.RS_integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (α:ℝ → ℝ) (h: ∀ x ∈ (I:Set ℝ), f x = g x) : RS_integ f P α = RS_integ g P α := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Analogue of {name}`PiecewiseConstantOn.integ_congr`. -/
theorem PiecewiseConstantOn.RS_integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} (α:ℝ → ℝ)
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : RS_integ f I α = RS_integ g I α := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [RS_integ, hf, hg])
  rw [PiecewiseConstantWith.RS_integ_congr α h, ←RS_integ_def hg.choose_spec, ←RS_integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Analogue of Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ)
  (hf: PiecewiseConstantOn f I) {α:ℝ → ℝ} (_: Monotone α) :
  RS_integ (c • f) I α = c * RS_integ f I α
   := by
  obtain ⟨P, hPf⟩ := hf
  have hPcf : PiecewiseConstantWith (c • f) P := by
    intro J hJ
    obtain ⟨k, hk⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
    exact ConstantOn.of_const (c := c * k) (fun x hx ↦ by simp [hk x hx])
  rw [RS_integ_def hPcf α, RS_integ_def hPf α]
  simp only [PiecewiseConstantWith.RS_integ, Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro J hJ
  obtain ⟨k, hk⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hJne hk,
        ConstantOn.const_eq hJne (c := c * k) (fun x hx ↦ by simp [hk x hx])]
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; ring

/-- Theorem 11.8.8 (c) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (_: Monotone α)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ (f - g) I α = RS_integ f I α - RS_integ g I α := by
  obtain ⟨P, hPf, hPg⟩ := exists_common hf hg
  have hPfg : PiecewiseConstantWith (f - g) P :=
    PiecewiseConstantWith.binop (· - ·) (fun _ ↦ rfl) hPf hPg
  rw [RS_integ_def hPfg α, RS_integ_def hPf α, RS_integ_def hPg α]
  simp only [PiecewiseConstantWith.RS_integ, ← Finset.sum_sub_distrib, ← sub_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  obtain ⟨cf, hcf⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
  obtain ⟨cg, hcg⟩ := (PiecewiseConstantWith.def g).mp hPg J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hJne hcf, ConstantOn.const_eq hJne hcg,
        ConstantOn.const_eq hJne (c := cf - cg) (fun x hx ↦ by simp [hcf x hx, hcg x hx])]
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne]; ring

/-- Theorem 11.8.8 (d) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, 0 ≤ f x) (hf: PiecewiseConstantOn f I) :
  0 ≤ RS_integ f I α := by
  obtain ⟨P, hP⟩ := hf
  rw [RS_integ_def hP α]
  apply Finset.sum_nonneg
  intro J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · obtain ⟨x, hx⟩ := hJne
    have hxI : x ∈ I := P.contains _ hJ x (by rwa [← mem_iff] at hx)
    have hcv : constant_value_on f (J:Set ℝ) = f x := by rw [← (hP J hJ).eq hx]
    rw [hcv]
    exact mul_nonneg (h x hxI) (α_length_nonneg_of_monotone hα J)
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [α_length_of_empty α hJne, mul_zero]

/-- Theorem 11.8.8 (e) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, f x ≤ g x) (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ f I α ≤ RS_integ g I α := by
  have hgf : 0 ≤ RS_integ (g - f) I α :=
    RS_integ_of_nonneg hα (fun x hx ↦ by simp [sub_nonneg, h x hx]) (sub hg hf)
  rw [RS_integ_sub hα hg hf] at hgf
  linarith

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_const (c: ℝ) (I: BoundedInterval) {α:ℝ → ℝ} (_: Monotone α) :
  RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  have hP : PiecewiseConstantWith (fun _ : ℝ ↦ c) (⊥ : Partition I) := by
    intro J hJ
    rw [Partition.mem_intervals_iff, Partition.intervals_of_bot, Finset.mem_singleton] at hJ
    subst hJ
    exact ConstantOn.of_const' c _
  rw [RS_integ_def hP α]
  simp only [PiecewiseConstantWith.RS_integ, Partition.intervals_of_bot, Finset.sum_singleton]
  by_cases hI : (I : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hI (c := c) (fun _ _ ↦ rfl)]
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    rw [α_length_of_empty α hI, mul_zero, mul_zero]

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_const' {f:ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α) (h: ConstantOn f I) :
  RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  by_cases hI : (I : Set ℝ).Nonempty
  · set c := constant_value_on f (I:Set ℝ) with hc_def
    rw [RS_integ_congr α (g := fun _ ↦ c) (fun x hx ↦ h.eq hx), RS_integ_const _ _ hα]
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    rw [α_length_of_empty α hI, mul_zero]
    rw [RS_integ_congr α (g := fun _ ↦ (0:ℝ))
          (fun x hx ↦ by rw [hI] at hx; exact hx.elim),
        RS_integ_const _ _ hα, zero_mul]

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (_: Monotone α):
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J :=
  PiecewiseConstantOn.of_extend hIJ h

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = RS_integ f I α := by
  by_cases hI : (I : Set ℝ).Nonempty
  · obtain ⟨P, hP⟩ := h
    rw [RS_integ_def (hP.extend hIJ hI) α, RS_integ_def hP α]
    change ∑ K ∈ P.intervals ∪ {leftFlank J I, rightFlank J I}, _ = _
    rw [← Finset.sum_subset Finset.subset_union_left (fun K hKQ hKP => ?_)]
    · refine Finset.sum_congr rfl (fun K hK => ?_)
      congr 1
      refine constant_value_on_congr (fun x hx => ?_)
      have hxI : x ∈ I :=
        (mem_iff _ _).mpr ((subset_iff _ _).mp (P.contains K hK) hx)
      simp [hxI]
    · simp at hKQ
      rcases hKQ with rfl | rfl | hKP'
      · exact constant_value_on_zero_mul_α_length
          (fun x hx => by simp [leftFlank_notMem x hx])
      · exact constant_value_on_zero_mul_α_length
          (fun x hx => by simp [rightFlank_notMem x hx])
      · exact absurd hKP' hKP
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    have hf : ConstantOn f (I : Set ℝ) := hI ▸ ConstantOn.of_subsingleton
    have hxnI : ∀ x, x ∉ I := by intro x h; rw [mem_iff, hI] at h; exact h
    rw [RS_integ_congr α (g := fun _ => (0:ℝ)) (fun x _ => by simp [hxnI x]),
        RS_integ_const _ _ hα, RS_integ_const' hα hf, α_length_of_empty α hI]
    ring

/-- Theorem 11.8.8 (h) (Laws of RS integration) / Exercise 11.8.8 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K: BoundedInterval} (hIJK: K.joins' I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) {α:ℝ → ℝ} (_: Monotone α):
  RS_integ f K α = RS_integ f I α + RS_integ f J α := by
  obtain ⟨⟨PI, hPI⟩, ⟨PJ, hPJ⟩⟩ := (of_join hIJK.1 f).mp h
  have hJoined : PiecewiseConstantWith f (PI.join PJ hIJK.1) := by
    intro L hL
    rw [Partition.mem_intervals_iff, Partition.intervals_of_join,
        Finset.mem_union] at hL
    rcases hL with hLI | hLJ
    · exact hPI L hLI
    · exact hPJ L hLJ
  rw [RS_integ_def hJoined α, RS_integ_def hPI α, RS_integ_def hPJ α]
  show ∑ L ∈ (PI.join PJ hIJK.1).intervals, _ = _
  rw [Partition.intervals_of_join]
  have h_inter_zero : ∀ L ∈ PI.intervals ∩ PJ.intervals,
      constant_value_on f (L : Set ℝ) * α[L]ₗ = 0 := fun L hL => by
    rw [Finset.mem_inter] at hL
    have hLempty : (L : Set ℝ) = ∅ := Set.eq_empty_of_subset_empty
      (hIJK.1.1 ▸ Set.subset_inter
        ((subset_iff _ _).mp (PI.contains L hL.1))
        ((subset_iff _ _).mp (PJ.contains L hL.2)))
    rw [α_length_of_empty α hLempty]; ring
  have hu := @Finset.sum_union_inter _ _ PI.intervals PJ.intervals _
    (fun L => constant_value_on f (L : Set ℝ) * α[L]ₗ) _
  rw [Finset.sum_eq_zero h_inter_zero, add_zero] at hu
  exact hu

/-- Analogue of Definition 11.3.2 (Uppper and lower Riemann integrals )-/
noncomputable abbrev upper_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sInf ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sSup ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

lemma RS_integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ M, ⟨ ⟨ ?_, ?_ ⟩, PiecewiseConstantOn.RS_integ_const M I hα ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : -M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ -M, ⟨ ⟨ ?_, ?_ ⟩, by convert PiecewiseConstantOn.RS_integ_const _ _ hα using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_upper_of_bounded h hα)

lemma RS_integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_lower_of_bounded h hα)

lemma RS_integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  {α:ℝ → ℝ} (hα: Monotone α)
  (ha: a ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    have ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    have ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]; apply hhp.RS_integ_mono hα _ hgp; intro _ hx; linarith [hmin _ hx, hmaj _ hx]

lemma RS_integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  BddBelow ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (RS_integral_bound_lower_nonempty h hα).some
    intro a ha; exact RS_integral_bound_lower_le_upper hα ha (RS_integral_bound_lower_nonempty h hα).some_mem

lemma RS_integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α):
  BddAbove ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (RS_integral_bound_upper_nonempty h hα).some
    intro b hb; exact RS_integral_bound_lower_le_upper hα (RS_integral_bound_upper_nonempty h hα).some_mem hb

lemma le_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  -M * α[I]ₗ ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above (BddOn.of_bounded h) hα) (RS_integral_bound_lower_of_bounded h hα)

lemma lower_RS_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  lower_RS_integral f I α ≤ upper_RS_integral f I α := by
  apply csSup_le (RS_integral_bound_lower_nonempty h hα)
  intros
  apply le_csInf (RS_integral_bound_upper_nonempty h hα)
  intros; solve_by_elim [RS_integral_bound_lower_le_upper]

lemma RS_upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ M * α[I]ₗ :=
  csInf_le (RS_integral_bound_below (.of_bounded h) hα) (RS_integral_bound_upper_of_bounded h hα)

lemma upper_RS_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
  csInf_le (RS_integral_bound_below hf hα) ⟨ g, by simpa [hg] ⟩

lemma integ_le_lower_RS_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above hf hα) ⟨ h, by simpa [hg] ⟩

lemma lt_of_gt_upper_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α: ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: upper_RS_integral f I α < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_csInf_lt (RS_integral_bound_upper_nonempty hf hα) hX
  simp at hY; have ⟨ g, ⟨ hmaj, hgp ⟩, hgi ⟩ := hY; exact ⟨ g, hmaj, hgp, by rwa [hgi] ⟩

lemma gt_of_lt_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: X < lower_RS_integral f I α) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_lt_csSup (RS_integral_bound_lower_nonempty hf hα) hX
  simp at hY; have ⟨ h, ⟨ hmin, hhp ⟩, hhi ⟩ := hY; exact ⟨ h, hmin, hhp, by rwa [hhi] ⟩

/-- Analogue of Definition 11.3.4 -/
noncomputable abbrev RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ) : ℝ := upper_RS_integral f I α

noncomputable abbrev RS_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ) : Prop :=
  BddOn f I ∧ lower_RS_integral f I α = upper_RS_integral f I α

/-- With `α = id`, the piecewise constant RS integral is the ordinary one. -/
theorem PiecewiseConstantOn.RS_integ_eq_integ (g:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ g I (fun x ↦ x) = integ g I := by
  by_cases hg : PiecewiseConstantOn g I
  · rw [RS_integ_def hg.choose_spec, integ_def hg.choose_spec]
    exact PiecewiseConstantWith.RS_integ_eq_integ _
  · simp [RS_integ, integ, hg]

/-- Analogue of various components of Lemma 11.3.3 -/
theorem upper_RS_integral_eq_upper_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  upper_RS_integral f I (fun x ↦ x) = upper_integral f I := by
  rw [upper_RS_integral, upper_integral]
  congr 1
  exact Set.image_congr (fun g _ ↦ PiecewiseConstantOn.RS_integ_eq_integ g I)

theorem lower_RS_integral_eq_lower_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  rw [lower_RS_integral, lower_integral]
  congr 1
  exact Set.image_congr (fun g _ ↦ PiecewiseConstantOn.RS_integ_eq_integ g I)

theorem RS_integ_eq_integ (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ f I (fun x ↦ x) = integ f I := by
  rw [RS_integ, integ]
  exact upper_RS_integral_eq_upper_integral f I

theorem RS_IntegrableOn_iff_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  rw [RS_IntegrableOn, IntegrableOn]
  congr!
  . exact lower_RS_integral_eq_lower_integral f I
  . exact upper_RS_integral_eq_upper_integral f I

/-- Analogue of Definition 11.3.9 (Riemann sums), weighted by `α_length`. -/
noncomputable abbrev upper_RS_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α:ℝ → ℝ) : ℝ :=
  ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * α[J]ₗ

noncomputable abbrev lower_RS_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α:ℝ → ℝ) : ℝ :=
  ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * α[J]ₗ

/-- Analogue of Proposition 11.3.12. -/
theorem upper_RS_integ_le_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
    {α:ℝ → ℝ} (hα: Monotone α) (P: Partition I) :
    upper_RS_integral f I α ≤ upper_RS_riemann_sum f P α := by
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
  refine (upper_RS_integral_le_integ hf hf' hf'C hα).trans ?_
  show PiecewiseConstantOn.RS_integ f' I α ≤ ∑ J ∈ P.intervals, sSup (f '' (J:Set ℝ)) * α[J]ₗ
  rw [PiecewiseConstantOn.RS_integ_def hf'P]
  apply Finset.sum_le_sum
  intros J hJ
  rcases Set.eq_empty_or_nonempty (J:Set ℝ) with hJe | hJne
  · rw [α_length_of_empty α hJe, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right
      (ConstantOn.const_eq hJne (hf'_eq J hJ)).le (α_length_nonneg_of_monotone hα J)

/-- Analogue of Proposition 11.3.12 (lower bound). -/
theorem lower_RS_integ_ge_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
    {α:ℝ → ℝ} (hα: Monotone α) (P: Partition I) :
    lower_RS_riemann_sum f P α ≤ lower_RS_integral f I α := by
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
  refine le_trans ?_ (integ_le_lower_RS_integral hf hh' hh'C hα)
  show ∑ J ∈ P.intervals, sInf (f '' (J:Set ℝ)) * α[J]ₗ ≤ PiecewiseConstantOn.RS_integ h' I α
  rw [PiecewiseConstantOn.RS_integ_def hh'P]
  apply Finset.sum_le_sum
  intros J hJ
  rcases Set.eq_empty_or_nonempty (J:Set ℝ) with hJe | hJne
  · rw [α_length_of_empty α hJe, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right
      (ConstantOn.const_eq hJne (hh'_eq J hJ)).ge (α_length_nonneg_of_monotone hα J)

/-- Exercise 11.8.4 -/
theorem RS_integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I)
 {α:ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α := by
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨ hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  · haveI hsub : Subsingleton (I:Set ℝ) := length_of_subsingleton.mpr hsing
    have hfpc : PiecewiseConstantOn f I := ConstantOn.of_subsingleton.piecewiseConstantOn
    have h1 := upper_RS_integral_le_integ hfbound (fun x _ ↦ le_refl (f x)) hfpc hα
    have h2 := integ_le_lower_RS_integral hfbound (fun x _ ↦ le_refl (f x)) hfpc hα
    linarith [lower_RS_integral_le_upper hfbound hα]
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have main (ε:ℝ) (hε: ε > 0) :
      upper_RS_integral f I α - lower_RS_integral f I α ≤ ε * α[I]ₗ := by
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
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * α[J]ₗ := by
        have h1 := upper_RS_integ_le_upper_sum hfbound hα P
        have h2 := lower_RS_integ_ge_lower_sum hfbound hα P
        simp [sub_mul, upper_RS_riemann_sum, lower_RS_riemann_sum] at *
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε * α[J]ₗ := by
        apply Finset.sum_le_sum; intro J hJ
        apply mul_le_mul_of_nonneg_right _ (α_length_nonneg_of_monotone hα J)
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
      _ = ε * α[I]ₗ := by rw [← Finset.mul_sum, Partition.sum_of_α_length P α]
  have hαI : 0 ≤ α[I]ₗ := α_length_nonneg_of_monotone hα I
  rcases eq_or_lt_of_le hαI with hα0 | hαpos
  · have h1 := main 1 (by norm_num)
    rw [← hα0] at h1; simp at h1
    linarith [lower_RS_integral_le_upper hfbound hα]
  have lower_le_upper : 0 ≤ upper_RS_integral f I α - lower_RS_integral f I α := by
    linarith [lower_RS_integral_le_upper hfbound hα]
  obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
  · set ε := (upper_RS_integral f I α - lower_RS_integral f I α)/(2*α[I]ₗ) with hεdef
    have h2 : upper_RS_integral f I α - lower_RS_integral f I α
        ≤ (upper_RS_integral f I α - lower_RS_integral f I α)/2 := by
      convert main ε (div_pos h (by positivity)) using 1
      rw [hεdef]; field_simp
    linarith
  linarith

/-- Exercise 11.8.5 -/
theorem RS_integ_with_sign (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc (-1) 1)) :
    RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) Real.sign = 2 * f 0 := by
  have hmono : Monotone Real.sign := by
    intro a b hab; simp only [Real.sign]; split_ifs <;> first | rfl | (exfalso; linarith) | linarith
  have hucont : UniformContinuousOn f (Icc (-1:ℝ) 1) := UniformContinuousOn.of_continuousOn hf
  have hbdd : BddOn f (Icc (-1:ℝ) 1) := by
    rw [BddOn.iff']; exact hucont.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval _)
  refine ⟨ RS_integ_of_uniform_cts hucont hmono, ?_ ⟩
  -- left/right limits of `sign`
  have hr0 : right_lim Real.sign 0 = 1 := by
    rw [right_lim_of_monotone' 0 hmono]
    have : Real.sign '' Set.Ioi (0:ℝ) = {1} := by
      ext y; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_singleton_iff]
      exact ⟨fun ⟨x, hx, h⟩ ↦ h ▸ Real.sign_of_pos hx,
             fun h ↦ ⟨1, one_pos, by rw [h, Real.sign_one]⟩⟩
    rw [this, csInf_singleton]
  have hl0 : left_lim Real.sign 0 = -1 := by
    rw [left_lim_of_monotone' 0 hmono]
    have : Real.sign '' Set.Iio (0:ℝ) = {-1} := by
      ext y; simp only [Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨fun ⟨x, hx, h⟩ ↦ h ▸ Real.sign_of_neg hx,
             fun h ↦ ⟨-1, by norm_num, by rw [h]; exact Real.sign_of_neg (by norm_num)⟩⟩
    rw [this, csSup_singleton]
  have hlm1 : left_lim Real.sign (-1) = -1 := by
    rw [left_lim_of_monotone' (-1) hmono]
    have : Real.sign '' Set.Iio (-1:ℝ) = {-1} := by
      ext y; simp only [Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨fun ⟨x, hx, h⟩ ↦ h ▸ Real.sign_of_neg (by linarith),
             fun h ↦ ⟨-2, by norm_num, by rw [h]; exact Real.sign_of_neg (by norm_num)⟩⟩
    rw [this, csSup_singleton]
  have hr1 : right_lim Real.sign 1 = 1 := by
    rw [right_lim_of_monotone' 1 hmono]
    have : Real.sign '' Set.Ioi (1:ℝ) = {1} := by
      ext y; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_singleton_iff]
      exact ⟨fun ⟨x, hx, h⟩ ↦ h ▸ Real.sign_of_pos (by linarith),
             fun h ↦ ⟨2, by norm_num, by rw [h]; exact Real.sign_of_pos (by norm_num)⟩⟩
    rw [this, csInf_singleton]
  -- the only `sign`-length carrying mass is the point `{0}` (jump 2)
  have hLn : Real.sign[Ico (-1) 0]ₗ = 0 := by
    show (if (-1:ℝ) ≤ 0 then left_lim Real.sign 0 - left_lim Real.sign (-1) else 0) = 0
    rw [if_pos (by norm_num), hl0, hlm1]; norm_num
  have hL0 : Real.sign[Icc 0 0]ₗ = 2 := by
    show (if (0:ℝ) ≤ 0 then right_lim Real.sign 0 - left_lim Real.sign 0 else 0) = 2
    rw [if_pos (le_refl _), hr0, hl0]; norm_num
  have hLp : Real.sign[Ioc 0 1]ₗ = 0 := by
    show (if (0:ℝ) ≤ 1 then right_lim Real.sign 1 - right_lim Real.sign 0 else 0) = 0
    rw [if_pos (by norm_num), hr1, hr0]; norm_num
  -- the splitting partition [-1,0) ⊔ {0} ⊔ (0,1]
  have hj1 : (Icc (-1:ℝ) 0).joins' (Ico (-1) 0) (Icc 0 0) := join_Ico_Icc' (by norm_num) (by norm_num)
  have hj2 : (Icc (-1:ℝ) 1).joins' (Icc (-1) 0) (Ioc 0 1) := join_Icc_Ioc' (by norm_num) (by norm_num)
  -- any pc function equal to `f 0` at `0` integrates to `2 * f 0` against `sign`
  have key : ∀ (e : ℝ → ℝ),
      ConstantOn e ((Ico (-1:ℝ) 0 : BoundedInterval) : Set ℝ) →
      ConstantOn e ((Ioc (0:ℝ) 1 : BoundedInterval) : Set ℝ) → e 0 = f 0 →
      PiecewiseConstantOn e (Icc (-1) 1) ∧
        PiecewiseConstantOn.RS_integ e (Icc (-1) 1) Real.sign = 2 * f 0 := by
    intro e hen hep he0
    have hc0 : ConstantOn e ((Icc (0:ℝ) 0 : BoundedInterval) : Set ℝ) := by
      apply ConstantOn.of_const (c := f 0); intro x hx
      rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
      rw [show x = 0 from le_antisymm hx.2 hx.1, he0]
    have pcLeft : PiecewiseConstantOn e (Icc (-1) 0) :=
      (PiecewiseConstantOn.of_join hj1.1 e).mpr ⟨hen.piecewiseConstantOn, hc0.piecewiseConstantOn⟩
    have pcAll : PiecewiseConstantOn e (Icc (-1) 1) :=
      (PiecewiseConstantOn.of_join hj2.1 e).mpr ⟨pcLeft, hep.piecewiseConstantOn⟩
    refine ⟨pcAll, ?_⟩
    have hcv0 : constant_value_on e ((Icc (0:ℝ) 0 : BoundedInterval) : Set ℝ) = f 0 := by
      apply ConstantOn.const_eq (X := ((Icc (0:ℝ) 0 : BoundedInterval) : Set ℝ)) ⟨0, by simp⟩
      intro x hx
      rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
      rw [show x = 0 from le_antisymm hx.2 hx.1, he0]
    rw [PiecewiseConstantOn.RS_integ_of_join hj2 pcAll hmono,
        PiecewiseConstantOn.RS_integ_of_join hj1 pcLeft hmono,
        PiecewiseConstantOn.RS_integ_const' hmono hen,
        PiecewiseConstantOn.RS_integ_const' hmono hc0,
        PiecewiseConstantOn.RS_integ_const' hmono hep,
        hLn, hL0, hLp, hcv0]
    ring
  -- boundedness of `f` on the two halves
  have hsub_n : ((Icc (-1:ℝ) 0 : BoundedInterval) : Set ℝ) ⊆ ((Icc (-1:ℝ) 1 : BoundedInterval) : Set ℝ) := by
    rw [BoundedInterval.set_Icc, BoundedInterval.set_Icc]; exact Set.Icc_subset_Icc (le_refl _) (by norm_num)
  have hsub_p : ((Icc (0:ℝ) 1 : BoundedInterval) : Set ℝ) ⊆ ((Icc (-1:ℝ) 1 : BoundedInterval) : Set ℝ) := by
    rw [BoundedInterval.set_Icc, BoundedInterval.set_Icc]; exact Set.Icc_subset_Icc (by norm_num) (le_refl _)
  have hbA_n : BddAbove (f '' ((Icc (-1:ℝ) 0 : BoundedInterval) : Set ℝ)) :=
    isCompact_Icc.bddAbove_image (hf.mono hsub_n)
  have hbA_p : BddAbove (f '' ((Icc (0:ℝ) 1 : BoundedInterval) : Set ℝ)) :=
    isCompact_Icc.bddAbove_image (hf.mono hsub_p)
  have hbB_n : BddBelow (f '' ((Icc (-1:ℝ) 0 : BoundedInterval) : Set ℝ)) :=
    isCompact_Icc.bddBelow_image (hf.mono hsub_n)
  have hbB_p : BddBelow (f '' ((Icc (0:ℝ) 1 : BoundedInterval) : Set ℝ)) :=
    isCompact_Icc.bddBelow_image (hf.mono hsub_p)
  -- pc majorant: sup of `f` on each half, `f 0` at the jump
  set Mn := sSup (f '' ((Icc (-1:ℝ) 0 : BoundedInterval) : Set ℝ)) with hMn
  set Mp := sSup (f '' ((Icc (0:ℝ) 1 : BoundedInterval) : Set ℝ)) with hMp
  set g : ℝ → ℝ := fun x => if x < 0 then Mn else if 0 < x then Mp else f 0 with hgdef
  have hg_n : ∀ x, x < 0 → g x = Mn := by intro x hx; simp only [hgdef]; rw [if_pos hx]
  have hg_p : ∀ x, 0 < x → g x = Mp := by
    intro x hx; simp only [hgdef]; rw [if_neg (not_lt.mpr hx.le), if_pos hx]
  have hg_0 : g 0 = f 0 := by simp only [hgdef]; rw [if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
  have hg_cn : ConstantOn g ((Ico (-1:ℝ) 0 : BoundedInterval) : Set ℝ) :=
    ConstantOn.of_const (c := Mn) (fun x hx => by
      rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx; exact hg_n x hx.2)
  have hg_cp : ConstantOn g ((Ioc (0:ℝ) 1 : BoundedInterval) : Set ℝ) :=
    ConstantOn.of_const (c := Mp) (fun x hx => by
      rw [BoundedInterval.set_Ioc, Set.mem_Ioc] at hx; exact hg_p x hx.1)
  have hg_maj : MajorizesOn g f (Icc (-1) 1) := by
    intro x hx
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    rcases lt_trichotomy x 0 with hlt | heq | hgt
    · rw [hg_n x hlt]
      exact le_csSup hbA_n ⟨x, by rw [BoundedInterval.set_Icc, Set.mem_Icc]; exact ⟨hx.1, hlt.le⟩, rfl⟩
    · exact le_of_eq (by rw [heq, hg_0])
    · rw [hg_p x hgt]
      exact le_csSup hbA_p ⟨x, by rw [BoundedInterval.set_Icc, Set.mem_Icc]; exact ⟨hgt.le, hx.2⟩, rfl⟩
  -- pc minorant: inf of `f` on each half, `f 0` at the jump
  set mn := sInf (f '' ((Icc (-1:ℝ) 0 : BoundedInterval) : Set ℝ)) with hmn
  set mp := sInf (f '' ((Icc (0:ℝ) 1 : BoundedInterval) : Set ℝ)) with hmp
  set h : ℝ → ℝ := fun x => if x < 0 then mn else if 0 < x then mp else f 0 with hhdef
  have hh_n : ∀ x, x < 0 → h x = mn := by intro x hx; simp only [hhdef]; rw [if_pos hx]
  have hh_p : ∀ x, 0 < x → h x = mp := by
    intro x hx; simp only [hhdef]; rw [if_neg (not_lt.mpr hx.le), if_pos hx]
  have hh_0 : h 0 = f 0 := by simp only [hhdef]; rw [if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
  have hh_cn : ConstantOn h ((Ico (-1:ℝ) 0 : BoundedInterval) : Set ℝ) :=
    ConstantOn.of_const (c := mn) (fun x hx => by
      rw [BoundedInterval.set_Ico, Set.mem_Ico] at hx; exact hh_n x hx.2)
  have hh_cp : ConstantOn h ((Ioc (0:ℝ) 1 : BoundedInterval) : Set ℝ) :=
    ConstantOn.of_const (c := mp) (fun x hx => by
      rw [BoundedInterval.set_Ioc, Set.mem_Ioc] at hx; exact hh_p x hx.1)
  have hh_min : MinorizesOn h f (Icc (-1) 1) := by
    intro x hx
    rw [BoundedInterval.set_Icc, Set.mem_Icc] at hx
    rcases lt_trichotomy x 0 with hlt | heq | hgt
    · rw [hh_n x hlt]
      exact csInf_le hbB_n ⟨x, by rw [BoundedInterval.set_Icc, Set.mem_Icc]; exact ⟨hx.1, hlt.le⟩, rfl⟩
    · exact le_of_eq (by rw [heq, hh_0])
    · rw [hh_p x hgt]
      exact csInf_le hbB_p ⟨x, by rw [BoundedInterval.set_Icc, Set.mem_Icc]; exact ⟨hgt.le, hx.2⟩, rfl⟩
  -- squeeze: majorant and minorant both integrate to `2 * f 0`
  obtain ⟨hg_pc, hg_int⟩ := key g hg_cn hg_cp hg_0
  obtain ⟨hh_pc, hh_int⟩ := key h hh_cn hh_cp hh_0
  have hup : upper_RS_integral f (Icc (-1) 1) Real.sign ≤ 2 * f 0 := by
    rw [← hg_int]; exact upper_RS_integral_le_integ hbdd hg_maj hg_pc hmono
  have hlo : 2 * f 0 ≤ lower_RS_integral f (Icc (-1) 1) Real.sign := by
    rw [← hh_int]; exact integ_le_lower_RS_integral hbdd hh_min hh_pc hmono
  have hle := lower_RS_integral_le_upper hbdd hmono
  show upper_RS_integral f (Icc (-1) 1) Real.sign = 2 * f 0
  linarith

/-- Analogue of Lemma 11.3.7 -/
theorem RS_integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I)
  {α: ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
  have hbdd := bounded_of_piecewise_constant hf
  have h1 := upper_RS_integral_le_integ hbdd self_majorizes hf hα
  have h2 := integ_le_lower_RS_integral hbdd self_minorizes hf hα
  have h3 := lower_RS_integral_le_upper hbdd hα
  refine ⟨⟨hbdd, by linarith⟩, ?_⟩
  rw [RS_integ]
  linarith

end Chapter11
