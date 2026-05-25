import Mathlib.Tactic
import Analysis.Section_11_1

/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/

namespace Chapter11
open BoundedInterval

/-- Definition 11.2.1 -/
abbrev Constant {X Y:Type} (f: X → Y) : Prop := ∃ c, ∀ x, f x = c

open Classical in
noncomputable abbrev constant_value {X Y:Type} [hY: Nonempty Y] (f:X → Y) : Y :=
  if h: Constant f then h.choose else hY.some

theorem Constant.eq {X Y:Type} {f: X → Y} [Nonempty Y] (h: Constant f) (x:X) :
  f x = constant_value f := by simp [constant_value, h]; apply h.choose_spec

theorem Constant.of_const {X Y:Type} {f:X → Y} {c:Y} (h: ∀ x, f x = c) :
  Constant f := by use c

theorem Constant.const_eq {X Y:Type} {f:X → Y} [hX: Nonempty X] [Nonempty Y] {c:Y} (h: ∀ x, f x = c) :
  constant_value f = c := by rw [←eq (of_const h) hX.some, h hX.some]

theorem Constant.of_subsingleton {X Y:Type} [hs: Subsingleton X] [hY: Nonempty Y] {f:X → Y} :
  Constant f := by
  by_cases h:Nonempty X
  . use f h.some; intros; congr; exact hs.elim _ h.some
  simp at h; exact ⟨ hY.some, h.elim ⟩

abbrev ConstantOn (f: ℝ → ℝ) (X: Set ℝ) : Prop := Constant (fun x : X ↦ f ↑x)

noncomputable abbrev constant_value_on (f:ℝ → ℝ) (X: Set ℝ) : ℝ := constant_value (fun x : X ↦ f ↑x)

theorem ConstantOn.eq {f: ℝ → ℝ} {X: Set ℝ} (h: ConstantOn f X) {x:ℝ} (hx: x ∈ X) :
  f x = constant_value_on f X := by
  convert Constant.eq h ⟨ _, hx ⟩

theorem ConstantOn.of_const {f:ℝ → ℝ} {X: Set ℝ} {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  ConstantOn f X := ⟨ c, by grind ⟩

theorem ConstantOn.of_const' (c:ℝ) (X:Set ℝ): ConstantOn (fun _ ↦ c) X := of_const (c := c) (by simp)

theorem ConstantOn.const_eq {f:ℝ → ℝ} {X: Set ℝ} (hX: X.Nonempty) {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  constant_value_on f X = c := by
    rw [←eq (of_const h) hX.some_mem, h _ hX.some_mem]

theorem ConstantOn.congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) : ConstantOn f X ↔ ConstantOn g X := by
  simp_rw [ConstantOn, iff_iff_eq]; congr; grind

theorem ConstantOn.congr' {f g: ℝ → ℝ} {X: Set ℝ} (hf: ConstantOn f X) (h: ∀ x ∈ X, f x = g x) : ConstantOn g X := (congr h).mp hf

theorem ConstantOn.of_subsingleton {f: ℝ → ℝ} {X: Set ℝ} [Subsingleton X] :
  ConstantOn f X := Constant.of_subsingleton

theorem ConstantOn.mono {f: ℝ → ℝ} {X Y: Set ℝ} (h: ConstantOn f X) (hYX: Y ⊆ X) :
    ConstantOn f Y := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun ⟨x, hx⟩ => hc ⟨x, hYX hx⟩⟩

theorem constant_value_on_congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) :
  constant_value_on f X = constant_value_on g X := by
  simp [constant_value_on]; congr; grind

/-- Definition 11.2.3 (Piecewise constant functions I) -/
abbrev PiecewiseConstantWith (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : Prop := ∀ J ∈ P, ConstantOn f (J:Set ℝ)

theorem PiecewiseConstantWith.def (f:ℝ → ℝ) {I: BoundedInterval} {P: Partition I} :
  PiecewiseConstantWith f P ↔ ∀ J ∈ P, ∃ c, ∀ x ∈ J, f x = c := by
    simp [PiecewiseConstantWith, ConstantOn, Constant, mem_iff]

theorem PiecewiseConstantWith.congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P := by
  simp [PiecewiseConstantWith]; peel with J hJ
  apply ConstantOn.congr; have := P.contains _ hJ; grind [subset_iff]

/-- Definition 11.2.5 (Piecewise constant functions I) -/
abbrev PiecewiseConstantOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ P : Partition I, PiecewiseConstantWith f P

theorem PiecewiseConstantOn.def (f:ℝ → ℝ) (I: BoundedInterval):
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J:Set ℝ) := by rfl

theorem PiecewiseConstantOn.congr {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantOn f I ↔ PiecewiseConstantOn g I := by
  simp_rw [PiecewiseConstantOn, PiecewiseConstantWith.congr h]

theorem PiecewiseConstantOn.congr' {f g: ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) (h: ∀ x ∈ (I:Set ℝ), f x = g x) : PiecewiseConstantOn g I := (congr h).mp hf

/-- Example 11.2.4 / Example 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- junk value
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- junk value

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use ((((⊥ : Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
      (join_Ico_Icc (by norm_num) (by norm_num))).join (⊥ : Partition (Ioo 3 6))
      (join_Icc_Ioo (by norm_num) (by norm_num))).join (⊥ : Partition (Icc 6 6))
      (join_Ico_Icc (by norm_num) (by norm_num)))
  intro J hJ
  simp [Partition.mem_intervals_iff] at hJ
  rcases hJ with rfl | rfl | rfl | rfl
  · exact ConstantOn.of_const (c := 7) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 4) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 5) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 2) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use ((((((⊥ : Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 2))
      (join_Ico_Icc (by norm_num) (by norm_num))).join (⊥ : Partition (Ioo 2 3))
      (join_Icc_Ioo (by norm_num) (by norm_num))).join (⊥ : Partition (Icc 3 3))
      (join_Ico_Icc (by norm_num) (by norm_num))).join (⊥ : Partition (Ioo 3 5))
      (join_Icc_Ioo (by norm_num) (by norm_num))).join (⊥ : Partition (Ico 5 6))
      (join_Ico_Ico (by norm_num) (by norm_num))).join (⊥ : Partition (Icc 6 6))
      (join_Ico_Icc (by norm_num) (by norm_num))
  intro J hJ
  simp [Partition.mem_intervals_iff] at hJ
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ConstantOn.of_const (c := 7) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 7) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 7) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 4) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 5) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 5) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 2) (fun x hx ↦ by simp [f_11_2_4]; simp at hx; grind)

/-- Example 11.2.6 -/
theorem ConstantOn.piecewiseConstantOn {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f (I:Set ℝ)) :
  PiecewiseConstantOn f I := by
  use {
    intervals := {I},
    contains := by simp [subset_iff];
    exists_unique := by
      intro x hx
      use I
      simp
      exact hx
  }
  intro J hJ
  simp [Membership.mem] at hJ
  subst hJ
  exact h

lemma max_subset {I J : BoundedInterval} (P P': Partition I)
    (hJ : J ∈ max P P') : ∃ K ∈ P, J ⊆ K :=
  BoundedInterval.le_max' P P' J hJ

lemma max_subset' {I J : BoundedInterval} (P P': Partition I)
    (hJ : J ∈ max P P') : ∃ K ∈ P', J ⊆ K :=
  (BoundedInterval.le_max P P').2 J hJ

/-- Lemma 11.2.7 / Exercise 11.2.1 -/
theorem PiecewiseConstantWith.mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I} (hPP': P ≤ P')
  (hP: PiecewiseConstantWith f P) : PiecewiseConstantWith f P' := by
  rw [PiecewiseConstantWith.def] at hP ⊢
  intro J hJ
  have hJ' := hPP' _ hJ
  obtain ⟨K, hK, hJK⟩ := hPP' _ hJ
  have hP' := hP K hK
  obtain ⟨c, hc⟩ := hP'
  use c
  intro x hx
  exact hc x (hJK x hx)

/-- If {name}`f` and {name}`g` are both piecewise constant on {name}`I`, they share a common refining
partition on which each is piecewise constant. -/
theorem PiecewiseConstantOn.exists_common {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  ∃ P : Partition I, PiecewiseConstantWith f P ∧ PiecewiseConstantWith g P := by
  obtain ⟨Pf, hPf⟩ := hf
  obtain ⟨Pg, hPg⟩ := hg
  refine ⟨max Pf Pg, ?_, ?_⟩
  · exact PiecewiseConstantWith.mono (BoundedInterval.le_max' Pf Pg) hPf
  · exact PiecewiseConstantWith.mono ((BoundedInterval.le_max Pf Pg).2) hPg

/-- Pointwise binary operation preserves `PiecewiseConstantWith` on a fixed partition. -/
theorem PiecewiseConstantWith.binop {f g h: ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (op: ℝ → ℝ → ℝ) (hop: ∀ x, h x = op (f x) (g x))
  (hPf: PiecewiseConstantWith f P) (hPg: PiecewiseConstantWith g P) :
  PiecewiseConstantWith h P := by
  rw [PiecewiseConstantWith.def] at hPf hPg
  intro J hJ
  obtain ⟨cf, hcf⟩ := hPf J hJ
  obtain ⟨cg, hcg⟩ := hPg J hJ
  exact ConstantOn.of_const (c := op cf cg)
    (fun x hx ↦ by rw [hop, hcf x hx, hcg x hx])

/-- General binary combinator: any pointwise binary operation on two piecewise constant
functions is piecewise constant. -/
theorem PiecewiseConstantOn.binop {f g h: ℝ → ℝ} {I: BoundedInterval}
  (op: ℝ → ℝ → ℝ) (hop: ∀ x, h x = op (f x) (g x))
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  PiecewiseConstantOn h I := by
  obtain ⟨P, hPf, hPg⟩ := exists_common hf hg
  exact ⟨P, PiecewiseConstantWith.binop op hop hPf hPg⟩

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I :=
  binop (· + ·) (fun _ ↦ rfl) hf hg

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f - g) I :=
  binop (· - ·) (fun _ ↦ rfl) hf hg

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.max {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (max f g) I :=
  binop Max.max (fun _ ↦ rfl) hf hg

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.min {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (min f g) I :=
  binop Min.min (fun _ ↦ rfl) hf hg

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.mul {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f * g) I :=
  binop (· * ·) (fun _ ↦ rfl) hf hg

/-- Lemma 11.2.8 / Exercise 11.2.2 -/
theorem PiecewiseConstantOn.smul {f: ℝ → ℝ} {I: BoundedInterval}
  (c:ℝ) (hf: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P, ?_⟩
  rw [PiecewiseConstantWith.def] at hP
  intro J hJ
  obtain ⟨k, hk⟩ := hP J hJ
  exact ConstantOn.of_const (c := c * k) (fun x hx ↦ by simp [hk x hx])

/-- Lemma 11.2.8 / Exercise 11.2.2.  I believe the hypothesis that {name}`g` does not vanish is not needed. -/
theorem PiecewiseConstantOn.div {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f / g) I :=
  binop (· / ·) (fun _ ↦ rfl) hf hg

/-- Definition 11.2.9 (Piecewise constant integral I)-/
noncomputable abbrev PiecewiseConstantWith.integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * |J|ₗ

theorem PiecewiseConstantWith.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Example 11.2.12 -/
noncomputable abbrev f_11_2_12 : ℝ → ℝ := fun x ↦
    if x < 3 then 2 else
      if x = 3 then 4 else
        6

noncomputable abbrev P_11_2_12 : Partition (Icc 1 4) :=
  ((⊥: Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))

theorem pwc_11_2_12 : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  intro J hJ
  simp [Partition.mem_intervals_iff] at hJ
  rcases hJ with rfl | rfl | rfl
  · exact ConstantOn.of_const (c := 2) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 4) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 6) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)

theorem integ_11_2_12 : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  simp only [PiecewiseConstantWith.integ, Partition.intervals_of_bot]
  repeat rw [Finset.sum_union (by simp)]
  repeat rw [Finset.sum_singleton]
  rw [ConstantOn.const_eq (c := 2) ⟨1, by simp⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind),
      ConstantOn.const_eq (c := 4) ⟨3, by simp⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind),
      ConstantOn.const_eq (c := 6) ⟨4, by simp; norm_num⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind)]
  simp [BoundedInterval.length]
  norm_num

noncomputable abbrev P_11_2_12' : Partition (Icc 1 4) :=
  ((((⊥: Partition (Ico 1 2)).join (⊥ : Partition (Ico 2 3))
  (join_Ico_Ico (by norm_num) (by norm_num) )).join
  (⊥: Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num))).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))).add_empty

example : PiecewiseConstantWith f_11_2_12 P_11_2_12' := by
  intro J hJ
  simp [Partition.mem_intervals_iff] at hJ
  rcases hJ with rfl | rfl | rfl | rfl | rfl
  · exact ConstantOn.of_const (c := 2) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 2) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 4) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 6) (fun x hx ↦ by simp [f_11_2_12]; simp at hx; grind)
  · exact ConstantOn.of_const (c := 0) (fun x hx ↦ by simp at hx)

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12' = 10 := by
  simp only [PiecewiseConstantWith.integ, Partition.intervals_of_bot]
  repeat rw [Finset.sum_union (by simp)]
  repeat rw [Finset.sum_singleton]
  rw [ConstantOn.const_eq (X := (Ico 1 2 : Set ℝ)) (c := 2) ⟨1, by simp⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind),
      ConstantOn.const_eq (X := (Ico 2 3 : Set ℝ)) (c := 2) ⟨2, by simp; norm_num⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind),
      ConstantOn.const_eq (c := 4) ⟨3, by simp⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind),
      ConstantOn.const_eq (c := 6) ⟨4, by simp; norm_num⟩
        (fun x hx ↦ by simp at hx; simp [f_11_2_12]; grind)]
  simp [BoundedInterval.length]
  norm_num

/-- Two intervals in a partition that share a point are equal. Follows from {name}`exists_unique`. -/
theorem Partition.eq_of_mem {I: BoundedInterval} {Q: Partition I} {K₁ K₂: BoundedInterval}
    (hK₁: K₁ ∈ Q.intervals) (hK₂: K₂ ∈ Q.intervals)
    {x: ℝ} (hx₁: x ∈ (K₁:Set ℝ)) (hx₂: x ∈ (K₂:Set ℝ)) : K₁ = K₂ := by
  have hxI : x ∈ (I:Set ℝ) := by
    have hsub := Q.contains _ hK₁; rw [subset_iff] at hsub; exact hsub hx₁
  obtain ⟨_, _, huniq⟩ := Q.exists_unique x hxI
  exact (huniq K₁ ⟨hK₁, by rwa [mem_iff]⟩).trans (huniq K₂ ⟨hK₂, by rwa [mem_iff]⟩).symm

/-- Two pairs {lit}`(J₁, K₁), (J₂, K₂) ∈ Q × Q'` whose intersections agree as
{name}`BoundedInterval`s must either be the same pair or have empty intersection — otherwise a
witness {lit}`x` in the intersection would contradict {name}`exists_unique` on {lit}`Q` or
{lit}`Q'`. -/
theorem Partition.inter_empty_of_dup {I: BoundedInterval} {Q Q': Partition I}
    {J₁ K₁ J₂ K₂: BoundedInterval}
    (hJ₁: J₁ ∈ Q.intervals) (hK₁: K₁ ∈ Q'.intervals)
    (hJ₂: J₂ ∈ Q.intervals) (hK₂: K₂ ∈ Q'.intervals)
    (hne: (J₁, K₁) ≠ (J₂, K₂))
    (heq: ((J₁ ∩ K₁ : BoundedInterval):Set ℝ) = ((J₂ ∩ K₂ : BoundedInterval):Set ℝ)) :
    ((J₁ ∩ K₁ : BoundedInterval):Set ℝ) = ∅ := by
  by_contra hne_empty
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne_empty
  rw [BoundedInterval.inter_eq] at hx
  have hx2 : x ∈ ((J₂ ∩ K₂ : BoundedInterval):Set ℝ) := heq ▸ by
    rw [BoundedInterval.inter_eq]; exact hx
  rw [BoundedInterval.inter_eq] at hx2
  apply hne
  ext
  · exact Partition.eq_of_mem hJ₁ hJ₂ hx.1 hx2.1
  · exact Partition.eq_of_mem hK₁ hK₂ hx.2 hx2.2

/-- The partition {lit}`{J ∩ K : K ∈ Q}` of {name}`J`, when {lean}`J ⊆ I` and {lean}`Q : Partition I`. -/
noncomputable def Partition.restrict_inter {I: BoundedInterval} (Q: Partition I)
    (J: BoundedInterval) (hJ: J ⊆ I) : Partition J where
  intervals := Q.intervals.image (fun K ↦ (J ∩ K : BoundedInterval))
  exists_unique x hx := by
    have hxI : x ∈ (I:Set ℝ) := by rw [subset_iff] at hJ; exact hJ (by rwa [mem_iff] at hx)
    obtain ⟨K, ⟨hKQ, hxK⟩, huniq⟩ := Q.exists_unique x hxI
    refine ExistsUnique.intro (J ∩ K : BoundedInterval) ?_ ?_
    · refine ⟨?_, ?_⟩
      · simp; exact ⟨K, hKQ, rfl⟩
      · rw [mem_iff, BoundedInterval.inter_eq]; exact ⟨by rwa [mem_iff] at hx, hxK⟩
    · rintro L ⟨hL, hxL⟩
      simp at hL
      obtain ⟨K', hK'Q, rfl⟩ := hL
      rw [mem_iff, BoundedInterval.inter_eq] at hxL
      have : K' = K := huniq K' ⟨hK'Q, hxL.2⟩
      rw [this]
  contains L hL := by
    simp at hL
    obtain ⟨K, hK, rfl⟩ := hL
    rw [subset_iff, BoundedInterval.inter_eq]
    exact Set.inter_subset_left

theorem Partition.length_restrict_inter {I:BoundedInterval} (Q: Partition I)
    (J: BoundedInterval) (hJ: J ⊆ I) :
    ∑ K ∈ Q.intervals, |(J ∩ K : BoundedInterval)|ₗ = |J|ₗ := by
  rw [← Partition.sum_of_length J (Q.restrict_inter J hJ)]
  refine (Finset.sum_image_of_pairwise_eq_zero (g := fun L : BoundedInterval ↦ |L|ₗ) ?_).symm
  intro K₁ hK₁ K₂ hK₂ hne heq
  show |(J ∩ K₁ : BoundedInterval)|ₗ = 0
  apply length_of_empty
  by_contra hne_empty
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne_empty
  rw [BoundedInterval.inter_eq] at hx
  have hx2 : x ∈ ((J ∩ K₂ : BoundedInterval):Set ℝ) := heq ▸ by rw [BoundedInterval.inter_eq]; exact hx
  rw [BoundedInterval.inter_eq] at hx2
  exact hne (Partition.eq_of_mem hK₁ hK₂ hx.2 hx2.2)

/-- Rewrite {lean}`integ f (max P P')` as a double sum over {lit}`P × P'` of pieces {lit}`J ∩ K`.
The image-to-product conversion uses {name}`Finset.sum_image_of_pairwise_eq_zero`: when two pairs
{lit}`(J₁, K₁)` and {lit}`(J₂, K₂)` produce the same intersection, that intersection must be empty
(else {lit}`x` in it would contradict {lit}`exists_unique` on both {lit}`P` and {lit}`P'`), so the
summand vanishes. -/
theorem PiecewiseConstantWith.integ_max_eq_double_sum {f:ℝ → ℝ} {I: BoundedInterval}
    (P P': Partition I) :
    integ f (max P P') = ∑ J ∈ P.intervals, ∑ K ∈ P'.intervals,
      constant_value_on f ((J ∩ K : BoundedInterval):Set ℝ) * |(J ∩ K : BoundedInterval)|ₗ := by
  classical
  have h_max_intervals : (max P P').intervals =
      Finset.image (Function.uncurry fun J K ↦ (J ∩ K : BoundedInterval))
        (P.intervals ×ˢ P'.intervals) := by
    show Finset.image₂ _ _ _ = _
    rw [← Finset.image_uncurry_product]
  rw [show integ f (max P P') = ∑ L ∈ (max P P').intervals,
        constant_value_on f (L:Set ℝ) * |L|ₗ from rfl, h_max_intervals]
  rw [Finset.sum_image_of_pairwise_eq_zero
    (g := fun L : BoundedInterval ↦ constant_value_on f (L:Set ℝ) * |L|ₗ)
    (I := P.intervals ×ˢ P'.intervals)
    (f := Function.uncurry fun J K ↦ (J ∩ K : BoundedInterval))]
  swap
  · intro p₁ hp₁ p₂ hp₂ hne heq
    simp [Function.uncurry] at heq
    show constant_value_on f ((p₁.1 ∩ p₁.2 : BoundedInterval):Set ℝ)
      * |(p₁.1 ∩ p₁.2 : BoundedInterval)|ₗ = 0
    suffices h : |(p₁.1 ∩ p₁.2 : BoundedInterval)|ₗ = 0 by rw [h]; ring
    simp at hp₁ hp₂
    exact length_of_empty (Partition.inter_empty_of_dup hp₁.1 hp₁.2 hp₂.1 hp₂.2 hne (by rw [heq]))
  rw [Finset.sum_product]
  rfl

theorem PiecewiseConstantWith.integ_max {f:ℝ → ℝ} {I: BoundedInterval} (P P': Partition I)
  (hP: PiecewiseConstantWith f P): integ f P = integ f (max P P') := by
  rw [integ_max_eq_double_sum P P']
  rw [show integ f P = ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * |J|ₗ from rfl]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJsub : J ⊆ I := P.contains _ hJ
  have hconst : ConstantOn f (J:Set ℝ) := hP J hJ
  have heach : ∀ K ∈ P'.intervals,
      constant_value_on f ((J ∩ K : BoundedInterval):Set ℝ) * |(J ∩ K : BoundedInterval)|ₗ
        = constant_value_on f (J:Set ℝ) * |(J ∩ K : BoundedInterval)|ₗ := by
    intro K _
    by_cases hempty : ((J ∩ K : BoundedInterval):Set ℝ) = ∅
    · rw [length_of_empty hempty]; ring
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
      Partition.length_restrict_inter P' J hJsub]

theorem BoundedInterval.length_eq_set {I J: BoundedInterval} (h: I.toSet = J.toSet) : I.length = J.length := by
  by_cases hsub : Subsingleton (I:Set ℝ)
  · have hsubJ : Subsingleton (J:Set ℝ) := by
      rw [Set.subsingleton_coe] at hsub ⊢; rw [← h]; exact hsub
    rw [length_of_subsingleton.mp hsub, length_of_subsingleton.mp hsubJ]
  have hsubJ : ¬ Subsingleton (J:Set ℝ) := by
    rw [Set.subsingleton_coe] at hsub ⊢; rw [← h]; exact hsub
  have hI : I.a < I.b := by
    rw [Set.subsingleton_coe] at hsub
    by_contra hba
    push_neg at hba
    apply hsub
    cases I with
    | Ioo _ _ => simp [Set.Ioo_eq_empty (not_lt.mpr hba)] at *
    | Ioc _ _ => simp [Set.Ioc_eq_empty (not_lt.mpr hba)] at *
    | Ico _ _ => simp [Set.Ico_eq_empty (not_lt.mpr hba)] at *
    | Icc x y =>
      simp [a, b] at hba
      intro u hu v hv; simp at hu hv; linarith
  have hJ : J.a < J.b := by
    rw [Set.subsingleton_coe] at hsubJ
    by_contra hba
    push_neg at hba
    apply hsubJ
    cases J with
    | Ioo _ _ => simp [a, b, Set.Ioo_eq_empty (not_lt.mpr hba)] at *
    | Ioc _ _ => simp [a, b, Set.Ioc_eq_empty (not_lt.mpr hba)] at *
    | Ico _ _ => simp [a, b, Set.Ico_eq_empty (not_lt.mpr hba)] at *
    | Icc x y =>
      simp [a, b] at hba
      intro u hu v hv; simp at hu hv; linarith
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
  have hab : I.b - I.a = J.b - J.a := by
    rw [← hSupI, ← hInfI, ← hSupJ, ← hInfJ, h]
  simp [length, hab]

/-- The integral over {lit}`max P P'` and {lit}`max P' P` agree. They differ as {name}`Partition`s
because {name}`BoundedInterval.inter` is {name}`Classical.choose`-based, but
{lit}`(J ∩ K).toSet = (K ∩ J).toSet`, so the two double sums match termwise after a
{name}`Finset.sum_comm`. -/
theorem PiecewiseConstantWith.integ_max_comm {f:ℝ → ℝ} {I: BoundedInterval} (P P': Partition I) :
    integ f (max P P') = integ f (max P' P) := by
  rw [integ_max_eq_double_sum P P', integ_max_eq_double_sum P' P, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro J _
  apply Finset.sum_congr rfl; intro K _
  have hset : ((J ∩ K : BoundedInterval):Set ℝ) = ((K ∩ J : BoundedInterval):Set ℝ) := by
    rw [BoundedInterval.inter_eq, BoundedInterval.inter_eq, Set.inter_comm]
  rw [hset, BoundedInterval.length_eq_set hset]

/-- Proposition 11.2.13 (Piecewise constant integral is independent of partition) / Exercise 11.2.3 -/
theorem PiecewiseConstantWith.integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') : integ f P = integ f P' := by
  rw [integ_max P P' hP, integ_max_comm, ← integ_max P' P hP']

open Classical in
/-- Definition 11.2.14 (Piecewise constant integral II)  -/
noncomputable abbrev PiecewiseConstantOn.integ (f:ℝ → ℝ) (I: BoundedInterval) :
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.integ f h.choose else 0

noncomputable abbrev PiecewiseConstantOn.integ' {f:ℝ → ℝ} {I: BoundedInterval} (_:PiecewiseConstantOn f I) := integ f I

theorem PiecewiseConstantOn.integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) : integ f I = PiecewiseConstantWith.integ f P := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [integ, h']; exact PiecewiseConstantWith.integ_eq h'.choose_spec h

theorem PiecewiseConstantOn.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f I = integ g I := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [integ, hf, hg])
  rw [PiecewiseConstantWith.integ_congr h, ←integ_def hg.choose_spec, ←integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Example 11.2.15 -/
example : PiecewiseConstantOn.integ f_11_2_12 (Icc 1 4) = 10 :=
  (PiecewiseConstantOn.integ_def pwc_11_2_12).trans integ_11_2_12

/-- Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f + g) I = integ f I + integ g I := by
  obtain ⟨P, hPf, hPg⟩ := exists_common hf hg
  have hPfg : PiecewiseConstantWith (f + g) P :=
    PiecewiseConstantWith.binop (· + ·) (fun _ ↦ rfl) hPf hPg
  rw [integ_def hPfg, integ_def hPf, integ_def hPg]
  simp only [PiecewiseConstantWith.integ, ← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  obtain ⟨cf, hcf⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
  obtain ⟨cg, hcg⟩ := (PiecewiseConstantWith.def g).mp hPg J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hJne hcf, ConstantOn.const_eq hJne hcg,
        ConstantOn.const_eq hJne (c := cf + cg) (fun x hx ↦ by simp [hcf x hx, hcg x hx])]
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [BoundedInterval.length_of_empty hJne]; ring

/-- Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ) (hf: PiecewiseConstantOn f I) :
  integ (c • f) I = c * integ f I
   := by
  obtain ⟨P, hPf⟩ := hf
  have hPcf : PiecewiseConstantWith (c • f) P := by
    intro J hJ
    obtain ⟨k, hk⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
    exact ConstantOn.of_const (c := c * k) (fun x hx ↦ by simp [hk x hx])
  rw [integ_def hPcf, integ_def hPf]
  simp only [PiecewiseConstantWith.integ, Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_congr rfl
  intro J hJ
  obtain ⟨k, hk⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hJne hk,
        ConstantOn.const_eq hJne (c := c * k) (fun x hx ↦ by simp [hk x hx])]
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [BoundedInterval.length_of_empty hJne]; ring

/-- Theorem 11.2.16 (c) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f - g) I = integ f I - integ g I := by
  obtain ⟨P, hPf, hPg⟩ := exists_common hf hg
  have hPfg : PiecewiseConstantWith (f - g) P :=
    PiecewiseConstantWith.binop (· - ·) (fun _ ↦ rfl) hPf hPg
  rw [integ_def hPfg, integ_def hPf, integ_def hPg]
  simp only [PiecewiseConstantWith.integ, ← Finset.sum_sub_distrib, ← sub_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  obtain ⟨cf, hcf⟩ := (PiecewiseConstantWith.def f).mp hPf J hJ
  obtain ⟨cg, hcg⟩ := (PiecewiseConstantWith.def g).mp hPg J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hJne hcf, ConstantOn.const_eq hJne hcg,
        ConstantOn.const_eq hJne (c := cf - cg) (fun x hx ↦ by simp [hcf x hx, hcg x hx])]
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [BoundedInterval.length_of_empty hJne]; ring

/-- Theorem 11.2.16 (d) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, 0 ≤ f x)
  (hf: PiecewiseConstantOn f I) :
  0 ≤ integ f I := by
  obtain ⟨P, hP⟩ := hf
  rw [integ_def hP]
  apply Finset.sum_nonneg
  intro J hJ
  by_cases hJne : (J : Set ℝ).Nonempty
  · obtain ⟨x, hx⟩ := hJne
    have hxI : x ∈ I := P.contains _ hJ x (by rwa [← mem_iff] at hx)
    have hcv : constant_value_on f (J:Set ℝ) = f x := by
      rw [← (hP J hJ).eq hx]
    rw [hcv]
    exact mul_nonneg (h x hxI) (BoundedInterval.length_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty] at hJne
    rw [BoundedInterval.length_of_empty hJne, mul_zero]

/-- Theorem 11.2.16 (e) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_mono {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, f x ≤ g x)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ f I ≤ integ g I := by
  have hgf : 0 ≤ integ (g - f) I :=
    integ_of_nonneg (fun x hx ↦ by simp [sub_nonneg, h x hx]) (sub hg hf)
  rw [integ_sub hg hf] at hgf
  linarith

/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const (c: ℝ) (I: BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hP : PiecewiseConstantWith (fun _ : ℝ ↦ c) (⊥ : Partition I) := by
    intro J hJ
    rw [Partition.mem_intervals_iff, Partition.intervals_of_bot, Finset.mem_singleton] at hJ
    subst hJ
    exact ConstantOn.of_const' c _
  rw [integ_def hP]
  simp only [PiecewiseConstantWith.integ, Partition.intervals_of_bot, Finset.sum_singleton]
  by_cases hI : (I : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hI (c := c) (fun _ _ ↦ rfl)]
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    rw [BoundedInterval.length_of_empty hI, mul_zero, mul_zero]

/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const' {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  by_cases hI : (I : Set ℝ).Nonempty
  · set c := constant_value_on f (I:Set ℝ) with hc_def
    rw [integ_congr (g := fun _ ↦ c) (fun x hx ↦ h.eq hx), integ_const]
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    rw [BoundedInterval.length_of_empty hI, mul_zero]
    rw [integ_congr (g := fun _ ↦ (0:ℝ))
          (fun x hx ↦ by rw [hI] at hx; exact hx.elim),
        integ_const, zero_mul]

/-- Intersection of a {name}`BoundedInterval` with any {name}`Set.OrdConnected` set is again
representable as a {name}`BoundedInterval`. The intersection is bounded (subset of {lit}`J`)
and {name}`Set.OrdConnected` (intersection of two {name}`Set.OrdConnected`), so
{name}`BoundedInterval.ordConnected_iff` gives an explicit {name}`BoundedInterval` representative. -/
lemma BoundedInterval.exists_inter_ordConnected (J : BoundedInterval) (X : Set ℝ)
    (hX : X.OrdConnected) : ∃ K : BoundedInterval, (K : Set ℝ) = (J : Set ℝ) ∩ X := by
  have ⟨L, hL⟩ : ∃ L : BoundedInterval, (J : Set ℝ) ∩ X = L := by
    apply (ordConnected_iff _).mp
    refine ⟨?_, ?_⟩
    · exact (Bornology.IsBounded.of_boundedInterval J).subset Set.inter_subset_left
    · exact (((ordConnected_iff _).mpr ⟨J, rfl⟩).2).inter hX
  exact ⟨L, hL.symm⟩

/-- The "left exterior" cutoff of {lit}`I`: closed at {lit}`I.a` when {lit}`I` is open at
{lit}`I.a`, open otherwise. Intersecting {lit}`J` with this set yields the left flank. -/
def BoundedInterval.leftCutoff : BoundedInterval → Set ℝ
  | Ioo a _ => Set.Iic a
  | Ioc a _ => Set.Iic a
  | Icc a _ => Set.Iio a
  | Ico a _ => Set.Iio a

/-- The "right exterior" cutoff of {lit}`I`. -/
def BoundedInterval.rightCutoff : BoundedInterval → Set ℝ
  | Ioo _ b => Set.Ici b
  | Ico _ b => Set.Ici b
  | Icc _ b => Set.Ioi b
  | Ioc _ b => Set.Ioi b

lemma BoundedInterval.leftCutoff_ordConnected (I : BoundedInterval) :
    I.leftCutoff.OrdConnected := by
  cases I
  · exact Set.ordConnected_Iic
  · exact Set.ordConnected_Iio
  · exact Set.ordConnected_Iic
  · exact Set.ordConnected_Iio

lemma BoundedInterval.rightCutoff_ordConnected (I : BoundedInterval) :
    I.rightCutoff.OrdConnected := by
  cases I
  · exact Set.ordConnected_Ici
  · exact Set.ordConnected_Ioi
  · exact Set.ordConnected_Ioi
  · exact Set.ordConnected_Ici

lemma BoundedInterval.leftCutoff_inter_self (I : BoundedInterval) :
    I.leftCutoff ∩ (I : Set ℝ) = ∅ := by
  cases I <;> ext x <;> simp [leftCutoff] <;> intros <;> linarith

lemma BoundedInterval.rightCutoff_inter_self (I : BoundedInterval) :
    I.rightCutoff ∩ (I : Set ℝ) = ∅ := by
  cases I <;> ext x <;> simp [rightCutoff] <;> intros <;> linarith

lemma BoundedInterval.leftCutoff_inter_rightCutoff (I : BoundedInterval)
    (hI : (I : Set ℝ).Nonempty) : I.leftCutoff ∩ I.rightCutoff = ∅ := by
  obtain ⟨y, hy⟩ := hI
  cases I <;> simp at hy <;> ext x <;> simp [leftCutoff, rightCutoff] <;>
    intros <;> linarith

lemma BoundedInterval.cutoff_cover (I : BoundedInterval) :
    I.leftCutoff ∪ (I : Set ℝ) ∪ I.rightCutoff = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  cases I with
  | Ioo a b =>
    simp [leftCutoff, rightCutoff]
    rcases le_or_gt x a with h | h
    · left; left; exact h
    · rcases lt_or_ge x b with h' | h'
      · left; right; exact ⟨h, h'⟩
      · right; exact h'
  | Icc a b =>
    simp [leftCutoff, rightCutoff]
    rcases lt_or_ge x a with h | h
    · left; left; exact h
    · rcases le_or_gt x b with h' | h'
      · left; right; exact ⟨h, h'⟩
      · right; exact h'
  | Ioc a b =>
    simp [leftCutoff, rightCutoff]
    rcases le_or_gt x a with h | h
    · left; left; exact h
    · rcases le_or_gt x b with h' | h'
      · left; right; exact ⟨h, h'⟩
      · right; exact h'
  | Ico a b =>
    simp [leftCutoff, rightCutoff]
    rcases lt_or_ge x a with h | h
    · left; left; exact h
    · rcases lt_or_ge x b with h' | h'
      · left; right; exact ⟨h, h'⟩
      · right; exact h'

/-- The left flank: a {name}`BoundedInterval` whose underlying set is
{lit}`J ∩ I.leftCutoff`. -/
noncomputable def BoundedInterval.leftFlank (J I : BoundedInterval) : BoundedInterval :=
  (J.exists_inter_ordConnected I.leftCutoff I.leftCutoff_ordConnected).choose

lemma BoundedInterval.leftFlank_set (J I : BoundedInterval) :
    (J.leftFlank I : Set ℝ) = (J : Set ℝ) ∩ I.leftCutoff :=
  (J.exists_inter_ordConnected I.leftCutoff I.leftCutoff_ordConnected).choose_spec

noncomputable def BoundedInterval.rightFlank (J I : BoundedInterval) : BoundedInterval :=
  (J.exists_inter_ordConnected I.rightCutoff I.rightCutoff_ordConnected).choose

lemma BoundedInterval.rightFlank_set (J I : BoundedInterval) :
    (J.rightFlank I : Set ℝ) = (J : Set ℝ) ∩ I.rightCutoff :=
  (J.exists_inter_ordConnected I.rightCutoff I.rightCutoff_ordConnected).choose_spec

lemma BoundedInterval.leftFlank_notMem {J I : BoundedInterval} :
    ∀ x ∈ (J.leftFlank I : Set ℝ), x ∉ I := fun x hx h => by
  rw [leftFlank_set] at hx
  exact (Set.eq_empty_iff_forall_notMem.mp (leftCutoff_inter_self I)) x
    ⟨hx.2, (mem_iff _ _).mp h⟩

lemma BoundedInterval.rightFlank_notMem {J I : BoundedInterval} :
    ∀ x ∈ (J.rightFlank I : Set ℝ), x ∉ I := fun x hx h => by
  rw [rightFlank_set] at hx
  exact (Set.eq_empty_iff_forall_notMem.mp (rightCutoff_inter_self I)) x
    ⟨hx.2, (mem_iff _ _).mp h⟩

/-- If {lit}`f` vanishes on a bounded interval {lit}`F`, its contribution to a piecewise
constant integral is zero. -/
lemma constant_value_on_zero_mul_length {f : ℝ → ℝ} {F : BoundedInterval}
    (hf : ∀ x ∈ (F : Set ℝ), f x = 0) :
    constant_value_on f (F : Set ℝ) * |F|ₗ = 0 := by
  by_cases hFne : (F : Set ℝ).Nonempty
  · rw [ConstantOn.const_eq hFne hf]; ring
  · rw [Set.not_nonempty_iff_eq_empty] at hFne
    rw [BoundedInterval.length_of_empty hFne]; ring

/-- Given a partition {lit}`P` of nonempty {lit}`I ⊆ J`, extend it to a partition of
{lit}`J` by adjoining the left and right flanks {lit}`J \ I`. -/
noncomputable def Partition.extend {I J : BoundedInterval} (hIJ : I ⊆ J)
    (P : Partition I) (hI : (I : Set ℝ).Nonempty) : Partition J where
  intervals := P.intervals ∪ {leftFlank J I, rightFlank J I}
  contains := by
    intro K hK
    simp at hK
    rw [subset_iff]
    rcases hK with rfl | rfl | hK
    · rw [leftFlank_set]; exact Set.inter_subset_left
    · rw [rightFlank_set]; exact Set.inter_subset_left
    · exact (subset_iff _ _).mp ((P.contains K hK).trans hIJ)
  exists_unique := by
    intro x hxJ
    rw [mem_iff] at hxJ
    by_cases hxI : x ∈ (I : Set ℝ)
    · obtain ⟨K, ⟨hKP, hxK⟩, huniq⟩ := P.exists_unique x (by rwa [mem_iff])
      refine ExistsUnique.intro K ⟨by simp [hKP], hxK⟩ ?_
      rintro K' ⟨hK'mem, hxK'⟩
      simp at hK'mem
      rcases hK'mem with rfl | rfl | hK'P
      · exfalso
        rw [mem_iff, leftFlank_set] at hxK'
        exact (Set.eq_empty_iff_forall_notMem.mp (leftCutoff_inter_self I)) x ⟨hxK'.2, hxI⟩
      · exfalso
        rw [mem_iff, rightFlank_set] at hxK'
        exact (Set.eq_empty_iff_forall_notMem.mp (rightCutoff_inter_self I)) x ⟨hxK'.2, hxI⟩
      · exact huniq K' ⟨hK'P, hxK'⟩
    · have hcov : x ∈ I.leftCutoff ∪ (I : Set ℝ) ∪ I.rightCutoff := by
        rw [cutoff_cover]; trivial
      rcases hcov with (hL | hI') | hR
      · refine ExistsUnique.intro (leftFlank J I) ⟨by simp, ?_⟩ ?_
        · rw [mem_iff, leftFlank_set]; exact ⟨hxJ, hL⟩
        · rintro K' ⟨hK'mem, hxK'⟩
          simp at hK'mem
          rcases hK'mem with rfl | rfl | hK'P
          · rfl
          · exfalso
            rw [mem_iff, rightFlank_set] at hxK'
            exact (Set.eq_empty_iff_forall_notMem.mp
              (leftCutoff_inter_rightCutoff I hI)) x ⟨hL, hxK'.2⟩
          · exfalso
            have hxI' : x ∈ (I : Set ℝ) :=
              ((subset_iff _ _).mp (P.contains K' hK'P)) (by rwa [← mem_iff])
            exact hxI hxI'
      · exact absurd hI' hxI
      · refine ExistsUnique.intro (rightFlank J I) ⟨by simp, ?_⟩ ?_
        · rw [mem_iff, rightFlank_set]; exact ⟨hxJ, hR⟩
        · rintro K' ⟨hK'mem, hxK'⟩
          simp at hK'mem
          rcases hK'mem with rfl | rfl | hK'P
          · exfalso
            rw [mem_iff, leftFlank_set] at hxK'
            exact (Set.eq_empty_iff_forall_notMem.mp
              (leftCutoff_inter_rightCutoff I hI)) x ⟨hxK'.2, hR⟩
          · rfl
          · exfalso
            have hxI' : x ∈ (I : Set ℝ) :=
              ((subset_iff _ _).mp (P.contains K' hK'P)) (by rwa [← mem_iff])
            exact hxI hxI'

open Classical in
/-- The extended function {lit}`fun x ↦ if x ∈ I then f x else 0` is piecewise constant on
the extended partition {lit}`Partition.extend hIJ P hI`: equal to {lit}`f` on each piece of
{lit}`P` (subset of {lit}`I`), and constantly {lit}`0` on the two flanks. -/
lemma PiecewiseConstantWith.extend {I J : BoundedInterval} (hIJ : I ⊆ J)
    {f : ℝ → ℝ} {P : Partition I} (hP : PiecewiseConstantWith f P)
    (hI : (I : Set ℝ).Nonempty) :
    PiecewiseConstantWith (fun x ↦ if x ∈ I then f x else 0)
      (Partition.extend hIJ P hI) := by
  intro K hK
  change K ∈ P.intervals ∪ {leftFlank J I, rightFlank J I} at hK
  simp at hK
  rcases hK with rfl | rfl | hKP
  · exact ConstantOn.of_const (c := 0) (fun x hx => by simp [leftFlank_notMem x hx])
  · exact ConstantOn.of_const (c := 0) (fun x hx => by simp [rightFlank_notMem x hx])
  · refine ConstantOn.congr' (hP K hKP) (fun x hx => ?_)
    have hxI : x ∈ I :=
      (mem_iff _ _).mpr ((subset_iff _ _).mp (P.contains K hKP) hx)
    simp [hxI]

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  by_cases hI : (I : Set ℝ).Nonempty
  · obtain ⟨P, hP⟩ := h
    exact ⟨Partition.extend hIJ P hI, hP.extend hIJ hI⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    apply ConstantOn.piecewiseConstantOn
    apply ConstantOn.of_const (c := 0)
    intro x _
    have hxnI : x ∉ I := fun h => by rw [mem_iff, hI] at h; exact h
    simp [hxnI]

open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  by_cases hI : (I : Set ℝ).Nonempty
  · obtain ⟨P, hP⟩ := h
    rw [integ_def (hP.extend hIJ hI), integ_def hP]
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
      · exact constant_value_on_zero_mul_length
          (fun x hx => by simp [leftFlank_notMem x hx])
      · exact constant_value_on_zero_mul_length
          (fun x hx => by simp [rightFlank_notMem x hx])
      · exact absurd hKP' hKP
  · rw [Set.not_nonempty_iff_eq_empty] at hI
    have hf : ConstantOn f (I : Set ℝ) := hI ▸ ConstantOn.of_subsingleton
    have hxnI : ∀ x, x ∉ I := by intro x h; rw [mem_iff, hI] at h; exact h
    rw [integ_congr (g := fun _ => (0:ℝ)) (fun x _ => by simp [hxnI x]),
        integ_const, integ_const' hf, BoundedInterval.length_of_empty hI]
    ring

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  (f: ℝ → ℝ) : PiecewiseConstantOn f K ↔ PiecewiseConstantOn f I ∧ PiecewiseConstantOn f J := by
  have hIK : I ⊆ K := by rw [subset_iff, hIJK.2.1]; exact Set.subset_union_left
  have hJK : J ⊆ K := by rw [subset_iff, hIJK.2.1]; exact Set.subset_union_right
  constructor
  · rintro ⟨P, hP⟩
    have hrestrict : ∀ {M : BoundedInterval} (hMK : M ⊆ K),
        ∀ L ∈ (P.restrict_inter M hMK).intervals, ConstantOn f (L : Set ℝ) := by
      intro M hMK L hL
      obtain ⟨L', hL'P, rfl⟩ := Finset.mem_image.mp hL
      rw [BoundedInterval.inter_eq]
      exact (hP L' hL'P).mono Set.inter_subset_right
    exact ⟨⟨P.restrict_inter I hIK, hrestrict hIK⟩,
           ⟨P.restrict_inter J hJK, hrestrict hJK⟩⟩
  · rintro ⟨⟨PI, hPI⟩, ⟨PJ, hPJ⟩⟩
    refine ⟨PI.join PJ hIJK, ?_⟩
    intro L hL
    rw [Partition.mem_intervals_iff, Partition.intervals_of_join,
        Finset.mem_union] at hL
    rcases hL with hLI | hLJ
    · exact hPI L hLI
    · exact hPJ L hLJ

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) :
  integ f K = integ f I + integ f J := by
  obtain ⟨⟨PI, hPI⟩, ⟨PJ, hPJ⟩⟩ := (of_join hIJK f).mp h
  have hJoined : PiecewiseConstantWith f (PI.join PJ hIJK) := by
    intro L hL
    rw [Partition.mem_intervals_iff, Partition.intervals_of_join,
        Finset.mem_union] at hL
    rcases hL with hLI | hLJ
    · exact hPI L hLI
    · exact hPJ L hLJ
  rw [integ_def hJoined, integ_def hPI, integ_def hPJ]
  show ∑ L ∈ (PI.join PJ hIJK).intervals, _ = _
  rw [Partition.intervals_of_join]
  have h_inter_zero : ∀ L ∈ PI.intervals ∩ PJ.intervals,
      constant_value_on f (L : Set ℝ) * |L|ₗ = 0 := by
    intro L hL
    rw [Finset.mem_inter] at hL
    have hLempty : (L : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hxL
      have hxI : x ∈ (I : Set ℝ) := (subset_iff _ _).mp (PI.contains L hL.1) hxL
      have hxJ : x ∈ (J : Set ℝ) := (subset_iff _ _).mp (PJ.contains L hL.2) hxL
      have : x ∈ ((I : Set ℝ) ∩ (J : Set ℝ)) := ⟨hxI, hxJ⟩
      rw [hIJK.1] at this; exact this
    rw [BoundedInterval.length_of_empty hLempty]; ring
  have hu := @Finset.sum_union_inter _ _ PI.intervals PJ.intervals _
    (fun L => constant_value_on f (L : Set ℝ) * |L|ₗ) _
  rw [Finset.sum_eq_zero h_inter_zero, add_zero] at hu
  exact hu

end Chapter11
