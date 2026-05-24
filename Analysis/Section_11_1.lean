import Mathlib.Tactic

/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/

namespace Chapter11

inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

/-- There is a technical issue in that this coercion is not injective: the empty set
is represented by multiple bounded intervals.  This causes some of the statements in
this section to be a little uglier than necessary.-/
@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make {name}`Finset`s of {name}`BoundedInterval`s work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

-- Definition 11.1.1
#check Set.ordConnected_def

/-- Examples 11.1.3 -/
example : (Set.Icc 1 2 : Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro x hx y hy z hxy
  simp at hx hy hxy ⊢
  constructor <;> linarith

example : (Set.Ioo 1 2 : Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro x hx y hy z hxy
  simp at hx hy hxy ⊢
  constructor <;> linarith

example : ¬(Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  push Not
  use 1
  simp
  use 3
  simp
  norm_num
  by_contra h
  have hx: (2.5:ℝ) ∈ Set.Icc (1:ℝ) 3 := by norm_num
  have := h hx
  simp at this
  norm_num at this


example : (.univ :Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro _ _ _ _ _ _
  exact Set.mem_univ _

example : (∅:Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro x hx
  exact False.elim hx

example (x:ℝ) : ({x}: Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro y hy z hz h
  simp at hy hz
  subst y z
  simp

/-- Lemma 11.1.4 / Exercise 11.1.1 -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  match I with
  | Ioo a b => simpa using Metric.isBounded_Ioo a b
  | Icc a b => simpa using Metric.isBounded_Icc a b
  | Ioc a b => simpa using Metric.isBounded_Ioc a b
  | Ico a b => simpa using Metric.isBounded_Ico a b

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  constructor
  . intro h
    obtain ⟨hb, hconn⟩ := h
    rcases X.eq_empty_or_nonempty with hX | hX
    · exact ⟨∅, by simp [hX]⟩
    obtain ⟨hbb, hba⟩ := isBounded_iff_bddBelow_bddAbove.mp hb
    set a := sInf X with ha_def
    set b := sSup X with hb_def
    have hXIcc : X ⊆ Set.Icc a b := fun x hx =>
      ⟨csInf_le hbb hx, le_csSup hba hx⟩
    have hIooX : Set.Ioo a b ⊆ X := by
      intro x ⟨hax, hxb⟩
      obtain ⟨x₁, hx₁, hx₁x⟩ := exists_lt_of_csInf_lt hX hax
      obtain ⟨x₂, hx₂, hxx₂⟩ := exists_lt_of_lt_csSup hX hxb
      exact hconn.out' hx₁ hx₂ ⟨le_of_lt hx₁x, le_of_lt hxx₂⟩
    by_cases haX : a ∈ X
    · by_cases hbX : b ∈ X
      · refine ⟨Icc a b, ?_⟩
        apply Set.eq_of_subset_of_subset hXIcc
        exact hconn.out' haX hbX
      · refine ⟨Ico a b, ?_⟩
        apply Set.eq_of_subset_of_subset
        · intro x hx
          exact ⟨(hXIcc hx).1, lt_of_le_of_ne (hXIcc hx).2 (fun heq => hbX (heq ▸ hx))⟩
        · rintro x ⟨hax, hxb⟩
          rcases eq_or_lt_of_le hax with rfl | hax
          · exact haX
          · exact hIooX ⟨hax, hxb⟩
    · by_cases hbX : b ∈ X
      · refine ⟨Ioc a b, ?_⟩
        apply Set.eq_of_subset_of_subset
        · intro x hx
          exact ⟨lt_of_le_of_ne (hXIcc hx).1 (fun heq => haX (heq ▸ hx)), (hXIcc hx).2⟩
        · rintro x ⟨hax, hxb⟩
          rcases eq_or_lt_of_le hxb with rfl | hxb
          · exact hbX
          · exact hIooX ⟨hax, hxb⟩
      · refine ⟨Ioo a b, ?_⟩
        apply Set.eq_of_subset_of_subset
        · intro x hx
          refine ⟨lt_of_le_of_ne (hXIcc hx).1 (fun heq => haX (heq ▸ hx)),
                  lt_of_le_of_ne (hXIcc hx).2 (fun heq => hbX (heq ▸ hx))⟩
        · exact hIooX
  . intro h
    obtain ⟨I, rfl⟩ := h
    constructor
    . apply Bornology.IsBounded.of_boundedInterval I
    . match I with
      | Ioo a b => simp; exact Set.ordConnected_Ioo
      | Icc a b => simp; exact Set.ordConnected_Icc
      | Ioc a b => simp; exact Set.ordConnected_Ioc
      | Ico a b => simp; exact Set.ordConnected_Ico

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  have ⟨hib, hic⟩ := (BoundedInterval.ordConnected_iff I).mpr ⟨I, rfl⟩
  have ⟨hjb, hjc⟩ := (BoundedInterval.ordConnected_iff J).mpr ⟨J, rfl⟩
  have hijb : Bornology.IsBounded (I.toSet ∩ J.toSet) := by
    rw [isBounded_iff_bddBelow_bddAbove] at hib hjb ⊢
    constructor
    . obtain ⟨M, hM⟩ := hib.1
      obtain ⟨N, hN⟩ := hjb.1
      use max M N
      intro x hx
      simp at hx
      exact max_le (hM hx.1) (hN hx.2)
    . obtain ⟨M, hM⟩ := hib.2
      obtain ⟨N, hN⟩ := hjb.2
      use min M N
      intro x hx
      simp at hx
      exact le_min (hM hx.1) (hN hx.2)
  have hijc : (I.toSet ∩ J.toSet).OrdConnected := by exact Set.OrdConnected.inter'
  exact (BoundedInterval.ordConnected_iff _).mp ⟨hijb, hijc⟩

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (BoundedInterval.inter I J).choose_spec.symm

example :
  (Icc 2 4 ∩ Icc 4 6) = (Icc 4 4 : Set ℝ) := by
  simp
  ext x
  simp
  constructor
  . intro h
    linarith
  . intro h
    subst x
    norm_num

example : Set.Icc 2 4 ∩ Set.Icc 4 6 = Set.Icc 4 4 := by
  ext x
  simp only [Nat.reduceLeDiff, Set.Icc_inter_Icc_eq_singleton, Set.mem_singleton_iff, Set.Icc_self]

-- note for BoundedIntervals this is not provable
-- example : Icc 2 4 ∩ Icc 4 6 = Icc 4 4, because we don't have extensionality for BoundedIntervals

instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

instance BoundedInterval.instTrans : IsTrans BoundedInterval (· ⊆ ·) where
  trans I J K hIJ hJK := by grind [subset_iff]

@[simp]
theorem BoundedInterval.mem_inter (I J: BoundedInterval) (x:ℝ) :
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J := by simp [mem_iff]

abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

example : |Icc 3 5|ₗ = 2 := by simp [length, a, b]; norm_num

example : |Ioo 3 5|ₗ = 2 := by simp [length, a, b]; norm_num

example : |Icc 5 5|ₗ = 0 := by simp [length, a, b]

theorem BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ |I|ₗ := by
  simp

theorem BoundedInterval.empty_of_lt {I: BoundedInterval} (h: I.b < I.a) : (I:Set ℝ) = ∅ := by
  cases I with
  | Ioo _ _ => simp [le_of_lt h]
  | Icc _ _ => simp [h]
  | Ioc _ _ => simp [le_of_lt h]
  | Ico _ _ => simp [le_of_lt h]

theorem BoundedInterval.length_of_empty {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : |I|ₗ = 0 := by
  simp [length, BoundedInterval.a, BoundedInterval.b]
  cases I with
  | Ioo a b =>
    rw [set_Ioo, Set.Ioo_eq_empty_iff, not_lt] at hI
    exact hI
  | Icc a b =>
    rw [set_Icc, Set.Icc_eq_empty_iff, not_le] at hI
    exact hI.le
  | Ioc a b =>
    rw [set_Ioc, Set.Ioc_eq_empty_iff, not_lt] at hI
    exact hI
  | Ico a b =>
    rw [set_Ico, Set.Ico_eq_empty_iff, not_lt] at hI
    exact hI

theorem BoundedInterval.length_of_subsingleton {I: BoundedInterval} : Subsingleton (I:Set ℝ) ↔ |I|ₗ = 0 := by
  constructor
  . intro h
    rw [Set.subsingleton_coe] at h
    suffices hba : I.b ≤ I.a by simp [length, sub_nonpos.mpr hba]
    by_contra hba
    push_neg at hba
    apply absurd h
    rw [Set.not_subsingleton_iff]
    match I with
    | Ioo a b =>
      refine ⟨(2 * a + b) / 3, ?_, (a + 2 * b) / 3, ?_, ?_⟩
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; constructor <;> linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; constructor <;> linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba; intro heq; linarith
    | Icc a b =>
      refine ⟨a, ?_, b, ?_, ?_⟩
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba; intro heq; linarith
    | Ioc a b =>
      refine ⟨(a + b) / 2, ?_, b, ?_, ?_⟩
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; constructor <;> linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba; intro heq; linarith
    | Ico a b =>
      refine ⟨a, ?_, (a + b) / 2, ?_, ?_⟩
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba ⊢; constructor <;> linarith
      · simp [BoundedInterval.a, BoundedInterval.b] at hba; intro heq; linarith
  . intro h
    simp at h
    constructor
    intro x y
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    suffices x = y by simp [this]
    simp [BoundedInterval.a, BoundedInterval.b] at h
    match I with
    | Ioo a b =>
      simp at hx hy; linarith
    | Icc a b =>
      simp at hx hy; linarith
    | Ioc a b =>
      simp at hx hy; linarith
    | Ico a b =>
      simp at hx hy; linarith


theorem BoundedInterval.dist_le_length {I:BoundedInterval} {x y:ℝ} (hx: x ∈ I) (hy: y ∈ I) : |x - y| ≤ |I|ₗ := by
  apply subset_Icc I at hx; apply subset_Icc I at hy; simp_all [mem_iff, abs_le']; grind

abbrev BoundedInterval.joins (K I J: BoundedInterval) : Prop := (I:Set ℝ) ∩ (J:Set ℝ) = ∅
  ∧ (K:Set ℝ) = (I:Set ℝ) ∪ (J:Set ℝ) ∧ |K|ₗ = |I|ₗ + |J|ₗ

theorem BoundedInterval.join_Icc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Icc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Icc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins (Icc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ioc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins (Ioc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins (Ioc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ico_Icc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Ico a b) (Icc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ico_Ico {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins (Ico a b) (Ico b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioo_Icc {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins (Ioo a b) (Icc b c) := by
  simp_all [joins, le_of_lt hab]; grind

theorem BoundedInterval.join_Ioo_Ico {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins (Ioo a b) (Ico b c) := by
  simp_all [joins, le_of_lt hab]; grind

@[ext]
structure Partition (I: BoundedInterval) where
  intervals : Finset BoundedInterval
  exists_unique (x:ℝ) (hx : x ∈ I) : ∃! J, J ∈ intervals ∧ x ∈ J
  contains (J : BoundedInterval) (hJ : J ∈ intervals) : J ⊆ I

#check Partition.mk

instance Partition.instMembership (I: BoundedInterval) : Membership BoundedInterval (Partition I) where
  mem P J := J ∈ P.intervals

theorem Partition.mem_intervals_iff {I: BoundedInterval} (P: Partition I) (J: BoundedInterval) :
  J ∈ P ↔ J ∈ P.intervals := Iff.rfl

instance Partition.instBot (I: BoundedInterval) : Bot (Partition I) where
  bot := {
    intervals := {I}
    exists_unique x hx := by apply ExistsUnique.intro I <;> grind
    contains := by grind [subset_iff]
    }

@[simp]
theorem Partition.intervals_of_bot (I:BoundedInterval) : (⊥:Partition I).intervals = {I} := by
  rfl

noncomputable abbrev Partition.join {I J K:BoundedInterval} (P: Partition I) (Q: Partition J) (h: K.joins I J) : Partition K
:=
{
  intervals := P.intervals ∪ Q.intervals
  exists_unique x hx := by
    have := congr(x ∈ $(h.1))
    simp [mem_iff, h.2] at hx; obtain hx | hx := hx
    . choose L _ _ using (P.exists_unique _ hx).exists
      apply ExistsUnique.intro L (by grind)
      intro K ⟨hK, hxK⟩; simp at hK; obtain _ | hKQ := hK
      map_tacs [apply (P.exists_unique _ hx).unique; apply (K.subset_iff _).mp (Q.contains _ hKQ) at hxK]
      all_goals grind
    choose L hLQ hxL using (Q.exists_unique _ hx).exists
    apply ExistsUnique.intro L (by grind)
    intro K ⟨hK, hxK⟩; simp at hK; obtain hKP | _ := hK
    map_tacs [apply (K.subset_iff _).mp (P.contains _ hKP) at hxK; apply (Q.exists_unique _ hx).unique]
    all_goals grind
  contains L hL := by
    simp at hL; obtain hLP | hLQ := hL
    . apply (P.contains _ hLP).trans; simp [h, subset_iff]
    apply (Q.contains _ hLQ).trans; simp [h, subset_iff]
}

@[simp]
theorem Partition.intervals_of_join {I J K:BoundedInterval} {h:K.joins I J} (P: Partition I) (Q: Partition J) : (P.join Q h).intervals = P.intervals ∪ Q.intervals := by
  simp

noncomputable abbrev Partition.add_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals ∪ {∅}
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by aesop)
    intro K ⟨ hK, _ ⟩; simp at hK; obtain rfl | hK := hK
    · simp_all [mem_iff]
    apply (P.exists_unique _ hx).unique <;> grind
  contains L hL := by
    simp at hL; obtain rfl | hL := hL
    · simp [subset_iff]
    exact P.contains _ hL
}

open Classical in
noncomputable abbrev Partition.remove_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals.filter (fun J ↦ (J:Set ℝ).Nonempty)
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by grind [mem_iff, Set.nonempty_of_mem])
    intro K ⟨ hK, _ ⟩; simp at hK
    apply (P.exists_unique _ hx).unique <;> grind
  contains _ _ := P.contains _ (by grind)
}

@[simp]
theorem Partition.intervals_of_add_empty (I: BoundedInterval) (P: Partition I) : (P.add_empty).intervals = P.intervals ∪ {∅} := by
  simp

example : ∃ P:Partition (Icc 1 8),
  P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8, ∅} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num) )
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num) )
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num) )
  use P5.add_empty; simp_all; aesop

example : ∃ P:Partition (Icc 1 8), P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8} := by
  use {
    intervals := {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8}
    exists_unique x hx := by
      simp [mem_iff] at hx
      obtain ⟨hx1, hx8⟩ := hx
      -- pick the interval containing x based on its position
      rcases lt_or_eq_of_le hx1 with hx1 | hx1
      · rcases lt_or_ge x 3 with hx3 | hx3
        · -- x ∈ Ioo 1 3
          refine ExistsUnique.intro (Ioo 1 3) ⟨by simp, by simp [mem_iff]; exact ⟨hx1, hx3⟩⟩ ?_
          rintro J ⟨hJmem, hJx⟩
          simp at hJmem
          rcases hJmem with rfl | rfl | rfl | rfl | rfl <;>
            simp [mem_iff] at hJx <;> first | rfl | linarith
        · rcases lt_or_eq_of_le hx3 with hx3 | hx3
          · rcases lt_or_ge x 5 with hx5 | hx5
            · -- x ∈ Ico 3 5
              refine ExistsUnique.intro (Ico 3 5) ⟨by simp, by simp [mem_iff]; exact ⟨hx3.le, hx5⟩⟩ ?_
              rintro J ⟨hJmem, hJx⟩
              simp at hJmem
              rcases hJmem with rfl | rfl | rfl | rfl | rfl <;>
                simp [mem_iff] at hJx <;> first | rfl | linarith
            · rcases lt_or_eq_of_le hx5 with hx5 | hx5
              · -- x ∈ Ioc 5 8
                refine ExistsUnique.intro (Ioc 5 8) ⟨by simp, by simp [mem_iff]; exact ⟨hx5, hx8⟩⟩ ?_
                rintro J ⟨hJmem, hJx⟩
                simp at hJmem
                rcases hJmem with rfl | rfl | rfl | rfl | rfl <;>
                  simp [mem_iff] at hJx <;> first | rfl | linarith
              · -- x = 5
                subst hx5
                refine ExistsUnique.intro (Icc 5 5) ⟨by simp, by simp [mem_iff]⟩ ?_
                rintro J ⟨hJmem, hJx⟩
                simp at hJmem
                rcases hJmem with rfl | rfl | rfl | rfl | rfl <;>
                  simp [mem_iff] at hJx <;> first | rfl | linarith
          · -- x = 3
            subst hx3
            refine ExistsUnique.intro (Ico 3 5) ⟨by simp, by simp [mem_iff]; norm_num⟩ ?_
            rintro J ⟨hJmem, hJx⟩
            simp at hJmem
            rcases hJmem with rfl | rfl | rfl | rfl | rfl <;>
              simp [mem_iff] at hJx <;> first | rfl | linarith
      · -- x = 1
        subst hx1
        refine ExistsUnique.intro (Icc 1 1) ⟨by simp, by simp [mem_iff]⟩ ?_
        rintro J ⟨hJmem, hJx⟩
        simp at hJmem
        rcases hJmem with rfl | rfl | rfl | rfl | rfl <;>
          simp [mem_iff] at hJx; rfl
    contains J hJ := by
      simp at hJ
      cases hJ with
      | inl hJ => subst J; rw [subset_iff]; simp;
      | inr hJ => cases hJ with
        | inl hJ => subst J; rw [subset_iff]; simp; intro x hx; simp at hx ⊢; constructor <;> linarith
        | inr hJ => cases hJ with
          | inl hJ => subst J; rw [subset_iff]; simp; intro x hx; simp at hx ⊢; constructor <;> linarith
          | inr hJ => cases hJ with
            | inl hJ => subst J; rw [subset_iff]; simp; norm_num
            | inr hJ => subst J; rw [subset_iff]; simp; intro x hx; simp at hx ⊢; constructor <;> linarith
  }

example : ¬∃ P:Partition (Icc 1 5), P.intervals = {Icc 1 4, Icc 3 5} := by
  simp
  intro P
  by_contra h
  have hmem : (3:ℝ) ∈ (Icc (1:ℝ) 5 : BoundedInterval) := by simp [mem_iff]; norm_num
  obtain ⟨J, ⟨hJP, hJ3⟩, huniq⟩ := P.exists_unique 3 hmem
  have h1 : Icc (1:ℝ) 4 ∈ P.intervals := by rw [h]; simp
  have h2 : Icc (3:ℝ) 5 ∈ P.intervals := by rw [h]; simp
  have h13 : (3:ℝ) ∈ (Icc (1:ℝ) 4 : BoundedInterval) := by simp [mem_iff]; norm_num
  have h23 : (3:ℝ) ∈ (Icc (3:ℝ) 5 : BoundedInterval) := by simp [mem_iff]; norm_num
  have e1 := huniq (Icc 1 4) ⟨h1, h13⟩
  have e2 := huniq (Icc 3 5) ⟨h2, h23⟩
  rw [← e2] at e1
  exact absurd e1 (by intro heq; injection heq with h1 _; norm_num at h1)

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 1 3, Ioo 3 5} := by
  simp
  intro P
  by_contra h
  have hmem : (3:ℝ) ∈ (Ioo (1:ℝ) 5 : BoundedInterval) := by simp [mem_iff]; norm_num
  obtain ⟨J, ⟨hJP, hJ3⟩, _⟩ := P.exists_unique 3 hmem
  rw [h] at hJP
  simp at hJP
  rcases hJP with rfl | rfl
  · simp [mem_iff] at hJ3
  · simp [mem_iff] at hJ3

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 0 3, Ico 3 5} := by
  simp
  intro P
  by_contra h
  have hsub := P.contains (Ioo 0 3) (by rw [h]; simp)
  rw [subset_iff] at hsub
  have hmem : (1/2 : ℝ) ∈ ((Ioo (0:ℝ) 3 : BoundedInterval) : Set ℝ) := by simp; norm_num
  have := hsub hmem
  simp at this; linarith

/-- Exercise 11.1.3.  The exercise only claims c ≤ b, but the stronger claim c < b is true and useful. -/
theorem Partition.exist_right {I: BoundedInterval} (hI: I.a < I.b) (hI': I.b ∉ I)
  {P: Partition I}
  : ∃ c ∈ Set.Ico I.a I.b, Ioo c I.b ∈ P ∨ Ico c I.b ∈ P := by
  by_contra h
  push Not at h
  have hIform : I = Ioo I.a I.b ∨ I = Ico I.a I.b := by
    cases I with
    | Ioo a b => left; rfl
    | Ico a b => right; rfl
    | Icc a b => exfalso; apply hI'; simp [mem_iff]; exact le_of_lt hI
    | Ioc a b => exfalso; apply hI'; simp [mem_iff]; exact hI
  have hmem_of : ∀ y, I.a < y → y < I.b → y ∈ I := by
    intro y hy1 hy2
    rcases hIform with hf | hf <;> rw [hf] <;> simp [mem_iff]
    · exact ⟨hy1, hy2⟩
    · exact ⟨hy1.le, hy2⟩
  classical
  -- helpers: containment in J via the Ioo interior, and Icc-bracketing in I
  have mem_J_of_Ioo : ∀ (K:BoundedInterval) z, K.a < z → z < K.b → z ∈ K := fun K z h1 h2 =>
    K.Ioo_subset _ (by rw [mem_iff]; exact ⟨h1, h2⟩)
  have in_I_Icc : ∀ z, z ∈ I → I.a ≤ z ∧ z ≤ I.b := fun z hz => by
    have := (I.subset_iff _).mp I.subset_Icc hz; simpa [mem_iff] using this
  set S : Finset BoundedInterval :=
    P.intervals.filter (fun J => (J:Set ℝ).Nonempty) with hSdef
  have hSne : S.Nonempty := by
    have hmid : (I.a + I.b) / 2 ∈ I := hmem_of _ (by linarith) (by linarith)
    obtain ⟨J, ⟨hJP, hJmid⟩, _⟩ := P.exists_unique _ hmid
    exact ⟨J, by simp [hSdef, hJP]; exact ⟨_, hJmid⟩⟩
  obtain ⟨J, hJS, hJmax⟩ := S.exists_max_image (fun J => J.b) hSne
  rw [hSdef, Finset.mem_filter] at hJS
  obtain ⟨hJP, y₀, hy₀⟩ := hJS
  have hJsub : J ⊆ I := P.contains _ hJP
  have hy₀I : y₀ ∈ I := (J.subset_iff _).mp hJsub hy₀
  have hy₀J : J.a ≤ y₀ ∧ y₀ ≤ J.b := by
    have := (J.subset_iff _).mp J.subset_Icc hy₀; simpa [mem_iff] using this
  have hy₀Icc := in_I_Icc _ hy₀I
  have hy₀_lt : y₀ < I.b := hy₀Icc.2.lt_of_ne fun heq => hI' (heq ▸ hy₀I)
  have hJb_le_Ib : J.b ≤ I.b := by
    by_contra hcontra
    push_neg at hcontra
    set z := (I.b + J.b) / 2 with hzdef
    have hzJa : J.a < z := by simp [hzdef]; linarith [hy₀J.1]
    have hzJb : z < J.b := by simp [hzdef]; linarith
    have hzI := in_I_Icc _ ((J.subset_iff _).mp hJsub (mem_J_of_Ioo _ _ hzJa hzJb))
    linarith [hzI.2]
  have hJb_eq : J.b = I.b := by
    refine le_antisymm hJb_le_Ib ?_
    by_contra hcontra
    push_neg at hcontra
    set y₁ := (J.b + I.b) / 2 with hy₁def
    have hy₁_in : y₁ ∈ I :=
      hmem_of _ (by linarith [hy₀Icc.1, hy₀J.1, hy₀J.2]) (by simp [hy₁def]; linarith)
    obtain ⟨J', ⟨hJ'P, hJ'mem⟩, _⟩ := P.exists_unique _ hy₁_in
    have hJ'S : J' ∈ S := by simp [hSdef, hJ'P]; exact ⟨_, hJ'mem⟩
    have hJ'b : y₁ ≤ J'.b := by
      have := (J'.subset_iff _).mp J'.subset_Icc hJ'mem; simpa [mem_iff] using this.2
    linarith [hJmax J' hJ'S, show J.b < y₁ by simp [hy₁def]; linarith]
  have hI_b_notinJ : I.b ∉ J := fun hbJ => hI' ((J.subset_iff _).mp hJsub hbJ)
  have hJ_a_lt_b : J.a < J.b := hy₀J.1.trans_lt (hJb_eq.symm ▸ hy₀_lt)
  -- J.b = I.b and I.b ∉ J force J to be right-open
  have hJform : J = Ioo J.a I.b ∨ J = Ico J.a I.b := by
    rcases J with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
    · exact .inl (by show Ioo a b = Ioo a I.b; rw [show b = I.b from hJb_eq])
    · exfalso; apply hI_b_notinJ; rw [mem_iff]
      exact ⟨hJb_eq ▸ hJ_a_lt_b.le, hJb_eq.ge⟩
    · exfalso; apply hI_b_notinJ; rw [mem_iff]
      exact ⟨hJb_eq ▸ hJ_a_lt_b, hJb_eq.ge⟩
    · exact .inr (by show Ico a b = Ico a I.b; rw [show b = I.b from hJb_eq])
  have hJ_a_ge : I.a ≤ J.a := by
    by_contra hcontra; push_neg at hcontra
    set z := (J.a + I.a) / 2 with hzdef
    have hz_lt_Ia : z < I.a := by simp [hzdef]; linarith
    have hz_in_J : z ∈ J :=
      mem_J_of_Ioo J z (by simp [hzdef]; linarith)
        (by rw [hJb_eq]; simp [hzdef]; linarith)
    linarith [(in_I_Icc _ ((J.subset_iff _).mp hJsub hz_in_J)).1]
  obtain ⟨h1, h2⟩ := h J.a ⟨hJ_a_ge, hJb_eq ▸ hJ_a_lt_b⟩
  rcases hJform with hf | hf
  · exact h1 (hf ▸ hJP)
  · exact h2 (hf ▸ hJP)

/-- Theorem 11.1.13 (Length is finitely additive). -/
theorem Partition.sum_of_length  (I: BoundedInterval) (P: Partition I) :
  ∑ J ∈ P.intervals, |J|ₗ = |I|ₗ := by
  -- This proof is written to follow the structure of the original text.
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  . rw [Finset.card_eq_zero] at hcard
    have : (I:Set ℝ) = ∅ := by
      have := P.exists_unique
      by_contra h
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
      obtain ⟨J, ⟨hJP, _⟩, _⟩ := this x hx
      rw [hcard] at hJP
      exact Finset.notMem_empty _ hJP
    grind [length_of_empty]
  -- the proof in the book treats the n=1 case separately, but this is unnecessary
  by_cases h : Subsingleton (I:Set ℝ)
  . have (J: BoundedInterval) (hJ: J ∈ P) : Subsingleton (J:Set ℝ) := by
      have : J ⊆ I := P.contains _ hJ
      rw [subset_iff] at this
      rw [Set.subsingleton_coe] at h ⊢
      exact Set.Subsingleton.anti h this
    simp_rw [length_of_subsingleton] at *
    convert Finset.sum_eq_zero this
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := by
          rcases K with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
          · -- Ioo: pick midpoint of (a, I.b), must equal I.b → contradiction
            rw [show ((Ioo a b:BoundedInterval):Set ℝ) = Set.Ioo a b from rfl,
                Set.eq_singleton_iff_unique_mem] at hbK
            obtain ⟨⟨hlt1, hlt2⟩, huniq⟩ := hbK
            have := huniq ((a + I.b)/2) ⟨by linarith, by linarith⟩
            linarith
          · -- Icc a b = {I.b} ↔ a = I.b ∧ b = I.b
            simp at hbK; obtain ⟨rfl, rfl⟩ := hbK; rfl
          · rw [show ((Ioc a b:BoundedInterval):Set ℝ) = Set.Ioc a b from rfl,
                Set.eq_singleton_iff_unique_mem] at hbK
            obtain ⟨⟨hlt1, hle2⟩, huniq⟩ := hbK
            have := huniq ((a + I.b)/2) ⟨by linarith, by linarith⟩
            linarith
          · rw [show ((Ico a b:BoundedInterval):Set ℝ) = Set.Ico a b from rfl,
                Set.eq_singleton_iff_unique_mem] at hbK
            obtain ⟨⟨hle1, hlt2⟩, huniq⟩ := hbK
            have := huniq ((I.b + b)/2) ⟨by linarith, by linarith⟩
            linarith
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc <;> order
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
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc]
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      grind [join_Ioo_Ico]
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo]
      use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico]
  obtain ⟨ K, L, hK, ⟨ h1, h2, h3 ⟩ ⟩ := this
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
  rw [h3, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
  apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.1.14 (Finer and coarser partitions) -/
instance Partition.instLE (I: BoundedInterval) : LE (Partition I) where
  le P P' := ∀ J ∈ P'.intervals, ∃ K ∈ P, J ⊆ K

instance Partition.instPreOrder (I: BoundedInterval) : Preorder (Partition I) where
  le_refl P := by
    intro J hJ
    use J, hJ
    solve_by_elim
  le_trans P P' P'' hP hP' := by
    intro J hJ
    obtain ⟨K, hKP', hJK⟩ := hP' J hJ
    obtain ⟨L, hLP, hKL⟩ := hP K hKP'
    use L, hLP
    solve_by_elim

instance Partition.instOrderBot (I: BoundedInterval) : OrderBot (Partition I) where
  bot_le := by
    intro P J hJ
    refine ⟨I, ?_, P.contains _ hJ⟩
    show I ∈ (⊥:Partition I).intervals
    rw [intervals_of_bot]; exact Finset.mem_singleton.mpr rfl

/-- Example 11.1.15 -/
noncomputable def P : Partition (Icc 1 4) := {
  intervals := {Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 4}
  exists_unique x hx := by
    simp [mem_iff] at hx
    obtain ⟨hx1, hx4⟩ := hx
    rcases lt_or_ge x 2 with hx2 | hx2
    · refine ExistsUnique.intro (Ico 1 2) ⟨by simp, by simp [mem_iff]; exact ⟨hx1, hx2⟩⟩ ?_
      rintro J ⟨hJmem, hJx⟩
      simp at hJmem
      rcases hJmem with rfl | rfl | rfl | rfl <;>
        simp [mem_iff] at hJx <;> first | rfl | linarith
    · rcases eq_or_lt_of_le hx2 with hx2 | hx2
      · subst hx2
        refine ExistsUnique.intro (Icc 2 2) ⟨by simp, by simp [mem_iff]⟩ ?_
        rintro J ⟨hJmem, hJx⟩
        simp at hJmem
        rcases hJmem with rfl | rfl | rfl | rfl <;>
          simp [mem_iff] at hJx <;> first | rfl | linarith
      · rcases lt_or_ge x 3 with hx3 | hx3
        · refine ExistsUnique.intro (Ioo 2 3) ⟨by simp, by simp [mem_iff]; exact ⟨hx2, hx3⟩⟩ ?_
          rintro J ⟨hJmem, hJx⟩
          simp at hJmem
          rcases hJmem with rfl | rfl | rfl | rfl <;>
            simp [mem_iff] at hJx <;> first | rfl | linarith
        · refine ExistsUnique.intro (Icc 3 4) ⟨by simp, by simp [mem_iff]; exact ⟨hx3, hx4⟩⟩ ?_
          rintro J ⟨hJmem, hJx⟩
          simp at hJmem
          rcases hJmem with rfl | rfl | rfl | rfl <;>
            simp [mem_iff] at hJx <;> first | rfl | linarith
  contains J hJ := by
    simp at hJ
    rcases hJ with rfl | rfl | rfl | rfl <;>
      rw [subset_iff] <;> intro x hx <;> simp at hx ⊢ <;>
      first | exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
            | exact ⟨by linarith, by linarith⟩
}

noncomputable def P' : Partition (Icc 1 4) := {
  intervals := {Icc 1 2, Ioc 2 4}
  exists_unique x hx := by
    simp [mem_iff] at hx
    obtain ⟨hx1, hx4⟩ := hx
    rcases le_or_gt x 2 with hx2 | hx2
    · refine ExistsUnique.intro (Icc 1 2) ⟨by simp, by simp [mem_iff]; exact ⟨hx1, hx2⟩⟩ ?_
      rintro J ⟨hJmem, hJx⟩
      simp at hJmem
      rcases hJmem with rfl | rfl <;>
        simp [mem_iff] at hJx <;> first | rfl | linarith
    · refine ExistsUnique.intro (Ioc 2 4) ⟨by simp, by simp [mem_iff]; exact ⟨hx2, hx4⟩⟩ ?_
      rintro J ⟨hJmem, hJx⟩
      simp at hJmem
      rcases hJmem with rfl | rfl <;>
        simp [mem_iff] at hJx <;> first | rfl | linarith
  contains J hJ := by
    simp at hJ
    rcases hJ with rfl | rfl <;>
      rw [subset_iff] <;> intro x hx <;> simp at hx ⊢ <;>
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
}

example : P' ≤ P := by
  intro J hJ
  show ∃ K ∈ P'.intervals, J ⊆ K
  simp [P] at hJ
  rcases hJ with rfl | rfl | rfl | rfl
  · exact ⟨Icc 1 2, by simp [P'], by rw [subset_iff]; intro x hx; simp at hx ⊢; exact ⟨hx.1, hx.2.le⟩⟩
  · exact ⟨Icc 1 2, by simp [P'], by rw [subset_iff]; intro x hx; simp at hx ⊢; exact ⟨by linarith, by linarith⟩⟩
  · exact ⟨Ioc 2 4, by simp [P'], by rw [subset_iff]; intro x hx; simp at hx ⊢; exact ⟨hx.1, by linarith [hx.2]⟩⟩
  · exact ⟨Ioc 2 4, by simp [P'], by rw [subset_iff]; intro x hx; simp at hx ⊢; exact ⟨by linarith [hx.1], hx.2⟩⟩

/-- Definition 11.1.16 (Common refinement)-/
noncomputable instance Partition.instMax (I: BoundedInterval) : Max (Partition I) where
  max P P' := {
    intervals := Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    exists_unique x hx := by
      choose J _ _ using P.exists_unique _ hx
      choose K _ _ using P'.exists_unique _ hx
      simp at *
      apply ExistsUnique.intro (J ∩ K)
      . simp_all; grind
      simp; grind [mem_inter]
    contains L hL := by
      simp at hL; obtain ⟨ J, hJ, K, hK, rfl ⟩ := hL
      apply P.contains at hJ; apply P'.contains at hK
      simp [subset_iff] at *; grind [Set.inter_subset_left]
    }


/-- Example 11.1.17.  Stated at the set-level on the third conjunct because
{name}`BoundedInterval.inter` is defined via {name}`Classical.choose` and does not commit to
a canonical constructor for the result. -/
example : ∃ P P' : Partition (Icc 1 4),
    P.intervals = {Ico 1 3, Icc 3 4} ∧
    P'.intervals = {Icc 1 2, Ioc 2 4} ∧
    (P' ⊔ P).intervals.image toSet =
      {Set.Icc 1 2, Set.Ioo 2 3, Set.Icc 3 4, ∅} := by
  set P : Partition (Icc 1 4) :=
    (⊥ : Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 4))
      (join_Ico_Icc (by norm_num) (by norm_num)) with hP
  set P' : Partition (Icc 1 4) :=
    (⊥ : Partition (Icc 1 2)).join (⊥ : Partition (Ioc 2 4))
      (join_Icc_Ioc (by norm_num) (by norm_num)) with hP'
  refine ⟨P, P', ?_, ?_, ?_⟩
  · simp [hP, Partition.intervals_of_join]
  · simp [hP', Partition.intervals_of_join]
  · simp [hP, hP', Partition.intervals_of_join, Max.max, BoundedInterval.inter_eq]
    have h1 : Set.Icc (1:ℝ) 2 ∩ Set.Icc 3 4 = ∅ := by
      ext x; simp; intros; linarith
    have h2 : Set.Icc (1:ℝ) 2 ∩ Set.Ico 1 3 = Set.Icc 1 2 := by
      ext x; constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; refine ⟨⟨h1, h2⟩, h1, ?_⟩; linarith
    have h3 : Set.Ioc (2:ℝ) 4 ∩ Set.Ico 1 3 = Set.Ioo 2 3 := by
      ext x; simp; constructor
      · rintro ⟨⟨h1, _⟩, _, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; refine ⟨⟨h1, ?_⟩, ?_, h2⟩ <;> linarith
    have h4 : Set.Ioc (2:ℝ) 4 ∩ Set.Icc 3 4 = Set.Icc 3 4 := by
      ext x; simp; intros; constructor <;> linarith
    rw [h1, h2, h3, h4]
    ext s; simp; tauto

/-- Lemma 11.1.8 / Exercise 11.1.4 -/
theorem BoundedInterval.le_max' {I: BoundedInterval} (P P': Partition I) :
  P ≤ P ⊔ P' := by
  intro J hJ
  simp [Max.max] at hJ
  obtain ⟨b, hb, a, ha, rfl⟩ := hJ
  use b, hb
  rw [subset_iff, inter_eq]
  exact Set.inter_subset_left

/-- Commutativity at the {lit}`≤` level.  We cannot prove {lit}`P ⊔ P' = P' ⊔ P` as
{name}`Partition`s because {name}`BoundedInterval.inter` is {name}`Classical.choose`-based
and does not commit to a canonical constructor — so {lit}`a ∩ b` and {lit}`b ∩ a` are
equal as sets but not as {name}`BoundedInterval`s, hence the underlying
{name}`intervals` Finsets differ structurally. -/
theorem Partition.sup_comm_le {I: BoundedInterval} (P P': Partition I) :
  P ⊔ P' ≤ P' ⊔ P := by
  intro J hJ
  change J ∈ Finset.image₂ _ P'.intervals P.intervals at hJ
  simp at hJ
  obtain ⟨b, hb, a, ha, rfl⟩ := hJ
  refine ⟨(a ∩ b : BoundedInterval), ?_, ?_⟩
  · change (a ∩ b : BoundedInterval) ∈ Finset.image₂ _ P.intervals P'.intervals
    simp; exact ⟨a, ha, b, hb, rfl⟩
  · rw [subset_iff, inter_eq, inter_eq, Set.inter_comm]

theorem BoundedInterval.le_max {I: BoundedInterval} (P P': Partition I) :
  P ≤ P ⊔ P' ∧ P' ≤ P ⊔ P' := by
  refine ⟨BoundedInterval.le_max' P P', ?_⟩
  exact (BoundedInterval.le_max' P' P).trans (Partition.sup_comm_le P' P)

/-- Not from textbook: the reverse inclusion -/
theorem BoundedInterval.max_le_iff (I: BoundedInterval) {P P' P'': Partition I}
  {hP : P ≤ P''} {hP': P' ≤ P''} : P ⊔ P' ≤ P''  := by
  intro J hJ
  obtain ⟨a, ha⟩ := hP J hJ
  obtain ⟨b, hb⟩ := hP' J hJ
  use a ∩ b
  constructor
  . rw [Partition.mem_intervals_iff]
    simp [Max.max]
    exact ⟨a, ha.1, b, hb.1, rfl⟩
  . rw [subset_iff, inter_eq]
    have ha' := ha.2
    have hb' := hb.2
    rw [subset_iff] at ha' hb'
    exact Set.subset_inter ha' hb'

end Chapter11
