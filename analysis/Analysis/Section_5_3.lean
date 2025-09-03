import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
  rw [Sequence.equiv_def] at *
  intro ε hε
  specialize hab (ε / 2) (by linarith)
  specialize hbc (ε / 2) (by linarith)
  simp [Rat.eventuallyClose_iff] at *
  obtain ⟨N1, hN1⟩ := hab
  obtain ⟨N2, hN2⟩ := hbc
  use max N1 N2
  intro n hn
  specialize hN1 n (by aesop)
  specialize hN2 n (by aesop)
  calc
    |a n - c n| = |(a n - b n) + (b n - c n)| := by ring_nf
    _ ≤ |a n - b n| + |b n - c n| := by exact abs_add _ _
    _ ≤ |a n - b n| + ε / 2 := by gcongr
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring_nf

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
    refl := by
      intro x
      rw [Sequence.equiv_def]
      intro ε hε
      rw [Rat.eventuallyClose_iff]
      simp
      use 0
      intro n hn
      exact le_of_lt hε
    symm := Sequence.equiv_symm.mp
    trans := Sequence.equiv_trans
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  intro ε hε
  rw [Rat.eventuallySteady_def]
  use 0
  simp_all
  rw [Rat.Steady]
  intro n hn m hm
  simp_all
  rw [Rat.Close]
  simp only [sub_self, abs_zero]
  exact le_of_lt hε

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  obtain ⟨a, rfl⟩ := Quot.exists_rep x
  let f := fun n ↦ a n
  have hf : (f:Sequence).IsCauchy := by
    simp only [f, CauchySequence.coe_to_sequence]
    exact a.cauchy
  use f
  constructor
  . exact hf
  . rw [LIM_def hf]
    apply Quotient.sound
    rw [CauchySequence.equiv_iff, Sequence.equiv_iff]
    simp [f]
    intro ε hε
    use 0
    intro n hn
    exact le_of_lt hε

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

-- why so slow
set_option maxHeartbeats 2000000 in
/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  obtain ⟨M1, hM1, haBound⟩ := isBounded_of_isCauchy ha
  obtain ⟨M2, hM2, hbBound⟩ := isBounded_of_isCauchy hb
  simp at hM1 hM2
  by_cases hM1': 0 = M1
  . subst M1
    rw [boundedBy_def] at haBound
    simp at haBound
    rw [coe]
    simp [Section_4_3.dist_eq]
    intro ε hε
    use 0
    intro j hj k hk
    have haj := haBound j (by norm_cast)
    have hak := haBound k (by norm_cast)
    simp at haj hak
    simp [haj, hak]
    exact le_of_lt hε
  by_cases hM2': 0 = M2
  . -- same as above, todo refactor to lemma
    subst M2
    rw [boundedBy_def] at hbBound
    simp at hbBound
    rw [coe]
    simp [Section_4_3.dist_eq]
    intro ε hε
    use 0
    intro j hj k hk
    have hbj := hbBound j (by norm_cast)
    have hbk := hbBound k (by norm_cast)
    simp at hbj hbk
    simp [hbj, hbk]
    exact le_of_lt hε
  replace hM1 : 0 < M1 := by
    rw [le_iff_lt_or_eq] at hM1
    simp [hM1'] at hM1
    exact hM1
  replace hM2 : 0 < M2 := by
    rw [le_iff_lt_or_eq] at hM2
    simp [hM2'] at hM2
    exact hM2
  rw [coe] at ha hb ⊢
  simp [Section_4_3.dist_eq] at ha hb ⊢

  intro ε hε -- we want pick - ε₁ * M1 + ε₂ * M2 = ε so
  let M := max M1 M2
  specialize ha ((ε / 2) / M) (by positivity)
  specialize hb ((ε / 2) / M) (by positivity)
  have h': ε = ((ε / 2) / M) * M + ((ε / 2) / M) * M := by field_simp; ring
  obtain ⟨N1, h1⟩ := ha
  obtain ⟨N2, h2⟩ := hb
  use max N1 N2
  intro j hj k hk
  specialize h1 j (le_of_max_le_left hj) k (le_of_max_le_left hk)
  specialize h2 j (le_of_max_le_right hj) k (le_of_max_le_right hk)
  rw [←Rat.Close] at h1 h2 ⊢
  rw [h']
  have h'': ((ε / 2) / M) * |b j| + ((ε / 2) / M) * |a k| ≤ ((ε / 2) / M) * M + ((ε / 2) / M) * M := by
    gcongr
    . rw [boundedBy_def] at hbBound
      unfold M
      suffices |b j| ≤ M2 by exact le_trans this (le_max_right _ _)
      exact hbBound j
    . rw [boundedBy_def] at haBound
      unfold M
      suffices |a k| ≤ M1 by exact le_trans this (le_max_left _ _)
      exact haBound k
  apply (Section_4_3.close_mono . h'')
  -- pass arguments explicitly to make it faster
  exact Section_4_3.close_mul_mul'
    (ε:= (ε / 2) / M) (δ:= (ε / 2) / M) (x:= a j) (y := a k)
    (z := b j) (w := b k) h1 h2

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  obtain ⟨M, hM, haBound⟩ := isBounded_of_isCauchy hb
  by_cases hM : M = 0
  . subst M
    rw [boundedBy_def] at haBound
    simp at haBound
    rw [equiv_def] at *
    intro ε hε
    simp [Rat.eventuallyClose_def, Rat.closeSeq_def]
    use 0
    intro n hN _ _ _
    simp [hN]
    specialize haBound n hN
    simp [haBound]
    rw [Rat.Close]
    simp
    exact le_of_lt hε
  rw [equiv_def] at *
  intro ε hε
  specialize haa' (ε / M) (by positivity)
  rw [Rat.eventuallyClose_def] at *
  simp [Rat.closeSeq_def] at *
  simp_all
  obtain ⟨N, hN⟩ := haa'
  use N
  intro n hn hnMN
  lift n to ℕ using hn
  specialize hN n (by linarith) hnMN
  simp_all
  rw [show ε = ε / M * M by field_simp]
  have h' : ε / M * M ≥ ε / M * |b n| := by
    gcongr
    exact haBound n
  apply (Section_4_3.close_mono . h')
  exact Section_4_3.close_mul_right hN

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  constructor
  . repeat rw [Real.ratCast_def]
    intro h
    rw [LIM_eq_LIM (Sequence.IsCauchy.const q) (Sequence.IsCauchy.const r)] at h
    rw [Sequence.equiv_iff] at h
    by_cases h': |q - r| = 0
    . simp at h'
      linarith
    specialize h (|q - r| / 2) (by positivity)
    obtain ⟨N, h⟩ := h
    specialize h N (by rfl)
    . exfalso
      have h'': 0 < |q - r| := by
        have := abs_nonneg (q - r)
        rw [le_iff_lt_or_eq] at this
        cases' this with h h
        . exact h
        . symm at h
          contradiction
      rw [show |q - r| / 2 = |q - r| * (1 / 2) by field_simp] at h
      conv_lhs at h => rw [← mul_one (|q - r|)]
      have := le_of_mul_le_mul_left h h''
      linarith
  . intro h
    rw [h]

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  rw [ratCast_def, ratCast_def]
  rw [LIM_add]
  . have : (fun (x:ℕ) ↦ a) + (fun (x:ℕ) ↦ b) = (fun (x:ℕ) ↦ a + b) := by rfl
    rw [this, ← ratCast_def]
  . exact Sequence.IsCauchy.const a
  . exact Sequence.IsCauchy.const b

/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  rw [ratCast_def, ratCast_def]
  rw [LIM_mul]
  . have : (fun (x:ℕ) ↦ a) * (fun (x:ℕ) ↦ b) = (fun (x:ℕ) ↦ a * b) := by rfl
    rw [this, ← ratCast_def]
  . exact Sequence.IsCauchy.const a
  . exact Sequence.IsCauchy.const b

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

theorem neg_def (x:Real) : -x = ((-1:ℚ):Real) * x := by rfl

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  rw [neg_def]
  rw [ratCast_mul]
  simp

theorem Real.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at ha ⊢
  intro ε hε
  specialize ha ε hε
  obtain ⟨N, hN⟩ := ha
  use N
  intro j hj k hk
  specialize hN j hj k hk
  simp [Section_4_3.dist] at hN ⊢
  rw [abs_sub_comm] at hN
  rw [add_comm]
  have : a k + (- a j) = a k - a j := by ring
  rw [this]
  exact hN

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  rw [LIM_def ha, LIM_def (Real.IsCauchy.neg a ha)]
  convert Quotient.liftOn₂_mk _ _ _ _
  simp
  rw [dif_pos _]
  . ext
    . simp
    . simp
  . simp
    have : (fun (x:ℕ) ↦ -1) * (fun (x:ℕ) ↦ a x) = (fun (x:ℕ) ↦ -(a x)) := by
      funext x
      simp
    rw [this]
    exact IsCauchy.neg a ha

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms

(by sorry)

(by
  intro a
  obtain ⟨a, rfl⟩ := Quot.exists_rep a
  rw [← Real.LIM.zero]
  apply Quotient.sound
  have := Sequence.IsCauchy.const 0
  simp [this] -- why doesn't it simplify
  sorry
)

(by sorry)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by sorry

/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by sorry

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by sorry

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by sorry

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  natCast_succ := by sorry
  intCast_negSucc := by sorry

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by sorry

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by sorry

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by sorry

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by sorry
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by sorry
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by sorry

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by congr; field_simp [ha' m, ha' n]; grind
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx, -Quotient.eq]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  sorry

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  sorry

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by sorry
  mul_inv_cancel := by sorry
  inv_zero := by sorry
  ratCast_def := by sorry
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by sorry

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  sorry

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by sorry

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by sorry

end Chapter5
