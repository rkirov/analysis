import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

namespace Chapter7

open Filter Real EReal

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α':EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n:ℝ)):ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> grind


/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_:0 < 1/(n:ℝ)) <;> try positivity
    rw [show (1:EReal) = (1:ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

private lemma tendsto_rpow_div_nat :
    atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^(1/(n:ℝ))) (nhds 1) :=
  tendsto_rpow_div.comp tendsto_natCast_atTop_atTop

private lemma tendsto_succ_rpow_div :
    atTop.Tendsto (fun n:ℕ ↦ ((n:ℝ)+1)^(1/(n:ℝ))) (nhds 1) := by
  -- Squeeze: n^(1/n) ≤ (n+1)^(1/n) ≤ (2n)^(1/n) = 2^(1/n) · n^(1/n), all → 1
  have h2 : atTop.Tendsto (fun n:ℕ ↦ (2:ℝ)^(1/(n:ℝ))) (nhds 1) := by
    convert (continuous_const_rpow (by norm_num : (2:ℝ) ≠ 0)).continuousAt.tendsto.comp
      tendsto_one_div_atTop_nhds_zero_nat using 1
    ext n; simp
  have hupper : atTop.Tendsto (fun n:ℕ ↦ ((2:ℝ)*(n:ℝ))^(1/(n:ℝ))) (nhds 1) := by
    have : (fun n:ℕ ↦ ((2:ℝ)*(n:ℝ))^(1/(n:ℝ))) =
        (fun n:ℕ ↦ (2:ℝ)^(1/(n:ℝ)) * (n:ℝ)^(1/(n:ℝ))) := by
      ext n; exact mul_rpow (by positivity) (by positivity)
    rw [this]; simpa using h2.mul tendsto_rpow_div_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_rpow_div_nat hupper
  · apply Eventually.of_forall; intro n
    exact rpow_le_rpow (by positivity) (by linarith : (n:ℝ) ≤ n + 1) (by positivity)
  · rw [eventually_atTop]; use 1; intro n hn
    exact rpow_le_rpow (by positivity)
      (by linarith [show (1:ℝ) ≤ n from Nat.one_le_cast.mpr hn]) (by positivity)

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.diverges := by
  use (fun (_:ℕ) ↦ (1:ℝ) : Series)
  refine ⟨?_, diverges_of_nodecay ?_⟩
  · apply tendsto_nhds_of_eventually_eq
    rw [eventually_atTop]; use 0; intro n hn
    simp [show (0:ℤ) ≤ n from hn, one_rpow]
  · intro h
    rw [LinearOrderedAddCommGroup.tendsto_nhds] at h
    obtain ⟨N, hN⟩ := (h 1 (by positivity)).exists_forall_of_atTop
    have := hN (max N 0) (le_max_left _ _)
    simp [show max N 0 ≥ (0:ℤ) from le_max_right _ _] at this

private lemma zeta_2_absConverges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).absConverges := by
  have key : ∀ n:ℤ, (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).abs.seq n =
      (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).seq n := by
    intro n; simp
    split
    · rw [abs_of_nonneg]; apply inv_nonneg.mpr; exact sq_nonneg _
    · simp
  have : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).abs = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series) := by
    ext
    · rfl
    · exact key _
  rw [Series.absConverges, this]; exact Series.zeta_2_converges

private lemma zeta_2_nonzero : ∀ n ≥ (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).m,
    (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).seq n ≠ 0 := by
  intro n hn; simp [show (0:ℤ) ≤ n from hn]
  positivity

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
  use (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series)
  refine ⟨?_, zeta_2_absConverges⟩
  rw [show (atTop : Filter ℤ) = map Nat.cast atTop from Nat.map_cast_int_atTop.symm,
    Filter.tendsto_map'_iff]
  have hsimpl : ((fun n:ℤ ↦ |(fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).seq n|^(1/(n:ℝ))) ∘ Nat.cast) =
      (fun n:ℕ ↦ (1/((n:ℝ)+1)^2)^(1/(n:ℝ))) := by
    ext n; simp; rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  rw [hsimpl]
  -- (1/(n+1)^2)^(1/n) = ((n+1)^(1/n))⁻¹ ^ 2 → 1⁻¹ ^ 2 = 1
  suffices h : atTop.Tendsto (fun n:ℕ ↦ (((n:ℝ)+1)^(1/(n:ℝ)))⁻¹ ^ 2) (nhds 1) by
    apply h.congr; intro n
    simp only [sq, one_div, _root_.mul_inv]
    rw [← inv_rpow (by positivity : (0:ℝ) ≤ (n:ℝ)+1),
      mul_rpow (by positivity) (by positivity)]
  convert (tendsto_succ_rpow_div.inv₀ (by norm_num : (1:ℝ) ≠ 0)).pow 2 using 1
  simp

/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, liminf_le_limsup ?_ ?_, ?_ ⟩ <;> try isBoundedDefault
  · set L' := liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
    by_cases hL : L' = ⊥; · simp [hL]
    have hRootPos : (0:EReal) ≤ liminf (fun n ↦ (((c n) ^ (1 / (n:ℝ)):ℝ):EReal)) atTop := by
      apply le_liminf_of_le (by isBoundedDefault)
      rw [eventually_atTop]; use m; intro n hn
      exact_mod_cast rpow_nonneg (le_of_lt (hpos n hn)) _
    apply le_of_forall_lt_imp_le_of_dense
    intro y hy
    by_cases hy' : y = ⊥; · simp [hy']
    have hyT : y ≠ ⊤ := ne_top_of_lt hy
    have : y = y.toReal := (coe_toReal hyT hy').symm
    rw [this] at hy ⊢
    by_cases hr : y.toReal ≤ 0
    · exact le_trans (by exact_mod_cast hr) hRootPos
    push_neg at hr; set r := y.toReal
    have hev := eventually_lt_of_lt_liminf hy (by isBoundedDefault)
    rw [eventually_atTop] at hev; obtain ⟨N', hN⟩ := hev
    set N := max N' (max m 1)
    have hratio (n:ℤ) (hn: n ≥ N) : r ≤ c (n+1) / c n := by
      have := hN n (by omega); norm_cast at this; exact le_of_lt this
    set B := c N * r^(-N)
    have hB : 0 < B := mul_pos (hpos N (by omega)) (zpow_pos hr _)
    have hrne : (r:ℝ) ≠ 0 := ne_of_gt hr
    have lower (n:ℤ) (hn: n ≥ N) : B * r^n ≤ c n := by
      suffices h : ∀ k : ℕ, B * r^(N + k) ≤ c (N + k) by
        have := h (n - N).toNat
        rwa [show N + ↑(n - N).toNat = n from by omega] at this
      intro k; induction k with
      | zero =>
        simp only [Nat.cast_zero, add_zero, B]
        rw [mul_assoc, zpow_neg_mul_zpow_self _ hrne, mul_one]
      | succ k ih =>
        have hck : c (N + ↑k) > 0 := hpos (N + ↑k) (by omega)
        have hrat := hratio (N + ↑k) (le_add_of_nonneg_right (Nat.cast_nonneg k))
        have hrat' : r * c (N + ↑k) ≤ c (N + ↑k + 1) := by
          nlinarith [mul_comm (c (N + ↑k)) r,
            div_mul_cancel₀ (c (N + ↑k + 1)) (ne_of_gt hck)]
        have hstep : (N:ℤ) + ↑(k + 1) = N + ↑k + 1 := by push_cast; ring
        rw [hstep]
        calc B * r ^ (N + ↑k + 1)
            = r * (B * r ^ (N + ↑k)) := by rw [zpow_add_one₀ hrne]; ring
          _ ≤ r * c (N + ↑k) := mul_le_mul_of_nonneg_left ih hr.le
          _ ≤ c (N + ↑k + 1) := hrat'
    have lower_root (n:ℤ) (hn: n ≥ N) :
        ((B^(1/(n:ℝ)) * r:ℝ):EReal) ≤ (((c n)^(1/(n:ℝ)):ℝ):EReal) := by
      rw [EReal.coe_le_coe_iff]
      have hn' : n > 0 := by omega
      calc B^(1/(n:ℝ)) * r
          = B^(1/(n:ℝ)) * ((r^n)^(1/(n:ℝ))) := by
            congr 1
            rw [←rpow_intCast, ←rpow_mul hr.le]
            convert rpow_one _; field_simp
        _ = (B * r^n)^(1/(n:ℝ)) := (mul_rpow (by positivity) (by positivity)).symm
        _ ≤ _ := rpow_le_rpow (by positivity) (lower n hn) (by positivity)
    calc (r:EReal)
      _ = (atTop.liminf (fun n:ℤ ↦ ((B^(1/(n:ℝ)):ℝ):EReal))) *
          (atTop.liminf (fun n:ℤ ↦ ((r:ℝ):EReal))) := by
          symm; simp [-coe_mul]; convert one_mul _
          apply Tendsto.liminf_eq
          convert Tendsto.comp (f := fun n:ℤ ↦ (B ^ (n:ℝ)⁻¹))
            (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
          · apply continuous_coe_real_ereal.tendsto'; norm_num
          convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹)
            (g := fun x:ℝ ↦ B^x) (y := nhds 0) _ _
          · apply (continuous_const_rpow (ne_of_gt hB)).tendsto'; simp
          exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop
      _ ≤ atTop.liminf (fun n:ℤ ↦ ((B^(1/(n:ℝ)) * r:ℝ):EReal)) := by
          apply EReal.le_liminf_mul
          · apply Eventually.of_forall; intros; simp; positivity
          · apply Eventually.of_forall; intros; simp; positivity
      _ ≤ _ := by
          apply liminf_le_liminf <;> try isBoundedDefault
          rw [eventually_atTop]; exact ⟨N, lower_root⟩
  set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
  by_cases hL : L' = ⊤; simp [hL]
  have hL'pos : 0 ≤ L' := by
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N; use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := (bot_lt_zero.trans_le hL'pos).ne'
  set L := L'.toReal
  have hL' : L' = L := (coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤; simp [hy']
  have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by grind
  replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
  rw [this]
  have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [eventually_atTop] at this; choose N' hN using this
  set N := max N' (max m 1)
  have (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this; norm_cast at hN; order
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by specialize hpos N (by omega); positivity
  have hLε : (L + ε : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hLεpos : (0:ℝ) < L + ε := by linarith
  have hratio := this
  have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
    suffices h : ∀ k : ℕ, c (N + k) ≤ A * (L+ε)^(N + k) by
      have := h (n - N).toNat
      rwa [show N + ↑(n - N).toNat = n from by omega] at this
    intro k; induction k with
    | zero =>
      simp only [Nat.cast_zero, add_zero, A]
      rw [mul_assoc, zpow_neg_mul_zpow_self _ hLε, mul_one]
    | succ k ih =>
      have hck : c (N + ↑k) > 0 := hpos (N + ↑k) (by omega)
      have hrat := hratio (N + ↑k) (le_add_of_nonneg_right (Nat.cast_nonneg k))
      have hrat' : c (N + ↑k + 1) ≤ (L + ε) * c (N + ↑k) := by
        nlinarith [mul_comm (c (N + ↑k)) (L + ε), div_mul_cancel₀ (c (N + ↑k + 1)) (ne_of_gt hck)]
      have : (N:ℤ) + ↑(k + 1) = N + ↑k + 1 := by push_cast; ring
      rw [this]
      calc c (N + ↑k + 1)
          ≤ (L + ε) * c (N + ↑k) := hrat'
        _ ≤ (L + ε) * (A * (L + ε) ^ (N + ↑k)) :=
            mul_le_mul_of_nonneg_left ih hLεpos.le
        _ = A * (L + ε) ^ (N + ↑k + 1) := by
            rw [zpow_add_one₀ hLε]; ring
  have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
        apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
      _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←rpow_intCast, ←rpow_mul (by positivity)]
        convert rpow_one _
        field_simp
  calc
    _ ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
      apply limsup_le_limsup <;> try isBoundedDefault
      unfold EventuallyLE; rw [eventually_atTop]
      use N
    _ ≤ (atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal))) * (atTop.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal))) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Frequently.of_forall; intros; positivity
      . apply Eventually.of_forall; simp; positivity
      . simp [-coe_add]
      simp [-coe_add]; grind
    _ = (L+ε:ℝ) := by
      simp; convert one_mul _
      apply Tendsto.limsup_eq
      convert Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
      . apply continuous_coe_real_ereal.tendsto'; norm_num
      convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
      . apply (continuous_const_rpow (by positivity)).tendsto'; simp
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
  use (fun (_:ℕ) ↦ (1:ℝ) : Series)
  refine ⟨?_, ?_, diverges_of_nodecay ?_⟩
  · intro n hn; simp [show (0:ℤ) ≤ n from hn]
  · apply tendsto_nhds_of_eventually_eq
    rw [eventually_atTop]; use 0; intro n hn
    simp [show (0:ℤ) ≤ n from hn, show (0:ℤ) ≤ n + 1 from by omega]
  · intro h
    rw [LinearOrderedAddCommGroup.tendsto_nhds] at h
    obtain ⟨N, hN⟩ := (h 1 (by positivity)).exists_forall_of_atTop
    have := hN (max N 0) (le_max_left _ _)
    simp [show max N 0 ≥ (0:ℤ) from le_max_right _ _] at this

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
  use (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series)
  refine ⟨zeta_2_nonzero, ?_, zeta_2_absConverges⟩
  rw [show (atTop : Filter ℤ) = map Nat.cast atTop from Nat.map_cast_int_atTop.symm,
    Filter.tendsto_map'_iff]
  have hsimpl : ((fun n:ℤ ↦ |(fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).seq (n+1)| /
      |(fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).seq n|) ∘ Nat.cast) =
      (fun n:ℕ ↦ ((n+1:ℝ)/(n+2))^2) := by
    ext n; simp only [Function.comp]
    simp only [show (0:ℤ) ≤ (n:ℤ) from Int.natCast_nonneg n,
      show (0:ℤ) ≤ (n:ℤ) + 1 from by omega, ite_true,
      show (n:ℤ).toNat = n from rfl, show ((n:ℤ) + 1).toNat = n + 1 from by omega]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (↑(n+1) + 1) ^ 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((n:ℝ) + 1) ^ 2)]
    have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have h2 : (0:ℝ) < ↑(n+1) + 1 := by positivity
    push_cast; field_simp; ring
  rw [hsimpl]
  -- ((n+1)/(n+2))^2 → 1: suffices (n+1)/(n+2) → 1, then square
  suffices h : atTop.Tendsto (fun n:ℕ ↦ ((n:ℝ)+1)/((n:ℝ)+2)) (nhds 1) by
    convert h.pow 2 using 1; simp
  have heq : (fun n:ℕ ↦ ((n:ℝ)+1)/((n:ℝ)+2)) = (fun n:ℕ ↦ 1 - 1/((n:ℝ)+2)) := by
    ext n; field_simp; ring
  rw [heq]
  have : atTop.Tendsto (fun n:ℕ ↦ 1/((n:ℝ)+2)) (nhds 0) := by
    have h := Filter.Tendsto.comp tendsto_one_div_atTop_nhds_zero_nat
      (Filter.tendsto_add_atTop_iff_nat 2 |>.mpr tendsto_id)
    exact h.congr (fun n ↦ by simp [one_div])
  simpa using tendsto_const_nhds.sub this

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) := by
  -- Apply Lemma 7.5.2 (ratio_ineq) to c(n) = n
  obtain ⟨hli, _, hls⟩ := ratio_ineq (c := fun n:ℤ ↦ (n:ℝ)) 1
    (fun n hn ↦ by dsimp; exact_mod_cast (show (0:ℤ) < n by omega))
  -- The ratio (n+1)/n → 1, so its EReal limsup and liminf both equal 1
  have hratio : atTop.Tendsto
      (fun n:ℤ ↦ ((↑(n+1) / ↑n : ℝ) : EReal)) (nhds ((1:ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr <| by
      rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff,
        show ((fun n:ℤ ↦ (↑(n+1) / ↑n : ℝ)) ∘ (Nat.cast : ℕ → ℤ)) =
          (fun n:ℕ ↦ ((n:ℝ) + 1) / n) from by
          ext; simp only [Function.comp_apply, Int.cast_natCast, Int.cast_add, Int.cast_one]]
      have h1 : Tendsto (fun n:ℕ ↦ 1 + 1/(n:ℝ)) atTop (nhds 1) := by
        simpa using (tendsto_const_nhds (x := (1:ℝ))).add
          tendsto_one_div_atTop_nhds_zero_nat
      exact (Filter.tendsto_congr' (eventually_atTop.mpr ⟨1, fun n hn ↦ by
        have : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); field_simp⟩)).mpr h1
  rw [hratio.liminf_eq] at hli
  rw [hratio.limsup_eq] at hls
  -- Squeeze: 1 ≤ liminf(n^{1/n}) ≤ limsup(n^{1/n}) ≤ 1, so the limit is 1
  have hroot : atTop.Tendsto
      (fun n:ℤ ↦ (((n:ℝ)^(1/(n:ℝ)) : ℝ) : EReal)) (nhds ((1:ℝ) : EReal)) :=
    tendsto_of_le_liminf_of_limsup_le hli hls
  -- Transfer from EReal/ℤ to ℝ/ℕ
  have hreal := EReal.tendsto_coe.mp hroot
  rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff] at hreal
  exact hreal.congr (fun n ↦ by simp [Function.comp_apply, Int.cast_natCast])

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
  -- Apply root test: |a_n|^(1/n) = n^(q/n) · |x| → |x| < 1
  have habs : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).absConverges := by
    apply root_test_pos
    -- Show limsup |a_n|^(1/n) < 1 by showing it tends to |x|
    have htend : atTop.Tendsto (fun n:ℤ ↦ ((|(fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).seq n|^(1/(n:ℝ)):ℝ):EReal))
        (nhds ↑(|x|)) := by
      rw [show (atTop : Filter ℤ) = map Nat.cast atTop from Nat.map_cast_int_atTop.symm,
        Filter.tendsto_map'_iff]
      -- Reduce to ℕ, then show |n^q·x^n|^(1/n) = n^(q/n)·|x| for n ≥ 1
      apply (continuous_coe_real_ereal.tendsto _).comp
      have hsimp : ∀ n:ℕ, n ≥ 1 →
          (|(fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).seq (n:ℤ)|^(1/(n:ℝ))) = (n:ℝ)^(q/(n:ℝ)) * |x| := by
        intro n hn
        simp only [show (0:ℤ) ≤ (n:ℤ) from Int.natCast_nonneg n, ite_true]
        have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
        simp only [Int.toNat_natCast]
        rw [_root_.abs_mul, _root_.abs_of_nonneg (rpow_nonneg (by positivity) q),
          abs_pow, mul_rpow (rpow_nonneg (by positivity) q) (by positivity),
          ← rpow_natCast |x| n, ← rpow_mul (abs_nonneg x), ← rpow_mul (by positivity : (0:ℝ) ≤ n)]
        congr 1 <;> field_simp
      apply Filter.Tendsto.congr' (f₁ := fun n:ℕ ↦ (n:ℝ)^(q/(n:ℝ)) * |x|)
      · rw [Filter.eventuallyEq_iff_exists_mem]; use Set.Ici 1, Filter.Ici_mem_atTop 1
        intro n hn; exact (hsimp n hn).symm
      -- n^(q/n) · |x| → 1 · |x| = |x|
      have : atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^(q/(n:ℝ))) (nhds 1) := by
        have : (fun n:ℕ ↦ (n:ℝ)^(q/(n:ℝ))) = (fun n:ℕ ↦ ((n:ℝ)^(1/(n:ℝ)))^q) := by
          ext n; rw [← rpow_mul (by positivity : (0:ℝ) ≤ n)]; ring_nf
        rw [this]
        convert tendsto_rpow_div_nat.rpow_const (Or.inl (by norm_num : (1:ℝ) ≠ 0)) using 2
        exact (one_rpow q).symm
      simpa using this.mul tendsto_const_nhds
    rw [htend.limsup_eq]; exact_mod_cast hx
  have hconv := converges_of_absConverges habs
  refine ⟨hconv, ?_⟩
  have hdecay := decay_of_converges hconv
  -- decay_of_converges gives Tendsto over ℤ, extract over ℕ
  rw [show (atTop : Filter ℤ) = map Nat.cast atTop from Nat.map_cast_int_atTop.symm,
    Filter.tendsto_map'_iff] at hdecay
  exact hdecay.congr (fun n ↦ by simp)

end Chapter7
