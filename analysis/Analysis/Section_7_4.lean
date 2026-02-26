import Mathlib.Tactic
import Analysis.Section_7_3

/-!
# Analysis I, Section 7.4: Rearrangement of series

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Rearrangement of non-negative or absolutely convergent series.
-/

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

/-- Proposition 7.4.1 -/
theorem Series.converges_of_permute_nonneg {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    specialize ha (f n.toNat); grind
  set S := (a:Series).partial
  set T := (af:Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q := (converges_of_nonneg_iff ha).mp hconv
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  . have Ssum : L = (a:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      . use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      . use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    simp [←Ssum, ←Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1
  have hTL (M:ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    . have hM' : M < 0 := by linarith
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by simp [S, Series.partial]; symm; apply sum_eq_sum (N:=N) a; positivity
      _ ≤ L := by apply le_ciSup _ (N:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]
  have hSL' (N:ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    . have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨ _, hm, ?_ ⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    have sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0)
      : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
    calc
      _ = ∑ n ∈ X, a n := by simp [S, sum_eq_sum, hN, X]
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        . intro h; obtain ⟨ m, rfl, hm' ⟩ := hM _ h; use m
        rintro ⟨ _, ⟨ _, _⟩, rfl ⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        . aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by apply le_ciSup _ (M:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
  linarith [ciSup_le hSL', ciSup_le hTL]

/-- Example 7.4.2 -/
theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by
  set a := (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series)
  have ha : a.nonneg := by intro n; simp [a]; by_cases h : n ≥ 0 <;> simp [h]; positivity
  rw [converges_of_nonneg_iff ha]
  set b := (mk' (m := 1) fun (n : {n : ℤ // n ≥ 1}) ↦ 1 / (↑↑n : ℝ) ^ (2:ℕ) : Series)
  have hconv : b.converges := by
    convert (converges_qseries 2 (by norm_num)).mpr (by norm_num) using 3 with n; norm_cast
  have hb : b.nonneg := by intro n; simp [b]; by_cases h : 1 ≤ n <;> simp [h]; positivity
  obtain ⟨M, hM⟩ := (converges_of_nonneg_iff hb).mp hconv
  use M; intro N
  by_cases hN : N < 0
  · rw [partial_of_lt (by omega)]; linarith [partial_nonneg hb 0, hM 0]
  · push_neg at hN
    have hterm : ∀ k ∈ Finset.Icc (0:ℤ) N, a.seq k = b.seq (k+1) := by
      intro k hk; simp [Finset.mem_Icc] at hk
      have hkr : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.1
      simp [a, b, hk.1, show k + 1 ≥ (1:ℤ) from by omega, hkr]
    calc a.partial N
        = ∑ k ∈ Finset.Icc 0 N, b.seq (k+1) := by
          simp only [Series.partial]; exact Finset.sum_congr rfl hterm
      _ = ∑ k ∈ Finset.Icc 1 (N+1), b.seq k := by
          apply Finset.sum_nbij (· + 1)
          · intro k hk; simp at hk ⊢; omega
          · intro x _ y _ (h : x + 1 = y + 1); omega
          · intro k hk
            simp only [Set.mem_image, Finset.mem_coe, Finset.mem_Icc] at *
            exact ⟨k - 1, by omega, by omega⟩
          · intros; rfl
      _ ≤ b.partial (N+1) := by
          simp only [Series.partial]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp at hk ⊢; exact hk
          · intro k _ _; exact hb k
      _ ≤ M := hM _

private def f_perm : ℕ → ℕ := fun n => if Even n then n + 1 else n - 1

private theorem f_perm_involutive : Function.Involutive f_perm := by
  intro n; simp only [f_perm]
  by_cases h : Even n
  · have : ¬ Even (n + 1) := by intro ⟨k, hk⟩; obtain ⟨j, rfl⟩ := h; omega
    simp [h, this]
  · have hn : n ≥ 1 := by
      by_contra h0; push_neg at h0; interval_cases n; simp at h
    have : Even (n - 1) := by
      obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp h; exact ⟨k, by omega⟩
    simp [h, this]; omega

private theorem f_perm_eq (n : ℕ) :
    (fun k:ℕ ↦ 1/((k:ℝ)+1)^2) (f_perm n) = if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 := by
  simp only [f_perm]
  by_cases h : Even n
  · simp [h]; ring
  · simp [h]
    have hn : n ≥ 1 := by
      by_contra h0; push_neg at h0; interval_cases n; simp at h
    congr 1; exact_mod_cast show (n - 1 + 1 : ℕ) = n from by omega

private theorem permuted_eq_composed :
    (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series) =
    (fun n ↦ (fun k:ℕ ↦ 1/((k:ℝ)+1)^2) (f_perm n) : Series) := by
  ext n
  · rfl
  · by_cases hn : n ≥ 0 <;> simp only [hn, ite_true, ite_false]
    exact (f_perm_eq n.toNat).symm

theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
    have ha : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).nonneg := by
      intro n; by_cases h : n ≥ 0 <;> simp [h]; positivity
    have hperm := @converges_of_permute_nonneg (fun n:ℕ ↦ 1/(n+1:ℝ)^2) ha zeta_2_converges f_perm f_perm_involutive.bijective
    rw [permuted_eq_composed]; exact hperm.1

theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
    have ha : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).nonneg := by
      intro n; by_cases h : n ≥ 0 <;> simp [h]; positivity
    have hperm := @converges_of_permute_nonneg (fun n:ℕ ↦ 1/(n+1:ℝ)^2) ha zeta_2_converges f_perm f_perm_involutive.bijective
    rw [permuted_eq_composed]; exact hperm.2.symm

/-- Proposition 7.4.3 (Rearrangement of series) -/
theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    convert converges_of_permute_nonneg (a := fun n ↦ |a n|) _ _ hf using 3
    . simp; ext n; by_cases n ≥ 0 <;> grind
    . intro n; by_cases h: n ≥ 0 <;> simp [h]
    convert ha with n; by_cases n ≥ 0 <;> grind
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L'
  . simp [sum_of_converges this, absConverges]
    convert habs.1 with n; by_cases n ≥ 0 <;> grind
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds]
  intro ε hε
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv
    choose N hN using hconv _ (half_pos hε)
    use max N N₁, (by grind); apply hN; grind
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl
  choose M hM using this; use M; intro M' hM'
  have hM'_pos : M' ≥ 0 := by linarith
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    intro n hn; simp at hn ⊢
    exact ⟨finv n, by have := hM n hn; omega, Function.invFun_eq (hf.2 n)⟩
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by
      convert Finset.sum_union _ using 2
      . simp [X, why]
      . infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto
  choose q' hq using X.bddAbove
  set q := max q' N.toNat
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by
    intro x hx
    have hxX : x ∈ (X : Set ℕ) := hx
    simp only [X, Finset.mem_sdiff, Finset.mem_Iic] at hx
    simp [Finset.mem_Icc]; exact ⟨by omega, le_max_of_le_left (hq hxX)⟩
  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp
    _ ≤ ε/2 := by
      convert ha (N.toNat+1) _ q _ <;> try omega
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring


/-- Example 7.4.4 -/
noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)

private theorem Series.a_7_4_4_eq_mk' :
    (a_7_4_4 : Series) = mk' (m := 0) (fun n ↦ (-1:ℝ) ^ (↑n : ℤ) / ((↑n : ℝ) + 2)) := by
  ext
  · rfl
  · rename_i n; simp only [a_7_4_4]
    by_cases hn : n ≥ 0
    · simp [hn]; rw [← zpow_natCast]
      have hnt : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      have hntR : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast hnt
      rw [show (n.toNat : ℤ) = n from hnt, hntR]
    · simp [hn]

theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by
  set g : { n : ℤ // n ≥ 0 } → ℝ := fun n ↦ 1 / ((n.val : ℝ) + 2)
  rw [a_7_4_4_eq_mk']
  suffices h : (mk' (m := 0) (fun n ↦ (-1) ^ (↑n : ℤ) * g n)).converges by
    convert h using 2; ext n; exact (mul_one_div _ _).symm
  have hg_nn : ∀ n : { n : ℤ // n ≥ 0 }, g n ≥ 0 := by intro ⟨n, hn⟩; simp [g]; positivity
  have hg_anti : Antitone g := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ (hxy : x ≤ y)
    simp only [g]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show x + 2 ≤ y + 2 from by omega))
  apply (converges_of_alternating hg_nn hg_anti).mpr
  have : Nonempty { n : ℤ // n ≥ 0 } := ⟨⟨0, le_refl _⟩⟩
  have hkey : Filter.Tendsto (fun (x : { n : ℤ // n ≥ 0 }) => (x.val : ℝ) + 2)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr; intro b
    exact ⟨⟨max ⌈b⌉ 0, le_max_right _ _⟩, fun ⟨n, hn⟩ hle => by
      have : ⌈b⌉ ≤ n := le_trans (le_max_left _ _) hle
      have : (n : ℝ) ≥ b := le_trans (Int.le_ceil b) (by exact_mod_cast this)
      linarith⟩
  exact (tendsto_inv_atTop_zero.comp hkey).congr fun ⟨n, hn⟩ => by simp [g, one_div]

private theorem Series.a_7_4_4_partial_bound (n : ℕ) :
    (a_7_4_4 : Series).partial (n : ℤ) ≥ 1/6 := by
  have hp_succ (k : ℕ) : (a_7_4_4 : Series).partial ↑(k + 1) =
      (a_7_4_4 : Series).partial ↑k + a_7_4_4 (k + 1) := by
    have h := partial_succ (a_7_4_4 : Series) (N := (k : ℤ)) (by simp)
    simp only [show (k : ℤ) + 1 = ↑(k + 1) from by push_cast; ring] at h; exact h
  have hp0 : (a_7_4_4 : Series).partial ↑(0:ℕ) = 1/2 := by
    have h := partial_succ (a_7_4_4 : Series) (N := (-1:ℤ)) (by simp)
    simp only [show (-1:ℤ) + 1 = ↑(0:ℕ) from by norm_num] at h
    rw [h, partial_of_lt (by simp : (-1:ℤ) < (a_7_4_4 : Series).m)]; simp [a_7_4_4]
  have ha (k : ℕ) : a_7_4_4 k = (-1:ℝ)^k / ((k:ℝ) + 2) := rfl
  induction n using Nat.strongRec with
  | _ n ih =>
    match n with
    | 0 => rw [hp0]; norm_num
    | 1 => rw [hp_succ 0, hp0, ha]; norm_num
    | n + 2 =>
      by_cases hn : Even n
      · rw [show (n+2:ℕ) = (n+1)+1 from rfl, hp_succ (n+1), ha]
        obtain ⟨k, rfl⟩ := hn
        have hpow : (-1:ℝ) ^ (k + k + 1 + 1) = 1 := by
          rw [show k + k + 1 + 1 = 2 * (k + 1) from by omega]; simp [pow_mul]
        have : (-1:ℝ) ^ (k + k + 1 + 1) / (↑(k + k + 1 + 1) + 2) ≥ 0 := by
          rw [hpow]; positivity
        linarith [ih (k + k + 1) (by omega)]
      · rw [show (n+2:ℕ) = (n+1)+1 from rfl, hp_succ (n+1), hp_succ n, ha, ha]
        rw [Nat.not_even_iff_odd] at hn; obtain ⟨k, rfl⟩ := hn
        simp only [show 2*k+1+1 = 2*(k+1) from by ring,
          show (-1:ℝ)^(2*(k+1)) = 1 from by simp [pow_mul],
          show (-1:ℝ)^(2*(k+1)+1) = -1 from by simp [pow_succ, pow_mul]]
        have h1 : (0:ℝ) < ↑(2*(k+1)) + 2 := by positivity
        have h2 : (0:ℝ) < ↑(2*(k+1)+1) + 2 := by positivity
        have : (1:ℝ) / (↑(2*(k+1)) + 2) + -1 / (↑(2*(k+1)+1) + 2) > 0 := by
          rw [div_add_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
          exact div_pos (by push_cast; linarith) (by positivity)
        linarith [ih (2*k+1) (by omega)]

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by
  suffices h : (a_7_4_4 : Series).sum ≥ 1/6 by linarith
  apply ge_of_tendsto (convergesTo_sum ex_7_4_4_conv)
  simp only [Filter.eventually_atTop]
  exact ⟨0, fun N hN => by rw [show N = ↑N.toNat from by omega]; exact a_7_4_4_partial_bound _⟩

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 4 * (n/3) + 2 * (n % 3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by
  refine ⟨fun m n h => ?_, fun m => ?_⟩
  · simp only [f_7_4_4] at h; split_ifs at h <;> omega
  · by_cases hm : m % 2 = 0
    · exact ⟨3 * (m / 2), by simp only [f_7_4_4]; split_ifs <;> omega⟩
    · by_cases hm4 : m % 4 = 1
      · exact ⟨3 * (m / 4) + 1, by simp only [f_7_4_4]; split_ifs <;> omega⟩
      · exact ⟨3 * (m / 4) + 2, by simp only [f_7_4_4]; split_ifs <;> omega⟩

private lemma Series.f_7_4_4_vals (k : ℕ) :
    f_7_4_4 (3*k) = 2*k ∧ f_7_4_4 (3*k+1) = 4*k+1 ∧ f_7_4_4 (3*k+2) = 4*k+3 := by
  simp only [f_7_4_4]; constructor <;> [skip; constructor] <;> split_ifs <;> omega

private lemma Series.triple_sum (k : ℕ) :
    a_7_4_4 (f_7_4_4 (3*k)) + a_7_4_4 (f_7_4_4 (3*k+1)) + a_7_4_4 (f_7_4_4 (3*k+2))
    = -1 / ((2*(k:ℝ)+2) * (4*k+3) * (4*k+5)) := by
  obtain ⟨h0, h1, h2⟩ := f_7_4_4_vals k
  simp only [h0, h1, h2, a_7_4_4]
  have hp0 : (-1:ℝ)^(2*k) = 1 := by rw [pow_mul]; simp
  have hp1 : (-1:ℝ)^(4*k+1) = -1 := by
    rw [show 4*k+1 = 2*(2*k) + 1 from by ring, pow_add, pow_mul]; simp
  have hp2 : (-1:ℝ)^(4*k+3) = -1 := by
    rw [show 4*k+3 = 2*(2*k+1) + 1 from by ring, pow_add, pow_mul]; simp
  rw [hp0, hp1, hp2]
  have hd1 : (2*(k:ℝ)+2) ≠ 0 := by positivity
  have hd2 : (4*(k:ℝ)+3) ≠ 0 := by positivity
  have hd3 : (4*(k:ℝ)+5) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

private noncomputable abbrev Series.b_7_4_4 : ℕ → ℝ := fun n ↦ a_7_4_4 (f_7_4_4 n)

private noncomputable abbrev Series.c_7_4_4 : ℕ → ℝ := fun k ↦
  -1 / ((2*(k:ℝ)+2) * (4*k+3) * (4*k+5))

private lemma Series.b_7_4_4_partial_succ (k : ℕ) :
    (b_7_4_4 : Series).partial ↑(k + 1) =
    (b_7_4_4 : Series).partial ↑k + b_7_4_4 (k + 1) := by
  have h := partial_succ (b_7_4_4 : Series) (N := (k : ℤ)) (by simp)
  simp only [show (k : ℤ) + 1 = ↑(k + 1) from by push_cast; ring] at h
  convert h using 2

private lemma Series.partial_triple (k : ℕ) :
    (b_7_4_4 : Series).partial (3*(k:ℤ)+2) =
    ∑ j ∈ Finset.range (k+1), c_7_4_4 j := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, mul_zero, Finset.sum_range_one]
    have h0 : (b_7_4_4 : Series).partial ↑(0:ℕ) = b_7_4_4 0 := by
      have h := partial_succ (b_7_4_4 : Series) (N := (-1:ℤ)) (by simp)
      simp only [show (-1:ℤ) + 1 = ↑(0:ℕ) from by norm_num] at h
      rw [h, partial_of_lt (by simp : (-1:ℤ) < (b_7_4_4 : Series).m), zero_add]
      simp
    have : (2:ℤ) = ↑(1+1:ℕ) := by norm_num
    rw [this, b_7_4_4_partial_succ 1, b_7_4_4_partial_succ 0, h0]
    exact triple_sum 0
  | succ k ih =>
    rw [show 3*(↑(k+1):ℤ)+2 = ↑(3*k+4+1) from by push_cast; ring]
    rw [b_7_4_4_partial_succ (3*k+4), b_7_4_4_partial_succ (3*k+3),
        b_7_4_4_partial_succ (3*k+2)]
    rw [show ↑(3*k+2) = 3*(↑k:ℤ)+2 from by push_cast; ring, ih]
    conv_rhs => rw [show k + 1 + 1 = (k + 1) + 1 from rfl, Finset.sum_range_succ]
    have ht : b_7_4_4 (3*k+2+1) + b_7_4_4 (3*k+3+1) + b_7_4_4 (3*k+4+1) =
        c_7_4_4 (k+1) := triple_sum (k+1)
    linarith

private lemma Series.c_7_4_4_neg (k : ℕ) : c_7_4_4 k < 0 := by
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

private lemma Series.triple_partial_antitone :
    Antitone (fun k : ℕ => ∑ j ∈ Finset.range (k+1), c_7_4_4 j) :=
  antitone_nat_of_succ_le fun n => by
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl, Finset.sum_range_succ]
    linarith [c_7_4_4_neg (n + 1)]

private lemma Series.triple_partial_bound (k : ℕ) :
    ∑ j ∈ Finset.range (k+1), c_7_4_4 j ≤ -1/30 := by
  have h0 : ∑ j ∈ Finset.range 1, c_7_4_4 j = -1/30 := by
    simp [c_7_4_4]; norm_num
  calc ∑ j ∈ Finset.range (k+1), c_7_4_4 j
      ≤ ∑ j ∈ Finset.range 1, c_7_4_4 j := triple_partial_antitone (by omega)
    _ = -1/30 := h0

private lemma Series.f_7_4_4_lower_bound (n : ℕ) : f_7_4_4 n ≥ 2 * (n / 3) := by
  simp only [f_7_4_4]; split_ifs <;> omega

private lemma Series.b_7_4_4_bound (n : ℕ) : |b_7_4_4 n| ≤ 1 / (2 * (↑(n/3) : ℝ) + 2) := by
  simp only [b_7_4_4, a_7_4_4, abs_div, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_pos (show (0:ℝ) < ↑(f_7_4_4 n) + 2 from by positivity)]
  exact one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast show 2 * (n / 3) + 2 ≤ f_7_4_4 n + 2 from by simp only [f_7_4_4]; split_ifs <;> omega)

private lemma Series.c_7_4_4_ge (j : ℕ) : c_7_4_4 j ≥ -1/((j:ℝ)+1)^2 := by
  have : (1:ℝ) / ((2*(j:ℝ)+2) * (4*j+3) * (4*j+5)) ≤ 1/((j:ℝ)+1)^2 :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  simp only [c_7_4_4, ge_iff_le]; rw [neg_div, neg_div]; linarith

private lemma Series.inv_sq_sum_le (k : ℕ) :
    ∑ j ∈ Finset.range (k+1), (1:ℝ)/((j:ℝ)+1)^2 ≤ 2 - 1/((k:ℝ)+1) := by
  induction k with
  | zero => simp; norm_num
  | succ k ih =>
    rw [show k + 1 + 1 = (k+1) + 1 from rfl, Finset.sum_range_succ]
    conv_rhs => rw [show ((↑(k+1) : ℝ) + 1) = ((k:ℝ) + 2) from by push_cast; ring]
    conv_lhs => rw [show ((↑(k+1) : ℝ) + 1) = ((k:ℝ) + 2) from by push_cast; ring]
    suffices h : (1:ℝ)/((k:ℝ)+2)^2 ≤ 1/((k:ℝ)+1) - 1/((k:ℝ)+2) by linarith
    calc (1:ℝ)/((k:ℝ)+2)^2
        ≤ 1/(((k:ℝ)+1)*((k:ℝ)+2)) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = 1/((k:ℝ)+1) - 1/((k:ℝ)+2) := by field_simp; ring

private lemma Series.triple_partial_lower_bound (k : ℕ) :
    ∑ j ∈ Finset.range (k+1), c_7_4_4 j ≥ -2 := by
  calc ∑ j ∈ Finset.range (k+1), c_7_4_4 j
      ≥ ∑ j ∈ Finset.range (k+1), (-1/((j:ℝ)+1)^2) :=
        Finset.sum_le_sum (fun j _ => c_7_4_4_ge j)
    _ = -(∑ j ∈ Finset.range (k+1), 1/((j:ℝ)+1)^2) := by
        simp only [neg_div, Finset.sum_neg_distrib]
    _ ≥ -2 := by linarith [inv_sq_sum_le k, show (0:ℝ) < 1/((k:ℝ)+1) from by positivity]

private lemma Series.gap_bound (k n : ℕ) (h1 : 3*k+2 ≤ n) (h2 : n ≤ 3*k+4) :
    |(b_7_4_4 : Series).partial ↑n - (b_7_4_4 : Series).partial ↑(3*k+2)| ≤ 1/((k:ℝ)+2) := by
  have hn : n = 3*k+2 ∨ n = 3*k+3 ∨ n = 3*k+4 := by omega
  have hk2 : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hterm : ∀ m, 3*k+3 ≤ m → m ≤ 3*k+4 →
      |b_7_4_4 m| ≤ 1 / (2*((k:ℝ)+2)) := by
    intro m hm1 hm2
    calc |b_7_4_4 m| ≤ 1 / (2 * ↑(m/3) + 2) := b_7_4_4_bound m
      _ ≤ 1 / (2*((k:ℝ)+2)) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (k:ℝ) + 1 ≤ ↑(m / 3) := by exact_mod_cast show k + 1 ≤ m / 3 from by omega
          linarith
  rcases hn with rfl | rfl | rfl
  · simp [le_of_lt hk2]
  · have h3 := b_7_4_4_partial_succ (3*k+2)
    rw [show 3*k+2+1 = 3*k+3 from by ring] at h3
    rw [h3, add_sub_cancel_left]
    calc |b_7_4_4 (3*k+3)| ≤ 1 / (2*((k:ℝ)+2)) := hterm _ (by omega) (by omega)
      _ ≤ 1 / ((k:ℝ)+2) := by
          apply one_div_le_one_div_of_le hk2; linarith
  · have h3 := b_7_4_4_partial_succ (3*k+2)
    rw [show 3*k+2+1 = 3*k+3 from by ring] at h3
    have h4 := b_7_4_4_partial_succ (3*k+3)
    rw [show 3*k+3+1 = 3*k+4 from by ring] at h4
    rw [h4, h3]
    calc |_ + b_7_4_4 (3*k+3) + b_7_4_4 (3*k+4) - _|
        = |b_7_4_4 (3*k+3) + b_7_4_4 (3*k+4)| := by ring_nf
      _ ≤ |b_7_4_4 (3*k+3)| + |b_7_4_4 (3*k+4)| := abs_add ..
      _ ≤ 1/(2*((k:ℝ)+2)) + 1/(2*((k:ℝ)+2)) :=
          add_le_add (hterm _ (by omega) (by omega)) (hterm _ (by omega) (by omega))
      _ = 1/((k:ℝ)+2) := by rw [← two_mul]; field_simp

theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by
  rw [show (fun n ↦ a_7_4_4 (f_7_4_4 n) : ℕ → ℝ) = b_7_4_4 from rfl]
  set s := (b_7_4_4 : Series)
  set T := fun k : ℕ => ∑ j ∈ Finset.range (k+1), c_7_4_4 j
  obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto T Filter.atTop (nhds L) :=
    Real.tendsto_of_bddBelow_antitone
      ⟨-2, fun _ ⟨k, hk⟩ => by rw [← hk]; exact triple_partial_lower_bound k⟩
      triple_partial_antitone
  -- Full partial sums converge to L (gap between partial(n) and nearest T_k vanishes)
  apply converges_of_convergesTo (L := L)
  rw [convergesTo, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := Metric.tendsto_atTop.mp hL (ε/2) (half_pos hε)
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℕ, 1/((K₂:ℝ)+2) < ε/2 := by
    obtain ⟨M, hM⟩ := exists_nat_gt (2/ε)
    refine ⟨M, ?_⟩
    rw [one_div, ← inv_div]
    exact inv_strictAnti₀ (by positivity) (by linarith)
  set K := max K₁ K₂
  refine ⟨↑(3*K+2), fun n hn => ?_⟩
  have hn0 : n ≥ 0 := le_trans (Nat.cast_nonneg (3*K+2)) hn
  have hmn : (↑n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0.le
  set m := n.toNat
  have hm_ge : m ≥ 3*K+2 := by omega
  set j := (m - 2) / 3
  have hj1 : 3*j+2 ≤ m := by omega
  have hj2 : m ≤ 3*j+4 := by omega
  have hjK : j ≥ K := by omega
  rw [Real.dist_eq]
  have htri := partial_triple j
  rw [show 3*(j:ℤ)+2 = ↑(3*j+2) from by push_cast; ring] at htri
  calc |s.partial n - L|
      = |s.partial ↑m - L| := by rw [hmn]
    _ = |(s.partial ↑m - s.partial ↑(3*j+2)) + (s.partial ↑(3*j+2) - L)| := by ring_nf
    _ ≤ |s.partial ↑m - s.partial ↑(3*j+2)| + |s.partial ↑(3*j+2) - L| := abs_add ..
    _ ≤ 1/((j:ℝ)+2) + |T j - L| := by
        apply add_le_add (gap_bound j m hj1 hj2)
        rw [htri]
    _ < ε/2 + ε/2 := by
        apply add_lt_add
        · calc (1:ℝ)/((j:ℝ)+2) ≤ 1/((K₂:ℝ)+2) := by
                apply one_div_le_one_div_of_le (by positivity)
                exact_mod_cast (show K₂ + 2 ≤ j + 2 from by omega)
            _ < ε/2 := hK₂
        · rw [← Real.dist_eq]; exact hK₁ j (le_trans (le_max_left _ _) hjK)
    _ = ε := by ring

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by
  have hconv := ex_7_4_4'_conv
  rw [show (fun n ↦ a_7_4_4 (f_7_4_4 n) : ℕ → ℝ) = b_7_4_4 from rfl] at hconv ⊢
  set s := (b_7_4_4 : Series)
  suffices h : s.sum ≤ -1/30 by linarith
  -- Subsequence at triple boundaries: s.partial(3k+2) → s.sum
  have hsub : Filter.Tendsto (fun k:ℕ => s.partial (3*(k:ℤ)+2)) Filter.atTop (nhds s.sum) :=
    (convergesTo_sum hconv).comp (Filter.tendsto_atTop_atTop.mpr
      (fun b => ⟨b.toNat, fun n hn => by omega⟩))
  -- At triple boundaries: s.partial(3k+2) = T_k ≤ -1/30
  exact le_of_tendsto hsub (Filter.eventually_atTop.mpr
    ⟨0, fun k _ => by rw [partial_triple]; exact triple_partial_bound k⟩)

/-- Exercise 7.4.1 -/
theorem Series.absConverges_of_subseries {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by
  suffices (fun n ↦ |a (f n)| : Series).converges by
    have heq : (fun n ↦ a (f n):Series).abs = (fun n ↦ |a (f n)| : Series) := by
      ext; · rfl
      next n => rw [abs_seq]; by_cases hn : (0:ℤ) ≤ n <;> simp [hn]
    rwa [absConverges, heq]
  have ha' : (fun n ↦ |a n| : Series).converges := by
    have heq : (a:Series).abs = (fun n ↦ |a n| : Series) := by
      ext; · rfl
      next n => rw [abs_seq]; by_cases hn : (0:ℤ) ≤ n <;> simp [hn]
    rwa [absConverges, heq] at ha
  have hnn : (fun n ↦ |a (f n)| : Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h]
  have hnn' : (fun n ↦ |a n| : Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h]
  obtain ⟨M, hM⟩ := (converges_of_nonneg_iff hnn').mp ha'
  rw [converges_of_nonneg_iff hnn]; use M; intro N
  by_cases hN : N < 0
  · linarith [partial_of_lt (s := (fun n ↦ |a (f n)| : Series)) (by omega : N < 0),
              hM (-1 : ℤ), partial_of_lt (s := (fun n ↦ |a n| : Series)) (by omega : (-1:ℤ) < 0)]
  · push_neg at hN
    calc (fun n ↦ |a (f n)| : Series).partial N
        = ∑ m ∈ Finset.Iic N.toNat, |a (f m)| := by
          simp [Series.partial]; exact sum_eq_sum (fun n ↦ |a (f n)|) hN
      _ = ∑ n ∈ (Finset.Iic N.toNat).image f, |a n| := by
          symm; exact Finset.sum_image (fun x _ y _ h => hf.injective h)
      _ ≤ ∑ n ∈ Finset.Iic (f N.toNat), |a n| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx; simp at hx ⊢; obtain ⟨m, hm, rfl⟩ := hx; exact hf.monotone hm
          · intro _ _ _; exact abs_nonneg _
      _ = (fun n ↦ |a n| : Series).partial ↑(f N.toNat) := by
          simp [Series.partial]; symm; exact sum_eq_sum (fun n ↦ |a n|) (by positivity)
      _ ≤ M := hM _

/-- Exercise 7.4.1 (generalization): injective suffices, strict monotonicity not needed. -/
theorem Series.absConverges_of_subseries' {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: Function.Injective f) :
  (fun n ↦ a (f n):Series).absConverges := by
  suffices (fun n ↦ |a (f n)| : Series).converges by
    have heq : (fun n ↦ a (f n):Series).abs = (fun n ↦ |a (f n)| : Series) := by
      ext; · rfl
      next n => rw [abs_seq]; by_cases hn : (0:ℤ) ≤ n <;> simp [hn]
    rwa [absConverges, heq]
  have ha' : (fun n ↦ |a n| : Series).converges := by
    have heq : (a:Series).abs = (fun n ↦ |a n| : Series) := by
      ext; · rfl
      next n => rw [abs_seq]; by_cases hn : (0:ℤ) ≤ n <;> simp [hn]
    rwa [absConverges, heq] at ha
  have hnn : (fun n ↦ |a (f n)| : Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h]
  have hnn' : (fun n ↦ |a n| : Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h]
  obtain ⟨M, hM⟩ := (converges_of_nonneg_iff hnn').mp ha'
  rw [converges_of_nonneg_iff hnn]; use M; intro N
  by_cases hN : N < 0
  · linarith [partial_of_lt (s := (fun n ↦ |a (f n)| : Series)) (by omega : N < 0),
              hM (-1 : ℤ), partial_of_lt (s := (fun n ↦ |a n| : Series)) (by omega : (-1:ℤ) < 0)]
  · push_neg at hN
    set K := ((Finset.Iic N.toNat).image f).sup id
    calc (fun n ↦ |a (f n)| : Series).partial N
        = ∑ m ∈ Finset.Iic N.toNat, |a (f m)| := by
          simp [Series.partial]; exact sum_eq_sum (fun n ↦ |a (f n)|) hN
      _ = ∑ n ∈ (Finset.Iic N.toNat).image f, |a n| := by
          symm; exact Finset.sum_image (fun x _ y _ h => hf h)
      _ ≤ ∑ n ∈ Finset.Iic K, |a n| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx; exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hx)
          · intro _ _ _; exact abs_nonneg _
      _ = (fun n ↦ |a n| : Series).partial ↑K := by
          simp [Series.partial]; symm; exact sum_eq_sum (fun n ↦ |a n|) (by positivity)
      _ ≤ M := hM _

/-- Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
    and expressing `a n` as the difference of `a n + |a n|` and `|a n|`. -/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum := by
  set b : ℕ → ℝ := fun n ↦ a n + |a n|
  set c : ℕ → ℝ := fun n ↦ |a n|
  have hc_conv : (c:Series).converges := by
    have heq : (a:Series).abs = (c:Series) := by
      ext
      · rfl
      · next n => rw [abs_seq]; by_cases hn : (0:ℤ) ≤ n <;> simp [c, hn]
    rwa [absConverges, heq] at ha
  have ha_conv := converges_of_absConverges ha
  have hb_conv : (b:Series).converges := by
    rw [show (b:Series) = (a:Series) + (c:Series) from (add_coe a c).symm]
    exact (Series.add ha_conv hc_conv).1
  have hb_nn : (b:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [b, h]
    linarith [neg_abs_le (a n.toNat)]
  have hc_nn : (c:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [c, h]
  have hb_perm := converges_of_permute_nonneg hb_nn hb_conv hf
  have hc_perm := converges_of_permute_nonneg hc_nn hc_conv hf
  have ha_eq : (a:Series) = (b:Series) - (c:Series) := by
    simp only [sub_coe]; congr 1; ext n; simp [b, c]
  have haf_eq : (fun n ↦ a (f n):Series) =
      (fun n ↦ b (f n):Series) - (fun n ↦ c (f n):Series) := by
    congr 1; ext n; by_cases hn : (0:ℤ) ≤ n <;> simp [b, c, hn]
  constructor
  · show (fun n ↦ a (f n):Series).abs.converges
    have heq : (fun n ↦ a (f n):Series).abs = (fun n ↦ c (f n):Series) := by
      ext
      · rfl
      · next n => rw [abs_seq]; by_cases hn : (0:ℤ) ≤ n <;> simp [c, hn]
    rw [heq]; exact hc_perm.1
  · have h1 : (a:Series).sum = (b:Series).sum - (c:Series).sum := by
      conv_lhs => rw [ha_eq]; rw [(Series.sub hb_conv hc_conv).2]
    have h2 : (fun n ↦ a (f n):Series).sum =
        (fun n ↦ b (f n):Series).sum - (fun n ↦ c (f n):Series).sum := by
      conv_lhs => rw [haf_eq]; rw [(Series.sub hb_perm.1 hc_perm.1).2]
    linarith [hb_perm.2, hc_perm.2]

end Chapter7
