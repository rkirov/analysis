import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    constructor
    · intro h ε hε N hN
      obtain ⟨n, hn, hclose⟩ := h ε hε N hN
      change n ≥ max a.m N at hn
      have hn' : n ≥ N := by omega
      use n, hn'
      rw [Real.close_def, Real.dist_eq] at hclose
      rw [a.from_eval hn'] at hclose
      exact hclose
    · intro h ε hε N hN
      obtain ⟨n, hn, hclose⟩ := h ε hε N hN
      have hn' : n ≥ max a.m N := by omega
      use n, hn'
      rw [Real.close_def, Real.dist_eq]
      rw [a.from_eval (by omega)]
      exact hclose

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

private lemma ex643_eval {n : ℤ} (hn : n ≥ 0) :
    (Example_6_4_3 : ℤ → ℝ) n = 1 - (10:ℝ) ^ (-n - 1) := by
  show (if n ≥ 0 then _ else _) = _; simp [hn]

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  refine ⟨0, le_refl _, ?_⟩
  show dist (Example_6_4_3 (0:ℤ)) 0.8 ≤ 0.1
  rw [Real.dist_eq, abs_of_nonneg (by norm_num)]
  norm_num

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  intro h
  obtain ⟨n, hn, hclose⟩ := h 1 (show (1:ℤ) ≥ 0 by omega)
  change n ≥ max 0 1 at hn
  rw [Example_6_4_3.from_eval (show n ≥ 1 by omega), Real.close_def, Real.dist_eq] at hclose
  rw [ex643_eval (by omega : n ≥ 0)] at hclose
  have h02 : (10:ℝ) ^ (-n - 1) ≤ 1/100 := calc
    (10:ℝ) ^ (-n - 1) ≤ (10:ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1/100 := by norm_num
  linarith [(abs_le.mp hclose).2]

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro N hN; change N ≥ 0 at hN
  refine ⟨N, show N ≥ (Example_6_4_3.from N).m by change N ≥ max 0 N; omega, ?_⟩
  rw [Real.close_def, Real.dist_eq, Example_6_4_3.from_eval (show N ≥ N by omega)]
  rw [ex643_eval (show N ≥ 0 by omega)]
  rw [show (1:ℝ) - (10:ℝ) ^ (-N - 1) - 1 = -((10:ℝ) ^ (-N - 1)) by ring,
      abs_neg, abs_of_pos (by positivity)]
  calc (10:ℝ) ^ (-N - 1) ≤ (10:ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 0.1 := by norm_num

/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  rw [Sequence.limit_point_def]; intro ε hε N hN
  obtain ⟨M, hM, hpow⟩ := pow_archimedian ε hε
  refine ⟨max N M, by omega, ?_⟩
  rw [ex643_eval (show max N M ≥ 0 by omega)]
  rw [show (1:ℝ) - (10:ℝ) ^ (-(max N M : ℤ) - 1) - 1 = -((10:ℝ) ^ (-(max N M : ℤ) - 1)) by ring,
      abs_neg, abs_of_pos (by positivity)]
  calc (10:ℝ) ^ (-(max N M : ℤ) - 1)
      ≤ (10:ℝ) ^ (-(M : ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = ((10:ℝ) ^ ((M : ℤ) + 1))⁻¹ := by rw [show -(M : ℤ) - 1 = -((M : ℤ) + 1) by ring, zpow_neg]
    _ ≤ ε := le_of_lt (by rw [inv_lt_comm₀ (by positivity) hε, ← one_div]; linarith)

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

private lemma ex644_eval {n : ℤ} (hn : n ≥ 0) :
    (Example_6_4_4 : ℤ → ℝ) n = (-1:ℝ) ^ n.toNat * (1 + (10:ℝ) ^ (-n - 1)) := by
  show (if n ≥ 0 then _ else _) = _; simp [hn]

private lemma ex644_even (N : ℤ) (hN : N ≥ 0) :
    (-1:ℝ) ^ (2 * N).toNat = 1 :=
  Even.neg_one_pow ⟨N.toNat, by omega⟩

private lemma ex644_odd (N : ℤ) (hN : N ≥ 0) :
    (-1:ℝ) ^ (2 * N + 1).toNat = -1 :=
  Odd.neg_one_pow ⟨N.toNat, by omega⟩

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  refine ⟨0, le_refl _, ?_⟩
  show dist (Example_6_4_4 (0:ℤ)) 1 ≤ 0.1
  rw [Real.dist_eq, abs_of_nonneg (by norm_num)]
  norm_num

/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  intro N hN; change N ≥ 0 at hN
  refine ⟨2 * N, show 2 * N ≥ (Example_6_4_4.from N).m by change 2 * N ≥ max 0 N; omega, ?_⟩
  rw [Real.close_def, Real.dist_eq, Example_6_4_4.from_eval (show 2 * N ≥ N by omega)]
  rw [ex644_eval (by omega : 2 * N ≥ 0), ex644_even N hN, one_mul]
  rw [show (1:ℝ) + (10:ℝ) ^ (-(2 * N) - 1) - 1 = (10:ℝ) ^ (-(2 * N) - 1) by ring,
      abs_of_pos (by positivity)]
  calc (10:ℝ) ^ (-(2 * N) - 1) ≤ (10:ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 0.1 := by norm_num

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  rw [Sequence.limit_point_def]; intro ε hε N hN
  obtain ⟨M, hM, hpow⟩ := pow_archimedian ε hε
  refine ⟨2 * max N M, by omega, ?_⟩
  rw [ex644_eval (by omega : 2 * max N M ≥ 0),
      ex644_even (max N M) (by omega), one_mul]
  rw [show (1:ℝ) + (10:ℝ) ^ (-(2 * max N M) - 1) - 1 = (10:ℝ) ^ (-(2 * max N M) - 1) by ring,
      abs_of_pos (by positivity)]
  calc (10:ℝ) ^ (-(2 * max N M) - 1)
      ≤ (10:ℝ) ^ (-(M : ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = ((10:ℝ) ^ ((M : ℤ) + 1))⁻¹ := by rw [show -(M : ℤ) - 1 = -((M : ℤ) + 1) by ring, zpow_neg]
    _ ≤ ε := le_of_lt (by rw [inv_lt_comm₀ (by positivity) hε, ← one_div]; linarith)

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  rw [Sequence.limit_point_def]; intro ε hε N hN
  obtain ⟨M, hM, hpow⟩ := pow_archimedian ε hε
  refine ⟨2 * max N M + 1, by omega, ?_⟩
  rw [ex644_eval (by omega : 2 * max N M + 1 ≥ 0),
      ex644_odd (max N M) (by omega)]
  rw [show (-1:ℝ) * (1 + (10:ℝ) ^ (-(2 * max N M + 1) - 1)) - (-1) =
      -((10:ℝ) ^ (-(2 * max N M + 1) - 1)) by ring, abs_neg, abs_of_pos (by positivity)]
  calc (10:ℝ) ^ (-(2 * max N M + 1) - 1)
      ≤ (10:ℝ) ^ (-(M : ℤ) - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = ((10:ℝ) ^ ((M : ℤ) + 1))⁻¹ := by rw [show -(M : ℤ) - 1 = -((M : ℤ) + 1) by ring, zpow_neg]
    _ ≤ ε := le_of_lt (by rw [inv_lt_comm₀ (by positivity) hε, ← one_div]; linarith)

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  rw [Sequence.limit_point_def]; push_neg
  refine ⟨1/2, by norm_num, 0, show (0:ℤ) ≥ 0 by omega, ?_⟩
  intro n hn
  rw [ex644_eval (by omega : n ≥ 0), sub_zero]
  have : |(-1:ℝ) ^ n.toNat * (1 + (10:ℝ) ^ (-n - 1))| = 1 + (10:ℝ) ^ (-n - 1) := by
    rw [_root_.abs_mul, abs_pow, _root_.abs_neg, _root_.abs_one, one_pow, one_mul,
        abs_of_pos (by positivity)]
  rw [this]
  linarith [show (0:ℝ) < (10:ℝ) ^ (-n - 1) from by positivity]

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  rw [limit_point_def]; intro ε hε N hN
  rw [tendsTo_iff] at h; obtain ⟨N₀, hN₀⟩ := h ε hε
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ (le_max_right _ _)⟩

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }

noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

example (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
  apply le_antisymm
  · apply Sequence.sup_le_upper; intro m hm
    change m ≥ max 0 ↑n at hm
    have hm_nat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
    rw [Example_6_4_7.from_eval (show m ≥ ↑n from by omega)]
    simp only [show (m:ℤ) ≥ 0 from by omega, ↓reduceIte, EReal.coe_le_coe_iff]
    rcases Nat.even_or_odd m.toNat with he_m | ho_m <;> split_ifs with he_n
    · rw [Even.neg_one_pow he_m, one_mul]
      linarith [zpow_le_zpow_right₀ (show (1:ℝ) ≤ 10 by norm_num)
        (show -(m.toNat:ℤ)-1 ≤ -(↑n:ℤ)-1 from by omega)]
    · obtain ⟨a, ha⟩ := he_m; obtain ⟨b, hb⟩ := Nat.not_even_iff_odd.mp he_n
      rw [Even.neg_one_pow ⟨a, ha⟩, one_mul]
      linarith [zpow_le_zpow_right₀ (show (1:ℝ) ≤ 10 by norm_num)
        (show -(m.toNat:ℤ)-1 ≤ -(↑n:ℤ)-2 from by omega)]
    · rw [Odd.neg_one_pow ho_m]
      nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(m.toNat:ℤ) - 1),
                 zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(↑n:ℤ) - 1)]
    · rw [Odd.neg_one_pow ho_m]
      nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(m.toNat:ℤ) - 1),
                 zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(↑n:ℤ) - 2)]
  · split_ifs with he_n
    · calc ↑(1 + (10:ℝ) ^ (-(↑n:ℤ) - 1))
          = ((Example_6_4_7.from ↑n) ↑n : EReal) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_7.from_eval (le_refl _)]
            simp only [show (↑n:ℤ) ≥ 0 from by omega, ↓reduceIte, Int.toNat_natCast]
            rw [Even.neg_one_pow he_n, one_mul]
        _ ≤ (Example_6_4_7.from ↑n).sup :=
            Sequence.le_sup (by change (↑n:ℤ) ≥ max 0 ↑n; omega)
    · have he_n1 : Even (n + 1) := (Nat.not_even_iff_odd.mp he_n).add_one
      calc ↑(1 + (10:ℝ) ^ (-(↑n:ℤ) - 2))
          = ((Example_6_4_7.from ↑n) ↑(n+1) : EReal) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_7.from_eval (show (↑(n+1):ℤ) ≥ ↑n by omega)]
            simp only [show (↑(n+1):ℤ) ≥ 0 from by omega, ↓reduceIte, Int.toNat_natCast]
            rw [Even.neg_one_pow he_n1, one_mul,
                show -(↑(n+1):ℤ) - 1 = -(↑n:ℤ) - 2 from by push_cast; ring]
        _ ≤ (Example_6_4_7.from ↑n).sup :=
            Sequence.le_sup (by change (↑(n+1):ℤ) ≥ max 0 ↑n; omega)

example : Example_6_4_7.limsup = 1 := by
  -- Helper: bound each tail sup by 1 + 10^(-2k-1)
  have bound : ∀ k : ℕ, Example_6_4_7.limsup ≤ ((1 + (10:ℝ) ^ (-(2*(k:ℤ))-1)):ℝ) := by
    intro k
    calc Example_6_4_7.limsup
        ≤ Example_6_4_7.upperseq (2*k) :=
          sInf_le ⟨2*k, by change (2*(k:ℤ)) ≥ 0; omega, rfl⟩
      _ ≤ ((1 + (10:ℝ) ^ (-(2*(k:ℤ))-1)):ℝ) := by
          apply Sequence.sup_le_upper; intro n hn
          change n ≥ max 0 (2*(k:ℤ)) at hn
          have hn_nat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
          rw [EReal.coe_le_coe_iff,
              Example_6_4_7.from_eval (show n ≥ (2*(k:ℤ)) from by omega)]
          simp only [show (n:ℤ) ≥ 0 from by omega, ↓reduceIte]
          rcases Nat.even_or_odd n.toNat with he | ho
          · rw [he.neg_one_pow, one_mul]
            linarith [zpow_le_zpow_right₀ (show (1:ℝ) ≤ 10 by norm_num)
              (show -(n.toNat:ℤ)-1 ≤ -(2*(k:ℤ))-1 from by omega)]
          · rw [ho.neg_one_pow]
            nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(n.toNat:ℤ) - 1),
                       zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(2*(k:ℤ)) - 1)]
  apply le_antisymm
  · -- limsup ≤ 1: by contradiction using Archimedean property
    rw [← not_lt]; intro hlt
    have hne_bot : Example_6_4_7.limsup ≠ ⊥ := ne_of_gt (lt_trans (EReal.bot_lt_coe 1) hlt)
    have hne_top : Example_6_4_7.limsup ≠ ⊤ := by
      intro heq; have := bound 0; rw [heq] at this
      exact absurd this (not_le.mpr (EReal.coe_lt_top _))
    set r := Example_6_4_7.limsup.toReal
    have hr : Example_6_4_7.limsup = (r : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
    have hr_gt : r > 1 := by rw [hr] at hlt; exact_mod_cast hlt
    obtain ⟨M, hM, hpow⟩ := pow_archimedian (r - 1) (by linarith)
    have h1 : r ≤ 1 + (10:ℝ) ^ (-(2*M)-1) := by
      have := bound M.toNat; rw [hr] at this
      rw [show (M.toNat : ℤ) = M from Int.toNat_of_nonneg (by omega)] at this
      exact_mod_cast this
    have h2 : (10:ℝ) ^ (-(2*M)-1) < r - 1 := calc
      (10:ℝ) ^ (-(2*M)-1) ≤ (10:ℝ) ^ (-(M:ℤ)-1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = ((10:ℝ) ^ ((M:ℤ)+1))⁻¹ := by rw [show -(M:ℤ)-1 = -((M:ℤ)+1) by ring, zpow_neg]
      _ < r - 1 := by rw [inv_lt_comm₀ (by positivity) (by linarith), ← one_div]; linarith
    linarith
  · -- 1 ≤ limsup: every upperseq N ≥ 1, witnessed by even index 2N
    apply le_sInf; rintro _ ⟨N, hN, rfl⟩
    change N ≥ 0 at hN
    have h_mem : 2*N ≥ (Example_6_4_7.from N).m := by change 2*N ≥ max 0 N; omega
    have h_val : (Example_6_4_7.from N) (2*N) = 1 + (10:ℝ) ^ (-(2*N) - 1) := by
      rw [Example_6_4_7.from_eval (show 2*N ≥ N by omega), ex644_eval (by omega : 2*N ≥ 0),
          ex644_even N hN, one_mul]
    calc (1:EReal) ≤ ((1 + (10:ℝ) ^ (-(2*N) - 1)):ℝ) := by
          exact_mod_cast show (1:ℝ) ≤ 1 + (10:ℝ) ^ (-(2*N)-1) from
            by linarith [zpow_pos (show (0:ℝ) < 10 by norm_num) (-(2*N)-1)]
      _ = ((Example_6_4_7.from N) (2*N) : EReal) := by rw [EReal.coe_eq_coe_iff]; exact h_val.symm
      _ ≤ (Example_6_4_7.from N).sup := Sequence.le_sup h_mem

example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  apply le_antisymm
  · split_ifs with he_n
    · calc (Example_6_4_7.from ↑n).inf
          ≤ ((Example_6_4_7.from ↑n) ↑(n+1) : EReal) :=
            Sequence.ge_inf (by change (↑(n+1):ℤ) ≥ max 0 ↑n; omega)
        _ = ↑(-(1 + (10:ℝ)^(-(n:ℤ)-2))) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_7.from_eval (show (↑(n+1):ℤ) ≥ ↑n by omega)]
            simp only [show (↑(n+1):ℤ) ≥ 0 from by omega, ↓reduceIte, Int.toNat_natCast]
            rw [he_n.add_one.neg_one_pow,
                show -(↑(n+1):ℤ) - 1 = -(↑n:ℤ) - 2 from by push_cast; ring]
            ring
    · calc (Example_6_4_7.from ↑n).inf
          ≤ ((Example_6_4_7.from ↑n) ↑n : EReal) :=
            Sequence.ge_inf (by change (↑n:ℤ) ≥ max 0 ↑n; omega)
        _ = ↑(-(1 + (10:ℝ)^(-(n:ℤ)-1))) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_7.from_eval (le_refl _)]
            simp only [show (↑n:ℤ) ≥ 0 from by omega, ↓reduceIte, Int.toNat_natCast]
            rw [(Nat.not_even_iff_odd.mp he_n).neg_one_pow]; ring
  · apply Sequence.inf_ge_lower; intro m hm
    change m ≥ max 0 ↑n at hm
    have hm_nat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
    rw [ge_iff_le, Example_6_4_7.from_eval (show m ≥ ↑n from by omega)]
    simp only [show (m:ℤ) ≥ 0 from by omega, ↓reduceIte, EReal.coe_le_coe_iff]
    rcases Nat.even_or_odd m.toNat with he_m | ho_m <;> split_ifs with he_n
    · rw [he_m.neg_one_pow, one_mul]
      nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(m.toNat:ℤ) - 1),
                 zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(↑n:ℤ) - 2)]
    · rw [he_m.neg_one_pow, one_mul]
      nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(m.toNat:ℤ) - 1),
                 zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(↑n:ℤ) - 1)]
    · rw [ho_m.neg_one_pow]
      obtain ⟨a, ha⟩ := ho_m; obtain ⟨b, hb⟩ := he_n
      nlinarith [zpow_le_zpow_right₀ (show (1:ℝ) ≤ 10 by norm_num)
        (show -(m.toNat:ℤ)-1 ≤ -(↑n:ℤ)-2 from by omega)]
    · rw [ho_m.neg_one_pow]
      nlinarith [zpow_le_zpow_right₀ (show (1:ℝ) ≤ 10 by norm_num)
        (show -(m.toNat:ℤ)-1 ≤ -(↑n:ℤ)-1 from by omega)]

example : Example_6_4_7.liminf = -1 := by
  -- Helper: bound each tail inf from below by -(1 + 10^(-2k-2))
  have bound : ∀ k : ℕ, ((-(1 + (10:ℝ) ^ (-(2*(k:ℤ))-2)):ℝ)) ≤ Example_6_4_7.liminf := by
    intro k
    calc ((-(1 + (10:ℝ) ^ (-(2*(k:ℤ))-2)):ℝ))
        ≤ Example_6_4_7.lowerseq (2*k+1) := by
          apply Sequence.inf_ge_lower; intro n hn
          change n ≥ max 0 (2*(k:ℤ)+1) at hn
          have hn_nat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
          rw [ge_iff_le, EReal.coe_le_coe_iff,
              Example_6_4_7.from_eval (show n ≥ 2*(k:ℤ)+1 from by omega)]
          simp only [show (n:ℤ) ≥ 0 from by omega, ↓reduceIte]
          rcases Nat.even_or_odd n.toNat with he | ho
          · rw [he.neg_one_pow, one_mul]
            nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(n.toNat:ℤ) - 1),
                       zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(2*(k:ℤ)) - 2)]
          · rw [ho.neg_one_pow]
            nlinarith [zpow_le_zpow_right₀ (show (1:ℝ) ≤ 10 by norm_num)
                         (show -(n.toNat:ℤ)-1 ≤ -(2*(k:ℤ))-2 from by omega),
                       zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(2*(k:ℤ)) - 2)]
      _ ≤ Example_6_4_7.liminf :=
          le_sSup ⟨2*k+1, by change (2*(k:ℤ)+1) ≥ 0; omega, rfl⟩
  apply le_antisymm
  · -- liminf ≤ -1: every lowerseq N ≤ -1 (witnessed by odd index 2N+1)
    apply sSup_le; rintro _ ⟨N, hN, rfl⟩
    change N ≥ 0 at hN
    have h_mem : 2*N+1 ≥ (Example_6_4_7.from N).m := by change 2*N+1 ≥ max 0 N; omega
    have h_val : (Example_6_4_7.from N) (2*N+1) = -(1 + (10:ℝ) ^ (-(2*N+1) - 1)) := by
      rw [Example_6_4_7.from_eval (show 2*N+1 ≥ N by omega),
          ex644_eval (by omega : 2*N+1 ≥ 0), ex644_odd N hN, neg_one_mul]
    calc (Example_6_4_7.from N).inf
        ≤ ((Example_6_4_7.from N) (2*N+1) : EReal) := Sequence.ge_inf h_mem
      _ = ((-(1 + (10:ℝ) ^ (-(2*N+1) - 1))):ℝ) := by rw [EReal.coe_eq_coe_iff]; exact h_val
      _ ≤ ((-1:ℝ):EReal) := by
          rw [EReal.coe_le_coe_iff]
          linarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(2*N+1)-1)]
  · -- -1 ≤ liminf: by contradiction using Archimedean property
    rw [← not_lt]; intro hlt
    have hne_top : Example_6_4_7.liminf ≠ ⊤ := by
      intro h; rw [h] at hlt; exact absurd hlt (not_lt.mpr le_top)
    have hne_bot : Example_6_4_7.liminf ≠ ⊥ := by
      intro heq; have := bound 0; rw [heq] at this; exact absurd this (not_le.mpr (EReal.bot_lt_coe _))
    set r := Example_6_4_7.liminf.toReal
    have hr : Example_6_4_7.liminf = (r : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
    have hr_lt : r < -1 := by
      rw [hr, show (-1:EReal) = ((-1:ℝ):EReal) from by simp [EReal.coe_neg]] at hlt
      exact_mod_cast hlt
    obtain ⟨M, hM, hpow⟩ := pow_archimedian (-1 - r) (by linarith)
    have h1 : -(1 + (10:ℝ) ^ (-(2*M)-2)) ≤ r := by
      have := bound M.toNat; rw [hr] at this
      rw [show (M.toNat : ℤ) = M from Int.toNat_of_nonneg (by omega)] at this
      exact_mod_cast this
    have h2 : (10:ℝ) ^ (-(2*M)-2) < -1 - r := calc
      (10:ℝ) ^ (-(2*M)-2) ≤ (10:ℝ) ^ (-(M:ℤ)-1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = ((10:ℝ) ^ ((M:ℤ)+1))⁻¹ := by rw [show -(M:ℤ)-1 = -((M:ℤ)+1) by ring, zpow_neg]
      _ < -1 - r := by rw [inv_lt_comm₀ (by positivity) (by linarith), ← one_div]; linarith
    linarith

example : Example_6_4_7.sup = (1.1:ℝ) := by
  apply le_antisymm
  · apply Sequence.sup_le_upper; intro n hn
    rw [EReal.coe_le_coe_iff]; change n ≥ 0 at hn
    simp only [hn, ↓reduceIte]
    rcases Nat.even_or_odd n.toNat with he | ho
    · simp only [he.neg_one_pow, one_mul]
      linarith [(zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 10)
        (show -(n.toNat:ℤ)-1 ≤ -1 by omega)).trans_eq (show (10:ℝ)^(-1:ℤ) = 1/10 from by norm_num)]
    · simp only [ho.neg_one_pow]
      nlinarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(n.toNat:ℤ) - 1)]
  · have : (Example_6_4_7 (0:ℤ) : EReal) = (1.1:ℝ) := by
      rw [EReal.coe_eq_coe_iff]; simp; norm_num
    rw [← this]; exact Sequence.le_sup (by change (0:ℤ) ≥ 0; omega)

example : Example_6_4_7.inf = (-1.01:ℝ) := by
  apply le_antisymm
  · have : (Example_6_4_7 (1:ℤ) : EReal) = (-1.01:ℝ) := by
      rw [EReal.coe_eq_coe_iff]; simp; norm_num
    rw [← this]; exact Sequence.ge_inf (by change (1:ℤ) ≥ 0; omega)
  · apply Sequence.inf_ge_lower; intro n hn
    rw [ge_iff_le, EReal.coe_le_coe_iff]; change n ≥ 0 at hn
    simp only [hn, ↓reduceIte]
    rcases Nat.even_or_odd n.toNat with he | ho
    · simp only [he.neg_one_pow, one_mul]
      linarith [zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(n.toNat:ℤ) - 1)]
    · simp only [ho.neg_one_pow]
      have hge : n.toNat ≥ 1 := ho.pos
      nlinarith [(zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 10)
        (show -(n.toNat:ℤ)-1 ≤ -2 by omega)).trans_eq (show (10:ℝ)^(-2:ℤ) = 1/100 from by norm_num),
        zpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (-(n.toNat:ℤ) - 1)]

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

private lemma ex648_even {n : ℕ} (h : Even n) :
    (Example_6_4_8 : ℤ → ℝ) ↑n = ↑n + 1 := by
  show (if (↑n:ℤ) ≥ 0 then (if Even (↑n:ℤ).toNat then _ else _) else 0) = _
  rw [if_pos (show (↑n:ℤ) ≥ 0 by omega), Int.toNat_natCast, if_pos h]

private lemma ex648_odd {n : ℕ} (h : ¬Even n) :
    (Example_6_4_8 : ℤ → ℝ) ↑n = -(↑n:ℝ) - 1 := by
  show (if (↑n:ℤ) ≥ 0 then (if Even (↑n:ℤ).toNat then _ else _) else 0) = _
  rw [if_pos (show (↑n:ℤ) ≥ 0 by omega), Int.toNat_natCast, if_neg h]

private lemma ex648_upperseq_top (n : ℕ) : Example_6_4_8.upperseq n = ⊤ := by
  rw [sSup_eq_top]; intro b hb
  by_cases hb' : b = ⊥
  · exact ⟨_, ⟨2*↑n, show (2*(↑n:ℤ)) ≥ max (0:ℤ) ↑n by omega, rfl⟩,
          hb' ▸ EReal.bot_lt_coe _⟩
  · set M := b.toReal
    have hb_eq : b = (M : EReal) := (EReal.coe_toReal (ne_top_of_lt hb) hb').symm
    obtain ⟨K, hK⟩ := exists_nat_gt M
    set k : ℕ := 2 * max n K
    refine ⟨_, ⟨↑k, show (↑k:ℤ) ≥ max (0:ℤ) ↑n by omega, rfl⟩, ?_⟩
    rw [hb_eq, Example_6_4_8.from_eval (show (↑k:ℤ) ≥ ↑n by omega),
        ex648_even ⟨max n K, by omega⟩, EReal.coe_lt_coe_iff]
    have : (k:ℝ) ≥ K := by exact_mod_cast show k ≥ K from by omega
    linarith

example : Example_6_4_8.limsup = ⊤ := by
  rw [sInf_eq_top]; rintro _ ⟨N, hN, rfl⟩; change N ≥ 0 at hN
  rw [← Int.toNat_of_nonneg hN]; exact ex648_upperseq_top N.toNat

private lemma ex648_lowerseq_bot (n : ℕ) : Example_6_4_8.lowerseq n = ⊥ := by
  rw [sInf_eq_bot]; intro b hb
  by_cases hb' : b = ⊤
  · exact ⟨_, ⟨2*↑n+1, show 2*(↑n:ℤ)+1 ≥ max (0:ℤ) ↑n by omega, rfl⟩,
          hb' ▸ EReal.coe_lt_top _⟩
  · set M := b.toReal
    have hb_eq : b = (M : EReal) := (EReal.coe_toReal hb' (ne_bot_of_gt hb)).symm
    obtain ⟨K, hK⟩ := exists_nat_gt (-M)
    set k : ℕ := 2 * max n K + 1
    have hkodd : ¬ Even k := Nat.not_even_iff_odd.mpr ⟨max n K, by omega⟩
    refine ⟨_, ⟨↑k, show (↑k:ℤ) ≥ max (0:ℤ) ↑n by omega, rfl⟩, ?_⟩
    rw [hb_eq, Example_6_4_8.from_eval (show (↑k:ℤ) ≥ ↑n by omega),
        ex648_odd hkodd, EReal.coe_lt_coe_iff]
    have : (k:ℝ) ≥ K := by exact_mod_cast show k ≥ K from by omega
    linarith

example : Example_6_4_8.liminf = ⊥ := by
  rw [sSup_eq_bot]; rintro _ ⟨N, hN, rfl⟩; change N ≥ 0 at hN
  rw [← Int.toNat_of_nonneg hN]; exact ex648_lowerseq_bot N.toNat

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

private lemma ex649_even {n : ℕ} (h : Even n) :
    (Example_6_4_9 : ℤ → ℝ) ↑n = ((n : ℝ) + 1)⁻¹ := by
  show (if (↑n:ℤ) ≥ 0 then (if Even (↑n:ℤ).toNat then _ else _) else 0) = _
  rw [if_pos (show (↑n:ℤ) ≥ 0 by omega), Int.toNat_natCast, if_pos h]

private lemma ex649_odd {n : ℕ} (h : ¬Even n) :
    (Example_6_4_9 : ℤ → ℝ) ↑n = -((n : ℝ) + 1)⁻¹ := by
  show (if (↑n:ℤ) ≥ 0 then (if Even (↑n:ℤ).toNat then _ else _) else 0) = _
  rw [if_pos (show (↑n:ℤ) ≥ 0 by omega), Int.toNat_natCast, if_neg h]

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ := by
  apply le_antisymm
  · apply Sequence.sup_le_upper; intro m hm
    change m ≥ max 0 ↑n at hm
    have hm_nat : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
    rw [Example_6_4_9.from_eval (show m ≥ ↑n from by omega)]
    simp only [show (m:ℤ) ≥ 0 from by omega, ↓reduceIte, EReal.coe_le_coe_iff]
    rcases Nat.even_or_odd m.toNat with he_m | ho_m
    · -- m even: 1/(m+1) ≤ ...
      rw [if_pos he_m]; split_ifs with he_n
      · exact inv_anti₀ (by positivity) (by exact_mod_cast show n + 1 ≤ m.toNat + 1 by omega)
      · obtain ⟨b, hb⟩ := Nat.not_even_iff_odd.mp he_n
        obtain ⟨a, ha⟩ := he_m
        exact inv_anti₀ (by positivity) (by exact_mod_cast show n + 2 ≤ m.toNat + 1 by omega)
    · -- m odd: negative ≤ positive
      rw [if_neg (Nat.not_even_iff_odd.mpr ho_m)]; split_ifs
      · exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
      · exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
  · split_ifs with he_n
    · calc ↑((n + 1 : ℝ)⁻¹)
          = ((Example_6_4_9.from ↑n) ↑n : EReal) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_9.from_eval (le_refl _), ex649_even he_n]
        _ ≤ (Example_6_4_9.from ↑n).sup :=
            Sequence.le_sup (by change (↑n:ℤ) ≥ max 0 ↑n; omega)
    · have he_n1 : Even (n + 1) := (Nat.not_even_iff_odd.mp he_n).add_one
      calc ↑((n + 2 : ℝ)⁻¹)
          = ((Example_6_4_9.from ↑n) ↑(n+1) : EReal) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_9.from_eval (show (↑(n+1):ℤ) ≥ ↑n by omega),
                ex649_even he_n1]
            push_cast; ring
        _ ≤ (Example_6_4_9.from ↑n).sup :=
            Sequence.le_sup (by change (↑(n+1):ℤ) ≥ max 0 ↑n; omega)

private lemma ex649_upperseq_le (k : ℕ) :
    Example_6_4_9.limsup ≤ ((2*k + 1 : ℝ)⁻¹) := by
  calc Example_6_4_9.limsup
      ≤ Example_6_4_9.upperseq (2*k) :=
        sInf_le ⟨2*k, by change (2*(k:ℤ)) ≥ 0; omega, rfl⟩
    _ ≤ ((2*k + 1 : ℝ)⁻¹) := by
        apply Sequence.sup_le_upper; intro m hm
        change m ≥ max 0 (2*(k:ℤ)) at hm
        rw [Example_6_4_9.from_eval (show m ≥ (2*(k:ℤ)) from by omega)]
        simp only [show (m:ℤ) ≥ 0 from by omega, ↓reduceIte, EReal.coe_le_coe_iff]
        rcases Nat.even_or_odd m.toNat with he | ho
        · rw [if_pos he]
          exact inv_anti₀ (by positivity)
            (by exact_mod_cast show 2*k + 1 ≤ m.toNat + 1 by omega)
        · rw [if_neg (Nat.not_even_iff_odd.mpr ho)]
          exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity)

example : Example_6_4_9.limsup = 0 := by
  apply le_antisymm
  · rw [← not_lt]; intro hlt
    have hne_bot : Example_6_4_9.limsup ≠ ⊥ := ne_of_gt (lt_trans (EReal.bot_lt_coe 0) hlt)
    have hne_top : Example_6_4_9.limsup ≠ ⊤ := by
      intro heq; have := ex649_upperseq_le 0; rw [heq] at this
      exact absurd this (not_le.mpr (EReal.coe_lt_top _))
    set r := Example_6_4_9.limsup.toReal
    have hr : Example_6_4_9.limsup = (r : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
    have hr_pos : r > 0 := by rw [hr] at hlt; exact_mod_cast hlt
    obtain ⟨K, hK⟩ := exists_nat_gt r⁻¹
    have h1 : r ≤ (2*K + 1 : ℝ)⁻¹ := by
      have := ex649_upperseq_le K; rw [hr] at this; exact_mod_cast this
    have h2 : (2*K + 1 : ℝ)⁻¹ < r := by
      rw [inv_lt_comm₀ (by positivity) hr_pos]; linarith
    linarith
  · apply le_sInf; rintro _ ⟨N, hN, rfl⟩
    change N ≥ 0 at hN
    have hk_mem : 2*N ≥ (Example_6_4_9.from N).m := by change 2*N ≥ max 0 N; omega
    calc (0:EReal) ≤ ((2*(N:ℝ) + 1)⁻¹ : ℝ) := by exact_mod_cast inv_nonneg.mpr (by positivity)
      _ = ((Example_6_4_9.from N) (2*N) : EReal) := by
          rw [EReal.coe_eq_coe_iff, Example_6_4_9.from_eval (show 2*N ≥ N by omega)]
          rw [show (2*N : ℤ) = ↑(2*N.toNat) from by omega,
              ex649_even (show Even (2*N.toNat) from ⟨N.toNat, by ring⟩)]
          push_cast; rw [show (N.toNat : ℝ) = ((N : ℤ) : ℝ) from by
            exact_mod_cast Int.toNat_of_nonneg hN]
      _ ≤ (Example_6_4_9.from N).sup := Sequence.le_sup hk_mem

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by
  apply le_antisymm
  · split_ifs with he_n
    · have ho_n1 : ¬Even (n + 1) := Nat.not_even_iff_odd.mpr (Even.add_one he_n)
      calc (Example_6_4_9.from ↑n).inf
          ≤ ((Example_6_4_9.from ↑n) ↑(n+1) : EReal) :=
            Sequence.ge_inf (by change (↑(n+1):ℤ) ≥ max 0 ↑n; omega)
        _ = ↑(-(n + 2 : ℝ)⁻¹) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_9.from_eval (show (↑(n+1):ℤ) ≥ ↑n by omega),
                ex649_odd ho_n1]
            push_cast; ring
    · calc (Example_6_4_9.from ↑n).inf
          ≤ ((Example_6_4_9.from ↑n) ↑n : EReal) :=
            Sequence.ge_inf (by change (↑n:ℤ) ≥ max 0 ↑n; omega)
        _ = ↑(-(n + 1 : ℝ)⁻¹) := by
            rw [EReal.coe_eq_coe_iff, Example_6_4_9.from_eval (le_refl _), ex649_odd he_n]
  · apply Sequence.inf_ge_lower; intro m hm
    change m ≥ max 0 ↑n at hm
    rw [ge_iff_le, Example_6_4_9.from_eval (show m ≥ ↑n from by omega)]
    simp only [show (m:ℤ) ≥ 0 from by omega, ↓reduceIte, EReal.coe_le_coe_iff]
    rcases Nat.even_or_odd m.toNat with he_m | ho_m
    · rw [if_pos he_m]; split_ifs
      · exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
      · exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho_m)]; split_ifs with he_n
      · obtain ⟨a, ha⟩ := ho_m; obtain ⟨b, hb⟩ := he_n
        rw [_root_.neg_le_neg_iff]
        exact inv_anti₀ (by positivity) (by exact_mod_cast show n + 2 ≤ m.toNat + 1 by omega)
      · rw [_root_.neg_le_neg_iff]
        exact inv_anti₀ (by positivity) (by exact_mod_cast show n + 1 ≤ m.toNat + 1 by omega)

private lemma ex649_lowerseq_ge (k : ℕ) :
    ((-((2*(k:ℝ) + 1)⁻¹)):ℝ) ≤ Example_6_4_9.liminf := by
  calc ((-((2*(k:ℝ) + 1)⁻¹)):ℝ)
      ≤ Example_6_4_9.lowerseq (2*k) := by
        apply Sequence.inf_ge_lower; intro m hm
        change m ≥ max 0 (2*(k:ℤ)) at hm
        rw [ge_iff_le, EReal.coe_le_coe_iff,
            Example_6_4_9.from_eval (show m ≥ (2*(k:ℤ)) from by omega)]
        simp only [show (m:ℤ) ≥ 0 from by omega, ↓reduceIte]
        rcases Nat.even_or_odd m.toNat with he | ho
        · rw [if_pos he]
          exact le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
        · rw [if_neg (Nat.not_even_iff_odd.mpr ho), _root_.neg_le_neg_iff]
          exact inv_anti₀ (by positivity)
            (by exact_mod_cast show 2*k + 1 ≤ m.toNat + 1 by omega)
    _ ≤ Example_6_4_9.liminf :=
        le_sSup ⟨2*k, by change (2*(k:ℤ)) ≥ 0; omega, rfl⟩

example : Example_6_4_9.liminf = 0 := by
  apply le_antisymm
  · apply sSup_le; rintro _ ⟨N, hN, rfl⟩
    change N ≥ 0 at hN
    set k := 2 * N + 1 with hk_def
    have hk_odd : ¬Even (2 * N.toNat + 1) := Nat.not_even_iff_odd.mpr ⟨N.toNat, by ring⟩
    have hk_mem : k ≥ (Example_6_4_9.from N).m := by change 2*N+1 ≥ max 0 N; omega
    calc (Example_6_4_9.from N).inf
        ≤ ((Example_6_4_9.from N) k : EReal) := Sequence.ge_inf hk_mem
      _ = ((-(2*(N:ℝ) + 2)⁻¹):ℝ) := by
          rw [EReal.coe_eq_coe_iff, Example_6_4_9.from_eval (show k ≥ N by omega)]
          rw [show (k : ℤ) = ↑(k.toNat) from by omega,
              ex649_odd (show ¬Even k.toNat from by
                rwa [show k.toNat = 2*N.toNat + 1 from by omega])]
          rw [show (k.toNat : ℝ) = ((k : ℤ) : ℝ) from by
            exact_mod_cast Int.toNat_of_nonneg (show k ≥ 0 by omega)]
          simp only [hk_def]; push_cast; ring
      _ ≤ (0:EReal) := by exact_mod_cast neg_nonpos.mpr (by positivity)
  · rw [← not_lt]; intro hlt
    have hne_top : Example_6_4_9.liminf ≠ ⊤ := by
      intro h; rw [h] at hlt; exact absurd hlt (not_lt.mpr le_top)
    have hne_bot : Example_6_4_9.liminf ≠ ⊥ := by
      intro heq; have := ex649_lowerseq_ge 0; rw [heq] at this
      exact absurd this (not_le.mpr (EReal.bot_lt_coe _))
    set r := Example_6_4_9.liminf.toReal
    have hr : Example_6_4_9.liminf = (r : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
    have hr_neg : r < 0 := by rw [hr] at hlt; exact_mod_cast hlt
    obtain ⟨K, hK⟩ := exists_nat_gt (-r)⁻¹
    have h1 : -((2*(K:ℝ) + 1)⁻¹) ≤ r := by
      have := ex649_lowerseq_ge K; rw [hr] at this; exact_mod_cast this
    have h2 : r < -((2*(K:ℝ) + 1)⁻¹) := by
      have hK_pos : (0:ℝ) < K := lt_trans (inv_pos.mpr (neg_pos.mpr hr_neg)) hK
      have h_inv : (K:ℝ)⁻¹ < -r := by rwa [inv_lt_comm₀ hK_pos (neg_pos.mpr hr_neg)]
      linarith [inv_anti₀ hK_pos (show (K:ℝ) ≤ 2*K + 1 by linarith)]
    linarith

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

private lemma ex6410_eval {n : ℤ} (hn : n ≥ 0) :
    (Example_6_4_10 : ℤ → ℝ) n = (n + 1 : ℝ) := by
  show (if n ≥ 0 then _ else _) = _; simp [hn]
  exact_mod_cast Int.toNat_of_nonneg hn

example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by
  show (Example_6_4_10.from n).sup = ⊤
  apply le_antisymm le_top (le_of_forall_lt _)
  intro c hc
  cases c with
  | bot =>
    exact lt_of_lt_of_le (EReal.bot_lt_coe _)
      ((Example_6_4_10.from n).le_sup (show (n:ℤ) ≥ max 0 ↑n by omega))
  | top => exact absurd hc (lt_irrefl _)
  | coe r =>
    let k := max n ⌈r⌉₊
    have hkn : k ≥ n := le_max_left _ _
    calc (r : EReal) < (Example_6_4_10.from n ↑k) := by
            rw [Example_6_4_10.from_eval (show (k:ℤ) ≥ n by omega),
                ex6410_eval (show (k:ℤ) ≥ 0 by omega)]
            rw [EReal.coe_lt_coe_iff]
            have h1 : (r:ℝ) ≤ ⌈r⌉₊ := Nat.le_ceil r
            have h2 : (⌈r⌉₊ : ℝ) ≤ k := by exact_mod_cast le_max_right n ⌈r⌉₊
            have : (↑(k : ℤ) : ℝ) = (k : ℝ) := Int.cast_natCast k
            linarith
      _ ≤ (Example_6_4_10.from n).sup :=
            (Example_6_4_10.from n).le_sup (show (k:ℤ) ≥ max 0 ↑n by omega)

example : Example_6_4_10.limsup = ⊤ := by
  apply le_antisymm le_top
  apply le_sInf
  rintro x ⟨N, hN, rfl⟩
  have hN' : N = ↑N.toNat := (Int.toNat_of_nonneg hN).symm
  rw [hN']
  show ⊤ ≤ (Example_6_4_10.from ↑N.toNat).sup
  rw [Sequence.sup]; apply le_of_forall_lt; intro c hc
  cases c with
  | bot =>
    exact lt_of_lt_of_le (EReal.bot_lt_coe _)
      (le_csSup (OrderTop.bddAbove _) ⟨↑N.toNat, by show (↑N.toNat : ℤ) ≥ max 0 ↑N.toNat; omega, rfl⟩)
  | top => exact absurd hc (lt_irrefl _)
  | coe r =>
    let k := max N.toNat ⌈r⌉₊
    have hmem : ↑((Example_6_4_10.from ↑N.toNat).seq ↑k) ∈
        { x : EReal | ∃ n ≥ (Example_6_4_10.from ↑N.toNat).m, x = ↑((Example_6_4_10.from ↑N.toNat).seq n) } :=
      ⟨↑k, by show (k:ℤ) ≥ max 0 ↑N.toNat; omega, rfl⟩
    apply lt_of_lt_of_le _ (le_csSup (OrderTop.bddAbove _) hmem)
    rw [Example_6_4_10.from_eval (show (k:ℤ) ≥ ↑N.toNat by omega),
        ex6410_eval (show (k:ℤ) ≥ 0 by omega)]
    rw [EReal.coe_lt_coe_iff]
    have h1 : (r:ℝ) ≤ ⌈r⌉₊ := Nat.le_ceil r
    have h2 : (⌈r⌉₊ : ℝ) ≤ k := by exact_mod_cast le_max_right N.toNat ⌈r⌉₊
    have : (↑(k : ℤ) : ℝ) = (k : ℝ) := Int.cast_natCast k
    linarith

private lemma ex6410_lowerseq (N : ℤ) (hN : N ≥ 0) :
    Example_6_4_10.lowerseq N = ↑((N : ℝ) + 1) := by
  show (Example_6_4_10.from N).inf = ↑((N : ℝ) + 1)
  apply le_antisymm
  · calc (Example_6_4_10.from N).inf
        ≤ Example_6_4_10.from N N :=
          (Example_6_4_10.from N).ge_inf (show N ≥ max 0 N by omega)
      _ = ↑((N : ℝ) + 1) := by
          rw [Example_6_4_10.from_eval (le_refl N), ex6410_eval hN]
  · apply (Example_6_4_10.from N).inf_ge_lower
    intro k hk
    have hkN : k ≥ N := by change k ≥ max 0 N at hk; omega
    rw [Example_6_4_10.from_eval hkN, ex6410_eval (by omega)]
    rw [ge_iff_le, EReal.coe_le_coe_iff]
    have : (N : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hkN
    linarith

example (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by
  rw [show (↑n + 1 : EReal) = ↑(↑n + 1 : ℝ) from by push_cast; ring_nf]
  exact ex6410_lowerseq ↑n (by omega)

example : Example_6_4_10.liminf = ⊤ := by
  apply le_antisymm le_top (le_of_forall_lt _)
  intro c hc
  cases c with
  | bot =>
    apply lt_of_lt_of_le (EReal.bot_lt_coe ((0:ℝ) + 1))
    apply le_sSup
    refine ⟨0, le_refl _, ?_⟩
    have := (ex6410_lowerseq 0 (le_refl _)).symm
    norm_cast at this ⊢
  | top => exact absurd hc (lt_irrefl _)
  | coe r =>
    have hmem : ↑((↑⌈r⌉₊ : ℝ) + 1) ∈
        { x : EReal | ∃ N ≥ Example_6_4_10.m, x = Example_6_4_10.lowerseq N } := by
      refine ⟨↑⌈r⌉₊, ?_, (ex6410_lowerseq ↑⌈r⌉₊ (by omega)).symm⟩
      show (⌈r⌉₊ : ℤ) ≥ 0; omega
    calc (r : EReal) < ↑((↑⌈r⌉₊ : ℝ) + 1) := by
            rw [EReal.coe_lt_coe_iff]
            have : (r:ℝ) ≤ ⌈r⌉₊ := Nat.le_ceil r; linarith
      _ ≤ _ := le_sSup hmem

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp [limsup, sInf_lt_iff] at h
  obtain ⟨_, ⟨ N, ⟨ hN, rfl ⟩ ⟩, ha ⟩ := h; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp [liminf, lt_sSup_iff] at h
  obtain ⟨_, ⟨ N, ⟨ hN, rfl ⟩ ⟩, ha ⟩ := h; use N
  simp [hN, lowerseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_lt_of_le ha ((a.from N).ge_inf hn') using 1
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  have hx : x > a.lowerseq N := by apply lt_of_le_of_lt (le_sSup _) h; simp; use N
  choose n hn _ hxn using exists_between_gt_inf hx
  grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  calc a.inf ≤ a.lowerseq a.m := by
        apply inf_ge_lower; intro n hn
        have hn' : n ≥ a.m := by change n ≥ max a.m a.m at hn; omega
        have := a.ge_inf hn'; rw [show (a.from a.m) n = a n from a.from_eval hn']; exact this
    _ ≤ a.liminf := le_sSup ⟨a.m, le_refl _, rfl⟩

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  apply sSup_le; intro x ⟨N, hN, hx⟩; subst hx
  apply le_sInf; intro y ⟨M, hM, hy⟩; subst hy
  -- Need: (a.from N).inf ≤ (a.from M).sup
  -- The sequence a.from (max N M) is a "subsequence" of both
  apply le_trans ((a.from N).ge_inf (show max N M ≥ (a.from N).m by change _ ≥ max a.m N; omega))
  apply le_trans _ ((a.from M).le_sup (show max N M ≥ (a.from M).m by change _ ≥ max a.m M; omega))
  rw [EReal.coe_le_coe_iff, a.from_eval (le_max_left _ _), a.from_eval (le_max_right _ _)]

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  calc a.limsup ≤ a.upperseq a.m := sInf_le ⟨a.m, le_refl _, rfl⟩
    _ ≤ a.sup := by
        apply sup_le_upper; intro n hn
        have hn' : n ≥ a.m := by change n ≥ max a.m a.m at hn; omega
        have := a.le_sup hn'; rw [show (a.from a.m) n = a n from a.from_eval hn']; exact this

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  rw [limit_point_def] at h
  have aux_ne_top : ∀ (b : Sequence), b.inf ≠ ⊤ :=
    fun b => ne_of_lt (lt_of_le_of_lt (b.ge_inf (le_refl _)) (EReal.coe_lt_top _))
  have aux_ne_bot : ∀ (b : Sequence), b.sup ≠ ⊥ :=
    fun b => ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (b.le_sup (le_refl _)))
  constructor
  · -- a.liminf ≤ ↑c
    apply sSup_le; rintro _ ⟨N, hN, rfl⟩
    by_contra hlt; push_neg at hlt
    -- hlt : ↑c < (a.from N).inf
    have hne_bot : (a.from N).inf ≠ ⊥ := ne_of_gt (lt_trans (EReal.bot_lt_coe c) hlt)
    have hne_top := aux_ne_top (a.from N)
    have hr : (a.from N).inf = ↑(a.from N).inf.toReal := (EReal.coe_toReal hne_top hne_bot).symm
    have hlt' : c < (a.from N).inf.toReal := by
      rwa [← EReal.coe_lt_coe_iff, ← hr]
    obtain ⟨n, hn, hclose⟩ := h (((a.from N).inf.toReal - c) / 2) (by linarith) N hN
    have hge : a n ≥ (a.from N).inf.toReal := by
      have h1 := (a.from N).ge_inf (show n ≥ (a.from N).m by change n ≥ max a.m N; omega)
      rw [hr] at h1; rw [show (a.from N) n = a n from a.from_eval hn] at h1
      exact EReal.coe_le_coe_iff.mp h1
    linarith [(abs_le.mp hclose).2]
  · -- ↑c ≤ a.limsup
    apply le_sInf; rintro _ ⟨N, hN, rfl⟩
    by_contra hlt; push_neg at hlt
    -- hlt : (a.from N).sup < ↑c
    have hne_top : (a.from N).sup ≠ ⊤ :=
      ne_of_lt (lt_trans hlt (EReal.coe_lt_top _))
    have hne_bot := aux_ne_bot (a.from N)
    have hr : (a.from N).sup = ↑(a.from N).sup.toReal := (EReal.coe_toReal hne_top hne_bot).symm
    have hlt' : (a.from N).sup.toReal < c := by
      rwa [← EReal.coe_lt_coe_iff, ← hr]
    obtain ⟨n, hn, hclose⟩ := h ((c - (a.from N).sup.toReal) / 2) (by linarith) N hN
    have hle : a n ≤ (a.from N).sup.toReal := by
      have h1 := (a.from N).le_sup (show n ≥ (a.from N).m by change n ≥ max a.m N; omega)
      rw [hr] at h1; rw [show (a.from N) n = a n from a.from_eval hn] at h1
      exact EReal.coe_le_coe_iff.mp h1
    linarith [(abs_le.mp hclose).1]

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  rw [limit_point_def]; intro ε hε N hN
  -- Since L_plus + ε > limsup, eventually a n < L_plus + ε
  have h_above : (↑(L_plus + ε) : EReal) > a.limsup := by
    show a.limsup < ↑(L_plus + ε); rw [h, EReal.coe_lt_coe_iff]; linarith
  -- Since L_plus - ε < limsup, for any N, ∃ n ≥ N with a n > L_plus - ε
  have h_below : (↑(L_plus - ε) : EReal) < a.limsup := by
    rw [h, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨N₁, _, hup⟩ := a.gt_limsup_bounds h_above
  obtain ⟨n, hn, hlow⟩ := a.lt_limsup_bounds h_below (show max N N₁ ≥ a.m by omega)
  use n, by omega
  rw [abs_le]; constructor
  · linarith [EReal.coe_lt_coe_iff.mp hlow]
  · linarith [EReal.coe_lt_coe_iff.mp (hup n (by omega))]

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  rw [limit_point_def]; intro ε hε N hN
  have h_below : (↑(L_minus - ε) : EReal) < a.liminf := by
    rw [h, EReal.coe_lt_coe_iff]; linarith
  have h_above : (↑(L_minus + ε) : EReal) > a.liminf := by
    show a.liminf < ↑(L_minus + ε); rw [h, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨N₁, _, hlow⟩ := a.lt_liminf_bounds h_below
  obtain ⟨n, hn, hup⟩ := a.gt_liminf_bounds h_above (show max N N₁ ≥ a.m by omega)
  use n, by omega
  rw [abs_le]; constructor
  · linarith [EReal.coe_lt_coe_iff.mp (hlow n (by omega))]
  · linarith [EReal.coe_lt_coe_iff.mp hup]

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor
  · -- Forward: TendsTo c → liminf = c ∧ limsup = c
    intro hconv
    have ⟨hli, hls⟩ := limit_point_between_liminf_limsup (limit_point_of_limit hconv)
    rw [tendsTo_iff] at hconv
    -- For any ε > 0, bound limsup and liminf
    have bounds : ∀ ε > 0, a.limsup ≤ ↑(c + ε) ∧ ↑(c - ε) ≤ a.liminf := by
      intro ε hε; obtain ⟨N₀, hN₀⟩ := hconv ε hε
      constructor
      · calc a.limsup ≤ a.upperseq (max N₀ a.m) := sInf_le ⟨max N₀ a.m, by omega, rfl⟩
          _ ≤ ↑(c + ε) := by
            apply sup_le_upper; intro n hn
            change n ≥ max a.m (max N₀ a.m) at hn
            rw [show (a.from (max N₀ a.m)) n = a n from a.from_eval (by omega)]
            rw [EReal.coe_le_coe_iff]
            linarith [(abs_le.mp (hN₀ n (by omega))).2]
      · calc ↑(c - ε) ≤ a.lowerseq (max N₀ a.m) := by
              apply inf_ge_lower; intro n hn
              change n ≥ max a.m (max N₀ a.m) at hn
              rw [show (a.from (max N₀ a.m)) n = a n from a.from_eval (by omega)]
              rw [ge_iff_le, EReal.coe_le_coe_iff]
              linarith [(abs_le.mp (hN₀ n (by omega))).1]
          _ ≤ a.liminf := le_sSup ⟨max N₀ a.m, by omega, rfl⟩
    -- limsup = ↑c: squeeze between ↑c ≤ limsup (from limit point) and limsup ≤ ↑c
    have hlimsup_le : a.limsup ≤ ↑c := by
      by_contra hgt; push_neg at hgt
      have hne_top : a.limsup ≠ ⊤ := by
        intro heq; have := (bounds 1 one_pos).1; rw [heq] at this
        exact absurd this (not_le.mpr (EReal.coe_lt_top _))
      have hne_bot : a.limsup ≠ ⊥ := ne_of_gt (lt_trans (EReal.bot_lt_coe c) hgt)
      obtain ⟨L, hL⟩ : ∃ L : ℝ, a.limsup = ↑L := ⟨_, (EReal.coe_toReal hne_top hne_bot).symm⟩
      have hgt' : c < L := by rwa [hL, EReal.coe_lt_coe_iff] at hgt
      have := (bounds ((L - c) / 2) (by linarith)).1
      rw [hL, EReal.coe_le_coe_iff] at this; linarith
    have hliminf_ge : ↑c ≤ a.liminf := by
      by_contra hlt; push_neg at hlt
      have hne_bot : a.liminf ≠ ⊥ := by
        intro heq; have := (bounds 1 one_pos).2; rw [heq] at this
        exact absurd this (not_le.mpr (EReal.bot_lt_coe _))
      have hne_top : a.liminf ≠ ⊤ := ne_of_lt (lt_trans hlt (EReal.coe_lt_top _))
      obtain ⟨L, hL⟩ : ∃ L : ℝ, a.liminf = ↑L := ⟨_, (EReal.coe_toReal hne_top hne_bot).symm⟩
      have hlt' : L < c := by rwa [hL, EReal.coe_lt_coe_iff] at hlt
      have := (bounds ((c - L) / 2) (by linarith)).2
      rw [hL, EReal.coe_le_coe_iff] at this; linarith
    exact ⟨le_antisymm hli hliminf_ge, le_antisymm hlimsup_le hls⟩
  · -- Backward: liminf = c ∧ limsup = c → TendsTo c
    intro ⟨hmin, hmax⟩
    rw [tendsTo_iff]; intro ε hε
    have h1 : (↑(c + ε) : EReal) > a.limsup := by
      show a.limsup < ↑(c + ε); rw [hmax, EReal.coe_lt_coe_iff]; linarith
    have h2 : (↑(c - ε) : EReal) < a.liminf := by
      rw [hmin, EReal.coe_lt_coe_iff]; linarith
    obtain ⟨N₁, _, hup⟩ := a.gt_limsup_bounds h1
    obtain ⟨N₂, _, hlow⟩ := a.lt_liminf_bounds h2
    use max N₁ N₂
    intro n hn
    exact abs_le.mpr
      ⟨by linarith [EReal.coe_lt_coe_iff.mp (hlow n (by omega))],
       by linarith [EReal.coe_lt_coe_iff.mp (hup n (by omega))]⟩

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
  apply sup_le_upper; intro n hn
  exact le_trans (by exact_mod_cast hab n hn) (b.le_sup (by omega))

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by
  apply inf_ge_lower; intro n hn
  have hn' : n ≥ a.m := by omega
  exact le_trans (a.ge_inf hn') (by exact_mod_cast hab n hn')

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
  apply le_sInf; rintro _ ⟨N, hN, rfl⟩
  calc a.limsup ≤ a.upperseq N := sInf_le ⟨N, by omega, rfl⟩
    _ ≤ b.upperseq N := by
      apply sup_mono
      · show (a.from N).m = (b.from N).m; change max a.m N = max b.m N; omega
      · intro n hn; change n ≥ max a.m N at hn
        rw [a.from_eval (by omega), b.from_eval (by omega)]
        exact hab n (by omega)

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by
  apply sSup_le; rintro _ ⟨N, hN, rfl⟩
  calc a.lowerseq N ≤ b.lowerseq N := by
        apply inf_mono
        · show (a.from N).m = (b.from N).m; change max a.m N = max b.m N; omega
        · intro n hn; change n ≥ max a.m N at hn
          rw [a.from_eval (by omega), b.from_eval (by omega)]
          exact hab n (by omega)
    _ ≤ b.liminf := le_sSup ⟨N, by omega, rfl⟩

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (habc: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by
  have hm': b.m = c.m := by rw [hm.1, hm.2]
  have ⟨hainf, hlsup⟩ := (tendsTo_iff_eq_limsup_liminf L).mp ha
  have ⟨hbinf, hblsup⟩ := (tendsTo_iff_eq_limsup_liminf L).mp hb
  have hab : ∀ n ≥ a.m, a n ≤ b n := by intro n hn; exact (habc n hn).1
  have hbc : ∀ n ≥ b.m, b n ≤ c n := by intro n hn; exact (habc n (by omega)).2
  have habsup: a.limsup ≤ b.limsup := a.limsup_mono hm.1.symm hab
  have hbcsup: b.limsup ≤ c.limsup := b.limsup_mono hm' hbc
  have hbcinf: b.liminf ≤ c.liminf := b.liminf_mono hm' hbc
  have habinf: a.liminf ≤ b.liminf := a.liminf_mono hm.1.symm hab
  rw [hainf, hlsup, hbinf, hblsup] at *
  have hb : b.limsup = L := le_antisymm hbcsup habsup
  have ha : b.liminf = L := le_antisymm hbcinf habinf
  exact (tendsTo_iff_eq_limsup_liminf L).mpr ⟨ha, hb⟩

private lemma tendsTo_const_div_succ (c : ℝ) :
    ((fun (n:ℕ) ↦ c/(n+1:ℝ)):Sequence).TendsTo 0 := by
  have h := Sequence.tendsTo_smul c (Sequence.lim_eq.mpr Sequence.lim_harmonic)
  simp at h
  rw [Sequence.tendsTo_iff] at h ⊢
  intro ε hε; obtain ⟨N, hN⟩ := h ε hε; use N; intro n hn
  specialize hN n hn; simp at hN ⊢; rwa [div_eq_mul_inv]

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := tendsTo_const_div_succ 2

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := tendsTo_const_div_succ (-2)

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  refine Sequence.lim_of_between (a := (fun (n:ℕ) ↦ -2/(n+1:ℝ)))
    (c := (fun (n:ℕ) ↦ 2/(n+1:ℝ))) ⟨rfl, rfl⟩ ?_ ?_ ?_
  · intro n hn; simp [hn]
    set k := n.toNat
    have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have hinv_sq_le : (((k:ℝ) + 1) ^ 2)⁻¹ ≤ ((k:ℝ) + 1)⁻¹ := by
      exact inv_anti₀ hk (by nlinarith)
    rcases neg_one_pow_eq_or ℝ k with h | h <;> simp only [h] <;> constructor <;>
      rw [div_eq_mul_inv, div_eq_mul_inv] <;> nlinarith [inv_nonneg.mpr hk.le, (by positivity : (0:ℝ) ≤ (((k:ℝ) + 1) ^ 2)⁻¹)]
  · exact tendsTo_const_div_succ (-2)
  · exact tendsTo_const_div_succ 2

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  refine Sequence.lim_of_between (a := (fun (_:ℕ) ↦ (0:ℝ)))
    (c := (fun (n:ℕ) ↦ 2/(n+1:ℝ))) ⟨rfl, rfl⟩ ?_ ?_ ?_
  · intro n hn; simp [hn]
    set k := n.toNat
    have hn' : n ≥ 0 := by simpa using hn
    have hnk : n = (k:ℤ) := (Int.toNat_of_nonneg hn').symm
    have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
    rw [show (2:ℝ) ^ n = 2 ^ (k:ℤ) from by rw [hnk], zpow_natCast]
    constructor
    · positivity
    · have hpow : (k:ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have h2k : (0:ℝ) < 2 ^ k := by positivity
      calc (2 ^ k : ℝ)⁻¹ ≤ ((k:ℝ) + 1)⁻¹ := inv_anti₀ hk hpow
        _ ≤ 2 * ((k:ℝ) + 1)⁻¹ := le_mul_of_one_le_left (inv_nonneg.mpr hk.le) one_le_two
  · rw [Sequence.tendsTo_iff]; intro ε hε; use 0; intro n hn; simp [hn]
    exact hε.le
  · exact tendsTo_const_div_succ 2

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  simp only [tendsTo_iff, sub_zero, abs_abs]

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  linarith

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  refine ⟨fun n ↦ 1 - 1/((n:ℝ)+1), fun _ ↦ 1, fun n ↦ by simp; positivity, ?_⟩
  -- Show both sups equal 1
  have hb : ((fun (_:ℕ) ↦ (1:ℝ)):Sequence).sup = 1 := by
    apply le_antisymm
    · apply sup_le_upper; intro n hn; simp [hn]
    · exact le_sup (a := (fun (_:ℕ) ↦ (1:ℝ))) (show (0:ℤ) ≥ 0 from le_refl _)
  have ha : ((fun (n:ℕ) ↦ 1 - 1/((n:ℝ)+1)):Sequence).sup = 1 := by
    apply le_antisymm
    · apply sup_le_upper; intro n hn; simp [hn]
      exact_mod_cast show 1 - ((n.toNat:ℝ)+1)⁻¹ ≤ 1 by linarith [show (0:ℝ) < ((n.toNat:ℝ)+1)⁻¹ from by positivity]
    · -- For any c < 1, find n with a n ≥ c
      apply le_of_forall_lt_imp_le_of_dense
      intro c hc
      induction c with
      | bot => exact bot_le
      | top => exact absurd hc (not_lt.mpr le_top)
      | coe c =>
        have hc' : c < 1 := by exact_mod_cast hc
        obtain ⟨N, hN⟩ := exists_nat_gt (1/(1 - c))
        have hc1 : (0:ℝ) < 1 - c := by linarith
        have hN' : (0:ℝ) < (N:ℝ) + 1 := by positivity
        have key : c ≤ 1 - 1/((N:ℝ)+1) := by
          have := (div_lt_iff₀ hc1).mp hN
          suffices 1/((N:ℝ)+1) ≤ 1 - c by linarith
          rw [div_le_iff₀ hN']; linarith
        calc (c:EReal) ≤ ↑(1 - 1/((N:ℝ)+1)) := by exact_mod_cast key
          _ ≤ _ := le_sup (a := (fun (n:ℕ) ↦ 1 - 1/((n:ℝ)+1))) (show (N:ℤ) ≥ 0 by omega)
  rw [hb]; exact not_lt.mpr (ha ▸ le_refl _)

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro h
  set a : Sequence := ((fun n ↦ (-1:ℝ)^n : ℕ → ℝ) : Sequence)
  have habs : a.abs.TendsTo 1 := by
    rw [Sequence.tendsTo_iff]; intro ε hε; use 0; intro n hn
    show |(|a.seq n|) - 1| ≤ ε
    have : a.seq n = (-1:ℝ)^n.toNat := by
      show (if n ≥ 0 then (-1:ℝ)^n.toNat else 0) = _; rw [if_pos hn]
    rw [this, abs_pow, abs_neg, abs_one, one_pow]; simp; linarith
  have hnotconv : ¬ a.TendsTo 1 := by
    rw [Sequence.tendsTo_iff]; push_neg
    refine ⟨1, one_pos, fun N => ⟨2 * max 0 N + 1, by omega, ?_⟩⟩
    have hn_pos : 2 * max 0 N + 1 ≥ 0 := by omega
    have : a.seq (2 * max 0 N + 1) = -1 := by
      show (if 2 * max 0 N + 1 ≥ 0 then (-1:ℝ)^(2 * max 0 N + 1).toNat else 0) = -1
      rw [if_pos hn_pos]
      exact Odd.neg_one_pow ⟨(max 0 N).toNat, by omega⟩
    rw [this]; norm_num
  exact hnotconv ((h a 1).mpr habs)

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

private lemma Sequence.not_bddAbove_from {a : Sequence} (h : ¬a.BddAbove)
    {N : ℤ} (hN : N ≥ a.m) (M : ℝ) : ∃ n ≥ N, a n > M := by
  by_contra h'; push_neg at h'
  apply h
  rcases eq_or_lt_of_le hN with rfl | hlt
  · exact ⟨M, h'⟩
  · have hne : (Finset.Ico a.m N).Nonempty :=
      ⟨a.m, Finset.mem_Ico.mpr ⟨le_refl _, hlt⟩⟩
    exact ⟨max M ((Finset.Ico a.m N).sup' hne a.seq), fun n hn => by
      rcases le_or_gt N n with hn' | hn'
      · exact le_trans (h' n hn') (le_max_left _ _)
      · exact le_trans (Finset.le_sup' a.seq (Finset.mem_Ico.mpr ⟨hn, hn'⟩))
                        (le_max_right _ _)⟩

private lemma Sequence.not_bddBelow_from {a : Sequence} (h : ¬a.BddBelow)
    {N : ℤ} (hN : N ≥ a.m) (M : ℝ) : ∃ n ≥ N, a n < M := by
  by_contra h'; push_neg at h'
  apply h
  rcases eq_or_lt_of_le hN with rfl | hlt
  · exact ⟨M, h'⟩
  · have hne : (Finset.Ico a.m N).Nonempty :=
      ⟨a.m, Finset.mem_Ico.mpr ⟨le_refl _, hlt⟩⟩
    exact ⟨min M ((Finset.Ico a.m N).inf' hne a.seq), fun n hn => by
      rcases le_or_gt N n with hn' | hn'
      · exact le_trans (min_le_left _ _) (h' n hn')
      · exact le_trans (min_le_right _ _)
                        (Finset.inf'_le a.seq (Finset.mem_Ico.mpr ⟨hn, hn'⟩))⟩

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by
  rcases EReal.def a.limsup with ⟨L, hL⟩ | htop | hbot
  · -- limsup = ↑L
    rw [← hL]; show a.LimitPoint L
    exact limit_point_of_limsup hL.symm
  · -- limsup = ⊤
    rw [htop]; show ¬ a.BddAbove; intro ⟨M, hM⟩
    have : a.limsup ≤ ↑M := calc
      a.limsup ≤ a.upperseq a.m := sInf_le ⟨a.m, le_refl _, rfl⟩
      _ ≤ ↑M := sup_le_upper fun n hn => by
        have hn' : n ≥ a.m := by change n ≥ max a.m a.m at hn; omega
        rw [show (a.from a.m) n = a n from a.from_eval hn']
        exact_mod_cast hM n hn'
    rw [htop] at this; exact absurd this (not_le.mpr (EReal.coe_lt_top _))
  · -- limsup = ⊥
    rw [hbot]; show ¬ a.BddBelow; intro ⟨M, hM⟩
    have : (↑M : EReal) ≤ a.limsup := by
      apply le_sInf; rintro _ ⟨N, hN, rfl⟩
      calc (↑M : EReal) ≤ ↑(a (max a.m N)) := by exact_mod_cast hM _ (by omega)
        _ ≤ (a.from N).sup := by
          have := (a.from N).le_sup (show max a.m N ≥ (a.from N).m from le_refl _)
          rwa [a.from_eval (le_max_right a.m N)] at this
    rw [hbot] at this; exact absurd this (not_le.mpr (EReal.bot_lt_coe _))

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by
  rcases EReal.def a.liminf with ⟨L, hL⟩ | htop | hbot
  · -- liminf = ↑L
    rw [← hL]; show a.LimitPoint L
    exact limit_point_of_liminf hL.symm
  · -- liminf = ⊤
    rw [htop]; show ¬ a.BddAbove; intro ⟨M, hM⟩
    have : a.liminf ≤ ↑M := sSup_le fun _ ⟨N, hN, hx⟩ => by
      subst hx
      calc (a.from N).inf ≤ ↑(a (max a.m N)) := by
            have := (a.from N).ge_inf (show max a.m N ≥ (a.from N).m from le_refl _)
            rwa [a.from_eval (le_max_right a.m N)] at this
        _ ≤ ↑M := by exact_mod_cast hM _ (by omega)
    rw [htop] at this; exact absurd this (not_le.mpr (EReal.coe_lt_top _))
  · -- liminf = ⊥
    rw [hbot]; show ¬ a.BddBelow; intro ⟨M, hM⟩
    have : (↑M : EReal) ≤ a.liminf := calc
      (↑M : EReal) ≤ a.lowerseq a.m := by
        apply inf_ge_lower; intro n hn
        have hn' : n ≥ a.m := by change n ≥ max a.m a.m at hn; omega
        rw [show (a.from a.m) n = a n from a.from_eval hn']
        exact_mod_cast hM n hn'
      _ ≤ a.liminf := le_sSup ⟨a.m, le_refl _, rfl⟩
    rw [hbot] at this; exact absurd this (not_le.mpr (EReal.bot_lt_coe _))

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by
  rcases EReal.def L with ⟨c, hc⟩ | htop | hbot
  · -- L = ↑c
    rw [← hc] at h ⊢
    exact (limit_point_between_liminf_limsup h).2
  · -- L = ⊤: ¬BddAbove → limsup = ⊤
    rw [htop] at h ⊢; change ¬ a.BddAbove at h
    apply le_sInf; rintro _ ⟨N, hN, rfl⟩
    show ⊤ ≤ (a.from N).sup
    suffices (a.from N).sup = ⊤ by rw [this]
    rcases EReal.def (a.from N).sup with ⟨S, hS⟩ | hsup_top | hsup_bot
    · exfalso
      obtain ⟨n, hn, hgt⟩ := not_bddAbove_from h hN S
      have : ↑(a n) ≤ (a.from N).sup := by
        have := (a.from N).le_sup (show n ≥ (a.from N).m by change n ≥ max a.m N; omega)
        rwa [a.from_eval hn] at this
      rw [← hS, EReal.coe_le_coe_iff] at this; linarith
    · exact hsup_top
    · exfalso
      have : ↑(a (max a.m N)) ≤ (a.from N).sup := by
        have := (a.from N).le_sup (show max a.m N ≥ (a.from N).m from le_refl _)
        rwa [a.from_eval (le_max_right a.m N)] at this
      rw [hsup_bot] at this; exact absurd this (not_le.mpr (EReal.bot_lt_coe _))
  · rw [hbot]; exact bot_le

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by
  rcases EReal.def L with ⟨c, hc⟩ | htop | hbot
  · -- L = ↑c
    rw [← hc] at h ⊢
    exact (limit_point_between_liminf_limsup h).1
  · rw [htop]; exact le_top
  · -- L = ⊥: ¬BddBelow → liminf = ⊥
    rw [hbot] at h ⊢; change ¬ a.BddBelow at h; show a.liminf ≤ ⊥
    apply sSup_le; rintro _ ⟨N, hN, rfl⟩
    show (a.from N).inf ≤ ⊥
    suffices (a.from N).inf = ⊥ by rw [this]
    rcases EReal.def (a.from N).inf with ⟨S, hS⟩ | hinf_top | hinf_bot
    · exfalso
      obtain ⟨n, hn, hlt⟩ := not_bddBelow_from h hN S
      have : (a.from N).inf ≤ ↑(a n) := by
        have := (a.from N).ge_inf (show n ≥ (a.from N).m by change n ≥ max a.m N; omega)
        rwa [a.from_eval hn] at this
      rw [← hS, EReal.coe_le_coe_iff] at this; linarith
    · exfalso
      have : (a.from N).inf ≤ ↑(a (max a.m N)) := by
        have := (a.from N).ge_inf (show max a.m N ≥ (a.from N).m from le_refl _)
        rwa [a.from_eval (le_max_right a.m N)] at this
      rw [hinf_top] at this; exact absurd this (not_le.mpr (EReal.coe_lt_top _))
    · exact hinf_bot

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by
  -- Sequence: 1, 0, -1, 2, 0, -2, 3, 0, -3, ...
  -- At position 3k: k+1, at 3k+1: 0, at 3k+2: -(k+1)
  set f : ℕ → ℝ := fun n ↦ if n % 3 = 0 then ((n/3 : ℕ) + 1 : ℝ)
    else if n % 3 = 1 then 0 else -((n/3 : ℕ) + 1 : ℝ) with hf_def
  have hf_pos (k : ℕ) : f (3*k) = k + 1 := by simp [hf_def]
  have hf_zero (k : ℕ) : f (3*k+1) = 0 := by simp [hf_def]
  have hf_neg (k : ℕ) : f (3*k+2) = -(k + 1) := by simp [hf_def]; omega
  have hm : (f:Sequence).m = 0 := rfl
  -- Evaluation lemma: (f:Sequence) at non-negative integer n equals f n.toNat
  have heval (n : ℤ) (hn : n ≥ 0) : (f:Sequence) n = f n.toNat := by simp [hn]
  refine ⟨f, fun L ↦ ?_⟩
  simp only [ExtendedLimitPoint]
  constructor
  · intro h
    induction L with
    | bot => exact Or.inl rfl
    | top => exact Or.inr (Or.inr rfl)
    | coe c =>
      right; left
      simp only [show (↑c : EReal) ≠ ⊤ from EReal.coe_ne_top _,
        show (↑c : EReal) ≠ ⊥ from EReal.coe_ne_bot _, ↓reduceIte, EReal.toReal_coe] at h
      -- h : LimitPoint c; show c = 0
      by_contra hc'
      have hc : c ≠ 0 := by intro h; apply hc'; simp [h]
      have hcpos : (0:ℝ) < |c| := abs_pos.mpr hc
      rw [limit_point_def] at h
      -- Choose ε = |c|/2 and N large enough that pos/neg terms are > 3|c|/2
      set N₀ : ℕ := ⌈3 * |c|⌉₊ + 1
      have hN₀_bound : (N₀ : ℝ) > 3 * |c| / 2 := by
        have := Nat.le_ceil (3 * |c|); push_cast [N₀]; linarith
      obtain ⟨n, hn, hclose⟩ := h (|c|/2) (by linarith) (↑(3 * N₀)) (by omega)
      have hn0 : n ≥ 0 := by omega
      rw [heval n hn0] at hclose
      set m := n.toNat
      have hm_large : m ≥ 3 * N₀ := by omega
      have hm3 : (m / 3 : ℕ) ≥ N₀ :=
        Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
      have hm3_bound : (↑(m / 3 : ℕ) : ℝ) + 1 > 3 * |c| / 2 := by
        linarith [show (N₀ : ℝ) ≤ (m / 3 : ℕ) from by exact_mod_cast hm3]
      have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · -- m % 3 = 0: f m = m/3 + 1, too far from c
        rw [show f m = f (3 * (m/3)) from by congr 1; omega, hf_pos] at hclose
        have := abs_le.mp hclose
        linarith [le_abs_self c, neg_abs_le c]
      · -- m % 3 = 1: f m = 0, so |c| ≤ |c|/2, contradiction
        rw [show f m = f (3 * (m/3) + 1) from by congr 1; omega, hf_zero] at hclose
        simp at hclose; linarith
      · -- m % 3 = 2: f m = -(m/3 + 1), too far from c
        rw [show f m = f (3 * (m/3) + 2) from by congr 1; omega, hf_neg] at hclose
        have := abs_le.mp hclose
        linarith [neg_abs_le c]
  · rintro (rfl | rfl | rfl)
    · -- L = ⊥: show ¬ BddBelow
      show ¬ (f:Sequence).BddBelow
      intro ⟨M, hM⟩
      set K : ℕ := ⌈-M⌉₊
      have hle : -M ≤ K := Nat.le_ceil _
      have := hM (↑(3 * K + 2)) (by omega)
      rw [heval _ (by omega), show (↑(3 * K + 2) : ℤ).toNat = 3 * K + 2 from by omega,
        hf_neg] at this
      linarith
    · -- L = 0: show LimitPoint 0
      show (f:Sequence).LimitPoint 0
      rw [limit_point_def]; intro ε hε N _
      set K : ℕ := (max 0 N).toNat
      refine ⟨↑(3 * K + 1), by omega, ?_⟩
      rw [heval _ (by omega), show (↑(3 * K + 1) : ℤ).toNat = 3 * K + 1 from by omega,
        hf_zero]
      simp; exact hε.le
    · -- L = ⊤: show ¬ BddAbove
      show ¬ (f:Sequence).BddAbove
      intro ⟨M, hM⟩
      set K : ℕ := ⌈M⌉₊
      have hle : M ≤ K := Nat.le_ceil _
      have := hM (↑(3 * K)) (by omega)
      rw [heval _ (by omega), show (↑(3 * K) : ℤ).toNat = 3 * K from by omega,
        hf_pos] at this
      linarith

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by
  rw [limit_point_def]
  intro ε hε N hN
  -- Get n with |b n - c| ≤ ε/2 (only need n ≥ b.m for hab)
  rw [limit_point_def] at hbc
  obtain ⟨n, hn, hclose_bc⟩ := hbc (ε / 2) (by linarith) b.m (le_refl _)
  -- Get m ≥ N with |a m - b n| ≤ ε/2
  have hab_n := hab n hn
  rw [limit_point_def] at hab_n
  obtain ⟨m, hm, hclose_ab⟩ := hab_n (ε / 2) (by linarith) N hN
  exact ⟨m, hm, calc
    |a.seq m - c| = |(a.seq m - b.seq n) + (b.seq n - c)| := by ring_nf
    _ ≤ |a.seq m - b.seq n| + |b.seq n - c| := abs_add _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hclose_ab hclose_bc
    _ = ε := by ring⟩

end Chapter6
