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
    (-1:ℝ) ^ (2 * N).toNat = 1 := by
  rw [show (2 * N).toNat = 2 * N.toNat from by omega, pow_mul, neg_one_sq, one_pow]

private lemma ex644_odd (N : ℤ) (hN : N ≥ 0) :
    (-1:ℝ) ^ (2 * N + 1).toNat = -1 := by
  rw [show (2 * N + 1).toNat = 2 * N.toNat + 1 from by omega,
      pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]

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
  sorry

example : Example_6_4_7.limsup = 1 := by sorry

example (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  sorry

example : Example_6_4_7.liminf = -1 := by sorry

example : Example_6_4_7.sup = (1.1:ℝ) := by sorry

example : Example_6_4_7.inf = (-1.01:ℝ) := by sorry

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

example (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by sorry

example : Example_6_4_8.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by sorry

example : Example_6_4_8.liminf = ⊥ := by sorry

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else -(n+2:ℝ)⁻¹ := by sorry

example : Example_6_4_9.limsup = 0 := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by sorry

example : Example_6_4_9.liminf = 0 := by sorry

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

example (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by sorry

example : Example_6_4_9.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_9.lowerseq n = n+1 := by sorry

example : Example_6_4_9.liminf = ⊤ := by sorry

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
  refine ⟨n, by omega, ?_⟩
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
  refine ⟨n, by omega, ?_⟩
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
    exact ⟨max N₁ N₂, fun n hn ↦ abs_le.mpr
      ⟨by linarith [EReal.coe_lt_coe_iff.mp (hlow n (by omega))],
       by linarith [EReal.coe_lt_coe_iff.mp (hup n (by omega))]⟩⟩

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

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  sorry

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
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  sorry

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by sorry

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by sorry

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by sorry

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by sorry

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by sorry

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by sorry


end Chapter6
