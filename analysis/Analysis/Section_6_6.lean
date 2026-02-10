import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by
  use fun n ↦ 2 * n
  constructor
  . intro m n hmn
    simp [hmn]
  . intro n
    simp

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by
  intro m n hmn
  unfold StrictMono at hf
  have h1 := @hf m n
  have h2 := @hf n m
  obtain h | rfl | h := lt_trichotomy m n
  . have : f m < f n := h1 h
    linarith
  . rfl
  . have : f n < f m := h2 h
    linarith

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n ↦ 2 * n, fun m n hmn ↦ by dsimp; omega, fun n ↦ ?_⟩
  simp only [show Even (2 * n) from ⟨n, by ring⟩, ↓reduceIte]
  congr 2; push_cast; omega

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n ↦ 2 * n + 1, fun m n hmn ↦ by dsimp; omega, fun n ↦ ?_⟩
  simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
  congr 2; push_cast; omega

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by
  use id
  constructor
  . intro m n hmn
    simp [hmn]
  . intro n
    simp

lemma compStrictMono {f g : ℕ → ℕ} (hf: StrictMono f) (hg: StrictMono g) : StrictMono (g ∘ f) := by
  intro m n hmn
  have h1 := @hf m n
  have h2 := @hg (f m) (f n)
  exact h2 (h1 hmn)

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
  obtain ⟨ f, hf, hab' ⟩ := hab
  obtain ⟨ g, hg, hbc' ⟩ := hbc
  use f ∘ g
  constructor
  . exact compStrictMono hg hf
  . intro n
    specialize hab' (g n)
    specialize hbc' n
    rw [hbc', hab']
    simp

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  constructor
  · intro h b hsubseq
    obtain ⟨f, hf, hab⟩ := hsubseq
    have hf_ge : ∀ n : ℕ, n ≤ f n := by
      intro n; induction n with
      | zero => omega
      | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf k.lt_succ_self))
    rw [tendsTo_iff] at h ⊢
    intro ε hε; obtain ⟨N, hN⟩ := h ε hε
    use max 0 N
    intro n hn
    have hn0 : (0 : ℤ) ≤ n := by omega
    simp only [hn0, ↓reduceIte, hab]
    have hfN : N ≤ ↑(f n.toNat) := by
      calc N ≤ n := by omega
        _ = ↑n.toNat := by omega
        _ ≤ ↑(f n.toNat) := by exact_mod_cast hf_ge n.toNat
    have := hN _ hfN
    simpa using this
  · intro h
    exact h a (Sequence.subseq_self a)

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  constructor
  . intro h
    rw [limit_point_def] at h
    -- specialize h at 1/n to get a sequence of points close to L, then use that as b
    sorry
  . intro h
    rw [limit_point_def]
    obtain ⟨ b, hb, ht ⟩ := h
    rw [tendsTo_iff] at ht
    intro ε hε N hN
    specialize ht ε hε
    obtain ⟨ N', hN' ⟩ := ht
    -- use N' to get a point b N' close to L, then use the subsequence property to get a point a (f N') close to L
    sorry

/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    apply isTrue
    refine ⟨fun n ↦ if Even n then 0 else 1, fun n ↦ if Even n then 1 else 0, ?_, ?_, ?_⟩
    · intro h; have := congr_fun h 0; simp at this
    · exact ⟨fun n ↦ n + 1, fun _ _ h ↦ by dsimp; omega,
        fun n ↦ by simp only [Nat.even_add_one]; split_ifs with h <;> simp⟩
    · exact ⟨fun n ↦ n + 1, fun _ _ h ↦ by dsimp; omega,
        fun n ↦ by simp only [Nat.even_add_one]; split_ifs with h <;> simp⟩

open Classical in
/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  have key : ∀ (M k : ℕ), ∃ n, n > k ∧ |a n| > (M : ℝ) := by
    intro M k
    by_contra h; push_neg at h
    apply ha
    obtain ⟨M', hM', hM'_bound⟩ := IsBounded.finite (fun i : Fin (k + 1) ↦ a i)
    exact ⟨max M M', le_max_of_le_right hM', fun n ↦ by
      by_cases hn : n ≥ 0
      · simp only [hn, ↓reduceIte]
        by_cases hk : n.toNat ≤ k
        · exact (hM'_bound ⟨n.toNat, by omega⟩).trans (le_max_right _ _)
        · exact (h n.toNat (by omega)).trans (le_max_left _ _)
      · simp only [show ¬ n ≥ 0 from hn, ↓reduceIte, abs_zero]; positivity⟩
  let f : ℕ → ℕ := fun i ↦ Nat.rec
    (key 0 0).choose
    (fun j fj ↦ (key (j + 1) fj).choose) i
  have hf_step : ∀ i, f (i + 1) > f i ∧ |a (f (i + 1))| > ((i + 1 : ℕ) : ℝ) :=
    fun i ↦ (key (i + 1) (f i)).choose_spec
  have hf_bound : ∀ i, |a (f i)| > (i : ℝ) := by
    intro i; cases i with
    | zero => exact (key 0 0).choose_spec.2
    | succ j => exact (hf_step j).2
  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ (fun i ↦ (hf_step i).1)
  use fun i ↦ a (f i)
  refine ⟨⟨f, hf_mono, fun _ ↦ rfl⟩, ?_⟩
  rw [inv_coe, tendsTo_iff]; intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use max 1 (N : ℤ); intro n hn
  have hn0 : n ≥ 0 := by omega
  have hn1 : 1 ≤ n.toNat := by omega
  have hnN : N ≤ n.toNat := by omega
  simp only [hn0, ↓reduceIte, sub_zero]
  have hab := hf_bound n.toNat
  have hn_pos : (0:ℝ) < n.toNat := by exact_mod_cast (show (0:ℕ) < n.toNat from by linarith)
  rw [abs_inv]
  have hN_pos : (0:ℝ) < N := lt_trans (div_pos one_pos hε) hN
  calc |a (f n.toNat)|⁻¹
      ≤ (↑n.toNat)⁻¹ := inv_anti₀ hn_pos (le_of_lt hab)
    _ ≤ (↑N)⁻¹ := inv_anti₀ hN_pos (by exact_mod_cast hnN)
    _ ≤ ε := by
        rw [inv_le_comm₀ hN_pos hε]
        exact le_of_lt (by rwa [one_div] at hN)

end Chapter6
