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
  congr 1; push_cast; omega

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  refine ⟨fun n ↦ 2 * n + 1, fun m n hmn ↦ by dsimp; omega, fun n ↦ ?_⟩
  simp only [show ¬ Even (2 * n + 1) from Nat.Odd.not_even ⟨n, rfl⟩, ↓reduceIte]
  congr 1; push_cast; omega

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
  apply h2

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
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
    apply isTrue
    -- use the sequences 0,1,0,1,... and 1,0,1,0,... as a counterexample
    sorry

/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  -- for each i, define N i, to be the least natural number such that |a (N i)| > i, and N i > N (i - 1) and define b i := a (N i)
  sorry

end Chapter6
