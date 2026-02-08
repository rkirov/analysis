import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  apply existsUnique_of_exists_of_unique
  use x.num / x.den
  . constructor
    . have hnz :(x.den : ℤ) ≠ 0 := by
        norm_cast
        exact x.den_nz
      have hdiv := Int.mul_ediv_self_le (x:=x.num) hnz
      apply le_of_mul_le_mul_right (a := (x.den:ℚ))
      . simp only [mul_den_eq_num]
        rw [mul_comm]
        qify at hdiv
        exact hdiv
      . have := Nat.zero_le x.den
        rw [le_iff_lt_or_eq] at this
        norm_cast at hnz
        cases' this with h h
        . norm_cast
        . tauto
    . have hden: 0 < (x.den:ℤ) := by
        norm_cast
        exact den_pos x
      have hdiv' := Int.lt_mul_ediv_self_add (x:=x.num) hden
      have den_pos': 0 < (x.den:ℤ) := by norm_cast; exact den_pos x
      qify at hdiv'
      apply lt_of_mul_lt_mul_right (a := (x.den:ℚ))
      . simp only [mul_den_eq_num]
        rw [add_mul, mul_comm, one_mul]
        exact hdiv'
      . norm_cast
        exact Nat.zero_le x.den
  . intro n n' ih ih'
    wlog h: n ≤ n'
    . specialize this x n' n ih' ih
      symm
      apply this
      simp only [not_le] at h
      exact Int.le_of_lt h
    have : n' < n + 1 := by
      qify
      apply lt_of_le_of_lt
      . exact ih'.1
      . exact ih.2
    linarith

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  obtain ⟨n, ⟨h1, h2⟩, _⟩ := Rat.between_int x
  obtain ⟨n', hn'⟩ := Int.eq_nat_or_neg n
  rcases hn' with ⟨rfl | rfl⟩
  . simp_all
    use ↑n' + 1
    simp only [cast_add, cast_one]
    exact h2
  . subst n
    use 1
    simp at h2
    have :0 ≤ (n':ℚ) := by positivity
    exact lt_of_add_lt_of_nonneg_right h2 this

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  intro h
  obtain ⟨a, ha⟩ := h
  have : ∀ n k, a n ≥ k := by
    intro n k
    induction' k with k hk generalizing n
    . exact zero_le (a n)
    . specialize hk (n + 1)
      specialize ha n
      have : k < a n := by exact Nat.lt_of_le_of_lt hk ha
      exact this -- turns out it is a > k is rfl a >= k + 1
  specialize this 0
  have hne := Nat.exists_gt (a 0)
  obtain ⟨n, hn⟩ := hne
  specialize this n
  norm_cast at hn
  linarith

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  apply isTrue
  use fun n ↦ -n
  intro n
  simp

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  apply isTrue
  use fun n ↦ ⟨1 / (↑n + 1), by positivity⟩
  intro n
  simp only [Subtype.mk_lt_mk]
  apply div_lt_div_of_pos_left one_pos (by positivity) (by push_cast; linarith)

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  induction' n with n ih
  . left
    exact ⟨0, by ring⟩
  rcases ih with (he | ho)
  . right
    rw [even_iff_exists_two_mul] at he
    obtain ⟨k, rfl⟩ := he
    use k
  . left; rw [odd_iff_exists_bit1] at ho
    obtain ⟨k, rfl⟩ := ho
    use k + 1
    ring

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  rintro ⟨he, ho⟩
  rw [even_iff_exists_two_mul] at he
  rw [odd_iff_exists_bit1] at ho
  obtain ⟨k, ne⟩ := he
  obtain ⟨m, no⟩ := ho
  rw [ne] at no
  omega

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . have hl: q ^ 2 < (2 * k) ^ 2 := by
          rw [this]
          aesop
        exact lt_of_pow_lt_pow_left' 2 hl
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      rw [odd_iff_exists_bit1] at hp ⊢
      obtain ⟨ k, rfl ⟩ := hp
      ring_nf
      use 2 * (k^2 + k)
      ring_nf
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
