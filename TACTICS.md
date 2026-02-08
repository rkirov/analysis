# Lean 4 Tactic Pitfalls & Workarounds

## `omega`

**Can't see through `abbrev` fields.** `omega` works on concrete `ℤ`/`ℕ` expressions but treats `abbrev`-defined fields as opaque. If `a.m` is definitionally `0` via an `abbrev`, `omega` won't use that.
- Fix: `change n ≥ 0 at hn` or `change n ≥ max 0 N` to expose the literal value before calling `omega`.

**Can't handle `Int.toNat`.** `omega` doesn't reason about `Int.toNat` conversions. Use `show (2 * N).toNat = 2 * N.toNat from by omega` works for simple linear cases, but complex `toNat` reasoning may need explicit lemmas like `Int.toNat_of_nonneg`.

## `linarith`

**Can't substitute equalities into inequalities across opaque atoms.** If `h1 : f x ≤ f y` and `h2 : f y = c`, `linarith` treats `f x` and `f y` as separate atoms and won't derive `f x ≤ c`.
- Fix: pre-combine into one hypothesis: `have : f x ≤ c := h1.trans h2.le` or use `calc`.

**Handles decimal literals.** `linarith` CAN evaluate `0.1`, `0.8` etc. (OfScientific) — no need to convert to fractions. But the atom-substitution issue above still applies.

## `rw`

**Matches syntactically, not up to definitional equality.** `rw [lemma]` won't fire if the goal has a coercion-wrapped form and the lemma's LHS doesn't.
- Fix: use `change <explicit form>` or `show <explicit form>` to align the syntax first.

**Single `rw [a, b, c]` applies sequentially.** Each rewrite changes the term before the next one matches. If rewrite `b` needs the original form (before `a`), split into `rw [a]; rw [b, c]`.

## `simp`

**Over-expands `abbrev`s.** `simp` may unfold `abbrev` definitions further than intended, producing raw `if`/`dite` expressions that break subsequent tactic applications.
- Fix: prefer `rw` or `change` for controlled rewriting. Use `simp only [specific_lemmas]` to limit what gets unfolded.

## `norm_num`

**Can't simplify `|x|` directly.** `norm_num` doesn't handle `abs` in general. It needs the `abs` to be removed first.
- Fix: use `abs_of_nonneg (by norm_num)` or `abs_of_pos (by positivity)` to rewrite `|x|` to `x`, then `norm_num` can close the arithmetic.

## `positivity`

**Works well with `zpow`.** `positivity` can prove `0 < (10:ℝ) ^ (-n - 1)` and `0 < 1 + (10:ℝ) ^ (-n - 1)` without help.

## Namespace shadowing with `open`

**`open EReal` shadows `ℝ` lemmas.** `EReal` defines its own `abs_mul`, `abs_neg`, `abs_one` etc. When `open EReal` is active, bare `abs_mul` resolves to `EReal.abs_mul` and fails on `ℝ` expressions.
- Fix: use `_root_.abs_mul`, `_root_.abs_neg`, `_root_.abs_one` for the `ℝ` versions.
- General rule: if a `rw` unexpectedly fails to match, check if a namespace is shadowing the lemma.

## Useful lemma patterns

- **zpow monotonicity:** `zpow_le_zpow_right₀ (by norm_num : 1 ≤ a) (by omega : m ≤ n) : a ^ m ≤ a ^ n`
- **Inverting zpow for archimedean bounds:** `inv_lt_comm₀ (by positivity) hε` converts `a⁻¹ < ε` to `ε⁻¹ < a`; combine with `← one_div` to reconcile `ε⁻¹` vs `1/ε`.
- **Even/odd powers of -1:** `pow_mul` + `neg_one_sq` + `one_pow` for `(-1)^(2k) = 1`; add `pow_add` + `pow_one` for `(-1)^(2k+1) = -1`.
