# Mathlib Coverage Analysis of Tao's Analysis I Exercises

**Based on systematic Mathlib-on-disk grep verification by 7 parallel agents.**

Total sorry lines in upstream: 730, across ~623 unique declarations.
(Agent counting includes sub-sorries within proofs, so totals per-agent are higher.)

## Classification

| Category | Description |
|----------|-------------|
| **A: Direct Mathlib** | Uses Mathlib types AND a named Mathlib lemma exists. Proof could be `exact mathlib_lemma` or minor glue. |
| **B: Math in Mathlib, custom types** | The mathematical result exists in Mathlib, but the exercise uses custom types/definitions. AI "knows" the math but must construct the proof from scratch. |
| **C: Not in Mathlib** | Counterexamples, decidability puzzles, bridge lemmas, computation exercises, or results specific to the textbook's custom framework. |

## Verified Results by Chapter

| Chapter group | Agent | Cat A | Cat B | Cat C | Total | Notes |
|---------------|-------|-------|-------|-------|-------|-------|
| **Ch 2–3** (custom Nat, Set) | 1 | 2 | 143 | 50 | 195 | Nearly all B — standard math on custom types. C = Peano uniqueness, ZFC internals, counterexamples |
| **Ch 4–5** (custom Int/Rat/Real) | 2 | 0 | 95 | 25 | 120 | Zero A — all custom types. C = bridge lemmas, custom notions (ε-Close), specific examples |
| **Ch 6–7** (Sequences, Series) | 3 | 25 | 95 | 45 | 165 | A = Finset.sum lemmas, EReal order. B = limit laws, series tests. C = bridge, counterexamples, n^(1/n)→1 |
| **Ch 8** (Cardinality, Zorn's) | 4 | 20 | 40 | 31 | 91 | A = Schröder-Bernstein, Zorn's, AC, well-ordering. C = Riemann rearrangement(!), concrete examples |
| **Ch 9** (Topology on ℝ) | 5 | 85 | 55 | 35 | 175 | A = closure lemmas, Heine-Borel, IVT, continuity. B = custom LimitPt/Convergesto. C = counterexamples |
| **Ch 10–11** (Derivatives, Integration) | 6 | 41 | 32 | 107 | 180 | Ch 10 ≈ 60% A (Mathlib types). Ch 11 ≈ 72% C (custom Riemann integral framework) |
| **Appendices + Measure Theory** | 7 | 1 | 55 | 75 | 131 | A = only `Uncountable ℝ`. B = outer measure, monotone convergence. C = custom Jordan/Lebesgue types |
| **TOTAL** | | **174** | **515** | **368** | **1057** | |

Note: agent totals (1057) exceed the 730 sorry lines because agents counted individual sorry sites
within multi-sorry declarations and some sub-lemmas separately. The ratios are what matter.

## Summary Percentages

| Category | Count | % of total |
|----------|-------|------------|
| **A: Direct Mathlib** | 174 | **16%** |
| **B: Math in Mathlib, custom types** | 515 | **49%** |
| **C: Not in Mathlib** | 368 | **35%** |

### Two ways to read "in Mathlib":

- **Generous (A+B): ~65%** — the underlying mathematical result is formalized somewhere in Mathlib. An AI trained on Mathlib has "seen" the math.
- **Strict (A only): ~16%** — the exercise can be solved by essentially calling a Mathlib lemma directly. These are mainly:
  - Ch 9.1: `closure_Ioo`, `closure_Ici`, `isClosed_Icc`, `isClosed_closure`, `closure_minimal`, etc.
  - Ch 10: `HasDerivWithinAt.add/mul/comp/inv/div`, `exists_hasDerivAt_eq_slope` (MVT), `lhopital_*`
  - Ch 8: `Function.Embedding.schroeder_bernstein`, `zorn_le`, `Classical.choice`
  - Ch 7.1: `Finset.sum_add_distrib`, `Finset.sum_le_sum`, `Finset.sum_union`, `norm_sum_le`

## What makes the 35% (Cat C) hard — breakdown:

| Sub-category | Approx count | Examples |
|--------------|-------------|----------|
| **Custom framework exercises** | ~140 | All Ch 11 Partition/PiecewiseConstant/RS_integ, all MeasureTheory Jordan/Lebesgue custom types |
| **Counterexample constructions** | ~80 | "∃ f,g such that...", decidability puzzles (true/false?) |
| **Bridge/equivalence lemmas** | ~50 | Ch 2 epilogue (Peano↔ℕ), Ch 5 epilogue (Real↔ℝ), Ch 6 epilogue (lim↔limUnder) |
| **Specific computations** | ~40 | "this integral = 22", "this series partial sum = ...", concrete ε-δ |
| **ZFC/logic internals** | ~25 | Russell's paradox, regularity axiom, quantifier exercises |
| **Genuinely absent from Mathlib** | ~33 | Riemann rearrangement theorem, n^(1/n)→1, ratio/root test internals |

## Key findings for AI impressiveness:

1. **Only 16% are directly closable via Mathlib.** For these, an AI just needs to know the right lemma name. Not very impressive.

2. **49% have known math but custom types.** The AI knows *what* to prove (e.g., "limit of sum = sum of limits") but must reconstruct the proof using a completely different API. This is like knowing a proof in one language and translating to another — genuinely non-trivial.

3. **35% are not in Mathlib at all.** These require:
   - Constructing specific counterexamples (creative, not just recall)
   - Working within a bespoke framework (custom Riemann integration, custom Jordan measure)
   - Building bridge infrastructure between type systems
   - The Riemann rearrangement theorem is notably absent from Mathlib

4. **Chapter difficulty varies enormously:**
   - Ch 10 (derivatives) is the easiest for AI — 60% Cat A, uses Mathlib types directly
   - Ch 11 (integration) is the hardest — 72% Cat C, entirely custom framework
   - Ch 2–5 are 0% Cat A but ~80% Cat B — standard math, just needs translation

## Notable Mathlib lemma matches (verified on disk):

| Exercise | Mathlib lemma | File |
|----------|--------------|------|
| `closure_of_Ioo` | `closure_Ioo` | `Topology/Order/DenselyOrdered.lean` |
| `closure_of_Ici` | `closure_Ici` | `Topology/Order/OrderClosed.lean` |
| `Heine_Borel` | `isCompact_iff_isSeqCompact` | `Topology/Sequences.lean` |
| `HasDerivWithinAt.of_add` | `HasDerivWithinAt.add` | `Analysis/Calculus/Deriv/Add.lean` |
| `HasDerivWithinAt.of_mul` | `HasDerivWithinAt.mul` | `Analysis/Calculus/Deriv/Mul.lean` |
| `HasDerivWithinAt.of_comp` | `HasDerivWithinAt.comp` | `Analysis/Calculus/Deriv/Comp.lean` |
| `HasDerivWithinAt.mean_value` | `exists_hasDerivAt_eq_slope` | `Analysis/Calculus/Deriv/MeanValue.lean` |
| `Filter.Tendsto.of_div` (L'Hôpital) | `HasDerivAt.lhopital_zero_nhdsNE` | `Analysis/Calculus/LHopital.lean` |
| `Schroder_Bernstein` | `Function.Embedding.schroeder_bernstein` | `Logic/Equiv/Embedding.lean` |
| `Zorns_lemma` | `zorn_le` | `Order/Zorn.lean` |
| `IsCompact.uniformContinuousOn` | `IsCompact.uniformContinuousOn_of_continuous` | `Topology/UniformSpace/HeineCantor.lean` |
| `intermediate_value_Icc` | `intermediate_value_Icc` | `Topology/Order/IntermediateValue.lean` |
| `Sequence.tendsTo_add` | `Filter.Tendsto.add` | `Topology/Algebra/Monoid/Defs.lean` |
| `Series.converges_of_absConverges` | `Summable.of_norm` | `Analysis/Normed/Group/InfiniteSum.lean` |

## Exercises definitively NOT in Mathlib:

| Exercise | Why not |
|----------|--------|
| Riemann rearrangement theorem (8.2.5–8.2.6') | Not formalized in Mathlib |
| `n^(1/n) → 1` | Not a named Mathlib lemma |
| All Ch 11 Partition/RS_integ exercises | Custom Riemann integral framework |
| All MeasureTheory Jordan measure exercises | Custom Jordan measure framework |
| `RealDecimal.not_inj_one` (0.999...=1) | Custom decimal type |
| Peano axiom uniqueness (Ch 2 epilogue) | Custom Peano axiom theory |
| `ratio_ineq` (liminf ratio ≤ liminf root ≤ ...) | Internal inequality chain |
