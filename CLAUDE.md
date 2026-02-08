# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Lean 4 formalization of Terry Tao's "Analysis I" textbook, plus additional mathematical content (Measure Theory, physical units, Erdős problems). The formalization prioritizes faithful paraphrasing of the textbook over efficiency or idiomatic Lean usage.

Theorems and their proofs from the text are already formalized. The `sorry`s mark exercises and examples that Tao leaves to the reader — these are what we work on filling in.

## Build Commands

```bash
# Build the Lean project (from repo root)
./build.sh

# Or manually (from analysis/ directory)
lake exe cache get && lake build

# Build a single file
lake build Analysis.Section_6_1

# Build web documentation (includes doc-gen4)
./build-web.sh
```

## Project Structure

- `Analysis/Section_X_Y.lean` - Textbook sections organized by chapter and section number
- `Analysis/Section_X_epilogue.lean` - Epilogues showing connections to Mathlib
- `Analysis/Appendix_*.lean` - Appendices on logic and decimal systems
- `Analysis/MeasureTheory/` - Measure Theory formalization (separate from main text)
- `Analysis/Misc/` - Additional content (units systems, probability, Erdős problems)

## Key Conventions

- **Exercises are `sorry`s**: Textbook exercises left for readers are marked with `sorry`
- **0-indexed sequences**: Unlike the textbook, sequences start from 0 to align with Mathlib
- **Junk values for partial functions**: Division by zero returns 0, etc., avoiding dependent type complexity
- **Gradual Mathlib transition**: Chapter 2 uses custom natural numbers; later chapters use Mathlib types
- **No forward references**: When filling a sorry in Chapter N, only use definitions and lemmas from Chapters ≤ N (and Mathlib). Don't look ahead to later chapters.

## Dependencies

- Lean 4 (see `lean-toolchain` for exact version)
- Mathlib4 (see `lakefile.lean` for version)
- Subverso and MD4Lean (for web documentation)

## Workflow

When asked to fill in a `sorry`:

1. Read the surrounding context: the theorem statement, any preceding lemmas, the imports, and the chapter's existing proof style.
2. Attempt a proof. Prefer short tactic proofs when possible.
3. **Write → check → verify**: Use the Lean LSP MCP tools (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`) for iterative development — they're incremental and much faster than a full rebuild. Only fall back to `lake build` as a final confirmation or when the LSP times out on large files. Only show me compiling proofs.
4. If stuck after 2-3 attempts, say what's blocking you (missing lemma? type mismatch? unclear goal state?) so I can nudge the direction. Don't hand over broken code.
5. Never silently replace a `sorry` with `native_decide` or `decide` on large instances just to close the goal. Ask first.

## Proof Style

- Prefer tactic mode over term mode.
- Prefer `calc` blocks for equational reasoning and chains of inequalities.
- Use structured proofs (`have`, `suffices`, `obtain`) over long tactic chains — readability matters.
- Minimize use of `simp` as a finishing tactic. If `simp` works, check whether a more explicit closer (`ring`, `omega`, `linarith`, `exact`) would be clearer.
- Keep automation pragmatic: `aesop`, `omega`, `positivity`, `field_simp` are all fine when they make the proof cleaner.
- Match the style of surrounding proofs in the same file.
- Introduce helper lemmas, when the proof gets too long.
- **Minimize comments.** Don't add comments that just restate what the Lean code below them does (e.g. `-- a n ≤ sup` before `have : (a n : EReal) ≤ a.sup`). Only comment when there's genuine insight: a non-obvious proof strategy, a subtle reason for a particular approach, or a reference to an external result. Let the Lean code speak for itself.
- **Reuse earlier lemmas.** Before writing a proof from scratch, check if earlier results in the same file (or section) already establish what you need. Prefer composing existing lemmas over re-deriving their internals — e.g. use `convergent_of_monotone` + `bounded_of_convergent` rather than reconstructing the boundedness argument.

## Mathlib

This project depends on Mathlib. You can use Mathlib lemmas freely, but:
- for pedagogial reasons, some concepts are first rebuilt in the repo (not using mathlib), and only later swapped with mathlib version. Don't import mathlib prematurely.
- Prefer discoverable names — if you use an obscure Mathlib lemma, add a short comment.
- If a proof needs a Mathlib lemma that seems like it should exist but you can't find it, say so rather than building a long workaround.

## What I Want to Learn

The primary goal is **learning Lean**, not just closing `sorry`s. I already know real analysis — the math itself isn't what I need help with.

When you fill in a proof:
- If the proof uses a Lean technique or tactic I haven't used elsewhere in the file, briefly explain why it works.
- If there are multiple reasonable proof strategies, mention the alternatives even if you only implement one.
- If you spot a way to simplify or generalize a preceding lemma, flag it.
- There could be typos in the statements — stop and flag it to me, I can upstream fixes.
- Don't stop to explain standard math tricks (epsilon/2, triangle inequality, etc.) — but do stop for non-obvious insights.

## Toolchain & Mathlib Maintenance

Help with rebasing onto upstream Mathlib updates and managing the Lean toolchain version when needed.

## What NOT to Do

- Don't refactor files or rename things unless I ask.
- Don't modify theorem statements — only fill in proofs.
- Don't add new imports without mentioning it.
- Don't bulk-solve many `sorry`s at once — pause frequently so I can review and learn. Small related batches are fine.
