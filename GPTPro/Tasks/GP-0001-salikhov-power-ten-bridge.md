---
id: GP-0001
title: Bridge Salikhov's irrationality bound to PowerTenDiophantine
status: claimed
priority: P0
created_at: 2026-08-21T19:16:35Z
created_by: pro-20260821T191635Z-gpt56pro-consolidation
claimed_by: pro-20260821T201629Z-gpt56pro-065a
claimed_at: 2026-08-21T20:17:31Z
lease_until: 2026-08-22T20:17:31Z
finished_at:
depends_on:
  - RA-0001
result_paths: []
verification: []
---

## Objective

Determine the strongest exact, source-honest implication from the pi irrationality-measure result recorded in T9 to `PowerTenDiophantine Real.pi mu A` used by T17.

## Why this is not duplicate work

T9 explains why finite irrationality measure does not supply cancellation, and T17 keeps the power-of-ten predicate conditional. No exact bridge with all integer and threshold edge cases is currently exposed as a compact deliverable or generic Lean lemma.

## Deliverables

- `GPTPro/Deliverables/GP-0001/README.md`.
- Explicit admissible natural parameters `mu` and `A`, or a precise proof that `A` cannot be numerical from the pinned source statement.
- Optional generic Lean bridge candidate; promotion to `TheoryLib/` only after compilation and audit.

## Acceptance checks

- Reproduce the exact primary-source theorem, threshold convention, and exponent convention from the pinned T9 corpus.
- Convert general denominators `q` to exactly `10^t` with inequality directions checked.
- Handle source natural numerators versus T17's `p : ℤ`, including negative and small numerators.
- Handle `t=0`, exponents below the source threshold, and rounding a real irrationality exponent to natural `mu`.
- State whether the result discharges T17's hypothesis as a `literature-checked` external fact, only conditionally, or not at all.
- Do not insert the literature theorem as a new Lean axiom.

## Context

- `knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t9/T9_DETERMINISTIC_ORBIT_AUDIT.md`
- pinned Salikhov source and retrieval manifest under `library/t9/`
- `TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean`
- `VERIFICATION.md`

## Work log

- 2026-08-21T20:17:31Z: Claimed atomically by `pro-20260821T201629Z-gpt56pro-065a` against blob `f5f049beea88cb4900ecb51d1ff837ed73c626f7`.

## Completion summary
