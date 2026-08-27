---
id: GP-0001
title: Bridge Salikhov's irrationality bound to PowerTenDiophantine
status: done
priority: P0
created_at: 2026-08-21T19:16:35Z
created_by: pro-20260821T191635Z-gpt56pro-consolidation
claimed_by: pro-20260821T201629Z-gpt56pro-065a
claimed_at: 2026-08-21T20:17:31Z
lease_until: 2026-08-22T20:17:31Z
finished_at: 2026-08-21T20:29:04Z
depends_on:
  - RA-0001
result_paths:
  - GPTPro/Deliverables/GP-0001/README.md
verification:
  - Pinned T9 theorem text, strict exponent convention, source metadata, and manifest locators were compared; no fresh PDF replay is claimed.
  - The substitution mu=8 and q=10^t was audited for inequality direction, all signed integer numerators, the finite threshold range, and the t=0 counterexample.
  - The result was matched quantifier-by-quantifier to T17's committed PowerTenDiophantine definition and its use of A <= k.
  - Commit 073165ee4c24292cd98999b0f6ae8f831d70a9f2 adds only GPTPro/Deliverables/GP-0001/README.md.
  - No TheoryLib or audit file changed, no axiom was added, and no Lean build is claimed; this runtime has no lean, lake, or pwsh executable.
  - The archived T9 reproduce script was statically found stale against the flattened current layout and was not reported as passing.
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
- 2026-08-21T20:28:10Z: Committed the exact bridge report in commit `073165ee4c24292cd98999b0f6ae8f831d70a9f2`; that commit changes only the GP-0001 deliverable.
- 2026-08-21T20:29:04Z: Closed after re-fetching the claimed task blob and checking the committed deliverable.

## Completion summary

Salikhov's recorded bound supports the external statement `∃ A >= 1, PowerTenDiophantine Real.pi 8 A`; `mu = 8` is the smallest justified natural exponent. The source does not expose its denominator threshold, so no numerical `A` is justified from the pinned theorem statement, while `A = 0` is explicitly false at `t = 0`, `p = 3`. Signed numerators and small positive numerators cause no gap. T17 remains kernel-conditional because no literature axiom or formalization was added. The unresolved mathematical bottleneck is still deterministic aggregated-Fourier cancellation, not the power-of-ten Diophantine premise.
