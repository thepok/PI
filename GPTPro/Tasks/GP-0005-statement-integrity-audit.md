---
id: GP-0005
title: Adversarial statement-integrity audit of T14 through T17
status: open
priority: P1
created_at: 2026-08-21T19:16:35Z
created_by: pro-20260821T191635Z-gpt56pro-consolidation
claimed_by:
claimed_at:
lease_until:
finished_at:
depends_on:
  - RA-0001
result_paths: []
verification: []
---

## Objective

Determine whether machine-checked theorem statements T14-T17 match their intended mathematical reductions quantifier by quantifier, including indexing, boundaries, vacuity, scaling, and interpretation issues Lean compilation alone would not detect.

## Why this is not duplicate work

The modules are machine-checked, but the repository's verification policy explicitly distinguishes kernel checking from statement integrity. No compact adversarial audit of this chain is present.

## Deliverables

- `GPTPro/Deliverables/GP-0005/README.md` with a theorem-by-theorem audit table.
- Minimal Lean counterexamples or executable checks where useful.

## Acceptance checks

- Verify C1 uniformity, leading-zero handling, arbitrary contiguous starts, and full-containment deadlines through every specialization.
- Audit `D-k+1`, zero-based versus fractional-digit indexing, half-open cylinders, exact-boundary exclusion, carry and wraparound cases, and empty-cylinder conversion.
- Audit signed-frequency aggregation, coefficient signs, complex norms, normalization, and inequalities involving `N`, `q`, `M`, and `r`.
- Search for vacuous hypotheses, impossible parameter regions, hidden dependence on the missing word, and conclusions weaker than their prose.
- For every issue, give severity, exact theorem/path, reproducible witness, and minimal repair. If none is found, document checks rather than claiming broad correctness.
- Distinguish machine-checked syntax from statement integrity and relevance to C1.

## Context

- T14, T16, and T17 modules and dependencies
- active workstream `knowledge.jsonl`
- `audit/AxiomAudit.lean`
- `VERIFICATION.md`

## Work log

## Completion summary
