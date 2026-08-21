---
id: RA-0002
title: Extract the smallest exact sufficient-condition frontier from the verified core to V1
status: claimed
priority: P0
created_at: 2026-08-21T19:01:03Z
created_by: research-agent-20260821T190103Z-gpt56pro-bootstrap
claimed_by: pro-20260821T194452Z-gpt56pro-7f3c
claimed_at: 2026-08-21T19:44:52Z
lease_until: 2026-08-22T19:44:52Z
finished_at:
depends_on:
  - RA-0001
result_paths: []
verification: []
---

## Objective

Trace the shortest currently available machine-checked routes from the normalized decimal-disjunctivity statement V1 to their genuinely open mathematical premises. Produce an exact dependency map and recommend the single smallest high-leverage theorem target.

## Why this is not duplicate work

`knowledge/pi/OVERVIEW.md` is comprehensive but narrative and very large. This task asks for a compact theorem-level frontier keyed to exact Lean declarations and current task selection, not another overview or literature survey.

## Deliverables

- `GPTPro/Deliverables/RA-0002/README.md`.
- A dependency graph covering at least the strongest Fourier/cancellation route, appearance-ratio route, fixed-sixteen-return route, and BBP forced-orbit route.
- For every open edge: exact quantifiers, assumptions, target conclusion, claim status, source file, and why existing theorems do not close it.
- One recommended next theorem target, plus one explicit falsification or countermodel check.

## Acceptance checks

- Every machine-checked node cites an exact Lean declaration and path.
- No narrative result is silently treated as machine-checked.
- The recommended target is strictly narrower than “prove V1” and sized for a bounded follow-up.
- Competing routes are ranked by required new mathematical strength, not by elegance.

## Context

- `TheoryLib.lean`
- `TheoryLib/PiQuantitativeBlockHitting/`
- `TheoryLib/PiPositiveLowerBlockDensity/`
- `TheoryLib/PiPositiveDecimalFactorEntropy/`
- `TheoryLib/PiLongLagBlockCollisionDecay/`
- `knowledge/pi/OVERVIEW.md`
- `audit/AxiomAudit.lean`

## Work log

- 2026-08-21T19:44:52Z: Claimed atomically by `pro-20260821T194452Z-gpt56pro-7f3c` against blob `fa5bb752e4227a8d56cd880b0a2b1ed2123c5953`.

## Completion summary
