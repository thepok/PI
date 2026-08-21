---
id: RA-0002
title: Extract the smallest exact sufficient-condition frontier from the verified core to V1
status: done
priority: P0
created_at: 2026-08-21T19:01:03Z
created_by: research-agent-20260821T190103Z-gpt56pro-bootstrap
claimed_by: pro-20260821T194452Z-gpt56pro-7f3c
claimed_at: 2026-08-21T19:44:52Z
lease_until: 2026-08-22T19:44:52Z
finished_at: 2026-08-21T20:16:48Z
depends_on:
  - RA-0001
result_paths:
  - GPTPro/Deliverables/RA-0002/README.md
  - GPTPro/Deliverables/RA-0002/frontier.dot
  - GPTPro/Deliverables/RA-0002/COUNTERMODEL.md
  - GPTPro/Deliverables/RA-0002/VERIFICATION.md
verification:
  - source-declaration audit against pi-core-consolidation through T109
  - RA-0003 axiom-registration finding and completed GP-0006 repair incorporated
  - Markdown structure and relative deliverable target checks passed
  - frontier.dot rendered successfully with Graphviz
  - no Lean source changed; lake build and check.ps1 not applicable
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
- 2026-08-21T20:06:45Z: Audited the exact T19, T17/C1, appearance-ratio, fixed-sixteen-return, BBP T104–T109, positive-density, entropy, and long-lag routes; added a theorem-level frontier, DOT graph, countermodel, and verification record.
- 2026-08-21T20:06:45Z: A concurrent verified BBP integration advanced the branch during finalization. The rejected stale fast-forward was not forced; T107–T109 were incorporated before rebasing the completion.
- 2026-08-21T20:06:45Z: Incorporated RA-0003's selective central T1–T17 axiom-registration finding without duplicating its repair task.
- 2026-08-21T20:15:48Z: Refreshed the audit status after concurrent `GP-0006` completed the nine central registrations and passed the current repository gate.
- 2026-08-21T20:16:48Z: Completed documentation-only task. Existing P0 task `GP-0002` was selected as the nonduplicate bounded follow-up.

## Completion summary

The smallest direct checked Fourier sufficient predicate is T19's `PiNaturalScaleCancellationExact`. The recommended bounded next theorem is the already-open `GP-0002` contrapositive package from T17's exact eventual aggregate upper bound to `C1`; no finite-small-length patch is needed. T107–T109 now close BBP Weyl-transfer, circle-density-transfer, and symbolic-packaging interfaces, but deliberately retain cancellation, density, and prescribed-code occurrence as explicit premises. The fixed-sixteen return and sampled-BBP arbitrarily-late circle density are V1-equivalent under their exact checked side conditions, while a constant-zero-stream countermodel shows that appearance ratio alone cannot imply disjunctivity. The genuine selected-route bottleneck is the pi-specific eventual strict upper bound on T17's exact `aggregatedFourierSum`, together with a justified power-of-ten Diophantine premise.
