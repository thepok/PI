---
id: GP-0003
title: Audit and optimize T17's suffix and frequency growth
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

Determine whether T17's `r = (mu-1)*D+1` and `M = 2*10^(2*k+r)` are avoidable artifacts of one global boundary width or comparable growth is forced by the current reduction.

## Why this is not duplicate work

T14-T17 prove a precise route but do not provide a focused optimization or no-go audit of its parameter growth.

## Deliverables

- `GPTPro/Deliverables/GP-0003/README.md`.
- Checked exact and asymptotic parameter derivation.
- At least one concrete improved reduction attempt, with supporting Lean, symbolic calculation, or counterexample artifacts.

## Acceptance checks

- Expand `N`, `D`, `r`, and `M` exactly and numerically for representative small `k`.
- Identify where each factor and exponent enters T14-T17.
- Analyze start-dependent suffix length, dyadic partition of orbit starts, and non-uniform boundary widths or Fourier cutoffs.
- For each redesign, derive a valid improved theorem with explicit constants or a rigorous obstruction.
- Inspect whether `aggregatedFourierSum` creates hidden dependence on `q` or `M`.
- End with one executable next theorem or experiment, not vague ideas.

## Context

- T14, T16, and T17 modules under `TheoryLib/PiQuantitativeBlockHitting/`
- T11 and T13 notes under the active workstream library
- T9 irrationality-measure analysis

## Work log

## Completion summary
