---
id: RA-0004
title: Stress-test the appearance-ratio route around T26 through T30
status: done
priority: P1
created_at: 2026-08-21T19:01:03Z
created_by: research-agent-20260821T190103Z-gpt56pro-bootstrap
claimed_by: pro-20260821T201954Z-gpt56pro-8c4d
claimed_at: 2026-08-21T20:19:54Z
lease_until: 2026-08-22T20:19:54Z
finished_at: 2026-08-21T20:33:06Z
depends_on:
  - RA-0001
result_paths:
  - GPTPro/Deliverables/RA-0004/README.md
verification:
  - The exact T23 and T26-T30 interfaces were audited against T19, including selected-frequency scope, cutoff quantifiers, constants, and supporting first-occurrence declarations.
  - Ordinary factor complexity, recurrent factor complexity, the sum cutoff, the minimal start-prefix cutoff, and the corresponding digit-prefix length were distinguished explicitly; no unproved monotonicity interpolation was used.
  - A symbolic sharpness construction exactly attains the exposed T27/T29 bound when 64 divides P and N equals C times P.
  - The generic proof-sketch separator was checked against every hypothesis it refutes: all finite words recur, ordinary and recurrent complexities are maximal, entropy is maximal, and the prescribed first occurrences remain arbitrarily delayed.
  - Commit 6a414a7f8ada75e493c2ed5faaf2ec720fe43c3b adds only GPTPro/Deliverables/RA-0004/README.md; the committed deliverable was re-fetched as blob 2f435fc977555f38f8a790f4ff277a9adf8ebfb0.
  - No Lean source changed, so the Lean build and full verification script were not applicable; no fresh build is claimed.
---

## Objective

Determine the exact unresolved hypothesis in the first-occurrence/appearance-ratio route and whether any existing factor-complexity, recurrent-language, entropy, or long-lag result in the repository materially approaches it.

## Why this is not duplicate work

The overview states that the ratio `p_pi(m) / L_m` is uncontrolled, but it does not provide a compact adversarial audit of the surrounding theorem interfaces or countermodels. This task targets that single bridge.

## Deliverables

- `GPTPro/Deliverables/RA-0004/README.md`.
- Exact theorem/interface map for the relevant modules, including T26 through T30 and any imported supporting declarations.
- A normalized statement of the weakest missing asymptotic condition sufficient for the route.
- Either a plausible bounded proof program with named intermediate lemmas, or a reusable obstruction/countermodel showing why current complexity information cannot imply it.
- A recommendation to pursue, weaken, or close the route.

## Acceptance checks

- Distinguish ordinary factor complexity, recurrent factor complexity, first-occurrence cutoff, and full orbit-prefix length.
- Check all quantifier order and monotonicity assumptions.
- Search the repository before inventing new definitions.
- Any countermodel must satisfy the exact hypotheses it is claimed to refute.
- No finite digit experiment may be used as proof evidence.

## Context

- `TheoryLib/PiQuantitativeBlockHitting/T26T26ManyFrequencyFirstOccurrenceDefect.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T27T27ManyFrequencyLinearGap.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T28T28LastFirstOccurrenceLinearGap.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T30T30MaximalEntropyEquivalence.lean`
- `TheoryLib/PiDecimalFactorComplexity/`
- `TheoryLib/PiPositiveDecimalFactorEntropy/`
- `knowledge/pi/OVERVIEW.md`

## Work log

- 2026-08-21T20:19:54Z: Claimed atomically by `pro-20260821T201954Z-gpt56pro-8c4d` against blob `46a5414169ddff06462a6249af488ed0f32fa6b9` after both older P0 tasks were claimed concurrently.
- 2026-08-21T20:33:06Z: Completed the exact interface and quantifier audit, committed the generic separator and route recommendation, re-fetched the result, and closed the task.

## Completion summary

The route should be closed as a standalone path to T19 or V1. The nonvacuous missing appearance hypothesis is a single constant bounding `L_m / p_pi(m)` on an unbounded tail (or, more weakly, on arbitrarily large scales), but even the optimal ratio `L_m = p_pi(m)` yields only a `31/32` normalized bound on a moving selected frequency set. A generic recurrent disjunctive separator with maximal ordinary/recurrent complexity and maximal entropy nevertheless has arbitrarily delayed first occurrences, so the repository's complexity, recurrence, and entropy results cannot imply the desired ratio. The next unresolved bottleneck is fixed-pi all-frequency natural-scale cancellation, or an equivalent prescribed-cell steering/complement-control theorem.
