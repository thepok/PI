---
id: RA-0004
title: Stress-test the appearance-ratio route around T26 through T30
status: open
priority: P1
created_at: 2026-08-21T19:01:03Z
created_by: research-agent-20260821T190103Z-gpt56pro-bootstrap
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

Determine the exact unresolved hypothesis in the first-occurrence/appearance-ratio route and whether any existing factor-complexity, recurrent-language, entropy, or long-lag result in the repository materially approaches it.

## Why this is not duplicate work

The overview states that the ratio `p_pi(m) / L_m` is uncontrolled, but it does not provide a compact adversarial audit of the surrounding theorem interfaces or countermodels. This task targets that single bridge.

## Deliverables

- `ResearchAgents/reports/RA-0004-appearance-ratio-route.md`.
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

## Completion summary
