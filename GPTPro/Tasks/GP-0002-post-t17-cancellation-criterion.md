---
id: GP-0002
title: Formalize the post-T17 cancellation criterion implying C1
status: open
priority: P0
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

Close T17 into the sharpest clean sufficient theorem stating that the power-of-ten Diophantine hypothesis plus an eventual strict upper bound on the exact aggregated Fourier quantity forces C1.

## Why this is not duplicate work

T17 exposes a lower bound under `not C1`, but the repository does not visibly package its contrapositive as the exact analytic target for future research.

## Deliverables

- `GPTPro/Deliverables/GP-0002/README.md`.
- Exact quantifier structure and Lean implementation or candidate patch.
- Promotion into `TheoryLib/` only after the full verification gate.

## Acceptance checks

Using the exact definitions

```text
q = 10^k
D = C*k*q
N = D-k+1
r = (mu-1)*D+1
M = 2*10^(2*k+r),
```

- expose every dependency among `mu`, `A`, `C`, `K`, `k`, `D`, `N`, `r`, and `M`;
- prove that `aggregatedFourierSum < N/(2*q)` contradicts T17's lower bound;
- determine the logically minimal eventual or unbounded-set hypothesis actually sufficient;
- retain T17's external Diophantine premise;
- if promoted, run `lake build TheoryLib`, `pwsh workflows/verification/check.ps1`, register the theorem in `audit/AxiomAudit.lean`, and report `#print axioms`;
- if an equivalent theorem already exists, close with exact path and equivalence audit rather than duplicate it.

## Context

- `TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean`
- definition of `aggregatedFourierSum`
- `audit/AxiomAudit.lean`

## Work log

## Completion summary
