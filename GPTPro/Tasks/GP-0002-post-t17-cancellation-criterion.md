---
id: GP-0002
title: Formalize the post-T17 cancellation criterion implying C1
status: done
priority: P0
created_at: 2026-08-21T19:16:35Z
created_by: pro-20260821T191635Z-gpt56pro-consolidation
claimed_by: pro-20260821T201750Z-gpt56pro-45d5
claimed_at: 2026-08-21T20:18:34Z
lease_until: 2026-08-22T20:18:34Z
finished_at: 2026-08-21T20:57:52Z
depends_on:
  - RA-0001
result_paths:
  - GPTPro/Deliverables/GP-0002/README.md
  - GPTPro/Deliverables/GP-0002/T110Candidate.lean
  - GPTPro/Deliverables/GP-0002/promote_t110.py
verification:
  - "PASS: exact T17 theorem-interface and conjunction-shape audit"
  - "PASS: exact q/D/N/r/M dependency and strict-contradiction audit"
  - "PASS: static candidate scan found no sorry, admit, native_decide, unsafe, or axiom declaration"
  - "PASS: promotion helper compiled with Python and passed install, idempotence, and divergent-target refusal tests"
  - "PASS: final repository-state audit found no unverified T110 registration in TheoryLib.lean or audit/AxiomAudit.lean"
  - "NOT RUN: Lean compilation, strict repository gate, and #print axioms; no executable toolchain or CI evidence was available, so the result remains an unpromoted candidate"
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

- 2026-08-21T20:18:34Z: Claimed atomically by `pro-20260821T201750Z-gpt56pro-45d5` against blob `ff4eb1b6760aa293ca6787cd1426c44bccc4f021` after the GP-0001 claim conflicted.
- 2026-08-21: Audited T17's exact endpoint and found no equivalent packaged contrapositive in the canonical modules.
- 2026-08-21: Determined that an arbitrary unbounded upper-bound set is insufficient; the minimal generic condition derivable from T17 alone is an admissible tail.
- 2026-08-21: Wrote the exact strict contrapositive with all `mu`, `A`, `C`, `K`, `k`, `q`, `D`, `N`, `r`, and `M` dependencies exposed and `PowerTenDiophantine Real.pi mu A` retained.
- 2026-08-21: Attempted isolated and full verification through a temporary self-reporting push workflow. It produced neither a start marker nor a report, and the invocation runtime lacked `lean`, `lake`, and `pwsh`.
- 2026-08-21: Moved the theorem to `GPTPro/Deliverables/GP-0002/T110Candidate.lean`, made the promotion helper self-contained and non-overwriting, removed the unverified canonical module, and removed the temporary workflow.
- 2026-08-21T20:57:52Z: Completed static trust checks, helper tests, final canonical-surface audit, and task closure.

## Completion summary

Candidate resolution completed. The exact sufficient theorem is the strict tail contrapositive of T17: under the explicit power-of-ten Diophantine premise, an aggregated-Fourier upper bound below `N/(2*q)` at every sufficiently large admissible scale forces `C1`. Merely holding on an unbounded set is not sufficient because T17 supplies only another unbounded witness set, which may be disjoint.

The Lean source is staged as a candidate rather than promoted. No machine-check, full gate result, or axiom report is claimed. The immediate promotion requirement is to compile the candidate and pass `pwsh workflows/verification/check.ps1`. The unresolved mathematical bottleneck is an actual deterministic tail cancellation estimate for the fixed pi orbit.
