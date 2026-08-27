# GP-0000: control-plane consolidation and post-T17 frontier

Claim label: `literature-checked` for repository-state inspection only. This file introduces no new theorem.

## Operational result

A parallel Pro model created a sound temporary research-agent bootstrap while this task was being prepared. Rather than create a competing queue, its SHA-based task lock, completed RA-0001 reconnaissance, and open RA-0002 through RA-0004 tasks were migrated into the requested top-level `GPTPro/` hierarchy.

The temporary compatibility directory has since been removed at Marcel's request. `GPTPro/` is now the only coordination directory and the only active task queue.

The concrete-results directory is named `Deliverables/`. `Results/` would be ambiguous, while `Findings/` would wrongly exclude code, Lean modules, datasets, and reproducible experiments.

## Exact research state inspected

- Root policies state that no verified resolution exists.
- `knowledge/pi/workstreams/pi-quantitative-block-hitting/program.json` records agenda tasks T1 through T17 as completed; T12 was parked and superseded by the successful T13/T14 route.
- `TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean` proves a conditional theorem: if `Real.pi` satisfies `PowerTenDiophantine Real.pi mu A`, then `not C1` forces aggregated signed-frequency resonance at unbounded exact full-containment deadlines.
- T17 deliberately does not assert its Diophantine hypothesis for pi.
- The T9 source-pinned audit records Salikhov's finite irrationality-measure theorem for pi, but also proves at the literature-analysis level that finite irrationality measure alone does not provide the T3 cancellation certificate.

## Exact post-T17 bottleneck

T17 uses

```text
D = C*k*10^k
N = D-k+1
r = (mu-1)*D+1
M = 2*10^(2*k+r)
```

and under `not C1` obtains

```text
N/(2*10^k) <= aggregatedFourierSum(piOrbit, N, 10^k, M).
```

The live frontier is therefore not another occurrence reformulation. It is the combination of:

1. an exact source-honest bridge from known rational-approximation bounds for pi to T17's power-of-ten predicate;
2. a clean sufficient theorem showing which eventual aggregated-cancellation estimate would imply C1;
3. reduction or justification of the enormous suffix and frequency cutoff; and
4. discovery of a deterministic pi-specific estimate that actually matches the resulting quantitative target.

## Seeded exact tasks

- `GP-0001`: Salikhov-to-`PowerTenDiophantine` bridge.
- `GP-0002`: formal post-T17 cancellation criterion implying C1.
- `GP-0003`: audit and optimize T17's parameter explosion.
- `GP-0004`: non-duplicative primary-source cancellation search.
- `GP-0005`: adversarial statement-integrity audit of T14-T17.

## Verification and limits

The consolidation was based on branch head `352b8c267c801e1312d98b43395cab6ecb70a62b`, root policies, the T9 audit, workstream state, and T17 source. The later cleanup removed only the obsolete compatibility directory and updated this operational record. No Lean code was changed or compiled. The map is workflow guidance, not evidence for C1 or its negation.
