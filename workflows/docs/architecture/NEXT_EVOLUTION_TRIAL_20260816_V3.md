# Next Evolution controlled trial v3

Status: **completed successfully and operator-paused after exactly three dispatches**. This is an architecture validation report, not a mathematical claim about pi.

## Live dispatches

| # | Record | Route | Knowledge packet | Independent review | Terminal outcome |
|---:|---|---|---|---|---|
| 1 | `T190 r0` | Terra guided execution | 10 records, 20,442 bytes, `afc1f1a4...c719` | Sol fixed-pi review | `revise`, pipeline metadata: one arXiv date |
| 2 | `T191 r0` | Terra guided execution | 10 records, 19,837 bytes, `9b5f754d...b57` | Sol fixed-pi review | `revise`, mathematical/completeness defects |
| 3 | `T190 r1` | Terra minimal repair from 12 staged prior artifacts | same deterministic T190 packet | Sol fixed-pi review | `accept` |

The scheduler had a retryable fourth action after T191, but repeatedly emitted no dispatch after the trial counter reached three. No fourth trial record exists.

## Result quality

- T190 is an internally accepted, source-pinned negative map for three related symbolic-model mechanisms. It selects no successor and explicitly claims no progress on pi, A1, C1, or C2.
- T191 was not accepted. Sol found that the purported named-point Fourier candidate was only an ambient limsup-set theorem, one applicability card omitted standing hypotheses, and the historical exclusion ledger used unauditable placeholders.
- Every record passed through deterministic artifact gates and Fixed-pi Sol review. No trusted artifact or verifier receipt was created by graph projection.
- Each post-review projection declared one result record. Neither `revise` created a terminal obstruction; this confirms the corrected obstruction lifecycle.

## Live invariant repairs made during the trial

1. **Cumulative retry memory.** Pipeline or operator interruptions no longer mask an earlier mathematical review. Retry feedback carries a bounded chronological review history and anchors legacy fields to the newest substantive review.
2. **Owned control cleanup.** Operator cleanup recognizes theory directors, theory skeptics, formulators, target scouts, and claim audits by exact argv/record attribution. Reclaimed control workflows receive terminal `run_control` state.
3. **Director commit ordering.** A failed or cancelled director without `theory_revision.json` no longer commits its context hash as an accepted empty decision. The context is rearmed at most twice, then parked to prevent a paid crash loop.
4. **Negative unfinished-item references.** The agenda validator permits explicit `independent of` / `without relying on` provenance statements while continuing to reject positive dependencies on unfinished items.

All four defects were first observed as real runtime behavior, corrected at their shared invariant, regression-tested, and then replayed successfully in the same controlled trial.

## Token telemetry

Across the three dispatched records, provider-reported token accounting was:

- total: 12,394,494;
- cache reads: 11,550,208 (93.19% of total);
- uncached input: 758,371;
- output: 50,986;
- reasoning: 34,929;
- execution phases: 7,841,297 total;
- review phases: 4,553,197 total.

The accepted T190 repair cost 2,294,959 total versus 4,530,064 for its first pass because it reused the 12 staged artifacts. Provider totals include cache reads and therefore should not be confused with newly billed/uncached input.

## Final verification

- knowledge graph audit: 26 corpora, 1,919 records, 2,170 evidence rows, 85 raw obstruction declarations; passed;
- compact retrieval shadow: all three cases preserved claim boundaries and active obstruction context; passed;
- `tools/test_research_knowledge.py`: 8 passed;
- `tools/test_orchestrator.py`: 284 passed, 2 expected failures (run in bounded chunks); all new regressions passed;
- Python compilation for the modified architecture modules: passed;
- final runtime: supervisor inactive, no owned workflow process, no pod, durable `OPERATOR_PAUSED` marker present.

The trial switch is disabled after completion. Future research still requires an explicit operator resume and a new or deliberately uncapped run policy.
