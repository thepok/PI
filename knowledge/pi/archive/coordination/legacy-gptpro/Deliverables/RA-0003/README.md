# RA-0003 — quantitative-block-hitting workstream audit

Agent: `pro-20260821T195133Z-gpt56pro-3244`  
Branch: `pi-core-consolidation`  
Audit date: 2026-08-21

## Decision

**Archive this workstream in place as a historical provenance bundle and replace it as a continuation authority.** Do not restart its removed director workflow. Preserve `program.json`, `knowledge.jsonl`, `log.jsonl`, `director-state.json`, and `library/` unchanged, but use the canonical [`TheoryLib.lean`](../../../TheoryLib.lean) import surface plus current [`GPTPro/Tasks/`](../../Tasks/) for all new work.

The workstream is internally exhausted: T1-T17 are finished except T12, which is parked after a rejected formalization attempt; the final director revision created no new item; and `director-state.json` points to a removed workflow record. Meanwhile the canonical import surface continues from T17 through T106. C1 remains a conjecture.

## Files and trust interpretation

| Input | Audited fact | Trust interpretation |
|---|---|---|
| [`program.json`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/program.json) | T1-T11 and T13-T17 are `done`; T12 is `parked` with exhausted attempts; C1 remains open. | Program labels are workflow metadata, not proof. |
| [`knowledge.jsonl`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/knowledge.jsonl) | Accepted records exist for T1-T11 and T13-T17; no accepted T12 record exists. | Each Lean claim was independently matched to a canonical file below. |
| [`log.jsonl`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/log.jsonl) | T12 was rejected; T14 required revision before acceptance; the last post-T17 revision added zero items. | Used only to reconstruct state; raw log content is not copied here. |
| [`director-state.json`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/director-state.json) | `applied: true`; record URI is `removed-workflow-record://...`. | The old scheduler is not a live coordination surface. |
| [`library/`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/) | Recursive Git tree was non-truncated. It contains t1-t11 and t13-t17; there is no t12 artifact. | Historical candidates and source bundles; not canonical by location alone. |
| [`knowledge/pi/OVERVIEW.md`](../../../knowledge/pi/OVERVIEW.md) | Status is `conjecture`, last audited 2026-08-13; it does not identify this workstream or T17 as the current frontier. | Useful narrative context, but stale as a task selector on this branch. |
| [`TheoryLib.lean`](../../../TheoryLib.lean) | Imports all nine promoted T1-T17 Lean modules and then T18-T106. | Canonical import authority. |
| [`audit/AxiomAudit.lean`](../../../audit/AxiomAudit.lean) | Does not centrally print the representative endtheorems listed below. | Reveals an audit-registration gap, not a mathematical counterexample. |

## Classification rule

- `promoted`: a corresponding canonical Lean module exists and is imported by `TheoryLib.lean`.
- `live`: not itself a promoted theorem, but still supplies a non-duplicated premise or source needed by an existing current task.
- `blocked`: the intended artifact failed and no accepted replacement exists under that task ID.
- `obsolete`: valid historical work whose proposed continuation has been superseded or whose hypotheses cannot specialize to fixed pi.
- `duplicate`: a prose precursor whose mathematical payload was subsequently formalized in the next accepted Lean artifact.
- `unclear`: repository evidence is insufficient. No record remained `unclear` after this audit.

## Record classification

| ID | Classification | Artifact and exact reason |
|---|---|---|
| T1 | `promoted` | [`library/t1/PiQuantitativeBlockHitting.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t1/PiQuantitativeBlockHitting.lean) → [`T1PiQuantitativeBlockHitting.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T1PiQuantitativeBlockHitting.lean). Canonical C1 statement and hostile-review surface. Canonical blob has later textual drift. |
| T2 | `promoted` | [`library/t2/ChampernowneQuantitativeCover.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t2/ChampernowneQuantitativeCover.lean) → [`T2ChampernowneQuantitativeCover.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T2ChampernowneQuantitativeCover.lean), byte-identical. Solved Champernowne analogue only; it proves nothing about pi. |
| T3 | `promoted` | [`library/t3/UniformPiAnalyticCover.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t3/UniformPiAnalyticCover.lean) → [`T3UniformPiAnalyticCover.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T3UniformPiAnalyticCover.lean). Conditional finite-frequency certificate; canonical blob has later textual drift. |
| T4 | `obsolete` | [`library/t4/T4_AUDIT.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t4/T4_AUDIT.md). Bounded literature map, superseded by T9 and later repository-wide audits; retained for source provenance only. |
| T5 | `promoted` | [`library/t5/PiQuantitativeResonanceObstruction.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t5/PiQuantitativeResonanceObstruction.lean) → [`T5PiQuantitativeResonanceObstruction.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T5PiQuantitativeResonanceObstruction.lean). Necessary obstruction with V1 split; canonical blob has later textual drift. |
| T6 | `promoted` | [`library/t6/PiNaturalScaleResonanceObstruction.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t6/PiNaturalScaleResonanceObstruction.lean) → [`T6PiNaturalScaleResonanceObstruction.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean). Natural-scale necessary obstruction; canonical blob has later textual drift. |
| T7 | `obsolete` | [`library/t7/T7_IID_DECIMAL_COVER.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t7/T7_IID_DECIMAL_COVER.md). IID benchmark, not a deterministic theorem for the fixed pi orbit. It does not discharge a live premise. |
| T8 | `promoted` | [`library/t8/PiNoV1NaturalScaleResonance.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t8/PiNoV1NaturalScaleResonance.lean) → [`T8PiNoV1NaturalScaleResonance.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T8PiNoV1NaturalScaleResonance.lean), byte-identical. Removes the V1 alternative but remains necessary-only. |
| T9 | `live` | [`library/t9/T9_DETERMINISTIC_ORBIT_AUDIT.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t9/T9_DETERMINISTIC_ORBIT_AUDIT.md). Source-pinned negative audit: Salikhov supplies pointwise lower bounds on rational approximation, not upper bounds for orbit sums. Its exact power-of-ten specialization is already assigned to [`GP-0001`](../../Tasks/GP-0001-salikhov-power-ten-bridge.md). |
| T10 | `obsolete` | [`library/t10/T10_GENERIC_RESONANT_COVER.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t10/T10_GENERIC_RESONANT_COVER.md). Generic resonant-cover construction does not specialize to the fixed pi orbit and was superseded by the boundary-robust T13/T14 route. |
| T11 | `obsolete` | [`library/t11/T11_COUNT_SENSITIVE_FOURIER_TRANSFER.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t11/T11_COUNT_SENSITIVE_FOURIER_TRANSFER.md). Conditional proof sketch; Salikhov gives only an astronomically large separation-derived cutoff and no cancellation bound. T13/T14 supersede its active estimator route. |
| T12 | `blocked` | [`program.json` agenda item T12](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/program.json). Formalization attempts were rejected and exhausted; no `library/t12/` and no accepted `knowledge.jsonl` record exist. T13/T14 replaced rather than completed this task. |
| T13 | `duplicate` | [`library/t13/T13_BOUNDARY_ROBUST_FEJER_DICHOTOMY.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t13/T13_BOUNDARY_ROBUST_FEJER_DICHOTOMY.md). Paper precursor subsequently formalized as T14. Preserve as rationale, not as an independent frontier item. |
| T14 | `promoted` | [`library/t14/T14BoundaryRobustFejerDichotomy.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t14/T14BoundaryRobustFejerDichotomy.lean) → [`T14T14BoundaryRobustFejerDichotomy.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean), byte-identical. Necessary boundary-count/aggregated-resonance dichotomy. |
| T15 | `duplicate` | [`library/t15/T15_DECIMAL_BOUNDARY_WORD_OBSTRUCTION.md`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t15/T15_DECIMAL_BOUNDARY_WORD_OBSTRUCTION.md). Paper precursor subsequently formalized as T16. |
| T16 | `promoted` | [`library/t16/T16DecimalBoundaryWordObstruction.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t16/T16DecimalBoundaryWordObstruction.lean) → [`T16T16DecimalBoundaryWordObstruction.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T16T16DecimalBoundaryWordObstruction.lean), byte-identical. Deterministic decimal carry/boundary translation. |
| T17 | `promoted` | [`library/t17/T17PowerTenDiophantineReduction.lean`](../../../knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t17/T17PowerTenDiophantineReduction.lean) → [`T17T17PowerTenDiophantineReduction.lean`](../../../TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean), byte-identical. Conditional on `PowerTenDiophantine Real.pi`; it does not prove that premise or C1. Canonical work continues at T18-T106. |

## Promotion verification

Git blob equality is stronger than matching a model-generated `sha256` field. The candidate and canonical Git blobs are:

| ID | Historical library blob | Canonical blob | Result |
|---|---|---|---|
| T1 | `295ee67d6f1f68d1de0fa174506711c865a517f5` | `b59681018b6107b2a94b919629678b675bf50466` | Promoted, non-identical canonical text. |
| T2 | `43e5a3d5e7659e703178e3986c2e9137053096a4` | `43e5a3d5e7659e703178e3986c2e9137053096a4` | Exact promotion. |
| T3 | `b47e65a880f3101a1d5edd9ef70745c8796d041f` | `df25c606dcd4226d3f303c3e718fa2136072f042` | Promoted, non-identical canonical text. |
| T5 | `21b30588f6209d812197db25d367b1d6cabb908b` | `31da98ae098f2528a5f6f31e484ed4ff6594d9ce` | Promoted, non-identical canonical text. |
| T6 | `3fb1758d5179fbcd295f0e64840bae95907aced4` | `0d5286c545e042fb5cfa4d97e0bb4ae7c661080f` | Promoted, non-identical canonical text. |
| T8 | `14b925491c8cb2739558aa09617c1c0340caeb47` | `14b925491c8cb2739558aa09617c1c0340caeb47` | Exact promotion. |
| T14 | `db2fd48455ad1d0a247bb319f51fa7e9643ec01c` | `db2fd48455ad1d0a247bb319f51fa7e9643ec01c` | Exact promotion. |
| T16 | `74e92935ce864346110b7c8b18f35388a9a24f32` | `74e92935ce864346110b7c8b18f35388a9a24f32` | Exact promotion. |
| T17 | `5ee0c650e5c36e05ea6bf0b45bacf7222e69fa99` | `5ee0c650e5c36e05ea6bf0b45bacf7222e69fa99` | Exact promotion. |

The visible drift in T1, T3, T5, and T6 includes comment-line mutations such as `constant` becoming `The constant`. This audit did not establish a theorem-statement change, but it also does not infer full semantic identity from visual inspection. The canonical blobs above are the only current source of truth.

## Central axiom-audit gap

Every promoted module contains local `#print axioms` commands. Exact searches in [`audit/AxiomAudit.lean`](../../../audit/AxiomAudit.lean) found **no central registration** for these representative endtheorems:

```text
Theory.PiDigits.QuantitativeBlockHitting.acceptance_audit_surface
Theory.PiDigits.QuantitativeChampernowneCover.champernowne_explicit_22_cover
Theory.PiDigits.QuantitativeAnalyticCover.explicit_uniform_pi_finiteFrequencyBounds_imply_C1
Theory.PiDigits.QuantitativeResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_resonance
Theory.PiDigits.PiNaturalScaleResonanceObstruction.not_C1_implies_V1_failure_or_unbounded_naturalScale_resonance
Theory.PiDigits.PiNoV1NaturalScaleResonance.not_C1_implies_unbounded_naturalScale_resonance
Theory.PiDigits.BoundaryRobustFejerDichotomy.not_C1_implies_unbounded_explicit_boundary_or_aggregated_resonance
Theory.PiDigits.DecimalBoundaryWordObstruction.not_C1_implies_unbounded_adjacent_word_or_aggregated_resonance
Theory.PiDigits.PowerTenDiophantineReduction.not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine
```

The central audit does print the T6 helper
`Theory.PiDigits.PiNaturalScaleResonanceObstruction.piOrbit_naturalScale_resonance_of_missingBefore`, so the gap is selective rather than a total absence of this namespace.

A single non-duplicate follow-up task was created: [`GP-0006`](../../Tasks/GP-0006-central-axiom-audit-registration.md). It is deliberately separate from [`GP-0005`](../../Tasks/GP-0005-statement-integrity-audit.md), which audits quantifiers and mathematical interpretation rather than central registration.

## Trustworthy continuation state

No new post-T17 mathematics task was created. Existing tasks already cover the live, non-duplicate frontier:

| Existing task | Covered bottleneck |
|---|---|
| [`GP-0001`](../../Tasks/GP-0001-salikhov-power-ten-bridge.md) | Exact Salikhov-to-power-of-ten specialization and comparison with T17. |
| [`GP-0002`](../../Tasks/GP-0002-post-t17-cancellation-criterion.md) | Sharpest post-T17 cancellation criterion. |
| [`GP-0003`](../../Tasks/GP-0003-t17-parameter-explosion.md) | T17 parameter growth and quantitative usability. |
| [`GP-0004`](../../Tasks/GP-0004-deterministic-cancellation-search.md) | Source-pinned deterministic cancellation search. |
| [`GP-0005`](../../Tasks/GP-0005-statement-integrity-audit.md) | Adversarial statement-integrity audit of T14-T17. |
| [`GP-0006`](../../Tasks/GP-0006-central-axiom-audit-registration.md) | Mechanical central axiom-audit registration repair. |

The next unresolved mathematical bottleneck is still a **fixed-pi, natural-scale relative cancellation or equivalent prescribed-cell steering theorem**. Salikhov-type scalar irrationality bounds, finite experiments, generic almost-everywhere results, and the conditional T17 premise do not supply it.

## Verification evidence and limitations

- Inspected all required control files and the complete non-truncated `library/` tree.
- Matched every accepted Lean promotion to an existing canonical module and to an explicit import in `TheoryLib.lean`.
- Compared candidate and canonical Git blob IDs for all nine promoted modules.
- Searched the exact representative declaration names in `audit/AxiomAudit.lean` and recorded the selective coverage gap.
- Confirmed that no T12 artifact or accepted T12 knowledge record exists.
- Confirmed that this audit adds no Lean theorem, axiom, proof, or status upgrade.
- No PDF was analyzed; only the retained source-tree/manifest structure and Markdown audit conclusions were used.
- No Lean source changed in RA-0003, so the full Lean gate is not triggered by this task's Markdown-only repository changes. A local checkout was unavailable in this runtime (`git clone` failed because DNS could not resolve `github.com`), so this deliverable does **not** claim a fresh `lake build` or `scripts/verify.ps1` result.
