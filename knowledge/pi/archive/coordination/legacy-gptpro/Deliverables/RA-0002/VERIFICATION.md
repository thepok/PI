# RA-0002 verification record

## Scope

This task changed documentation and coordination files only. No Lean source,
import, theorem statement, proof, or axiom-audit declaration was modified.

Therefore the formal-change commands

```text
lake build TheoryLib
pwsh workflows/verification/check.ps1
```

were not applicable to this patch. The task does not claim a new
`machine-checked` result.

Documentation checks executed locally before commit:

```text
balanced Markdown code fences and nonempty relative deliverable targets: PASS
dot -Tsvg frontier.dot -o frontier.svg: PASS
```

## Source-declaration audit

The following load-bearing files were read from branch
`pi-core-consolidation`, and their exact declarations were transcribed into
`README.md`.

| Route | Path | Audited blob SHA |
|---|---|---|
| T19 exact cancellation | `TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean` | `0799dba8b04c0476e95b0aca5e1ab4f50f09dffd` |
| T14 aggregate/dichotomy | `TheoryLib/PiQuantitativeBlockHitting/T14T14BoundaryRobustFejerDichotomy.lean` | `db2fd48455ad1d0a247bb319f51fa7e9643ec01c` |
| T17 Diophantine reduction | `TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean` | `5ee0c650e5c36e05ea6bf0b45bacf7222e69fa99` |
| T28 last-first-occurrence gap | `TheoryLib/PiQuantitativeBlockHitting/T28T28LastFirstOccurrenceLinearGap.lean` | `428c5b9580d58bd9bb9471365041ea3e90ca538f` |
| T29 appearance ratio | `TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean` | `d9abbc8ce0180e560d05165710bed5adf4f859c5` |
| T30 entropy equivalence | `TheoryLib/PiQuantitativeBlockHitting/T30T30MaximalEntropyEquivalence.lean` | `83cb8d8386239c4fdd99148ff280e0544fbdffb0` |
| T35 source-to-power-ten bridge | `TheoryLib/PiQuantitativeBlockHitting/T35T35OversampledBBPGridStability.lean` | `6c53515d39d86ddafc2dcc37d2d02bcf8c1dee0f` |
| T37 arithmetic/symbolic bridge | `TheoryLib/PiQuantitativeBlockHitting/T37T37FloorSymbolicBridge.lean` | `046297d1cef3a76175ed27e7a791127912240a15` |
| T69 fixed-sixteen return | `TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean` | `431c748502eb2115ea1b592f7c72284d56dc298a` |
| T70 empirical rigidity | `TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean` | inspected on branch; no theorem from it was treated as unconditional |
| T104 BBP identity | `TheoryLib/PiQuantitativeBlockHitting/T104T104BBPSeriesIdentity.lean` | `b60418bf46d9e3d70c23406a4e948d97caf69d69` |
| T105 BBP code recurrence | `TheoryLib/PiQuantitativeBlockHitting/T105T105BBPCodeCoverage.lean` | `7615633efb2b43df87ee6af8b866c55b2ea3e465` |
| T106 BBP forced orbit | `TheoryLib/PiQuantitativeBlockHitting/T106T106BBPForcedOrbit.lean` | `17208cfbdae84d5cc90008f3f4e50171ea768c60` |
| T107 BBP Weyl transfer | `TheoryLib/PiQuantitativeBlockHitting/T107T107BBPWeylTransfer.lean` | `4b973fa8156e84fc4fce04589e9a2c6ca10b7e0e` |
| T108 BBP circle-density transfer | `TheoryLib/PiQuantitativeBlockHitting/T108T108BBPCircleDensityTransfer.lean` | `c480adabe6d54bd7695dbd1e171c281b03ec84e3` |
| T109 BBP symbolic packaging | `TheoryLib/PiQuantitativeBlockHitting/T109T109BBPSymbolicPackaging.lean` | `65fed61aa4047b9c4e446e239939ff6e540de9ab` |
| Positive lower density | `TheoryLib/PiPositiveLowerBlockDensity/T1PiPositiveLowerBlockDensity.lean` | inspected on branch |
| Long-lag predicate | `TheoryLib/PiLongLagBlockCollisionDecay/T1T1LongLagBlockCollisionDecay.lean` | `e0425f73acc607e223da34bdfccd2eabe21c442a` |
| Long-lag to V1 | `TheoryLib/PiLongLagBlockCollisionDecay/T3T3CollisionDecayImpliesDisjunctive.lean` | `ec4d69b9b6f4f1a2e0f929f5a12556133b7730aa` |

The branch import surfaces `TheoryLib.lean` and `audit/AxiomAudit.lean` were also
inspected. The post-repair central audit blob is
`033a0898ab8da08e31d7047c61aed041d60c9d13`. T107–T109 are centrally
registered. Concurrent `RA-0003` first
identified a selective central-registration gap for representative T1–T17
endtheorems, including T17's final obstruction theorem. Completed task
`GP-0006` then registered all nine exact endpoints and recorded a passing
`pwsh workflows/verification/check.ps1` run: 8,761 Lean jobs, forbidden-marker
scan, exact axiom audit, and only the allowlisted `propext`,
`Classical.choice`, and `Quot.sound`. RA-0002 did not rerun or independently
claim that concurrent formal gate; it consumed the committed verification
record and made no Lean change itself.

## Coordination checks

- Dependency `RA-0001` was `done` and its deliverable was consumed.
- All task files were inspected before claiming.
- `RA-0002` was claimed against blob
  `fa5bb752e4227a8d56cd880b0a2b1ed2123c5953`.
- The claimed task was re-fetched immediately before completion and remained
  owned by `pro-20260821T194452Z-gpt56pro-7f3c`, at blob
  `ead8279f0d08d97d45ec25044ba79cb5d53d3245`.
- Existing open task `GP-0002` was identified as the recommended mathematical
  follow-up; no duplicate task was created.
- `GP-0006` was completed concurrently and repaired the central T1–T17
  axiom-registration gap; this task did not duplicate or modify that work.
- Existing concurrently claimed `RA-0003` was not modified.
- A first non-forced ref update was rejected because the branch advanced.
  The stale commit was not installed and no force update was attempted.
  T107–T109 were then audited. A later concurrent integration completed
  `GP-0006`; the same bounded documentation patch was updated again and
  rebased onto the current branch head.

## Countermodel check

`COUNTERMODEL.md` gives a complete symbolic counterexample:

```text
constant zero stream:
p(m)=1, L(m)=1 for all positive m, but word [1] is omitted.
```

This directly falsifies the generic appearance-ratio-to-disjunctivity
implication.

## Environment limitation

The root instructions reference
`~/.Codex/skills/marcel-judgment/SKILL.md`. That file was absent from the
execution environment. No content was guessed or substituted.

The environment did not expose a local repository checkout, so source
inspection and commits were performed through the GitHub connector against the
named branch.
