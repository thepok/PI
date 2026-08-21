# T128 bounded recovery search log

Search date: 2026-08-10 UTC.

## Protocol

The search began from the canonical statement and the staged T2, T7, T107,
T116, and T120 artifacts. It stopped after seven primary papers and four
retained cards. Temporary PDF text derivatives were made with
`pdftotext -layout`; each source counts once.

```text
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 12
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
```

| order | lane | query/fingerprint | source | disposition |
|---|---|---|---|---|
| 1 | symbolic entropy/collision | nested de Bruijn prefixes with effective extension | Ugalde 2000 | retain C-UG; exact coherent endpoint |
| 2 | structured exponential sums | explicit fixed-base lacunary discrepancy | Levin 1999 | retain C-LEV; all-prefix polylog count error |
| 3 | symbolic structure | finite nested-perfect interpretation of Levin | Becher-Carton 2019 | inspect, use as corroborating source, no new card |
| 4 | structured discrepancy | explicit finite necklace bound | Hofer-Larcher 2023 | inspect, use as finite-rate audit, no decimal card |
| 5 | fixed-point lacunary dynamics | one computable point with pointwise rate | Aistleitner et al. | retain C-ABS; square-root range |
| 6 | Mahler/functional equation | computable morphic point with exact factor frequencies | Balkova 2012 | retain jointly as C-TM source; no finite modulus |
| 7 | Mahler/automatic collision obstruction | effective word-family size | Goc-Schaeffer-Shallit | retain jointly as C-TM source; quantitative rejection |

## Excluded searches

- Ordinary normality without a finite uniform rate was stopped at the cheap
  test and not counted as a candidate.
- Almost-everywhere and invariant-measure genericity were excluded because
  they name no point.
- Renewal, game avoidance, global-L2 existence, and online vector balancing
  were excluded by the agenda. T116 and T120 were comparison inputs, not
  newly inspected primary sources.
- No claim of novelty is made beyond this bounded seven-source corpus.

## Prior and active artifact inventory

Readable comparison files and hashes:

```text
T2   knowledge_library/t2/NormalOrbitNearReturns.lean
     1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174
T7   knowledge_library/t7/FiniteCylinderEnergy.lean
     cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c
T107 knowledge_library/t107/T107AveragedTriangularFejer.lean
     45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28
T116 knowledge_library/t116/REPORT.md
     573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1
T120 knowledge_library/t120/REPORT.md
     8b375d1c06cbf9549e5f1919d25b227a9479be7bc3a5ed70955f5718a996dad5
```

T2, T7, and T107 have machine-checked Lean statements. T116 and T120 label
their source claims literature-checked and their deductions proof sketches.

The refreshed knowledge library contains T121. Its full report is vendored as
`prior-t121-REPORT.md`, SHA-256
`01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2`.
T121 REPORT lines 181-185 explicitly screen the Becher-Carton explicit-point
discrepancy route as already represented by T90/T110. This is the same
normalized lane as T128 C-LEV, whose overlap is now disclosed. T121 F-NECK is distinct from C-UG at the endpoint level: its exact
necklace card is a shifted finite block and T121 rejects treating it as an
initial prefix, whereas C-UG uses one nested prefix schedule.

The agenda names T122 as active, but the refreshed supplied knowledge library
has no `t122/` entry and supplies no T122 report, source extract, candidate
formula, or verification record. Accordingly T122 is compared only at this
availability boundary. No mechanism, verdict, overlap, distinctness, or
novelty conclusion is inferred, and no T122 premise is used. This replaces the
inherited scout's unsupported status-level description rather than preserving
it.

## Stopping reason

C-UG already meets the fingerprint exactly at `kappa=1`; C-LEV tests the
all-prefix relaxation; C-ABS tests a distinct computable lacunary selector;
C-TM supplies a functional-equation rejection. Further sources would not add
a new requested lane or change the first quantitative obstruction.
