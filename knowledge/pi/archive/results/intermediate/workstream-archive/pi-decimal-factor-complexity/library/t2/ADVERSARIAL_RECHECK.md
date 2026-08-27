# Adversarial recheck receipt

Recheck date: 2026-07-21 UTC.

This receipt records checks performed after drafting `APPLICABILITY_MATRIX.md`.
It is not evidence independent of the retained source files; it identifies the
commands and the downgrades made so a skeptic can repeat them.

## Canonical integrity

Command:

```text
sha256sum knowledge/pi/statements/pi-decimal-factor-complexity.txt
```

Observed SHA-256:

```text
e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43
```

This equals the required canonical hash.

## Lean recompile

No new Lean theorem is delivered by T2.  Because the matrix relies on the
accepted T1 one-sided bridge, that exact knowledge-library file was recompiled
from the workspace root after linking the pinned package cache:

```text
mkdir -p .lake
ln -sfn /opt/allmath-lean/.lake/packages .lake/packages
lake env lean removed-workflow-record://todo-theory-pi-decimal-factor-complexity-t2-1784634806-r0/knowledge_library/t1/DecimalFactorComplexity.lean
```

Result: exit status 0.  Lean printed only unused-section-variable linter
warnings.  The relevant axiom output was:

```text
DecimalFactorComplexity.morse_hedlund:
  [propext, Quot.sound]
DecimalFactorComplexity.morse_hedlund_canonical:
  [propext, Classical.choice, Quot.sound]
DecimalFactorComplexity.decimal_disjunctive_iff_canonical_factorComplexity:
  [propext, Classical.choice, Quot.sound]
```

These are within the specified allowlist.  The recompiled file SHA-256 remains
`8b61e1319cd9fc753b93723f6f059583741da721252bdb7d3cace8b9c7a80c2e`.

## Citation re-open

Each local PDF was re-read from the retained file rather than from the draft's
prose.

| Source | Material re-opened | Outcome |
|---|---|---|
| S1 Morse--Hedlund | Journal pp. 829--830, Theorems 7.3--7.4 | Scan visibly has `P(n) >= n+mu-1`; OCR drops the inequality glyph.  The draft uses the scan, not the lossy OCR, and preserves the two-sided trajectory hypothesis. |
| S2 Adamczewski--Bugeaud | Journal pp. 549--553 | Theorem 1 has integer base, irrationality, and algebraicity hypotheses and exact `liminf p(n)/n = infinity` conclusion.  Theorems 2--3 and the Fibonacci/Kempner examples match the matrix. |
| S3 Bailey--Crandall | Local PDF pp. 2--11 | Hypothesis A is explicitly unproved.  Theorem 1.1 gives base-2 normality only conditionally; the displayed recurrence gives base-16 normality only if equidistributed.  No base-10 transfer is stated. |
| S4 Niven | Journal p. 509 | The contradiction proves pi irrational. |
| S5 Lindemann | Journal pp. 213 and 223 | The opening states the algebraicity question; p. 223 concludes that pi cannot be a root of an algebraic equation with rational real or complex coefficients. |
| S6 Trueb | PDF pp. 1--3 | The report is finite, covers word lengths only 1--3, assumes binomial occurrence statistics for comparison bands, and describes consistency rather than proof. |

## Experiment reproducibility

The S6 experiment was not reproducible from the pinned materials.

- The arXiv `e-print` endpoint returned the same three-page PDF, not analysis
  source code.
- The linked `pi2e.ch` record gives y-cruncher, Chudnovsky/Bellard formulas,
  hardware, and run duration.
- Neither location supplies the 22.4-trillion-digit dataset, raw block counts,
  frequency-analysis implementation, or an exact analysis command.
- Recomputing the digit corpus would require the source-reported 1.25 TB RAM,
  large disk array, and approximately 7,664,613 seconds; a small-prefix rerun
  would be a different experiment and was not substituted silently.

The PI-3 row was therefore downgraded to **source-reported experiment, not
independently reproduced**.  Its numerical claims are not used to support any
theorem or applicability verdict.

## Corrections made

1. Removed the T1 one-sided bridge from the primary-literature summary rows.
   It remains separate machine-checked support with a clear evidence type.
2. Removed automaticity from AB-2's hypothesis list.  Automaticity is the
   property excluded by the theorem's conclusion, not an input hypothesis.
3. Added the explicit S6 reproducibility blocker and downgraded its evidence
   label.

After these corrections, no primary-source row reports a theorem as applying
to the canonical decimal stream of pi.  The separately machine-checked bridge
applies only to A4, and all stronger routes remain **NO** or **NOT KNOWN**.
