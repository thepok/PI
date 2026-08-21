# T82 source manifest

## Canonical statement

| File | Role | SHA-256 | Verification |
|---|---|---|---|
| `pi-positive-decimal-factor-entropy.txt` | Immutable canonical problem statement | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` | Byte-for-byte vendored copy; checked by `verify.sh` |

The canonical statement contains no external source URL.  T82 preserves it and
is explicitly a metric sibling benchmark, not a replacement statement.

## Kernel-checked interfaces

| Knowledge-library source | Module | SHA-256 | Interfaces used |
|---|---|---|---|
| `t56/T56LagSectorAudit.lean` | `TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit` | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` | `t56SampleLength`, short-sector endpoints, structured denominator |
| `t58/T58TriangularFejerAudit.lean` | `TheoryLib.PiPositiveDecimalFactorEntropy.T58T58TriangularFejerAudit` | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` | `bandwidth`, `shortRectangle`, `phi`, ten reduction, collision second moment |
| `t61/T61VaalerAnalytic.lean` | `TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic` | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` | residual mask, Vaaler coefficient, signed sum, zero mode, endpoints |

These three sources are indexed as kernel-checked accepted artifacts in the
provided knowledge library.  T82 does not treat any file under its `notes/`
subdirectory as a proved premise.

## New argument status

The finite L2 expansion, complete collision parameterization, multiplicity
bound, and Tonelli passage are proved in `T82_METRIC_SIGNED_RESIDUAL.md` as a
rigorous `proof sketch`.  The exact finite algebra is independently replayed by
`t82_symbolic_replay.py`.  It has not been formalized in Lean and is not
labeled `machine-checked`.

No literature novelty claim is made.  The only invoked analytic facts beyond
the imported interfaces are elementary trigonometric orthogonality,
`|sin|<=1`, `|cos|<=1`, `pi>3`, finite Cauchy-Schwarz, and Tonelli's theorem;
their uses and constants are displayed in the note.
