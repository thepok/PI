# T75 source manifest

## Canonical statement

- File: `pi-positive-decimal-factor-entropy.txt`
- Original source URL: none; the question was formulated locally on
  2026-07-22.
- SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
- Use: immutable canonical question, sibling-variant scope, and nonclaim rules.

## Kernel-checked internal inputs

- File: `T56T56LagSectorAudit.lean`
- Module:
  `TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit`
- SHA-256:
  `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc`
- Use: exact natural-division sample length, strict short-lag range, and
  parameterized short residual count.

- File: `T69T69FiveCaseCharging.lean`
- Module:
  `TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging`
- SHA-256:
  `43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9`
- Use: five endpoint cases, three cyclic permutations, `W5`, global `E3`, and
  `shortResidualPairCount_le_W5`.

Both Lean files are byte-exact vendored copies of the accepted kernel-checked
TheoryLib modules. T75 imports their modules instead of redeclaring them.

## Excluded sketch source

The T67 note was inspected only to identify claims that must not be inherited.
It is an unverified sketch, is not delivered as a source, and no T75 premise
depends on it. T75 re-proves its window cover, overlap, load bound, and inverse
claim.

## External literature

No external mathematical result is used. The finite Cauchy-Schwarz step is
already instantiated by the imported kernel-checked T69 module and is
reapplied explicitly in the T75 note. No novelty claim is made.
