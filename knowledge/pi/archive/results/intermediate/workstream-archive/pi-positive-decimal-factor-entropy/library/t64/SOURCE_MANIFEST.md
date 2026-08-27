# T64 source manifest

## Canonical statement

- Local source: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`
- Delivered byte-exact copy: `pi-positive-decimal-factor-entropy.txt`
- SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
- Original external URL: none; the question was formulated locally on
  2026-07-22.

## Kernel-checked inputs

The note uses the following accepted library modules. They are referenced,
not duplicated in this artifact set.

- `TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit`
  (`T56LagSectorAudit.lean`), SHA-256
  `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc`.
- `TheoryLib.PiPositiveDecimalFactorEntropy.T58T58TriangularFejerAudit`
  (`T58TriangularFejerAudit.lean`), SHA-256
  `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d`.
- `TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic`
  (`T61VaalerAnalytic.lean`), SHA-256
  `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993`.

The relevant public checked declarations are listed with exact locators in
`T64_COVARIANCE_OPERATOR_TEST.md`.

## Sketch-level motivation

- The T63 note `T63_AOC4_VAALER_CROSSWALK.md`, SHA-256
  `9270f11c49df45e3c0716dbf653ccc53a332f553e859007054a35e52a6dc4efc`,
  was consulted only to identify the proposed interface and the name
  `COV_63`. No claim from T63 is used as a discharged premise.
- The AOC_4 formula originates in the sketch-level T43 note. T64 restates the
  finite formula and proves the algebra and counterexample it uses.

No external literature claim is needed for this finite operator test.
