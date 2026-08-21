# Verified-core index

Canonical source: [TheoryLib](../../../TheoryLib/) and [TheoryLib.lean](../../../TheoryLib.lean).

Current major families:

- `PiDigits`
- `PiDecimalFactorComplexity`
- `PiQuantitativeBlockHitting`
- `PiPositiveLowerBlockDensity`
- `PiPositiveDecimalFactorEntropy`
- `PiLacunaryNearReturnSparsity`
- `PiLongLagBlockCollisionDecay`

The explicit theorem audit is [AxiomAudit.lean](../../../audit/AxiomAudit.lean). The exact allowlist is `propext`, `Classical.choice`, and `Quot.sound`.

No theorem in the core currently proves that every finite decimal word occurs in π.

