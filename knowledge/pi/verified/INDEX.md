# Verified-core index

Last audited: 2026-08-21 UTC

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

Latest machine-checked milestone: [T117 common-denominator and excess-gcd
decomposition](../results/machine-checked/t117_common_denominator_excess_gcd_20260821.md).
It removes the automatic common-denominator factor from the exact sampled-BBP
successor arithmetic and preserves the remaining gcd valuations. It proves no
gcd-size bound, cancellation, cell occupancy, density, V1, or prescribed
digit occurrence.

No theorem in the core currently proves that every finite decimal word occurs in π.
