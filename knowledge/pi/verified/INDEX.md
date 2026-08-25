# Verified-core index

Last audited: 2026-08-25 UTC

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

Latest machine-checked milestone: [T141 sampled-BBP five-adic numerator
divisibility](../results/machine-checked/t141_scaled_bbp_five_adic_numerator_20260825.md).
For `m >= 8`, the actual reduced rational `10^m * bbpPartial (7*m)` has
denominator prime to five and numerator divisible by `5^ceil(m/2)`. This is
exact representation arithmetic; it proves no Archimedean phase control,
cancellation, density, V1, or prescribed digit occurrence.

No theorem in the core currently proves that every finite decimal word occurs in π.
