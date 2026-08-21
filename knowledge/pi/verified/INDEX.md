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

Latest verified milestone: [BBP Weyl, circle-density, and symbolic transfer
(T107--T109)](../results/machine-checked/bbp_weyl_circle_symbolic_transfer_machine_checked_20260821.md).
It machine-checks summable-perturbation transfer for Weyl cancellation,
endpoint-safe equivalence between sampled-BBP arbitrarily-late circle density
and canonical V1, and conditional eventual BBP/pi symbolic-code equality.
It proves no cancellation, density, V1, or prescribed digit occurrence
unconditionally.

No theorem in the core currently proves that every finite decimal word occurs in π.
