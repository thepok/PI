# Verified-core index

Last audited: 2026-08-22 UTC

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

Latest machine-checked milestone: [T118 sampled-BBP normalized-excess cell
interval](../results/machine-checked/t118_sampled_bbp_normalized_excess_cell_20260822.md).
It identifies the actual successor's normalized signed numerator, positive
denominator, Euclidean residue, quotient cell, and exact half-open cell
interval. It proves no cell hit or recurrence, occupancy, cancellation,
density, V1, or prescribed digit occurrence.

No theorem in the core currently proves that every finite decimal word occurs in π.
