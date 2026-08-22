# T118 sampled-BBP normalized-excess cell interval

Status: `machine-checked`

Date: 2026-08-22 UTC

Canonical source:
[`T118T118SampledBBPNormalizedExcessCell.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T118T118SampledBBPNormalizedExcessCell.lean)

For the actual sampled-BBP successor, T118 combines the canonical T114 and
T117 identities to identify the reduced signed numerator as `X/k` and the
positive denominator as `W=H*d*e/k`. It proves `0<k`, `0<W`, and the exact
Euclidean remainder bounds

`0 <= R < W`, where `R = (X/k) % W`.

It then computes every `q`-cyclic cell from the quotient `q*R/W`. For
`0<q` and `a<q`, equality with cell `a` is equivalent to the endpoint-exact
half-open integer interval

`a*W <= q*R < (a+1)*W`.

The approved candidate artifact has SHA-256
`9189eec2abf3c1f5cd56bd4199af1e411792cadc11ef4ccae2a59666e25f9e04`;
its isolated gate log has SHA-256
`6b1f006302f69533ccd82ae3c9f04d16c686bed338330008ab21766c55d5c26f`.
The four public theorems compile in the canonical tree and are registered in
the central axiom audit with only the accepted axiom footprint.

This is a pointwise representation theorem. It proves no cell is ever hit or
repeated, no finite or arbitrarily-late occupancy, no density, cancellation,
normality, V1, decimal-word occurrence, or resolution of the Pi problem.
