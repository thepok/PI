# T141 sampled-BBP five-adic numerator divisibility

Status: `machine-checked`

Date: 2026-08-25 UTC

Canonical source:
[`T141T141ScaledBBPFiveAdicNumerator.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T141T141ScaledBBPFiveAdicNumerator.lean)

For the actual reduced rational

`scaledBBPRat m = 10^m * bbpPartial (7*m)`,

T141 proves that for every `m >= 8`

`not (5 divides (scaledBBPRat m).den)`

and

`5^((m+1)/2) divides (scaledBBPRat m).num.natAbs`.

Thus the reduced denominator is a five-adic unit while the reduced numerator
retains at least `ceil(m/2)` powers of five. The proof works directly with
the four registered BBP poles and the existing finite-sum valuation theorem;
it does not introduce a second common-denominator representation.

The theorem is registered in the central axiom audit. The strict verifier
accepts it with only `propext`, `Classical.choice`, and `Quot.sound`.

This is exact representation arithmetic. It does not control the remaining
Archimedean phase, primitive-frequency cancellation, T139, density, V1, or
decimal-word occurrence. In particular, the rejected covariance factorization
from the source memo is not part of T141.
