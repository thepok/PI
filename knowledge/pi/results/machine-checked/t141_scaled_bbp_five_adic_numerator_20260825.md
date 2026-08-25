# T141 sampled-BBP five-adic numerator divisibility

Status: `machine-checked`

Date: 2026-08-25 UTC

Canonical source:
[`T141T141ScaledBBPFiveAdicNumerator.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T141T141ScaledBBPFiveAdicNumerator.lean)

For the actual reduced rational

`scaledBBPRat m = 10^m * bbpPartial (7*m)`,

T141 proves the all-depth valuation bound

`m - Nat.log 5 (56*m+5) <= padicValRat 5 (scaledBBPRat m)`.

The constant uses the inclusive BBP range `0 <= k <= 7*m`; the largest of
the four reduced linear pole denominators is `8*(7*m)+5 = 56*m+5`.

Consequently, for every `m >= 2`,

`not (5 divides (scaledBBPRat m).den)`

and

`5^(m - Nat.log 5 (56*m+5)) divides (scaledBBPRat m).num.natAbs`.

Thus the reduced denominator is a five-adic unit while the reduced numerator
retains `m - O(log m)` powers of five. The earlier theorem for `m >= 8`, with
the simpler exponent `ceil(m/2)`, is preserved. The proof works directly with
the four registered BBP poles and the existing finite-sum valuation theorem;
it does not introduce a second common-denominator representation.

The theorems are registered in the central axiom audit. The strict verifier
accepts them with only `propext`, `Classical.choice`, and `Quot.sound`.

This is exact representation arithmetic. It does not control the remaining
Archimedean phase, primitive-frequency cancellation, T139, density, V1, or
decimal-word occurrence. In particular, the rejected covariance factorization
from the source memo is not part of T141.
