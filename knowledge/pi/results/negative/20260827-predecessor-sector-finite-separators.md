# Finite actual-pi separators for predecessor-sector heuristics

Status: `experiment`

Date: 2026-08-27 UTC

These calculations use the same 100-place outward interval arithmetic and
145-digit certified suffix cylinders as the registered finite parent replay.
They are not Lean theorems.  Their purpose is to falsify plausible shortcuts
before investing in an all-scale proof.

## Exact DFT comparison used

T177 proves

\[
 \Xi_d=10\Re Z_{10q,A+dq}(N)-\Re C_0.
\]

Consequently the common zero sector cancels exactly:

\[
 \Xi_d-\Xi_e=10\bigl(\Re Z_{10q,A+dq}(N)
                         -\Re Z_{10q,A+eq}(N)\bigr). \tag{1}
\]

At `(q,A,N)=(1000,334,10000)`, directed intervals give

```text
Re Z(10000,2334,10000) = 4.65970932349418189166...
Re Z(10000,4334,10000) = 4.97533077296234337808...
Re Z(10000,7334,10000) = -1.02339937864296306569...
```

Thus (1) certifies

\[
 \Xi_4-\Xi_2>3.1562144946816>3. \tag{2}
\]

The T172 remainder bound and the registered parent-score upper interval also
give the robust one-sided finite estimate `Xi_4 > 30.7`.  This is genuine
finite target-signed actual-pi data, but still has claim label `experiment`
until the T180/T181 Lean certificate is complete.

## Heuristics killed

Among the 18 occurrences of suffix `334` before `N=10000`, predecessor counts
for digits `0,...,9` are

```text
[1, 2, 4, 2, 3, 2, 0, 1, 1, 2].
```

Digit 2 is modal, yet digit 4 wins the exact signed correction by (2).
Therefore an occupancy/modal-predecessor rule cannot choose the DFT sector
sign.  Equal predecessor counts also do not determine it: digits `1,3,5,9`
all have count two, while their screened corrections have different signs.

The word `7334` occurs at start 5686 in the certified window, but its complete
primitive score is strictly negative.  Hence the existence of a target hit
does not imply a nonnegative primitive score.

Finally, the coherent numerical maximizer chain

```text
334 -> 4334 -> 24334 -> 624334 -> 2624334
```

has scores approximately `19.016, 4.975, 2.181, 2.287, 2.297`.  Once the
suffix occurrence becomes unique, the correct predecessor correction is
about `+20.69`, while every wrong digit is below `-2.29`; the nonzero sector
moduli stabilize rather than decay.  This kills sector-decay as the source of
prescribed-digit control.  Unique-hit localization remains a precise finite
phenomenon, but it merely recovers an already observed predecessor and does
not create an unbounded-horizon V1 consumer.
