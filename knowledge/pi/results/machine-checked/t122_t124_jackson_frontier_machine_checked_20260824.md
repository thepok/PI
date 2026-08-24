# T122--T124 Jackson frontier

Status: `machine-checked`

Date: 2026-08-24 UTC

## Result

Three new Lean modules sharpen and connect the natural-scale Jackson consumer.

- T122 defines the coefficient-weighted quadratic Fourier load and its exact
  pair-collision kernel. It proves weighted Cauchy--Schwarz, the centered pair
  identity, and a conditional collision premise implying T121's weighted
  cancellation and canonical V1.
- T123 groups equal integer frequencies before taking absolute values. It
  proves exact regrouping, aggregated load `<=` raw Jackson load, the same
  empty-interval threshold, aggregated smallness implying a hit, and the
  aggregated pi premise implying V1.
- T124 keeps the target-cylinder phase and signed real part before taking a
  modulus. It proves directional defect `<=` aggregated load, the directional
  empty-interval obstruction, and a wordwise pi premise with its own cutoff
  `N_s` for each word implying V1.

The exact checked implication chain is

```text
T19 pointwise premise
  -> raw T120/T121 Jackson premise
  -> T123 frequency-aggregated premise
  -> T124 wordwise directional premise
  -> canonical V1.
```

## Checked strictness

T123 contains an actual-Jackson finite separator at `q=2`, `N=8`: the seven-
point uniform grid plus a duplicated zero has

```text
aggregated load = 7/32 < 1/4 < 11/32 = raw load.
```

T124 contains an actual-Jackson finite separator at `q=1`, `N=1`, with the
single point at the center of `[0,1)`: its directional defect is `-1 < 1`,
while its aggregated load is exactly `1` and therefore fails the strict
threshold.

These witnesses prove strictness of the corresponding generic finite
criteria. They do not prove logical separation between properties of the
specific pi orbit. In particular, the T124 witness does not separately prove
that word-dependent cutoffs are strictly weaker than length-uniform cutoffs.

## Claim boundary

No collision, aggregated-cancellation, or directional-cancellation premise is
proved for the decimal orbit of pi. V1, density, normality, and decimal
disjunctivity remain open.

The closed Jackson coefficient formulas, exact low-frequency surcharge,
more-than-fourfold pointwise improvement, and the proposed separator at every
`q >= 5` remain `proof sketch`; they are not promoted by this report.

The proof authority is:

- `TheoryLib/PiQuantitativeBlockHitting/T122T122JacksonCollisionBridge.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T123T123AggregatedJacksonFrontier.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T124T124DirectionalJacksonFrontier.lean`
- `audit/AxiomAudit.lean`

The strict verification gate accepts only `propext`, `Classical.choice`, and
`Quot.sound` for the registered declarations.
