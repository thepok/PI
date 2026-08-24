# T122--T130 Jackson and boundary-kernel frontier

Status: `machine-checked`

Date: 2026-08-24 UTC

## Result

Nine Lean modules now sharpen and connect the natural-scale Jackson consumer
and two downstream audited mechanisms.

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
- T125 proves the exact total signed mass `2` of the Jackson coefficients and
  that frequency aggregation preserves it.
- T126 proves the generic zero-window concentration bridge used by the new
  effective-irrationality/UI no-go.
- T127 proves the exact affine ratio identity and strict monotonicity lemma
  needed by the boundary-matched kernel comparison.
- T128 proves the boundary-matched kernel's exact finite Fourier closed form,
  outside-sign property, coefficientwise domination of the old Jackson
  coefficients, positive explicit zero-mode lower bound, and finite
  directional hitting consumer.
- T129 proves exact closed forms for the Jackson and boundary signed zero
  modes, an exact formula for their gain, and strict positivity of that gain
  for every `q > 1`.
- T130 proves the exact aggregation gain identity, both piecewise cubic
  cross-determinant formulas and their positivity, and the actual normalized
  boundary improvement at the outer frequency `2q-1`.

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

T124 also contains an actual decimal-scale separator at `q=10`, `N=1`, with
the singleton `x=1/20` centered in `[0,1/10)`. Its directional defect is
exactly `-983/500 < 17/500`; the aggregated criterion already fails because
the single `h=10` contribution is `83/1000 > 17/500`.

These witnesses prove strictness of the corresponding generic finite
criteria. They do not prove logical separation between properties of the
specific pi orbit. In particular, the T124 witness does not separately prove
that word-dependent cutoffs are strictly weaker than length-uniform cutoffs.

## Claim boundary

No collision, aggregated-cancellation, or directional-cancellation premise is
proved for the decimal orbit of pi. V1, density, normality, and decimal
disjunctivity remain open.

The general closed Jackson coefficient formulas, exact low-frequency
surcharge, and all-scale claims remain `proof sketch`; they are not promoted
by this report. For the boundary-matched kernel, the general interior
frequency-fiber identification, full actual normalized coefficientwise
comparison, `q=10` boundary separators, and fixed-pi premise also remain
`proof sketch`.

The proof authority is:

- `TheoryLib/PiQuantitativeBlockHitting/T122T122JacksonCollisionBridge.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T123T123AggregatedJacksonFrontier.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T124T124DirectionalJacksonFrontier.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T125T125AggregatedJacksonCoefficientMass.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T126T126ZeroWindowCell.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T127T127BoundaryKernelRatioAlgebra.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T128T128BoundaryMatchedKernel.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T129T129BoundaryKernelNormalizedComparison.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T130T130BoundaryNonzeroCoefficientAlgebra.lean`
- `audit/AxiomAudit.lean`

The strict verification gate accepts only `propext`, `Classical.choice`, and
`Quot.sound` for the registered declarations.
