# Weighted natural-scale Fourier frontier

Status: `machine-checked`

Date: 2026-08-24 UTC

The trusted Lean core now retains the exact Jackson-coefficient weights that
T19 previously relaxed to a worst-frequency maximum.  For a finite sequence,
an empty interval of length `1/q` forces

```text
jacksonWeightedFourierLoad x N q >= 1/(3q) + 2/(3q^3).
```

At `q = 10^k`, the corresponding strict upper bound for the decimal orbit of
pi implies canonical V1.  The older T19 simultaneous pointwise condition
implies this weighted condition.  A two-point grid at `q = 1` satisfies the
weighted finite condition but violates the pointwise finite condition, so the
converse between those generic finite predicates fails.

The fixed-pi weighted estimate is not proved.  The separator is not a
separator between two established properties of pi.  V1 remains a
`conjecture`; no novelty or literature-optimality claim is made.

Proof authority:

- `TheoryLib/PiQuantitativeBlockHitting/T120T120WeightedNaturalScaleFrontier.lean`
- `TheoryLib/PiQuantitativeBlockHitting/T121T121WeightedNaturalScaleCriterion.lean`
- `audit/AxiomAudit.lean`

The audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.
