# T14 irrationality-measure digit-change bridge

Status: `machine-checked`

Date: 2026-08-24 UTC

From the explicit source premise

```text
IrrationalityMeasureBelow Real.pi 8
```

the trusted Lean core proves that there is a real constant `C14` such that,
for every `N >= 1`,

```text
(1 / log 8) * log N - C14 <= changeCount piDigit N.
```

The proof transfers the effective irrationality bound from pi to `pi - 3`,
uses the existing endpoint-safe period-one window gap, and counts changes in
disjoint exponential checkpoint intervals.

This closes a named conditional bridge used by the T18/T20 chain.  The
published irrationality-measure statement itself remains an external premise.
The theorem proves neither V1 nor V3, and no unconditional digit occurrence
claim follows from it.

Proof authority:

- `TheoryLib/PiDigits/T14IrrationalityMeasureDigitChanges.lean`
- `audit/AxiomAudit.lean`

The audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.
