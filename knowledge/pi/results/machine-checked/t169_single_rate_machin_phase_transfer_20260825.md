# T169 single-rate rational Machin phase transfer

Status: `machine-checked`

Date: 2026-08-25 UTC

Canonical source:
[`T169T169SingleRateMachinPhaseTransfer.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T169T169SingleRateMachinPhaseTransfer.lean)

T169 defines the explicit rational carrier

```text
delayedSingleRateMachinValue k n = 10^n * machinLower (n + k)
```

and the exact geometric ratio

```text
singleRateMachinErrorRatio = 10 / 625 = 2 / 125.
```

The public theorem `delayedSingleRateMachinValue_isRat` certifies that every
carrier value is the real embedding of a rational. The theorem
`scaled_machinLower_error_lt` proves, for every `t`,

```text
10^t * (Real.pi - machinLower t) < (2 / 125)^t.
```

For every integer `h != 0`, T169 then proves the pointwise transfer
`norm_phase_pi_sub_delayedSingleRateMachinValue_lt`:

```text
||phase h (10^n * pi) - phase h (delayedSingleRateMachinValue k n)||
  < 2*pi*|h| * (2/125)^(n+k) / 10^k.
```

Its natural-window specialization
`norm_phase_pi_sub_delayedSingleRateMachinValue_natural_lt` states that
`|h| < 2 * 10^k` implies

```text
||phase h (10^n * pi) - phase h (delayedSingleRateMachinValue k n)||
  < 4*pi * (2/125)^(n+k).
```

Finally,
`norm_sum_phase_pi_sub_delayedSingleRateMachinValue_natural_lt` sums this over
any horizon `N >= 1`, without making the bound depend on `N`:

```text
||sum_(j<N) phase h (10^(n+j) * pi)
    - sum_(j<N) phase h (delayedSingleRateMachinValue k (n+j))||
  < 4*pi * (2/125)^(n+k) / (1 - 2/125).
```

T169 also connects this pointwise-frequency transfer directly to the actual
positive-frequency T128/T139 coefficient family. It defines

```text
shiftedPositiveBoundaryPiScore k A n N
delayedSingleRateMachinBoundaryScore k A n N
```

using the exact `centeredBoundaryTerm` and `positiveBoundarySupport` at
`q=10^k`. The theorem
`norm_shiftedPositiveBoundaryPiScore_sub_machin_le` proves

```text
||shiftedPositiveBoundaryPiScore k A n N
    - delayedSingleRateMachinBoundaryScore k A n N||
  <= (4*pi*(2/125)^(n+k)/(1-2/125)) * positiveBoundaryLoad (10^k)
```

for every `N>=1`. Thus the complete target-centred positive score, not merely
each separate frequency, transfers to the explicit rational carrier with a
horizon-independent error.

Compared with T38, which uses the deeper index `3*t` and records a
fixed-frequency prefix transfer, T169 samples the checked T36 rational Machin
approximant at index `t` and covers the complete moving natural window needed
by the T139 setting. This is a carrier-transfer theorem only: the new weighted
declaration performs exact coefficient bookkeeping but supplies no sign or
cancellation estimate for `delayedSingleRateMachinBoundaryScore`. It proves
neither the T139 or T148 premise nor density, normality, decimal disjunctivity,
or V1.

The declarations are exported through `TheoryLib.lean` and registered in
`audit/AxiomAudit.lean`. Their audited axiom surface is exactly `propext`,
`Classical.choice`, and `Quot.sound`. The strict verifier passed on the current
tree.
