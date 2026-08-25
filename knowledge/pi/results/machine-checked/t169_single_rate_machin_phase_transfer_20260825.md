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

Compared with T38, which uses the deeper index `3*t` and records a
fixed-frequency prefix transfer, T169 samples the checked T36 rational Machin
approximant at index `t` and covers the complete moving natural window needed
by the T139 setting. This is a carrier-transfer theorem only: it does not prove
the coefficient-weighted T139 score transfer as a separate declaration, any
cancellation estimate for the rational carrier, the T139 premise, density,
normality, or V1.

The declarations are exported through `TheoryLib.lean` and registered in
`audit/AxiomAudit.lean`. Their audited axiom surface is exactly `propext`,
`Classical.choice`, and `Quot.sound`. The strict verifier passed on the current
tree.
