# T122 frequency-aggregated Jackson frontier

Status: `candidate`

Date: 2026-08-24

Branch: `progress/t122-frequency-aggregated-jackson`

Lean candidate:
`TheoryLib/PiQuantitativeBlockHitting/T122T122FrequencyAggregatedNaturalScaleFrontier.lean`

Exact finite certificate:
`knowledge/pi/results/intermediate/20260824-t122-q2-separator-certificate.py`

## Research contract

The attacked edge is the T120/T121 coefficient-weighted Jackson load.  T120
retains one summand for every Jackson index and takes absolute values before
indices carrying the same integer Fourier frequency are combined.

The proposed improvement groups the presentation by exact frequency first.
For a finite Fourier presentation with coefficients `c_i` and frequencies
`f_i`, put

```text
C_h = sum_{i : f_i = h} c_i.
```

The old index-weighted load is

```text
L_index(N) = (1/N) * sum_{i : f_i != 0} |c_i| * |S_{f_i}(N)|.
```

The new frequency-aggregated load is

```text
L_freq(N) = (1/N) * sum_{h != 0} |C_h| * |S_h(N)|,
```

where the sum is only over frequencies represented by the presentation.

The deliverable has three required parts:

1. a direct missing-interval obstruction in terms of `L_freq`;
2. a checked implication from the current T120/T121 premise to the new premise;
3. a concrete separator showing that the new finite premise is strictly
   weaker, not merely differently written.

The first two parts are encoded in the Lean candidate.  The third part is
proved exactly below and reproduced by the accompanying rational/cyclotomic
certificate.  The Lean candidate has not yet passed the repository kernel
and axiom gates, so this report is not promoted to `machine-checked` status.

## Direct obstruction

Let

```text
P(t) = sum_i c_i * exp(2*pi*i*f_i*t)
```

be a real-valued finite Fourier presentation satisfying `P(x_j-center) <= 0`
for all `j < N`.  Suppose its zero-frequency coefficient is at least `c0 > 0`.
Summing over `j` and separating the zero frequency gives

```text
c0 * N <=
  |sum_{i : f_i != 0}
      c_i * exp(-2*pi*i*f_i*center) * S_{f_i}(N)|.
```

Regrouping equal frequencies is an exact identity:

```text
sum_{i : f_i != 0}
    c_i * exp(-2*pi*i*f_i*center) * S_{f_i}(N)
=
sum_{h != 0}
    C_h * exp(-2*pi*i*h*center) * S_h(N).
```

Only after this identity is applied do we use the triangle inequality.  Since
the phase has norm one,

```text
c0 * N <= sum_{h != 0} |C_h| * |S_h(N)|,
```

and therefore

```text
c0 <= L_freq(N).
```

For the order-`q` Jackson minorant in T120, the same zero-mode lower bound is

```text
c0(q) = 1/(3*q) + 2/(3*q^3).
```

Thus `L_freq(N) < c0(q)` forces a hit in every interval of length `1/q`.
Specializing to `q = 10^k` gives a new conditional route to canonical V1.
No fixed-pi cancellation estimate is asserted here.

## Implication from the current weighted premise

For every represented frequency `h`, the fibrewise triangle inequality gives

```text
|C_h| = |sum_{i : f_i = h} c_i|
      <= sum_{i : f_i = h} |c_i|.
```

Multiplying by the nonnegative value `|S_h(N)|`, summing over frequencies, and
dividing by `N > 0` yields

```text
L_freq(N) <= L_index(N).
```

Consequently, the current T120/T121 weighted pi premise implies the proposed
frequency-aggregated pi premise, and the latter still implies V1 through the
direct obstruction above.

## Exact strictness separator for the actual Jackson presentation

Use Jackson parameters

```text
q = n = 2.
```

The presentation has 32 indices.  Exact aggregation gives the following
frequency coefficients:

| `h` | `-3` | `-2` | `-1` | `0` | `1` | `2` | `3` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| `C_h` | `1/8` | `3/8` | `3/8` | `1/4` | `3/8` | `3/8` | `1/8` |
| index multiplicity | `1` | `3` | `7` | `10` | `7` | `3` | `1` |

The exact nonzero masses are

```text
sum_{h != 0} |C_h| = 7/4,

sum_{i : f_i != 0} |c_i| = 11/4.
```

The total unfiltered index coefficient mass remains `4`, agreeing with T120.
The order-two zero-mode threshold is

```text
c0(2) = 1/(3*2) + 2/(3*2^3) = 1/4.
```

Now take the eight-point sequence

```text
x_0,...,x_7 = 0/7, 1/7, 2/7, 3/7, 4/7, 5/7, 6/7, 0.
```

For every nonzero Jackson frequency `h` in

```text
{-3,-2,-1,1,2,3},
```

multiplication by `h` permutes the residues modulo seven.  Hence, for a
primitive seventh root of unity `zeta`,

```text
sum_{j=0}^6 zeta^(h*j) = sum_{r=0}^6 zeta^r = 0.
```

The repeated point at zero contributes one, so

```text
S_h(8) = 1
```

for every represented nonzero frequency.  Therefore the two loads are exactly

```text
L_freq(8)  = (7/4)/8  = 7/32,
L_index(8) = (11/4)/8 = 11/32.
```

They straddle the same Jackson threshold:

```text
7/32 < 1/4 < 11/32.
```

Thus the frequency-aggregated finite premise holds while the current
index-weighted finite premise fails.  This is a separator for the actual
order-two Jackson coefficients, not an abstract coefficient toy model.

## Reproducible exact certificate

Run

```bash
python knowledge/pi/results/intermediate/20260824-t122-q2-separator-certificate.py
```

The program uses only `fractions.Fraction` and exact arithmetic in
`Q[z]/(1 + z + ... + z^6)`.  It performs no floating-point calculation.  It
checks the 32 Jackson terms, the complete coefficient table, frequency
multiplicities, both nonzero masses, the seventh-root exponential sums, and

```text
7/32 < 1/4 < 11/32.
```

A passing script is an exact finite certificate, not a substitute for the
Lean kernel gate.

## Claim boundary

This result does **not** prove any new cancellation estimate for the decimal
pi orbit.  It does **not** prove normality, density, decimal disjunctivity, or
V1 unconditionally.

The genuine progress is narrower and auditable:

```text
T121 index-weighted premise
            |
            v
strictly weaker frequency-aggregated premise
            |
            v
           V1
```

The remaining open input is still a fixed-pi estimate, but the required
analytic quantity now removes cancellation internal to repeated Jackson
frequency fibres before absolute values are taken.

## Verification status and stop condition

The exact finite separator has been independently reproduced by the attached
certificate.  The Lean candidate remains on a draft pull request because the
GitHub Actions job failed at runner startup before checkout and produced no
Lean step or log.  It must not be merged or described as machine-checked until
all of the following pass:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T122T122FrequencyAggregatedNaturalScaleFrontier.lean
lake build TheoryLib
pwsh workflows/verification/check.ps1
```

The stop condition is strict: any failure of the regrouping identity,
`L_freq <= L_index`, the pi-to-V1 bridge, the q=2 coefficient table, or the
axiom allowlist blocks promotion.
