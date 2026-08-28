# Delayed BBP tails form a strict Hausdorff moment sequence

Date: 2026-08-28 UTC

Claim label: `proof sketch` (independently audited).  This is new
π-specific one-sided Archimedean structure, but it is **not** yet signed
relative to a target `A`, child `d`, or the T179/T189 carrier.

## Corrected repository-indexed statement

Let `bbpRealPartial M` be the repository's inclusive canonical BBP partial
sum through index `M`.  Fix `K>=0` and define

```text
delta_n^(K) = 10^n * (pi-bbpRealPartial(n+K)).
```

Using the T102--T104 positive BBP integral, with

```text
a = sqrt(2)/2,
P(x) = bbpKernelNumerator(x)
     = 8*(a-x)*(x^2+1)*(x^2+sqrt(2)*x+1),
```

one obtains exactly

```text
delta_n^(K)
  = integral_[0,a] (10*x^8)^n
      * x^(8*(K+1))*P(x)/(1-x^8) dx
  = integral_[0,5/8] t^n dmu_K(t).
```

Here `mu_K` is the pushforward under `t=10*x^8`; it is a finite positive
measure with positive density on the interior of `(0,5/8)`.  The exponent
`K+1` is essential because `bbpRealPartial` is inclusive.

Consequently, for all `n,r>=0`,

```text
0 < delta_(n+1) < (5/8)*delta_n,
(-1)^r * Delta^r delta_n
  = integral t^n*(1-t)^r dmu_K(t) > 0.
```

For every pair of strictly increasing nonnegative index tuples
`i_1<...<i_m` and `j_1<...<j_m`, Andréief's identity and generalized
Vandermonde positivity give the strict total-positivity law

```text
det [delta_(i_r+j_s)]_(r,s=1..m) > 0.
```

In particular the sequence is strictly log-convex and the ratios
`delta_(n+1)/delta_n` strictly increase while remaining below `5/8`.

This law is all-depth and genuinely uses the distinguished positive BBP
integral for π.  If a real `alpha` made
`10^n*(alpha-bbpRealPartial(n+K))` a positive moment sequence supported in
`[0,5/8]` for every `n`, then its geometric decay would force `alpha=pi`.
That uniqueness observation is useful as a replacement check, though it is
already implied by convergence to the same BBP limit.

For simultaneous phases,

```text
exp(2*pi*i*h*10^n*pi) /
exp(2*pi*i*h*10^n*bbpRealPartial(n+K))
  = exp(2*pi*i*h*delta_n).
```

If `H*delta_0<1/2`, principal arguments recover the same positive moment
sequence for every `1<=h<=H`.  This retains coherent frequency-proportional
phase displacement, but does not determine the sign of a target-rotated
linear combination.

## Exact ten-child product identity

For the real T185 boundary kernel

```text
kappa_q(t) = (cos(2*pi*t)-cos(pi/q))
             * sin^4(pi*q*t)/(q^2*sin^4(pi*t)),
```

with continuous extension at integers, direct sine multiplication and the
Chebyshev product give, for `Q=10q`,

```text
product_(d=0)^9 kappa_Q(v-d/10)
  = -2^27/(10^20*q^18)
      * sin^36(10*pi*q*v) * kappa_q(10*v).
```

Away from zeros, a positive parent suffix gives exactly one positive child
kernel—the literal predecessor digit—and a nonpositive suffix gives none.
This pointwise chamber identity is universal in the orbit constant.  Its sign
is not preserved by summation over orbit times, so it is a structural
separator rather than fixed-π progress.

## Exact remaining boundary

The moment law orders the scalar BBP displacement, not the complete literal
T179/T189 readout.  A proposed nonlinear Taylor transfer remains conditional
on a target-dependent dual polynomial having one sign on `[0,5/8]`; no such
sign, Hessian margin, or legal-node instance has been proved.  The soft-min
readout also introduces transcendental exponential coefficients, so an
ordinary algebraic Sturm certificate is unavailable without redesign.

Reopen this route only with a proved target- and child-dependent dual-cone
inequality for the complete literal block, with enough magnitude to dominate
the carrier gap.  More moment-cone packaging alone does not advance T189.
