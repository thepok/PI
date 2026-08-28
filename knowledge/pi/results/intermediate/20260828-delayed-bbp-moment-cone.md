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

## Bounded literature comparison

Search date: 2026-08-28 UTC.  A targeted search of the local PaperSearch
database compared the exact moment law with the closest positive-measure
machinery.  Liu--Pego's [Hausdorff generating-function
characterization](https://arxiv.org/abs/1401.8052) supplies complete
monotonicity; standard total-positivity and variation-diminishing results as
used by Wulfsohn ([arXiv:math/0403185](https://arxiv.org/abs/math/0403185))
and Nowak ([arXiv:1108.3586](https://arxiv.org/abs/1108.3586)) control the
number of sign changes; Bhaskar--Song's generalized Descartes rule
([arXiv:1309.5056](https://arxiv.org/abs/1309.5056)) controls zeros after a
Laplace reparametrization; and Van Assche's Padé remainder formula
([arXiv:math/0609094](https://arxiv.org/abs/math/0609094)) gives a one-sided
error for real spectral points outside the measure support.

All four mechanisms stop at the same exact line.  For a fixed target and
child, first variation has the form

```text
sum_n c_n(q,A,d)*delta_n^(K)
  = integral_[0,5/8] P_(q,A,d)(t) dmu_K(t).
```

The target rotations make the coefficients `c_n(q,A,d)` oscillatory.
Positivity of `mu_K` signs the integral only after an independent proof that
the target-dependent polynomial `P_(q,A,d)` has the required sign.  Total
positivity can propagate or limit sign changes but cannot choose that initial
sign; the real-outside-support Padé order does not apply to the complex
unit-circle phases.  Lagarias' BBP orbit comparison
([arXiv:math/0101055](https://arxiv.org/abs/math/0101055)) likewise does not
provide uniform predecessor-digit stability.  Thus the searched literature
validates the scalar cone but supplies no target-signed T179/T189 theorem.

A legitimate fixed-node use would have to certify digit stability, prove a
one-signed Bernstein expansion for `P_(q,A,d)(5*t/8)`, and show that its
moment lower bound dominates both the rational-carrier deficit and the
quadratic Taylor remainder.  No searched source proves this Bernstein sign;
without a uniform source it would remain a finite certificate rather than
horizon transport.  This paragraph is `literature-checked` only for the
bounded dated comparison, not a claim of exhaustive absence.

## Audited finite and off-orbit boundaries

The infinite moment law does not distinguish π at any finite truncation.
For every fixed `J`, sufficiently small `epsilon` makes

```text
delta_n^(K)+10^n*epsilon,  0<=n<=J,
```

the first `J+1` moments of another measure with positive interior density on
`[0,5/8]`.  One may choose `J+1` narrow interior bumps whose moment matrix is
a perturbation of a nonsingular Vandermonde matrix and solve for the desired
finite perturbation.  Strict complete-monotonicity and ordered Hankel-minor
tests therefore remain true on a nontrivial interval of replacement
constants.

More decisively, for the class of measures with positive interior density and
every real polynomial `P`,

```text
inf_mu integral P dmu / mu([0,5/8]) = min_[0,5/8] P,
sup_mu integral P dmu / mu([0,5/8]) = max_[0,5/8] P.
```

Concentrated smooth bumps plus an arbitrarily small positive background prove
both equalities.  Hence strict total positivity can orient a universal dual
functional only after the target-dependent polynomial sign has already been
supplied.  This is a `proof sketch`, not an absence theorem for the one exact
BBP density.

There is also an exact orbit incompatibility.  With

```text
x_n(s)=10^n*bbpRealPartial(n+K)+s*delta_n^(K),
```

direct calculation gives

```text
x_(n+1)(s)-10*x_n(s)
  =(1-s)*10^(n+1)*bbpRealTerm(n+K+1) != 0   for s<1.
```

The defect lies strictly between zero and one.  Thus the interpolation is not
a decimal orbit except at `s=1`; T179's literal predecessor/suffix identity
and T139's primitive-shift compression cannot be used along its interior.
Only the defining full primitive Fourier polynomial has a legitimate smooth
off-orbit extension.  In that extension the fresh dual polynomial necessarily
factors as `P_D(t)=t^q*R_D(t)`, so a strict negative margin on the closed
support is impossible at `t=0`; any valid bound must be weighted by `t^q`.

The same calculation does give a strong sign-preservation statement.  Put
`Q=10q`.  The machine-checked T142 coefficient load implies the coordinate
derivative bound `<10*pi*m^2`.  Since the positive BBP summands satisfy
`bbpRealTerm(m)<16^(-m)` for `m>=1`, the direct full-primitive scores obey

```text
|D_d(pi)-D_d(carrier)|
  < (16*pi/9)*Q^2*16^(-K)*(5/8)^q,

|F_d(pi)-F_d(carrier)|
  < (16*pi/9)*(Q^2+q^2)*16^(-K).
```

Here `carrier` is a moving rational coordinate array, not a rational decimal
orbit, and `D_d,F_d` denote their defining Fourier extensions.  Positive
carrier margins exceeding these buffers imply actual-π same-child FMR.  The
fresh buffer is exponentially tiny: this preserves a sign already present at
the carrier but cannot create the literal fresh positivity or overcome the
`-21/10` correction at natural scale.  It is analogous to T169 and is not a
new target-signed source.
