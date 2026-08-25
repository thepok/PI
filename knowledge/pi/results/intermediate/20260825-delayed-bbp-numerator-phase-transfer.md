# Delayed BBP transfer to actual numerator phases

Status: `machine-checked` (the exact T154--T155 arithmetic identities and
horizon-uniform phase-transfer bounds listed below); `proof sketch` (the
explicit `nu_k <= 4*k` burn-in, its use to discharge the logarithmic
hypothesis, the coefficient-summed corollary, and the predecessor/residue CRT
identity, and the finite-local polynomial-division obstruction)

Date: 2026-08-25 UTC

This note records the independently audited positive part of the ChatGPT Pro
AY memo. It narrows a moving-natural-window Fourier sum for the decimal
pi-orbit to phases of the actual reduced BBP truncations. Its exact arithmetic
and phase-transfer core is now machine-checked in
[`T154`](../../../../TheoryLib/PiQuantitativeBlockHitting/T154T154DelayedBBPFivePrimary.lean)
and
[`T155`](../../../../TheoryLib/PiQuantitativeBlockHitting/T155T155DelayedBBPPhaseTransfer.lean).
It is not the whole T139 consumer and proves no cancellation or V1
consequence.

## Setup and logarithmic burn-in

Let

\[
B_m=\sum_{j=0}^{7m}\frac1{16^j}
\left(\frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6}\right),
\qquad
10^mB_m=\frac{P_m}{D_m}
\]

in lowest terms with `D_m > 0`, and put

\[
\rho=\frac{10}{16^7}=\frac5{2^{27}}.
\]

The machine-checked T106 tail bound and the strongest T141 valuation statement
give

\[
0<10^m(\pi-B_m)<\rho^m,
\qquad
5\nmid D_m,
\qquad
5^{m-\operatorname{Nat.log}_5(56m+5)}\mid P_m
\quad(m\ge2).
\]

For a decimal scale `q = 10^k`, define the exact integer burn-in

\[
\nu_k=\min\{n\in\mathbb N:5^n\ge224k\}.
\]

The following explicit simplification remains a `proof sketch`: `nu_k <= 4k`,
and for every `n >= nu_k`, with `m=n+k`,

\[
\operatorname{Nat.log}_5(56m+5)\le n,
\qquad 5^k\mid P_m.
\]

The informal derivation observes that, at `n=nu_k`,

\[
56(n+k)+5\le285k<1120k\le5^{n+1},
\]

and this strict inequality persists as `n` increases. T141 then gives the
claimed divisibility. T154 does not formalize this `nu_k` estimate; it assumes
the exact theorem-friendly logarithmic inequality. Thus, at `proof sketch`
level, the linear burn-in obtained from the simpler `5^ceil(m/2) | P_m`
corollary improves to `O(log k)`.

## Exact actual-numerator phase

Under the exact hypotheses

```text
2 <= n+k
Nat.log 5 (56*(n+k)+5) <= n,
```

T154 machine-checks `delayed_scaledBBPRat_five_arithmetic`, including
`5^k | P_(n+k)`, and
`scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator`. Set

\[
U_{n+k}=\frac{P_{n+k}}{5^k}\in\mathbb Z.
\]

T154's `delayed_bbpPartial_eq_num_div_two_pow_den` and T155's
`delayedBBPValue_eq_num_div_two_pow_den` and
`phase_delayedBBPValue_eq_delayedBBPNumeratorPhase` then machine-check the
exact identities

\[
\boxed{
10^nB_{n+k}=\frac{U_{n+k}}{2^kD_{n+k}},
\qquad
e(h10^nB_{n+k})
=e_{2^kD_{n+k}}(hU_{n+k}).}
\]

Here T154 machine-checks that `5` does not divide `D_(n+k)`, so the displayed
`2^k D_(n+k)` is a valid five-free denominator for the phase. It need not be
the reduced or minimal phase modulus: powers of two may still cancel against
`h U_(n+k)`. The additional reduced-coprimality observation is not promoted
beyond `proof sketch` here.

This identity uses the actual numerator and denominator of the sevenfold BBP
truncation, not merely a finite five-adic residue fiber. T141 removes the
five-primary factor from this presentation; it does not control the remaining
Archimedean phase.

## Horizon-uniform delayed natural-window transfer

Let `x_r = fract(10^r * pi)`. T155 first machine-checks the exact rescaling
`abs_piPoint_sub_delayedBBPValue` and the natural-window pointwise estimate
`norm_phase_pi_sub_delayedBBPValue_lt`. Its theorem
`norm_sum_phase_pi_sub_delayedBBPValue_lt` proves, for `N>=1` and every
integer `h` in the natural window

\[
|h|\le2\cdot10^k-1,
\]

the horizon-uniform comparison with the delayed real BBP values. Under the
pointwise exact burn-in hypotheses

```text
forall j < N,
  2 <= (n+j)+k /\ Nat.log 5 (56*((n+j)+k)+5) <= n+j,
```

`norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt` machine-checks the literal
actual-numerator-phase form

\[
\boxed{
\left|
\sum_{j=0}^{N-1}e(hx_{n+j})
-\sum_{j=0}^{N-1}
 e_{2^kD_{n+k+j}}(hU_{n+k+j})
\right|
<\frac{4\pi\rho^{n+k}}{1-\rho}.}
\]

The formal proof uses the pointwise T106 estimate

\[
|e(h10^{n+j}\pi)-e(h10^{n+j}B_{n+k+j})|
\le 2\pi\frac{|h|}{10^k}\rho^{n+k+j}
<4\pi\rho^{n+k+j};
\]

and sums the geometric tail. Its independence from `h` holds
only after imposing the displayed natural window; outside that window the
unsimplified estimate retains the factor `|h|/10^k`. Its independence from
the horizon `N` is genuine.

Specializing the exact logarithmic hypotheses from merely `n>=nu_k` still
uses the unformalized burn-in argument above and therefore remains a `proof
sketch`.

At `proof sketch` level, the triangle inequality consequently gives, for
arbitrary complex coefficients supported on
`0 < |h| <= 2q-1`,

\[
\left|
\sum_hc_h\sum_{j<N}e(hx_{n+j})
-\sum_hc_h\sum_{j<N}e_{2^kD_{n+k+j}}(hU_{n+k+j})
\right|
<\frac{4\pi\rho^{n+k}}{1-\rho}\sum_h|c_h|.
\]

This transfers a delayed signed natural-window sum, including a
target-centred coefficient vector, but does not by itself discharge the
initial segment, endpoint decomposition, or quantifiers of the complete T139
hit consumer.

## Exact predecessor/residue coupling

Status in this section: `proof sketch`; T154--T155 do not formalize this CRT
identity.

Write

\[
\frac{P_m}{D_m}=J_m+\frac{r_m}{D_m},
\qquad 0\le r_m<D_m.
\]

Since `5^k | P_m` and `5` does not divide `D_m`,

\[
J_m\equiv-r_mD_m^{-1}\pmod{5^k}.
\]

For `0 <= s < 2^k`, `0 <= t < 5^k`, and the natural-window lift
`h=5^k s+2^k t`, the matched predecessor/residue/successor characters collapse
exactly to the same actual numerator phase:

\[
e_{2^k}(s(J_m-w_2))
e_{5^k}(t(-r_mD_m^{-1}-w_5))
e_{10^k}\!\left(h\frac{r_m}{D_m}\right)
=e_{10^k}(-hw)e_{2^kD_m}(hU_m),
\]

where `w_2=w mod 2^k` and `w_5=w mod 5^k`. This is an arithmetic realization
of an ordinary natural-window frequency, not a new frequency algebra and not
a bypass of T139's primitive-ray reduction.

## Finite-local forcing reduction

Status in this section: `proof sketch`; this is the compact conclusion of the
independently audited AY follow-up and is not Lean-checked. It adds an exact
identity for the actual BBP sequence, but no positive cancellation estimate.

Put `R_m=10^m B_m=P_m/D_m`, let `E` be the forward shift, and write the exact
forcing and tail coboundary as

\[
F_m=R_{m+1}-10R_m=10\tau_m-\tau_{m+1}.
\]

For every `C(X)=sum_(r=0)^R c_r X^r` in `Z[X]`, set

\[
H=C(10),\qquad Q_C(X)=\frac{C(X)-C(10)}{X-10}\in\mathbb Z[X].
\]

Polynomial division by `X-10` gives the exact identities

\[
\boxed{C(E)R=C(10)R+Q_C(E)F},
\qquad
\boxed{Q_C(E)F=C(10)\tau-C(E)\tau}.
\]

Thus, for `q=10^k`, `m=n+k`, and `z_(n,k)=R_(n+k)/q`, the corresponding
finite product of delayed characters is simultaneously

\[
\prod_{r=0}^R e(c_r z_{n+r,k})
=e\!\left(\frac{H R_m+(Q_C(E)F)_m}{q}\right)
=e(H10^n\pi)
 e\!\left(-\frac{\sum_{r=0}^R c_r\tau_{m+r}}q\right).
\]

Because the tail is geometrically summable, this yields a finite-local
dichotomy. If `C(10)=0`, the products are a summable perturbation of `1`, so
their Cesaro averages tend to `1`, not `0`. If `C(10) != 0`, they remain a
summable perturbation of a nonzero fixed-pi character. At a T139
primitive-ray leaf whose earliest coefficient `c_0` is not divisible by ten,

\[
C(10)\equiv c_0\pmod {10};
\]

hence that surviving frequency is already decimal-primitive. For a general
nonzero `C(10)` divisible by ten, one must first perform the usual decimal-ray
reduction, including its finite endpoint terms; nonzero alone does not imply
primitive.

Consequently, the Archimedean forcing recurrence by itself cannot turn finite
character telescoping or finite-order van der Corput into the missing
cancellation: it gives either zero-frequency coherence or another nonzero
fixed-pi phase. Repeated differences of a single primitive character have
frequency `h * product_i (10^(r_i)-1)` and therefore stay primitive (with
`9^d` growth after `d` differences); this growth assertion is not being made
for arbitrary cross terms of a polynomial expansion.

This is incremental negative progress, not a closure of all finite BBP
arguments. It does not exclude finite arguments that also use exact nonlocal
relations among the actual numerators and denominators, cross-index
congruences, or the seven-term rational formula before it is collapsed to the
Archimedean recurrence. No primitive/off-diagonal estimate, T139 premise, or
V1 consequence is obtained.

## Narrowed live arithmetic target

After the transfer, the hard delayed rational sum is

\[
\boxed{
\sum_{0<|h|\le2q-1}c_{q,w}(h)
\sum_{j=0}^{N-1}
e_{2^kD_{n+k+j}}(hU_{n+k+j}).}
\]

The transfer error is exponentially small and uniform in `N`; no bound of the
required sign or size is known for this actual `(U_m,D_m)` sum. Progress now
requires joint/off-diagonal information about the varying reduced BBP
numerators, denominators, and seven-term forcing. No fixed-pi cancellation,
T139 premise, density, normality, or V1 follows from this note.

## Verification boundary

The strict verifier and exact axiom audit accept the following declarations:

- T154: `delayed_scaledBBPRat_five_arithmetic`,
  `scaledBBPRat_num_eq_five_pow_mul_delayedBBPNumerator`, and
  `delayed_bbpPartial_eq_num_div_two_pow_den`;
- T155: `delayedBBPValue_eq_num_div_two_pow_den`,
  `phase_delayedBBPValue_eq_delayedBBPNumeratorPhase`,
  `abs_piPoint_sub_delayedBBPValue`,
  `norm_phase_pi_sub_delayedBBPValue_lt`,
  `norm_sum_phase_pi_sub_delayedBBPValue_lt`, and
  `norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt`.

The explicit `nu_k<=4*k` derivation and the predecessor/residue CRT identity
are not among these declarations and remain `proof sketch`. No theorem listed
here proves cancellation, a T139 premise, density, normality, or V1.
