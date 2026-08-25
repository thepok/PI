# Delayed BBP transfer to actual numerator phases

Status: `machine-checked` (the exact T154--T155 arithmetic identities and
horizon-uniform phase-transfer bounds and the exact T159 top-band prime
projections, plus the exact T160 two-factor decimal resonance and its delayed
value/numerator-phase transfer bounds listed below); `proof sketch` (the explicit `nu_k <= 4*k`
burn-in, its use to discharge the logarithmic hypothesis, the
coefficient-summed corollary, the predecessor/residue CRT identity, the
finite-local polynomial-division obstruction, the general reciprocal-profile
adaptation, the scalar Hausdorff/TP2 diagnostic, and the critical
truncation-overlap law, including its all-finite-product and moving-horizon
generalizations)

Date: 2026-08-25 UTC

This note records the independently audited positive part of the ChatGPT Pro
AY memo. It narrows a moving-natural-window Fourier sum for the decimal
pi-orbit to phases of the actual reduced BBP truncations. Its exact arithmetic
and phase-transfer core is now machine-checked in
[`T154`](../../../../TheoryLib/PiQuantitativeBlockHitting/T154T154DelayedBBPFivePrimary.lean)
and
[`T155`](../../../../TheoryLib/PiQuantitativeBlockHitting/T155T155DelayedBBPPhaseTransfer.lean).
The exact top-band subset of the later reciprocal-prime adaptation is checked
in
[`T159`](../../../../TheoryLib/PiQuantitativeBlockHitting/T159T159ExactBBPTopPrimeProjection.lean).
The exact two-factor decimal-resonance transfer is checked in
[`T160`](../../../../TheoryLib/PiQuantitativeBlockHitting/T160T160DelayedBBPDecimalResonance.lean).
It is not the whole T139 consumer and proves no cancellation or V1
consequence. Later sections also retain the scoped proof-sketch conclusion of
the AY follow-up and the broader adaptation from the independently audited AZ
follow-up. Except for the explicitly identified T159 top-band subset, those
later statements are not promoted to the verified core.

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

## Reciprocal-prime profiles at the delayed phase

Status in this section: `machine-checked` only for the exact T159 top-band
subset stated next; `proof sketch` for the general quotient profiles,
middle bands, endpoint corrections, delayed CRT factorization, and all
cancellation discussion. This is the compact, independently audited part of
the ChatGPT Pro AZ follow-up. The general `p^2` localization,
height-protected survival, and simultaneous high-prime CRT skeleton are **not
new here**: they were already derived in
[`bbp_actual_odd_quotient_attack.md`](ultrapi-campaign/bbp_actual_odd_quotient_attack.md),
especially (27a)--(27b), and compressed further in
[`bbp_high_prime_phase_compression_20260813.md`](ultrapi-campaign/bbp_high_prime_phase_compression_20260813.md).
The new adaptation packages the clean sampled-depth localization into two
quotient profiles and connects it literally to the T154--T155 numerator
phase.

### Exact T159 top-band subset

Let `m,i,p in Nat`, assume that `p` is prime, `5<p`, and

```text
56*m+6 < 2*p.
```

For the first pole family additionally assume `p<=56*m+1` and `p=8*i+1`;
for the third pole family assume `p<=56*m+5` and `p=8*i+5`. In module
`Theory.PiDigits.T159ExactBBPTopPrimeProjection`, theorems
`bbpPartial_topPrimeProjection_one` and
`bbpPartial_topPrimeProjection_three` machine-check, respectively,

\[
 \operatorname{PrimeCongruent}_p
   \bigl(p\,\operatorname{bbpPartial}(7m),4\bigr).
\]

Here `PrimeCongruent p x y` means `x=y` or
`1<=padicValRat p (x-y)`. The scaled theorems
`scaledBBPRat_topPrimeProjection_one` and
`scaledBBPRat_topPrimeProjection_three` give the same exact residue for both
top pole families:

\[
 \boxed{\operatorname{PrimeCongruent}_p
   \bigl(p\,\operatorname{scaledBBPRat}(m),4\cdot10^m\bigr).}
\]

Finally, `scaledBBPRat_topPrime_val_eq_neg_one` and
`scaledBBPRat_topPrimeThree_val_eq_neg_one` prove, under the corresponding
hypotheses,

\[
 \boxed{\operatorname{padicValRat}_p
   (\operatorname{scaledBBPRat}(m))=-1.}
\]

The strict top band itself rules out a second multiple of `p`; T159 assumes
neither a general middle-band profile nor the clean-endpoint hypotheses used
below. It does not machine-check a delayed `U_m` CRT phase or any cancellation
estimate.

Keep the sampled notation above and write `X_m=56m`. For `L>=0`, define

\[
 C_+(L)=\sum_{\substack{r\ge0,\ s\in\{1,4,5,6\}\\8r+s\le L}}
 \frac{c_s}{16^r(8r+s)},
 \qquad (c_1,c_4,c_5,c_6)=(4,-2,-1,-1),
\]

and

\[
\begin{aligned}
 C_-(L)={}&-
 \sum_{\substack{r\ge0\\8r+2\le L}}\frac4{16^r(8r+2)}
 -\sum_{\substack{r\ge0\\8r+3\le L}}\frac2{16^r(8r+3)}\\
 &-\sum_{\substack{r\ge0\\8r+4\le L}}\frac2{16^r(8r+4)}
 +\sum_{\substack{r\ge0\\8r+7\le L}}\frac1{2\cdot16^r(8r+7)}.
\end{aligned}
\]

Fix `m in Nat` and a prime `p>5` satisfying

```text
p^2 > 56*m + 6,
p does not divide product_(t=1)^6 (56*m+t).
```

Put `L=floor(56*m/p)` and let `epsilon(p)=+` for `p=1 mod 4` and
`epsilon(p)=-` for `p=3 mod 4`. Reindexing the already recorded localization
gives the clean rational-value congruence

\[
 \boxed{p\,(10^mB_m)\equiv
 10^m C_{\varepsilon(p)}(L)\pmod p.}
\]

The congruence is in the `p`-local rationals after multiplication by `p`; it
is not a congruence of an arbitrarily chosen raw numerator. The first clean
hypothesis implies `L<p`, so all profile denominators are units modulo `p`.
If the second clean hypothesis is dropped, one explicit final pole term may
have to be added.
If `C_(epsilon(p))(L)` is nonzero modulo `p`, then `p` occurs to exponent one
in the reduced denominator `D_m`. Rational nonvanishing alone does not imply
this modular nonvanishing; the earlier height condition is still required
outside the already protected prime bands.

The Archimedean limits are

\[
 C_+(L)\longrightarrow\pi,
 \qquad C_-(L)\longrightarrow-\pi.
\]

The first is the ordinary BBP series. For the second, geometric summation
gives the proof-sketch identity

\[
 C_-(\infty)=\int_0^1
 \frac{-4x-2x^2-2x^3+\tfrac12x^6}{1-x^8/16}\,dx.
\]

Factoring numerator and denominator reduces the integrand to

\[
 -\frac{4x}{x^2-2x+2}+\frac2{x+\sqrt2}+\frac2{x-\sqrt2}.
\]

The antiderivative
`-2*log((x-1)^2+1)-4*arctan(x-1)+2*log|x^2-2|` has values `0` at `x=1`
and `pi` at `x=0`, proving `C_-(infinity)=-pi`. This real limit must not be
used as a modular phase approximation: reduction of a rational modulo `p`
uses its denominator inverse modulo `p`.

Now fix `k,n in Nat`, put `m=n+k`, and assume the exact T154 burn-in

```text
2 <= n+k,
Nat.log 5 (56*(n+k)+5) <= n.
```

Let `10^m B_m=P_m/D_m` be reduced and `U_m=P_m/5^k`. For every prime `p`
satisfying the clean hypotheses above and
`C_(epsilon(p))(floor(56*m/p)) != 0 mod p`, write `D_m=p*d_(m,p)`.
Then the new packaging specializes the exact T154 numerator phase to

\[
 \boxed{U_m(2^k d_{m,p})^{-1}\equiv
 10^n C_{\varepsilon(p)}(\lfloor56m/p\rfloor)\pmod p,}
\]

and, for every `h in Int`, CRT gives

\[
 e_{2^kD_m}(hU_m)=
 e_p\!\left(h10^nC_{\varepsilon(p)}(\lfloor56m/p\rfloor)\right)
 e_{2^kd_{m,p}}\!\left(hU_mp^{-1}\right).
\]

For a target left endpoint `A/10^k`, with arbitrary `A in Int`, the cleared
local numerator is `5^kU_m-A D_m`, so the `A D_m` term vanishes modulo every
such `p`. The same statement holds for the centre
`(A+1/2)/10^k` after clearing the factor two. Thus this particular local
prime component is target-independent. The valid conclusion is only that it
does not carry target dependence by itself: it may still contribute to a
target-signed estimate through its correlation with the complementary and
`q`-primary target characters and the target-dependent coefficient vector.
No independence or adversarial-correlation principle is available.

More generally, for `N>=1`, `|h|<=2*10^k-1`, and the displayed burn-in at
every `n+j` with `j<N`, T155 transfers the pi phase sum to these exact delayed
numerator phases with its horizon-independent error. The factorization above
may then be applied separately at every `m=n+j+k` and every prime satisfying
its stated local hypotheses. It does not supply a prime set stable in `j`, a
bound for the complementary characters, or cancellation of their product.

## Scalar forcing is a Hausdorff/TP2 diagnostic

Status in this section: `proof sketch`; no asymptotic determinant formula is
used. Put

\[
 F_m=10^{m+1}\sum_{r=1}^7 b_{7m+r},\qquad
 \rho=10/16^7,
\]

where `b_j` is the ordinary four-pole BBP summand. Since

\[
 \frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6}
 =\int_0^1x^{8j}(1-x)(x^2+2)(x^2+2x+2)\,dx,
\]

there is a positive measure `mu` on `[0,1]`, with support accumulating at
one, such that for every `m in Nat`

\[
 \boxed{F_m/\rho^m=\int_0^1t^m\,d\mu(t).}
\]

Consequently, for every `m,r in Nat`, the ordinary forward difference obeys

\[
 (-1)^r\Delta^r(F_m/\rho^m)>0.
\]

In particular `0<F_(m+1)<rho*F_m`, the sequence is strictly log-convex,
`F_mF_(m+2)>F_(m+1)^2`, and `F_(m+1)/F_m` increases to `rho`. If
`F_(m,r)=10^(m+1)b_(7m+r)`, then for every `m in Nat` and
`1<=r<s<=7`, the direct double-integral comparison gives the strict TP2 law

\[
 F_{m,r}F_{m+1,s}-F_{m+1,r}F_{m,s}>0.
\]

This is a negative diagnostic only for the scalar real forcing and its seven
positive slices: their `rho`-adapted differences are one-signed and their
relative weights are monotonically ordered. It does not rule out arbitrary
weighted or modular combinations, nonlinear characters, or the coupled
prime-skeleton/complement correlation above. In particular it proves no
signed primitive estimate, T139 premise, or V1 consequence.

## Critical truncation overlap and its consumer mismatch

Status in this section: `machine-checked` only for the three explicitly named
T160 two-factor statements below; the overlap identity, tail and critical
scale, log-uniform law, all-finite-product/moving-horizon generalization, and
gauge diagnostic remain `proof sketch`. This is the compact conclusion of the
independently audited ChatGPT Pro BB memo. It concerns the actual four-pole
BBP summand with the sevenfold truncation schedule `j<=7m`. Source:
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bb/answer.md`,
with the transfer audit in
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bb/turns/0002/answer.md`.

Put

\[
 Y_m=10^mB_m,\qquad
 \Delta_{m,r}=Y_{m+r}-10^rY_m.
\]

For every `m,r in Nat`, direct subtraction gives the exact overlap identity

\[
 \boxed{\Delta_{m,r}=10^{m+r}(B_{m+r}-B_m)
 =10^{m+r}\sum_{j=7m+1}^{7(m+r)}16^{-j}a_j,}
\]

where

\[
 a_j=\frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6}.
\]

Thus, for every `h in Int`,

\[
 e(hY_{m+r})e(-h10^rY_m)=e(h\Delta_{m,r}).
\]

Strict positivity holds for `r>=1`; for `r=0`, `Delta_(m,0)=0`. More
generally, for integer coefficients `c_nu` and nonnegative lags `r_nu`,

\[
 \sum_\nu c_\nu Y_{m+r_\nu}
 =\left(\sum_\nu c_\nu10^{r_\nu}\right)Y_m
  +\sum_\nu c_\nu\Delta_{m,r_\nu}.
\]

The tail bound makes the last term

\[
 O\!\left(\frac{\rho^m}{m}
   \sum_\nu |c_\nu|10^{r_\nu}\right),
 \qquad \rho=10/16^7.
\]

Accordingly, for every fixed `epsilon>0`, bounded-order stencils with
`max r_nu <= (Lambda-epsilon)m` and total coefficient `l1` mass
`sum |c_nu|=exp(o(m))` collapse to the single frequency
`sum c_nu*10^(r_nu)`, where

\[
 \Lambda=\log_{10}(16^7/10).
\]

Equivalently, the exact requirement is that the weighted `l1` mass
`sum |c_nu|*10^(r_nu)` be at most
`10^((Lambda-epsilon)m+o(m))`; allowing unbounded stencil order or larger
mass is not covered. This retires only those bounded/subcritical linear
stencils, not all possible overlap arguments.

The tail asymptotic

\[
 \boxed{m^2 16^{7m}(\pi-B_m)=\frac1{3136}+O(m^{-1})}
\]

was already recorded, in equivalent notation, in
[`bbp_rational_phase_density_separator_20260813.md`](ultrapi-campaign/bbp_rational_phase_density_separator_20260813.md),
equation (10). It is not new to this memo. Its new use is to identify the
critical overlap window. Fix `tau in Real`, and choose `m_0(tau)` so that
`Lambda*m+2*log_10(m)+tau>=1` for every `m>=m_0(tau)`. On that eventual
domain define

\[
 r_m(\tau)=\left\lfloor
 \Lambda m+2\log_{10}m+\tau\right\rfloor,
 \qquad
 \theta_m(\tau)=\left\{
 \Lambda m+2\log_{10}m+\tau\right\}.
\]

Then `r_m(tau)>=1` on this eventual domain, and

\[
 \boxed{\Delta_{m,r_m(\tau)}
 =\frac{10^{\tau-\theta_m(\tau)}}{3136}+O_\tau(m^{-1}),}
\]

uniformly when `tau` ranges over a fixed compact interval. The irrationality
of `Lambda` and partial summation show that
`theta_m(tau)` is uniformly distributed modulo one. Hence the empirical
distribution of the overlap defect is log-uniform on

\[
 \left[\frac{10^{\tau-1}}{3136},
       \frac{10^\tau}{3136}\right],
\]

and for every fixed `h in Int`,

(after assigning arbitrary nonnegative lags at the finitely many earlier
indices, which does not affect the limit),

\[
 \lim_{M\to\infty}\frac1{M-m_0(\tau)+1}
 \sum_{m=m_0(\tau)}^M e(h\Delta_{m,r_m(\tau)})
 =\frac1{\log 10}
   \int_{10^{\tau-1}/3136}^{10^\tau/3136}\frac{e(hx)}x\,dx.
\]

A fixed `O(1)` shift below the critical window means a fixed negative value
of `tau`; its limiting interval remains nondegenerate and the defect does
**not** vanish. Vanishing follows only when the lag lies an unbounded amount
below the critical window (or after a separate limit `tau -> -infinity`).

The follow-up audit also gives the following explicit one-sided form of the
already-known tail constant: for every integer `m>=1`,

\[
 \boxed{0<\frac1{3136}-m^2 16^{7m}(\pi-B_m)<\frac1{3430m}.}
\]

This sharpened error bound remains a `proof sketch`; it is not a new
asymptotic constant or a machine-checked result.

The fatal limitation is a consumer mismatch. At a nontrivial decimal scale
`q=10^k` with `k>=1`, the T154--T155 delayed phase is

\[
 e(hY_m/q)=e(h10^nB_{n+k}),\qquad m=n+k.
\]

T155's natural-window transfer assumes `|h|<=2q-1`; the live T139 primitive
consumer further has `0<|h|` and `10` not dividing `h`.

The overlap limit instead concerns `e(hY_m)`, which is the delayed phase at
frequency `qh`, already divisible by ten when `k>=1`. Its second overlap
frequency is `q*10^(r_m(tau))*h`: for `r_m(tau)>=1` it is divisible by ten and
has magnitude at least `10q`, far outside the primitive natural window.
T155's natural-window error bound therefore cannot transfer this mixed phase
to pi. Indeed, replacing each truncation value `Y_m` by the exact pi value
`10^m*pi` makes the analogue identically

\[
 e\!\left(h(10^{m+r}\pi-10^r10^m\pi)\right)=1.
\]

The log-uniform cancellation is therefore a truncation-overlap phenomenon,
not an actual-pi off-diagonal estimate. No extraction inequality bridging it
to the low primitive T155 phases is supplied, and the displayed frequency
mismatch prevents treating such a bridge as routine. This section proves no
T139 premise, cancellation for the required consumer, or V1 consequence; it
also does not retire overlap methods that use different coupled information.

The follow-up audit makes this incompatibility quantitative for every finite
decimal-resonant product. Write

\[
 V_{d,n}=10^nB_{n+d},\qquad
 \Phi_{d,n}(g)=e(gV_{d,n}),\qquad
 \rho=10/16^7.
\]

The exact two-factor core is now `machine-checked` in
`Theory.PiDigits.T160DelayedBBPDecimalResonance`. For every `h in Int` and
`n,r in Nat`, theorem `pi_decimal_resonant_phase_product` proves

\[
 \operatorname{phase}(h,10^{n+r}\pi)\,
 \operatorname{phase}(-10^rh,10^n\pi)=1.
\]

For `k0,k1,n,r in Nat`, if

\[
 |h|<2\,10^{k1},\qquad |-10^rh|<2\,10^{k0},
\]

theorem `norm_delayedBBP_resonant_product_sub_one_lt` proves

\[
 \left\|\Phi_{k1,n+r}(h)\Phi_{k0,n}(-10^rh)-1\right\|
 <4\pi\left(\rho^{n+r+k1}+\rho^{n+k0}\right).
\]

Under the additional burn-in hypotheses

\[
 2\le n+r+k1,\quad \log_5(56(n+r+k1)+5)\le n+r,
\]

\[
 2\le n+k0,\quad \log_5(56(n+k0)+5)\le n,
\]

theorem `norm_delayedBBPNumerator_resonant_product_sub_one_lt` gives the same
bound with both `Phi` factors replaced by the corresponding actual
`delayedBBPNumeratorPhase` values. These three declarations establish only a
preselected resonant pair inside both transfer windows; they provide no
cancellation or abundance of such pairs.

The following arbitrary finite-product strengthening remains `proof sketch`.

Fix `n>=0` and `s>=1`. For each `1<=nu<=s`, let
`r_nu,d_nu in Nat` and `g_nu in Int`, and assume

\[
 |g_\nu|<2\,10^{d_\nu},\qquad
 \sum_{\nu=1}^s g_\nu10^{r_\nu}=0.
\]

Then the pointwise T155 transfer bound and a telescoping product estimate give

\[
 \boxed{\left|\prod_{\nu=1}^s
 \Phi_{d_\nu,n+r_\nu}(g_\nu)-1\right|
 <4\pi\sum_{\nu=1}^s\rho^{n+r_\nu+d_\nu}
 \le 4\pi s\rho^n.}
\]

When every corresponding T154 burn-in hypothesis holds, these factors are
literally the actual delayed numerator/denominator phases. The same estimate
holds pointwise when all lags, delays, and frequencies move with `n` while
`s` stays fixed. Consequently, for every `M,H>=1`, their block average is
within `4*pi*s*rho^M` of `1`, uniformly in `H` and in those moving choices.
Thus every fully T155-admissible decimal-resonant product is exponentially
coherent, including at target-dependent later horizons.

For the two-factor critical defect at common delay `d`, put `m=n+d`. Its
nondegenerate scale is not the undelayed lag above but

\[
 r_{d,n}(\tau)=d+\left\lfloor
 \Lambda m+2\log_{10}m+\tau\right\rfloor.
\]

At this scale the earlier resonant frequency has magnitude
`|h|*10^(r_(d,n)(tau))`, which eventually violates
`|g|<2*10^d` for every fixed nonzero `h`. Conversely, if both resonant
frequencies satisfy their T155 windows, the magnified tail is exponentially
small and the defect phase tends to `1`. Hence a nondegenerate critical
truncation defect necessarily exits at least one verified transfer window;
increasing the BBP delay cannot rescue both criticality and transferability.

There is also an exact information-loss obstruction. For any real `beta`,
fixed nonzero integer `h`, delayed errors `epsilon_(d,n)`, and arbitrary
moving lags `r_n`, set

\[
 a_n^{(\beta)}=e\!\left(h(10^n\beta-\epsilon_{d,n})\right).
\]

Then

\[
 a_{n+r_n}^{(\beta)}
 \left(\overline{a_n^{(\beta)}}\right)^{10^{r_n}}
 =e\!\left(h(10^{r_n}\epsilon_{d,n}-\epsilon_{d,n+r_n})\right),
\]

independently of `beta`. The critical-defect data is therefore blind to the
lacunary carrier gauge `a_n -> a_n*e(h*10^n*gamma)`. This is not a separator
preserving the actual BBP numerator/denominator coupling; it proves only that
defect data alone cannot recover the carrier needed by an extraction theorem.
The genuine same-frequency correlation still contains the uncontrolled
factor `e(h*(10^r-1)*V_(d,n))`, so exact cross-index carrier arithmetic remains
the hard input.

For completeness, the critical log-uniform law gives, for fixed nonzero `h`,
a mean-square distance from the exact-pi resonant product `1` equal in the
limit to `2-2*Re(I_h(A_tau))`; as `tau -> +infinity` this tends to the
decorrelated value `2`, not the pointwise maximum squared distance `4`.
This reinforces non-transfer rather than proving cancellation for T139 or V1.

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
  `norm_sum_phase_pi_sub_delayedBBPNumeratorPhase_lt`;
- T159: `bbpPartial_topPrimeProjection_one`,
  `bbpPartial_topPrimeProjection_three`,
  `scaledBBPRat_topPrimeProjection_one`,
  `scaledBBPRat_topPrimeProjection_three`,
  `scaledBBPRat_topPrime_val_eq_neg_one`, and
  `scaledBBPRat_topPrimeThree_val_eq_neg_one`;
- T160: `pi_decimal_resonant_phase_product`,
  `norm_delayedBBP_resonant_product_sub_one_lt`, and
  `norm_delayedBBPNumerator_resonant_product_sub_one_lt`.

The explicit `nu_k<=4*k` derivation, predecessor/residue CRT identity,
finite-local polynomial reduction, general reciprocal-profile adaptation, and
Hausdorff/TP2 diagnostic, critical truncation-overlap law, and arbitrary
finite-product/moving-horizon extensions are not among these declarations and
remain `proof sketch`. No theorem listed here proves cancellation, a T139
premise, density, normality, or V1.
