# Accelerated Euler--Machin target-score carrier

Status: `proof sketch`

Date: 2026-08-25 UTC

Source: independently audited ChatGPT Pro memo
[`workflows/state/chatgpt-pro/20260825-open-frontier-creative-be/turns/0003/answer.md`](../../../../workflows/state/chatgpt-pro/20260825-open-frontier-creative-be/turns/0003/answer.md),
Sections 4--6, with the denominator statements below retained only as upper
bounds and with the audit corrections stated explicitly.

This note records an unconditional rational approximation to `pi` whose
moving-frequency phase error is summable over every late horizon.  It gives a
shifted full-T128 target-score replacement by a rational carrier dominated by
powers of `13`.  It proves no signed estimate for that carrier, no literal
T139 premise, no cylinder hit, and no V1 consequence.

## Verified dependencies and claim boundary

The proof sketch uses the machine-checked Machin identity and rational
infrastructure in
[`T36`](../../../../TheoryLib/PiQuantitativeBlockHitting/T36T36MachinGridStability.lean),
the boundary kernel from
[`T128`](../../../../TheoryLib/PiQuantitativeBlockHitting/T128T128BoundaryMatchedKernel.lean),
the actual positive-frequency coefficients from
[`T138`](../../../../TheoryLib/PiQuantitativeBlockHitting/T138T138PrimitiveRayCoefficientGap.lean),
and the exact primitive-prefix reconstruction in
[`T139`](../../../../TheoryLib/PiQuantitativeBlockHitting/T139T139PrimitiveRayBoundaryConsumer.lean).
For comparison with the literal delayed BBP phase it uses the exact arithmetic
of [`T154`](../../../../TheoryLib/PiQuantitativeBlockHitting/T154T154DelayedBBPFivePrimary.lean)
and the quadratic horizon transfer in
[`T164`](../../../../TheoryLib/PiQuantitativeBlockHitting/T164T164QuadraticBBPTailTransfer.lean).

None of the Euler expansion, corrected tail, accelerated carrier, or
denominator bounds in this note is Lean-checked.

## Exact Euler expansion and corrected tail

For an integer `q >= 2`, put

\[
 y_q=\frac1{q^2+1},\qquad
 c_j=\int_0^1(1-u^2)^j\,du
     =\frac{4^j(j!)^2}{(2j+1)!}.
\]

Then

\[
 \frac{c_{j+1}}{c_j}=\frac{2j+2}{2j+3}
\]

and geometric expansion of

\[
 1+\frac{u^2}{q^2}
 =\left(1+\frac1{q^2}\right)
  \left(1-y_q(1-u^2)\right)
\]

gives the exact positive series

\[
 \boxed{
 \arctan\frac1q
 =\frac{q}{q^2+1}\sum_{j=0}^{\infty}c_jy_q^j.}
\]

For `N >= 1`, define

\[
 \mathcal A_q(N)=
 \frac{q}{q^2+1}\sum_{j=0}^{N-1}\frac{c_j}{(q^2+1)^j}
 +\frac{c_N}{q(q^2+1)^N}
 -\frac{c_N}{q^3(2N+3)(q^2+1)^N}.
\]

The audited corrected-tail estimate is

\[
 \boxed{
 0\le \arctan\frac1q-\mathcal A_q(N)
 \le
 \frac{3(q^2+2)c_N}
 {2q^5(2N+3)^2(q^2+1)^N}.}
\tag{1}
\]

Indeed, with `D=2N+3` and

\[
 P_r=\frac{c_{N+r}}{c_N}
 =\prod_{j=0}^{r-1}\left(1-\frac1{D+2j}\right),
\]

the elementary product bounds give

\[
 0\le P_r-\left(1-\frac rD\right)
 \le\frac{3r^2}{2D^2}.
\]

Replacing `P_r` by `1-r/D` produces exactly the two displayed correction
terms.  Summing the residual with
`sum r^2 y^r = y(1+y)/(1-y)^3` yields (1), since

\[
 \frac{q}{q^2+1}\frac{y_q(1+y_q)}{(1-y_q)^3}
 =\frac{q^2+2}{q^5}.
\]

Also, for `N >= 1`,

\[
 c_N\le\int_0^\infty e^{-Nu^2}\,du
 =\frac{\sqrt\pi}{2\sqrt N}.
\tag{2}
\]

## Critical accelerated Machin carrier

Put

\[
 \beta_q=\log_{q^2+1}10,qquad
 N_q(m)=\lceil\beta_qm\rceil
\]

and, for `m >= 1`,

\[
 \boxed{
 \mathcal M_m=
 16\mathcal A_5(N_5(m))-4\mathcal A_{239}(N_{239}(m)).}
\tag{3}
\]

The machine-checked Machin identity

\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
\]

together with (1)--(2) gives

\[
 \boxed{
 10^m|\pi-\mathcal M_m|
 \le K_{\mathrm M}m^{-5/2},}
\tag{4}
\]

where

\[
 \boxed{
 K_{\mathrm M}=
 \frac{3(5^2+2)\sqrt\pi}{5^5\beta_5^{5/2}}
 +\frac{3(239^2+2)\sqrt\pi}
 {4\cdot239^5\beta_{239}^{5/2}}
 =0.1094207423\ldots .}
\tag{5}
\]

Here
`beta_5 = 0.7067270923...` and
`beta_239 = 0.2102252111...`.

## Moving-frequency and shifted target-score transfer

Let `Q=10^k`, `t=n+k >= 2`, and let `h` be an integer with
`0 < |h| < 2Q`.  For every `N >= 1`, phase Lipschitz continuity and (4) give

\[
 \boxed{
 \left|
 \sum_{r=0}^{N-1}e(h10^{n+r}\pi)
 -\sum_{r=0}^{N-1}e(h10^{n+r}\mathcal M_{t+r})
 \right|
 <\frac{8\pi K_{\mathrm M}}{3(t-1)^{3/2}}.}
\tag{6}
\]

The same inequality is trivially true when `N=0`; this case must be split off
because the named T164 horizon theorem used below assumes `N >= 1`.

For a target `A`, let

\[
 c_{Q,A}=\frac{2A+1}{2Q}
\]

and define the shifted full positive-frequency score

\[
 \mathscr P_{Q,A}(z;n,N)=
 \sum_{h=1}^{2Q-1}a_Q(h)e(-hc_{Q,A})
 \sum_{r=0}^{N-1}e(hz_{n+r}),
\]

where `a_Q(h)` is T138's `positiveBoundaryCoefficient`.  Aggregation cannot
increase the raw coefficient mass, so

\[
 L_Q:=\sum_{h=1}^{2Q-1}|a_Q(h)|
 \le Q^2(1-\cos(\pi/Q))+2
 \le \frac{\pi^2}{2}+2=:L_*.
\tag{7}
\]

Applying (6) frequency by frequency gives the complete target-signed bound

\[
 \boxed{
 |\mathscr P^\pi_{Q,A}(n,N)-
   \mathscr P^{\mathrm M}_{Q,A}(n,N)|
 <\frac{8\pi K_{\mathrm M}L_*}{3(t-1)^{3/2}}
 <\frac{6.36}{(t-1)^{3/2}}.}
\tag{8}
\]

This is uniform in `Q`, `A`, `N`, and the complete positive T128 frequency
support.

The score in (8) is a **shifted full-T128 score**, not literally the named
unshifted primitive-prefix quantity in T139.  The generic finite directional
identity can be instantiated on the shifted sequence
`r -> fract(10^(n+r)*pi)`, but a claim that (8) itself is a registered T139
premise would be incorrect.  Any cylinder-hit use must make that shifted
consumer or the corresponding prefix/endpoint bookkeeping explicit.

## Comparison with the actual delayed BBP score

Let `rho=10/16^7` and

\[
 \Lambda_t=(56t+9)(56t+10).
\]

For `N >= 1`, T164 machine-checks at each nonzero natural-window frequency

\[
 \left|
 \sum_{r<N}e(h10^{n+r}\pi)
 -\sum_{r<N}e(h10^{n+r}B_{7(t+r)})
 \right|
 <\frac{4\pi\rho^t}{\Lambda_t(1-\rho)}.
\tag{9}
\]

Under T154's pointwise burn-in, the second sum is literally the delayed
actual-numerator phase sum.  Combining (8)--(9) gives

\[
 \boxed{
 \begin{aligned}
 |\mathscr P^{\mathrm{BBP}}_{Q,A}(n,N)
  -\mathscr P^{\mathrm M}_{Q,A}(n,N)|
 <L_*\left(
 \frac{4\pi\rho^t}{\Lambda_t(1-\rho)}
 +\frac{8\pi K_{\mathrm M}}{3(t-1)^{3/2}}
 \right).
 \end{aligned}}
\tag{10}
\]

Burn-in is needed for the literal numerator-phase identification, not for the
real BBP-value comparison.  T165's reduced-modulus theorem applies only at
positive even sampled depths; a consecutive block contains both parities.
Thus (10) replaces the complete actual BBP score within an explicit additive
error, but it is not an equality of CRT coordinates.

## Denominator-support upper bounds

The identities

\[
 5^2+1=26=2\cdot13,
 \qquad
 239^2+1=57122=2\cdot13^4
\]

make `13` the only fixed prime whose exponent can grow linearly in this
presentation.  The following are **upper bounds only**; they do not assert an
exact reduced denominator, survival of any listed prime, or absence of
cancellation between the two Machin components.

Let `D^M_{k,m}` be the reduced denominator of
`10^(m-k) * M_m`, for `m >= k`, and put

\[
 \sigma=2\beta_5=1.413454184\ldots .
\]

Every prime divisor `p` of `D^M_{k,m}` outside
`{2,5,13,239}` satisfies

\[
 \boxed{p\le2N_5(m)+3\le\sigma m+5.}
\tag{11}
\]

For an odd prime, Legendre's formula gives

\[
 v_p(\operatorname{den}c_j)
 =\sum_{\ell\ge1}
 \left(
 \left\lfloor\frac{2j+1}{p^\ell}\right\rfloor
 -2\left\lfloor\frac j{p^\ell}\right\rfloor
 \right)
 \le\left\lfloor\log_p(2j+1)\right\rfloor.
\]

Consequently, safe presentation bounds are

\[
 v_p(D^M_{k,m})
 \le3\mathbf1_{\{5,239\}}(p)
 +2\left\lfloor\log_p(\sigma m+5)\right\rfloor
 \qquad(p\ne2,13),
\tag{12}
\]

and

\[
 v_{13}(D^M_{k,m})
 \le\max\{N_5(m),4N_{239}(m)\}
 +2\left\lfloor\log_{13}(\sigma m+5)\right\rfloor.
\tag{13}
\]

The dyadic upper bound in the source memo omitted the cancellation supplied
by the outer Machin coefficients `16` and `4`.  Including them sharpens it to

\[
 \boxed{
 v_2(D^M_{k,m})\le
 \max\left\{
 0,
 N_5(m)-4-(m-k),
 N_{239}(m)-2-(m-k)
 \right\}.}
\tag{14}
\]

This follows because the two unscaled Euler carriers need at most
`2^(N_5(m))` and `2^(N_239(m))` in their displayed denominators, while the
Machin coefficients remove four and two powers of two respectively and the
decimal scaling removes another `m-k`.  Reduction or cross-component
cancellation can only lower the exponent.

No multiplicative-order assertion is needed for this note.  In particular,
any use of `ord_(13^a)(10)=6*13^(a-1)` must state `a >= 1`.

## Remaining quantitative boundary

The transfer error in (8) is `O(t^(-3/2))`, whereas the T128/T139 cylinder-hit
margin is `O(1/Q)`.  A useful application must therefore choose a
scale-dependent late start with, at minimum, `t^(3/2)` large compared with
`Q`, retain the exact endpoint/shift budget, and prove a favorable signed
estimate for the complete accelerated Machin score.  No such estimate is
known here.

Accordingly, the carrier is a rigorous `proof sketch` reduction of arithmetic
support, not a fixed-pi cancellation theorem, density statement, normality
claim, or resolution of V1.
