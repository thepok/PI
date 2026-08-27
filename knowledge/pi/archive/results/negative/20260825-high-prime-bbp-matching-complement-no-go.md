# High-prime BBP matching-complement no-go

Status: `proof sketch`

Date: 2026-08-25 UTC

Source: ChatGPT Pro BE follow-up memo, Sections 2--3,
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-be/turns/0003/answer.md`,
after an independent mathematical audit. Nothing in this note is Lean-checked.

## Rough pole sector

Write `B_(7m)` for the literal four-pole BBP partial sum through row `7m`.
For `gamma>0`, let `H_(m,gamma)` be the sum of those individual pole terms
whose odd linear denominator has a prime factor `p>gamma*m`, and put

\[
C_{m,\gamma}=B_{7m}-H_{m,\gamma}.
\]

If `m>0` and `gamma*m>5`, every selected term occurs after row
`(gamma*m-5)/8`. Summing their absolute geometric tail gives

\[
|H_{m,\gamma}|
<\frac{128\sqrt2}{5\gamma m}\,16^{-\gamma m/8}.
\]

Let `Q=10^k`, `m>=k`, `0<|h|<2Q`, and
`eta_gamma=10*16^(-gamma/8)`. The phase Lipschitz bound then gives

\[
\left|
e\!\left(h10^{m-k}B_{7m}\right)
-e\!\left(h10^{m-k}C_{m,\gamma}\right)
\right|
<\frac{512\pi\sqrt2}{5\gamma m}\eta_\gamma^m.
\]

When `gamma>8*log_16(10)`, `eta_gamma<1`, so summing over any later horizon is
bounded independently of its length:

\[
\sum_{r\ge0}
\left|
e\!\left(h10^{m+r-k}B_{7(m+r)}\right)
-e\!\left(h10^{m+r-k}C_{m+r,\gamma}\right)
\right|
<
\frac{512\pi\sqrt2}{5\gamma(1-\eta_\gamma)}
\frac{\eta_\gamma^m}{m}.
\]

For the actual positive-frequency T128 coefficients, their total absolute
mass is at most

\[
L_*:=\frac{\pi^2}{2}+2.
\]

Therefore the same bound, multiplied by `L_*`, controls the perturbation of
the complete target-centred signed score. Here **joint contribution means
only this score perturbation**. The exponential score is nonlinear, so
`H_(m,gamma)` is not an additive summand of the score.

## Consequence for the verified prime coordinates

At their evaluated depths, the primes exposed by T159, T161 and T162 satisfy
`p>14m`; T165--T166 transport the same coordinates to the literal delayed
numerator. Taking `gamma=14` gives

\[
\eta_{14}=\frac5{64}.
\]

Thus all pole terms carrying the currently exposed large-prime coordinates,
together with their exact matching complementary factors, alter the full
target-signed score by only `O((5/64)^m/m)`, uniformly over the horizon. They
are exponentially near-coherent rather than independent macroscopic
oscillators.

This retires the route that tries to obtain cancellation by averaging the
known large-prime coordinates separately while discarding or bounding their
matching complement. It does **not** retire arguments that retain a genuinely
new joint correlation with the remaining low-prime carrier.

The CRT interpretation needs one qualification. In a general rough-sector
sum, candidate prime factors may cancel when the rational is reduced, so the
reduced rough denominator need not retain every prime appearing in an
individual pole. For the current T159--T162 coordinates, the verified
unique-pole valuation statements prevent that cancellation. The no-go is
therefore exact for the presently registered prime bands, not a blanket
statement about every possible rough prime.

## Limited critical-prefix consequence

Combining the four poles before truncation gives a stronger carrier
compression. Put `c=log_16(10)`, choose `0<=lambda<1`, and define

\[
J_\lambda(m)=
\left\lfloor cm-\lambda\log_{16}(m+1)\right\rfloor.
\]

Once `J_lambda(m)>=c*m/2`, the T164 quadratic tail scale yields, for every
natural-window frequency,

\[
\left|
e\!\left(h10^{m-k}B_{7m}\right)
-e\!\left(h10^{m-k}B_{J_\lambda(m)}\right)
\right|
<\frac{4\pi2^\lambda}{c^2}m^{\lambda-2}.
\]

Its absolute sum over an arbitrary later horizon is at most

\[
\frac{4\pi2^\lambda}{c^2}
\frac{2-\lambda}{1-\lambda}m^{\lambda-1},
\]

again multiplied by `L_*` for the complete target-signed score. Every
non-dyadic prime in this shorter rational carrier is at most

\[
8J_\lambda(m)+5
\le 8\log_{16}(10)m-8\lambda\log_{16}(m+1)+5.
\]

This is a genuine denominator-support compression, but only a limited
consequence: it replaces one unresolved target-signed carrier
by another and supplies no sign or cancellation estimate.

## Claim boundary

The note proves neither the fixed-pi signed premise required by T139 nor the
improved primitive premise consumed by T148. It supplies no interval hit,
density, normality, decimal disjunctivity, or V1 conclusion. The surviving
problem is still a target-dependent joint correlation estimate for the
remaining carrier.
