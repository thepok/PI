# BBP--Machin cross-carrier independence no-go

Status: `proof sketch`

Date: 2026-08-25 UTC

Source: ChatGPT Pro BD follow-up memo,
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bd/turns/0004/answer.md`,
after three independent audits. The source rendering drops essential complex
conjugation and modulus bars; the corrected statements are recorded below.
Nothing in this note is Lean-checked.

## Corrected cross-carrier theorem

Let `q=10^k`, `t=L+k`,

\[
P_{j,h}=e(h10^{L+j}\pi),\qquad
B_{j,h}=e(h10^{L+j}B_{L+j+k}),\qquad
M_{j,h}=e(h10^{L+j}M_{L+j+k}),
\]

where `B_s` is the literal delayed BBP approximation used by T164 and `M_s`
is T169's single-rate Machin lower approximation. Put

\[
\rho=\frac5{2^{27}},\qquad \sigma=\frac2{125},\qquad
\Lambda_t=(56t+9)(56t+10)
\]

and

\[
\Delta_t=4\pi\left(
  \frac{\rho^t}{\Lambda_t(1-\rho)}+
  \frac{\sigma^t}{1-\sigma}
\right).
\]

For `k>=1`, `L>=0`, `N>=1`, and `1<=u,v<=2q-1`, the T164 and
T169 pointwise transfers imply

\[
\left|
\sum_{j<N}B_{j,u}\overline{M_{j,v}}-
\sum_{j<N}e((u-v)10^{L+j}\pi)
\right|<\Delta_{L+k}.
\]

The error is independent of `N`, `u`, and `v`. The conjugation is essential:
without it the frequency is `u+v`, not `u-v`.

More generally, for coefficient families `a` and `b`, the corresponding
same-time Hermitian bilinear forms differ by at most

\[
\Delta_{L+k}\,\lVert a\rVert_1\lVert b\rVert_1.
\]

Use `<=` in the completely unrestricted statement; strict `<` requires both
coefficient families to have nonzero absolute mass. For T139's primitive
coefficients this identifies the BBP--Machin cross-energy with the actual
pi-orbit target-polynomial energy up to the displayed error. It gives
magnitude information, not the sign of the primitive sum required by T148.

## Fixed-frequency carrier contrast

At a fixed frequency `u`, let

\[
C_u=\sum_{j<N}B_{j,u}\overline{M_{j,u}}.
\]

The identity

\[
1-\Re(B_{j,u}\overline{M_{j,u}})
=\frac12|B_{j,u}-M_{j,u}|^2
\]

and the same two transfer bounds give

\[
0\le N-\Re C_u<\Gamma_{L+k},
\]

where

\[
\Gamma_t=8\pi^2\left(
 \frac{\rho^{2t}}{\Lambda_t^2(1-\rho^2)}+
 \frac{2(\rho\sigma)^t}{\Lambda_t(1-\rho\sigma)}+
 \frac{\sigma^{2t}}{1-\sigma^2}
\right).
\]

Thus the `2 x 2` Gram matrix indexed by the two carrier labels at this fixed
frequency has contrast eigenvalue below `Gamma_(L+k)`. This is **not** a
rank-one assertion about the full cross-frequency Toeplitz matrix.

For `L+k>=3`, direct arithmetic gives

\[
\Delta_{L+k}<5.24\cdot10^{-5},\qquad
\Gamma_{L+k}<1.35\cdot10^{-9}.
\]

Numerical primitive-score corollaries that use the universal coefficient-load
bound `pi^2/2+2<7` remain only proof sketches.

## Narrow route retired

The complete BBP and Machin phase arrays are not two independent samples of
the decimal pi orbit. Bounded linear combinations and same-time Hermitian
bilinear forms with controlled `l1` coefficient mass either retain the common
pi signal or subtract it and leave only their small approximation contrast.
Consequently, independence-based two-carrier averaging cannot manufacture a
new extensive direction or the target sign required by T148.

This does **not** rule out:

- arithmetic of exact numerators, denominators, or CRT state invisible to
  Archimedean phase closeness;
- estimating the common Toeplitz entries themselves;
- normalized discrepancy statistics that amplify the small carrier
  difference;
- nonlinear, time-shifted, or coefficient-amplified joint statistics outside
  the displayed bounds;
- representations or depths without the same pointwise closeness.

At `L=0`, the actual primitive score connects to T139/T148. For `L>0`, the
memo's shifted primitive score has no registered shifted T148 consumer. No
T139/T148 premise, target hit, density statement, normality statement, or V1
conclusion follows here. Formalizing this triangle-inequality corollary is not
a current priority because it supplies no new signed arithmetic estimate.
