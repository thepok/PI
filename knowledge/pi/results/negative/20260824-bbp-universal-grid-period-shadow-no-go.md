# BBP denominator-and-remainder shadowing cannot cover a full period

Status: `proof sketch`

Date: 2026-08-24 UTC

Source: the standalone period argument in the ChatGPT Pro memo
`workflows/state/chatgpt-pro/20260824-transfer-kernel-covariance-advance/answer.md`,
after an independent arithmetic and quantifier audit. The unrelated kernel,
covariance, and finite-modulus claims from that memo are not used here.

The full preperiod-amplification corollary below was prompted by
`workflows/state/chatgpt-pro/20260824-bbp-numerator-boundary-count/answer.md`,
but uses the stronger exact all-depth denominator formula already archived in
[`bbp_all_depth_two_adic_attack.md`](../intermediate/ultrapi-campaign/bbp_all_depth_two_adic_attack.md)
and independently checked in
[`bbp_all_depth_two_adic_independent_audit.md`](../intermediate/ultrapi-campaign/bbp_all_depth_two_adic_independent_audit.md).
The Pro memo's partial case split is not imported.

All logarithms below are natural logarithms.

## Exact truncation and decimal period

For `K >= 1`, define the `K`-term BBP truncation

\[
B_K=\sum_{j=0}^{K-1}\frac1{16^j}
 \left(\frac4{8j+1}-\frac2{8j+4}
       -\frac1{8j+5}-\frac1{8j+6}\right)
   =\frac{P_K}{Q_K},
\]

where `P_K/Q_K` is in lowest terms and `Q_K>0`. Factor

\[
Q_K=2^{a_K}5^{b_K}Q_{0,K},\qquad (Q_{0,K},10)=1,
\qquad s_K=\max(a_K,b_K).
\]

For all sufficiently large `K`, \(Q_{0,K}>1\); put

\[
\ell_K=\operatorname{ord}_{Q_{0,K}}(10).
\]

After the decimal preperiod `s_K`, the rational orbit of `B_K` has exactly
this period. In particular,

\[
Q_{0,K}\mid 10^{\ell_K}-1,
\qquad
\ell_K\ge \frac{\log(Q_{0,K}+1)}{\log 10}. \tag{1}
\]

## Surviving primes in the reduced denominator

For `K >= 2`, let `p` be prime with

\[
4K<p<8K,\qquad p\equiv1\ \text{or}\ 5\pmod 8. \tag{2}
\]

Then

\[
v_p(Q_K)=1,\qquad p\mid Q_{0,K}. \tag{3}
\]

Indeed, if `p` is `1` modulo `8`, it occurs uniquely as `8j+1`; if it is `5`
modulo `8`, it occurs uniquely as `8j+5`, with `0<=j<K`. Every linear
denominator in the truncation is below `8K<2p`, so no other one is divisible
by `p`. The combined BBP bracket is

\[
\frac{120j^2+151j+47}
 {(2j+1)(4j+3)(8j+1)(8j+5)}. \tag{4}
\]

At the two singular roots its numerator is respectively `30` and `-1/2`
modulo `p`, hence nonzero for the primes in (2). The unique singular summand
therefore has `p`-adic valuation `-1`, while every other summand is
`p`-integral. This proves (3). The restriction `K>=2` removes the exceptional
case `K=1,p=5`, because the factor `5` is deliberately removed from
\(Q_{0,K}\).

The prime number theorem in the two reduced residue classes modulo `8` gives

\[
\sum_{\substack{4K<p<8K\\p\equiv1,5\ (8)}}\log p=2K+o(K).
\]

Consequently the exact reduced denominator satisfies

\[
\log Q_{0,K}\ge 2K+o(K). \tag{5}
\]

This asymptotic step is an explicit external dependency, not formalized in
the repository. Source status checked 2026-08-24: the fixed-modulus PNT in
arithmetic progressions is classical; the repository already cites
[Bennett--Martin--O'Bryant--Rechnitzer, *Explicit bounds for primes in
arithmetic progressions* (2018), Theorem 1.2](https://arxiv.org/abs/1802.00085v3),
which is stronger than the asymptotic used here. The BBP identity itself is
machine-checked in
[`T104T104BBPSeriesIdentity.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T104T104BBPSeriesIdentity.lean)
and originates in
[Bailey--Borwein--Plouffe (1997)](https://doi.org/10.1090/S0025-5718-97-00856-9).
These source checks do not upgrade this note beyond `proof sketch`.

## A lower bound for the actual BBP remainder

Let

\[
R_K=\pi-B_K.
\]

Formula (4) is positive for every `j>=0`, so the first omitted term gives

\[
R_K\ge 16^{-K}
\frac{120K^2+151K+47}
 {(2K+1)(4K+3)(8K+1)(8K+5)}.
\]

For `K>=1`, bounding the four denominator factors by `3K`, `7K`, `9K`, and
`13K` yields

\[
\boxed{R_K\ge\frac{16^{-K}}{21K^2}}. \tag{6}
\]

Thus

\[
\log(1/R_K)\le K\log16+2\log K+\log21. \tag{7}
\]

The direction matters: this is a lower bound for the actual truncation error,
so it upper-bounds how long a universal shadow certificate can last.

## The post-preperiod magnitude radius is already the full circle

There is a stronger finite obstruction once the exact decimal preperiod is
retained.  The archived two-adic result uses the inclusive convention

\[
\widetilde B_N=\sum_{j=0}^{N}(\text{the }j\text{-th BBP term}),
\qquad
v_2(\operatorname{den}\widetilde B_N)=4N-v_2(N+1).
\]

The present convention has \(K\) terms, so \(B_K=\widetilde B_{K-1}\).  The
archived result proves the following formula for \(K\ge2\), and \(K=1\) is
the immediate value \(a_1=0\).  Thus the exponent in the reduced denominator
is exactly

\[
\boxed{a_K=4K-4-v_2(K).} \tag{7a}
\]

For \(K\ge3\), \(v_2(K)\le K-2\): if \(v_2(K)\ge K-1\), then
\(2^{K-1}\le K\), contradicting the elementary strict inequality
\(2^{K-1}>K\) for \(K\ge3\).  Since \(s_K=\max(a_K,b_K)\), (7a) gives

\[
s_K\ge a_K\ge3K-2. \tag{7b}
\]

Combining (6) and (7b),

\[
10^{s_K}R_K
\ge \frac{10^{3K-2}}{21K^2 16^K}
=\frac{(125/2)^K}{2100K^2}>1
\qquad(K\ge3). \tag{7c}
\]

The final strict inequality is exact, not asymptotic.  At the base case

\[
\frac{(125/2)^3}{2100\cdot3^2}
=\frac{1{,}953{,}125}{151{,}200}>1,
\]

and the ratio of consecutive lower bounds is

\[
\frac{125K^2}{2(K+1)^2}>1\qquad(K\ge3). \tag{7d}
\]

Define the post-preperiod one-sided magnitude-only uncertainty radius by

\[
\rho_{K,m}:=\min\{1,10^{s_K+m}R_K\},\qquad m\ge0.
\]

Equation (7c) implies the exact finite conclusion

\[
\boxed{K\ge3,\ m\ge0\quad\Longrightarrow\quad\rho_{K,m}=1.} \tag{7e}
\]

Thus every such one-sided magnitude-only uncertainty arc is already the full
circle at the first post-preperiod state and remains so thereafter.  No
separation of the exact rational numerator from decimal boundaries can rescue
that certificate: the uncertainty arc itself covers every boundary.

## The certified window is shorter than one period

A post-preperiod state of `B_K` lies on the grid with denominator
\(Q_{0,K}\).
Its circular distance from every decimal boundary `d/10` is at least
\(1/(10Q_{0,K})\). Hence the denominator and the error magnitude alone certify
that the `m`-th post-preperiod state of `B_K` and the corresponding state of
pi lie in the same decimal cylinder only while

\[
10^{s_K+m}R_K<\frac1{10Q_{0,K}}. \tag{8}
\]

Define the certified length by

\[
\sigma_K=\max\left\{L\in\mathbb N:
  \forall m<L,\quad
  10^{s_K+m}R_K<\frac1{10Q_{0,K}}
\right\}. \tag{9}
\]

The set contains `L=0` and is finite because `R_K>0`. Thus (9) has no
empty-set ambiguity: if even `m=0` is not certified, then `sigma_K=0`.

If `sigma_K>0`, applying (8) at `m=sigma_K-1` and discarding the nonnegative
preperiod term gives

\[
\sigma_K\log10
\le \log(1/R_K)-\log Q_{0,K}. \tag{10}
\]

For `sigma_K=0` the resulting asymptotic upper bound is automatic. Combining
(5), (7), and (10) gives

\[
\sigma_K\le
\frac{(\log16-2+o(1))K}{\log10}. \tag{11}
\]

Combining (1) and (5), then dividing (11) by the resulting lower bound for
`ell_K`, gives

\[
\boxed{
\limsup_{K\to\infty}\frac{\sigma_K}{\ell_K}
\le\frac{\log16-2}{2}=\log4-1<1.} \tag{12}
\]

Therefore, for all sufficiently large `K`, the BBP remainder together with
the universal denominator-grid separation certifies strictly fewer than the
\(\ell_K\) states in one complete post-preperiod decimal period. The proposed
universal route

```text
BBP truncation -> shadow a complete rational period -> transfer the period
```

cannot be justified from those two inputs alone.

## Scope firewall

This is a denominator-plus-remainder and post-preperiod magnitude-only
certificate no-go, not a theorem that sampled BBP shadowing fails before the
preperiod or that the exact tail phase is uncontrolled.  It does not rule out
signed carry information, signed Fourier cancellation, or another argument
using the exact tail phase rather than its one-sided magnitude arc.  Nothing
here proves or disproves a covariance estimate, decimal density, normality,
V1, or any occurrence statement for pi.
