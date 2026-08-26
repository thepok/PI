# T169 terminal-common-modulus prime-pulse no-go

Status: `proof sketch`

Date: 2026-08-26 UTC

Source: directed Codex subagent audit, checked locally against T36, T46, T138,
T139, and T169. Nothing new in this note is Lean-checked.

## The carrier target

Put `q=10^k`, and write the T36 rational Machin approximant as

\[
M_s=16\sum_{r=0}^{2s+1}\frac{(-1)^r}{(2r+1)5^{2r+1}}
-4\sum_{r=0}^{2s+2}\frac{(-1)^r}{(2r+1)239^{2r+1}}.
\]

For the T139 primitive coefficients `p_(q,A)(u)`, define the complete T169
carrier score

\[
\mathcal C_{q,A}(N)=
\sum_{t<N}\sum_{u\in\mathcal P_q}
p_{q,A}(u)e\!\left(u10^tM_{t+k}\right).
\]

Applying T169's pointwise natural-window transfer to the compressed primitive
support and then the triangle inequality gives

\[
\left|\operatorname{primitiveBoundaryFourierSum}(q,A,N)
-\mathcal C_{q,A}(N)\right|
<E_k\operatorname{primitiveBoundaryLoad}(q,A),
\]

uniformly in `N>=1`, where

\[
E_k=\frac{4\pi(2/125)^k}{1-2/125}.
\]

Consequently, the genuine positive carrier target

\[
\exists N\ge q:\qquad
\Re\mathcal C_{q,A}(N)\ge
E_k\operatorname{primitiveBoundaryLoad}(q,A)
\tag{CPE}
\]

would imply the nonnegative complete primitive excursion needed by the
T148/T156 consumer. This reduction is a `proof sketch`: T169 formalizes the
pointwise estimate and the uncompressed positive-boundary sum, not this
compressed corollary verbatim.

## Exact terminal-modulus embedding

Let

\[
L_s=\operatorname{lcm}\left(
\{(2r+1)5^{2r+1}:0\le r\le2s+1\}\cup
\{(2r+1)239^{2r+1}:0\le r\le2s+2\}\right)
\]

and `V_s=L_sM_s`, which is an integer. For a terminal depth `S` and
`k<=s<=S`, set

\[
X_{s,S}=10^{s-k}V_s\frac{L_S}{L_s}.
\]

Then the moving rational phases embed exactly in one terminal modulus:

\[
e\!\left(h10^{s-k}M_s\right)=e_{L_S}(hX_{s,S}).
\]

This does not by itself create a useful long fixed-modulus orbit. The exact
increment is

\[
X_{s+1,S}-10X_{s,S}
=10^{s-k+1}L_S(M_{s+1}-M_s),
\]

whose modulus and new denominator factors continue to change with `s`.

## New-prime coordinates are terminal pulses

There are infinitely many terminal depths `S` for which

\[
p=4S+5
\]

is prime, by Dirichlet's theorem for primes congruent to `1 mod 4`. For every
such `S>=k>=3`, the following hold:

\[
v_p(L_S)=1,
\qquad
X_{s,S}\equiv0\pmod p\quad(k\le s<S),
\]

whereas

\[
X_{S,S}\equiv
-4\,10^{S-k}\frac{L_S}{p\,239^p}\not\equiv0\pmod p.
\]

Indeed, all raw odd factors at depth `s<S` are at most `4s+5<p`, so the
factor `p` occurs in `L_S/L_s`. At depth `S`, only the final `239`-branch term
has denominator containing `p`; every other summand vanishes after reduction
modulo `p`. Since `p` is neither `2`, `5`, nor `239`, the displayed residue is
nonzero.

Thus each newly introduced terminal prime coordinate is zero on every earlier
sample and nonzero only at the terminal sample. It is a one-point pulse, not a
long rational-function or trace-function orbit on which square-root
cancellation could be invoked. If one interpolates it as a polynomial in the
distinct time residues `s=k,...,S`, its degree is at least `S-k`; bounded
complexity is lost as the horizon grows.

## Narrow conclusion

This retires only the proposal that the *new* prime factors of the terminal
common denominator supply a long bounded-complexity fixed-modulus family for
proving (CPE). It does **not** rule out:

- cancellation from prime factors already present through many time steps;
- an estimate using the complete complementary CRT phase rather than one
  projected coordinate;
- a direct recurrence estimate that does not require bounded conductor; or
- another pointwise arithmetic mechanism selecting the actual pi orbit.

Those surviving possibilities are the same hard fixed-modulus/complementary-
phase boundary already visible in T46. No pi cancellation, target hit, V1,
density, or normality statement is proved here.

## PaperSearch comparison

The local PaperSearch database contained full text for the nearest mechanisms:

- Fouvry--Kowalski--Michel, *The sliding-sum method for short exponential
  sums*, arXiv:1307.0135;
- Fouvry--Kowalski--Michel, *A study in sums of products*, arXiv:1405.2293;
- Kauers--Krattenthaler--Müller, *A method for determining the mod-`2^k`
  behaviour of recursive sequences*, arXiv:1107.2015; and
- Adolphson, *Exponential sums and finite field A-hypergeometric functions*,
  arXiv:1210.6400.

The first, second, and fourth require a genuine bounded-complexity finite-field
family rather than the terminal pulse above. The third concerns congruence
structure and supplies no target-signed Archimedean estimate for this carrier.
