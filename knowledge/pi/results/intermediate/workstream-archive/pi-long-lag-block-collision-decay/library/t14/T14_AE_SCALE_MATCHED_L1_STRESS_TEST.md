# T14: almost-everywhere stress test of the scale-matched L1 spectrum

Status: `proof sketch` (rigorous prose note, not machine-checked).

## 1. Provenance and claim boundary

The immutable canonical statement is the local source
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`. Its SHA-256 was
verified before this note was written:

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

There is no external source URL in that statement: it records a local problem
formulated by this theory program on 2026-07-23. The canonical question is the
fixed-pi collision conjecture C1. This note does not decide C1. It studies only
the almost-everywhere sibling obtained from T8's spectral sum by replacing the
orbit value `Real.pi` in

\[
  (10^a-10^b)\,\mathop{\rm pi}
\]

by `alpha`. The universal circle constant in
`exp(2*pi*i*x)` is not replaced.

The exact T8 source is the machine-checked knowledge-library module
`TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction`, indexed
with SHA-256

```text
f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9
```

Only its displayed definitions of the deterministic domain, coordinates, and
frequency range are transcribed below. Every counting and moment assertion
used by this note is derived here. In particular, no assertion from the T10 or
T11 notes is used as a premise; those notes have status `proof sketch`.

No result below is specialized to `alpha=pi`. No assertion about C1, the
decimal digits of pi, or a fixed-pi spectral estimate is made.

## 2. Normalized sibling statement and ambiguities

Write

\[
 e(x):=\exp(2\mathop{\rm pi} i x),\qquad H_m:=10^m,
 \qquad T_s(m,N):=N+N^2 10^{-sm}.
\tag{2.1}
\]

The statement under test has the following exact quantifier order:

\[
\boxed{
 \begin{gathered}
 \text{there is a measurable }\Omega\subseteq[0,1)
 \text{ with }\operatorname{Leb}(\Omega)=1\text{ such that}\\
 \forall\alpha\in\Omega\ \forall s\in\mathbb R\ (0<s<1)\
 \exists B_{\alpha,s}\ge1\ \forall m,N\in\mathbb Z_{\ge1},\\
 \sum_{h=1}^{H_m}|S_h(\alpha;m,N)|
 \le B_{\alpha,s}H_mT_s(m,N).
 \end{gathered}}
\tag{AE-L1}
\]

The dependence is important: `B_(alpha,s)` is selected after both `alpha` and
`s`, but before every positive integer `m,N`. It cannot depend on `m,N`.

The apparent `Q0` ambiguity in T8 causes no ambiguity here. We fix an arbitrary
natural number `Q0` before `m,N` and prove in Section 3 that at `(mu,c)=(8,1)`
the domain is independent of `Q0`. Lebesgue measure is always restricted to
`[0,1)`; all functions are one-periodic. Frequencies are exactly the positive
integers `1 <= h <= H_m`, including both endpoints. Pairs are ordered and the
lag cutoff is the weak inequality `|a-b| >= m`.

## 3. Exact deterministic T8 domain at `(mu,c)=(8,1)`

T8 represents a pair by an orientation and a core `(r,n)`. Its membership
conditions are

\[
 0<r,\qquad m\le r<N,\qquad 0\le n<N-r,
 \qquad \neg\operatorname{ArithmeticExcluded}(8,1,Q_0,m,n,r).
\tag{3.1}
\]

The two orientations represent `(n,n+r)` and `(n+r,n)`. The imported
arithmetic definition uses

\[
 d(n,r)=10^n(10^r-1)
\tag{3.2}
\]

and, after substituting `(mu,c)=(8,1)`, says

\[
 \operatorname{ArithmeticExcluded}(8,1,Q_0,m,n,r)
 \Longleftrightarrow
 Q_0\le d(n,r)\ \text{ and }\ 10^{-m}\le d(n,r)^{-7}.
\tag{3.3}
\]

All quantities in the second inequality are positive real numbers.

**Lemma 3.1 (the exclusion is empty).** For every `Q0 >= 0` and every core
satisfying the first four conditions in (3.1), (3.3) is false.

**Proof.** Put `x=10^m-1`. Since `r>=m>=1` and `n>=0`,

\[
 d(n,r)\ge 10^r-1\ge 10^m-1=x\ge9.
\tag{3.4}
\]

For `x>=9`, one has `x^7>=x^2>x+1`: indeed,
`x^2-(x+1)=x(x-1)-1>=71`. As `x+1=10^m`,

\[
 d(n,r)^7\ge x^7>10^m.
\tag{3.5}
\]

Taking reciprocals of positive numbers reverses the strict inequality, so
`d(n,r)^(-7)<10^(-m)`. This contradicts the second conjunct in (3.3),
independently of its first conjunct and independently of `Q0`. QED.

The coordinate map is therefore a bijection from T8's records to

\[
 Q_{m,N}:=\{(a,b)\in\mathbb Z^2:
       0\le a,b<N,\ |a-b|\ge m\}.
\tag{3.6}
\]

To verify surjectivity, an ordered pair in (3.6) has the unique core
`n=min(a,b)`, `r=|a-b|`, and its order fixes the orientation. Conversely,
(3.1) gives `n+r<N`, so each represented coordinate lies in
`{0,...,N-1}` and has lag `r>=m`. This also verifies that no orientation factor
has been suppressed.

Put `L=(N-m)_+=max(N-m,0)`. If `N<=m`, the domain is empty. If `N>m`, every
lag `r=m,...,N-1` has `N-r` starts in each of two orientations. Hence

\[
 \boxed{|Q_{m,N}|=2\sum_{r=m}^{N-1}(N-r)
 = (N-m)(N-m+1)=L(L+1).}
\tag{3.7}
\]

An upper endpoint below a lower endpoint denotes an empty sum. Formula (3.7)
therefore covers every positive `m,N`, including `N<=m`.

## 4. Exact phases and finite Fourier identities

For `q=(a,b) in Q_(m,N)`, define

\[
 \lambda_q=10^a-10^b\in\mathbb Z\setminus\{0\}.
\tag{4.1}
\]

The alpha sibling of T8's sum is exactly

\[
 \boxed{S_h(\alpha;m,N)=
   \sum_{q\in Q_{m,N}}e(h\lambda_q\alpha),
   \qquad 1\le h\le H_m.}
\tag{4.2}
\]

This is a restricted long-lag sum. For `m>1` it is not
`|sum_(a<N)e(h10^a alpha)|^2-N`, because that expression also includes all
deleted lags `1,...,m-1`.

The reverse of every pair belongs to `Q_(m,N)` and has frequency
`-lambda_q`. Pairing the two orientations proves the real-valued identity

\[
 S_h(\alpha;m,N)=2\operatorname{Re}
 \sum_{r=m}^{N-1}\sum_{a=0}^{N-r-1}
 e\bigl(h(10^{a+r}-10^a)\alpha\bigr).
\tag{4.3}
\]

**Lemma 4.1 (frequency injectivity).** The map
`q -> lambda_q` is injective on all ordered unequal pairs of nonnegative
integers, and hence on `Q_(m,N)`.

**Proof.** The sign determines the orientation. In the positive case `a>b`,

\[
 10^a-10^b=10^b(10^{a-b}-1).
\tag{4.4}
\]

The parenthesized integer ends in decimal digit 9, so it is not divisible by
10. Thus the exact number of trailing decimal zeroes recovers `b`. Division by
`10^b` then recovers `10^(a-b)-1`, hence `a-b` and `a`. The negative case
follows after changing sign. QED.

For every integer `k`, direct integration gives

\[
 \int_0^1e(k\alpha)\,d\alpha=
 \begin{cases}1,&k=0,\\0,&k\ne0.\end{cases}
\tag{4.5}
\]

For `k!=0`, this follows by evaluating
`e(k alpha)/(2*pi*i*k)` at 0 and 1; the endpoint values agree because
`e(k)=1`. The `k=0` integrand is identically one.

Because all sums below are finite, they may be expanded and integrated term
by term. Equations (4.1), (4.2), and (4.5) give

\[
 \boxed{\int_0^1S_h(\alpha;m,N)\,d\alpha=0}
 \qquad(1\le h\le H_m).
\tag{4.6}
\]

Expanding the square gives the exact counting identity

\[
 \begin{aligned}
 \int_0^1|S_h|^2\,d\alpha
 &=\sum_{q,q'\in Q_{m,N}}
   \int_0^1e\bigl(h(\lambda_q-\lambda_{q'})\alpha\bigr)\,d\alpha\\
 &=|\{(q,q')\in Q_{m,N}^2:h\lambda_q=h\lambda_{q'}\}|\\
 &=|Q_{m,N}|.
 \end{aligned}
\tag{4.7}
\]

The last equality uses `h>=1` and Lemma 4.1. No asymptotic or independence
claim enters (4.7).

Define the squared energy and the requested L1 sum by

\[
 E(\alpha;m,N):=\sum_{h=1}^{H_m}|S_h|^2,
 \qquad A(\alpha;m,N):=\sum_{h=1}^{H_m}|S_h|.
\tag{4.8}
\]

Summing (4.7) over exactly `H_m` frequencies proves

\[
 \boxed{\int_0^1E(\alpha;m,N)\,d\alpha
 =H_m|Q_{m,N}|.}
\tag{4.9}
\]

Pointwise Cauchy-Schwarz and nonnegativity of the cross terms give

\[
 E\le A^2\le H_mE.
\tag{4.10}
\]

Integrating (4.10) and using (4.9) proves both constants in

\[
 \boxed{H_m|Q_{m,N}|\le\int_0^1A^2\,d\alpha
 \le H_m^2|Q_{m,N}|.}
\tag{4.11}
\]

Also, pointwise triangle inequality gives

\[
 A(\alpha;m,N)\le H_m|Q_{m,N}|.
\tag{4.12}
\]

Equations (4.6)-(4.12) are all finite identities or inequalities proved in
this note, not imported from the T10 moment discussion.

## 5. The elementary tail estimate and its exact failure to sum

Fix `0<s<1` and `B>0`. Markov's inequality applied to the nonnegative random
variable `A^2`, followed by (4.11), gives

\[
 \begin{aligned}
 &\operatorname{Leb}\{\alpha\in[0,1):
 A(\alpha;m,N)>B H_mT_s(m,N)\}\\
 &\hspace{20mm}\le
 \min\left\{1,
 {\int_0^1A^2\,d\alpha\over B^2H_m^2T_s(m,N)^2}\right\}\\
 &\hspace{20mm}\le
 \boxed{\min\left\{1,{|Q_{m,N}|\over B^2T_s(m,N)^2}\right\}.}
 \end{aligned}
\tag{5.1}
\]

This proves the displayed tail bound, including its factor `B^(-2)`. Since
`|Q_(m,N)|<=N^2` and

\[
 T_s(m,N)=N(1+NH_m^{-s}),
\tag{5.2}
\]

(5.1) implies

\[
 \operatorname{Leb}\{A>B H_mT_s\}
 \le {1\over B^2(1+NH_m^{-s})^2}.
\tag{5.3}
\]

The right side is summable in `N` for each fixed `m`, but not uniformly in
`m`. To audit this exactly, set

\[
 U_m(s):=\sum_{N=1}^{\infty}{|Q_{m,N}|\over T_s(m,N)^2}.
\tag{5.4}
\]

With `x=H_m^(-s)`, the summand bound above and monotonicity of
`(1+xt)^(-2)` give

\[
 U_m(s)\le\sum_{N=1}^{\infty}{1\over(1+Nx)^2}
 \le\int_0^\infty{dt\over(1+xt)^2}
 ={1\over x}=H_m^s.
\tag{5.5}
\]

This upper scale cannot be improved within the same majorant. Suppose
`floor(H_m^s)>=4m`. For every integer
`2m<=N<=floor(H_m^s)`, (3.7) gives

\[
 |Q_{m,N}|=(N-m)(N-m+1)\ge N^2/4,
\tag{5.6}
\]

while `NH_m^(-s)<=1` gives `T_s(m,N)<=2N`. Each corresponding term in
(5.4) is therefore at least `1/16`. There are at least
`floor(H_m^s)/2` such integers, so

\[
 U_m(s)\ge {\lfloor H_m^s\rfloor\over32}.
\tag{5.7}
\]

For all sufficiently large `m`, both the premise and
`floor(H_m^s)>=H_m^s/2` hold. Thus

\[
 \boxed{H_m^s/64\le U_m(s)\le H_m^s
 \quad\text{for all sufficiently large }m.}
\tag{5.8}
\]

Consequently the sum over `m` of the second-moment/union-bound majorants
diverges. This is only a proof that the elementary argument is insufficient.
It is not a lower bound on the actual tail probabilities and is not an
almost-everywhere refutation.

For completeness, (4.12) gives the deterministic fixed-scale estimate

\[
 {A(\alpha;m,N)\over H_mT_s(m,N)}
 \le {|Q_{m,N}|\over T_s(m,N)}
 \le {N\over1+NH_m^{-s}}\le H_m^s.
\tag{5.9}
\]

Thus every normalized value is finite, and for a fixed `m` the supremum over
all positive integers `N` is finite. The unresolved issue is uniformity as
`m` also varies.

## 6. Dependencies that a valid tail estimate must retain

Fixed-`h` orthogonality in (4.7) does not extend jointly over `h`. A second
application of (4.5) proves the exact cross-frequency identity

\[
 \boxed{
 \int_0^1S_h(\alpha;m,N)\overline{S_k(\alpha;m,N)}\,d\alpha
 =|\{(q,q')\in Q_{m,N}^2:h\lambda_q=k\lambda_{q'}\}|.}
\tag{6.1}
\]

The right side can be nonzero when `h!=k`. If `N>=m+2`, the pairs

\[
 q=(m,0),\qquad q'=(m+1,1)
\tag{6.2}
\]

both have lag `m` and belong to `Q_(m,N)`, while

\[
 \lambda_{q'}=10^{m+1}-10=10(10^m-1)=10\lambda_q.
\tag{6.3}
\]

Therefore (6.1) contains a collision for `(h,k)=(10,1)`. Both frequencies
are legal because `H_m=10^m>=10`. The reversed ordered pairs give the
corresponding negative-frequency collision. Hence the `h`-indexed sums may
not be treated as independent or jointly orthogonal.

The domains are nested as `N` increases, but the complex shell added to
`S_h` can cancel the old sum. In particular, neither `|S_h|` nor `A` is
monotone in `N`. A bound at dyadic endpoint values of `N` therefore does not
by itself imply a bound at every integer `N`. The terminal estimate below is
deliberately quantified over every positive `N` and makes no independence
assumption.

## 7. Countable exponent reduction and all-integer closure

Only a countable family of exponents is needed. Suppose (AE-L1) has been
proved simultaneously for every rational `t in (0,1)` on full-measure sets
`Omega_t`. Their countable intersection has full measure. Given any real
`s in (0,1)`, choose a rational `t` with `s<t<1`. Since `H_m>1`,

\[
 H_m^{-t}\le H_m^{-s},\qquad
 T_t(m,N)\le T_s(m,N).
\tag{7.1}
\]

Thus the bound for `t` implies the bound for `s` with the same constant. This
proves the countable-`s` reduction without intersecting uncountably many
full-measure sets.

For the integer variables, no subsequence reduction is made. The collection
of all pairs `(m,N) in Z_(>=1)^2` is countable, so Borel-Cantelli applies once
the actual bad-event probabilities are summable over this entire collection.

## 8. One unresolved tail inequality that closes the verdict

The following is the single unresolved input left by this note.

**Tail(t).** For every rational `t` with `0<t<1`, there exist constants

\[
 K_t\ge1,\qquad C_t>0,\qquad p_t>1
\tag{8.1}
\]

chosen before `m,N`, such that for every pair of positive integers `m,N`,

\[
\boxed{
 \operatorname{Leb}\left\{\alpha\in[0,1):
 A(\alpha;m,N)>K_tH_mT_t(m,N)\right\}
 \le {C_t\over
 H_m(1+NH_m^{-t})^{p_t}}.}
\tag{Tail(t)}
\]

This is a precise concentration statement for the restricted domain (3.6),
with all cross-frequency and cross-`N` dependencies left intact. It is not
asserted or proved here.

Here is the complete verification that `Tail(t)` would close (AE-L1). For
`x=H_m^(-t)` and `p_t>1`, monotonicity and direct integration give

\[
 \sum_{N=1}^{\infty}(1+Nx)^{-p_t}
 \le\int_0^\infty(1+xy)^{-p_t}\,dy
 ={H_m^t\over p_t-1}.
\tag{8.2}
\]

Summing `Tail(t)` over every positive `m,N` would therefore give

\[
 \begin{aligned}
 \sum_{m=1}^{\infty}\sum_{N=1}^{\infty}
 \operatorname{Leb}\{A>K_tH_mT_t\}
 &\le {C_t\over p_t-1}
 \sum_{m=1}^{\infty}H_m^{t-1}\\
 &= {C_t\over p_t-1}
 {10^{-(1-t)}\over1-10^{-(1-t)}}<\infty.
 \end{aligned}
\tag{8.3}
\]

The first Borel-Cantelli lemma, which requires no independence, would then
show that for almost every `alpha` only finitely many integer pairs `(m,N)`
violate the threshold. For such an `alpha`, define

\[
 B_{\alpha,t}:=\max\left(1,K_t,
 \max_{(m,N)\text{ exceptional}}
 {A(\alpha;m,N)\over H_mT_t(m,N)}\right),
\tag{8.4}
\]

where the last maximum is omitted if the exceptional set is empty. Every
term is finite by (4.12), and the maximum is over a finite set. Hence one
`B_(alpha,t)` works before all positive integers `m,N`. Intersecting over
rational `t` and applying (7.1) then proves the exact quantifier order in
(AE-L1) for every real `s in (0,1)`.

The powers in `Tail(t)` expose the missing gain. The elementary estimate
(5.3) has the required decay exponent `2` in `1+NH_m^(-t)` but lacks the
factor `H_m^(-1)`; its all-`N` sum grows like `H_m^t`. The proposed factor
turns that into the summable scale `H_m^(t-1)`. Any proof of `Tail(t)` must
obtain this concentration while respecting the explicit collisions in
(6.1)-(6.3).

## 9. Metric verdict and exclusions

**Almost-everywhere sibling verdict: unresolved.** The exact deterministic
domain, frequencies, cardinality, first moments, second moments, elementary
tails, countable exponent reduction, and all-integer Borel-Cantelli reduction
are derived within this proof-sketch note. They do not prove or refute (AE-L1).
The one remaining quantified input is `Tail(t)` in Section 8; equations
(8.2)-(8.4) prove that it would close the almost-everywhere sibling verdict.

This unresolved metric verdict says nothing about the fixed value `pi`.
There is no fixed-pi spectral conclusion and no conclusion about C1.
