# T63: source-pinned applicability audit of pi-specific decimal arithmetic

Audit date: 2026-08-06 UTC.

Claim status: literature-checked applicability audit.  This is not a claim
about the canonical question, normality, equidistribution, FSFS, C1, or C2.
The finite T55/T61/T62 interfaces used below are machine-checked; every new
comparison with the literature is displayed in this report.

## 1. Canonical scope and quantifiers

The delivered byte-exact statement `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N >= 1`, the canonical quantity counts ordered pairs,
including the diagonal,

```text
Q_pi(n,N) = |{(i,j) in {0,...,N-1}^2 :
  ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}|.
```

The question asks whether

```text
for every A >= 1, there is n0 >= 1 such that for every n >= n0,
there is N >= 1 (allowed to depend on A,n) with
  A*n*Q_pi(n,N) <= N^2.
```

No statement audited here supplies those quantifiers.  In particular, a digit
algorithm, a bounded computation, a result for a different base, a rational
phase estimate, or a conditional dynamical alternative is not substituted for
the fixed-pi question.

The relevant recorded ambiguities are fixed as follows: pairs remain ordered;
the diagonal remains included; the strict circle-distance inequality remains;
the base is 10; powers are consecutive; `N` is existential after `A,n`; and no
infinitely-many-`n`, almost-everywhere, or prescribed-`N` sibling is used.

## 2. Source set and the version correction

`SOURCE_PINS.md` gives URLs, DOI data, exact PDF hashes, extraction hashes, and
page locators.  The key chronological fact is:

| source | date | actual content |
|---|---:|---|
| Zudilin arXiv v1 | 2024-09-16 | title and final paragraph claim a base-10 remote-digit scheme |
| Zudilin arXiv v2 | 2024-09-17 | title changes to base 5; decimal paragraph is deleted; Section 3 identifies the modular equality as incorrect |

The paper has no numbered theorem, proposition, lemma, or corollary.  Its
retained mathematical statements are equations and prose.  It explicitly
cites Bailey-Borwein-Plouffe (1997), not Bailey-Crandall or Lagarias.  The
latter sources are audited because they were named in the agenda's expert
feedback, not because Zudilin invokes them.

## 3. Exact retained primary-source statements

### 3.1 Bailey-Borwein-Plouffe (1997)

Theorem 1, equations (1.2)-(1.3), PDF p. 3 (printed p. 2), is the identity

\[
 \pi=\sum_{i=0}^{\infty}{1\over16^i}
 \left({4\over8i+1}-{2\over8i+4}-{1\over8i+5}-{1\over8i+6}\right).
\tag{3.1}
\]

The introduction, PDF pp. 2-3, states that in base `b` their `SC*` method
applies to integer linear combinations of series

\[
 \sum_{k=1}^{\infty}{p(k)\over b^{ck}q(k)},
 \qquad p,q\in\mathbb Z[X],\ c\in\mathbb Z_{>0}.
\tag{3.2}
\]

This is a digit-computation complexity statement, not an exponential-sum
estimate.  Section 6, PDF p. 12 (printed p. 11), says exactly that the authors
know no identity like (3.1) in base 10.  Section 7 then asks for an algorithm
for the `n`th decimal digit of pi in `SC*` and for a proof that pi is in `SC`
in every base.  Thus the primary BBP paper does not contain a base-10 formula
for pi.

### 3.2 Zudilin (2024), the valid identity and the invalid reduction

Equation (1), both versions, PDF p. 2, states

\[
 \sum_{n=0}^{\infty}{(1-2i)^{-(2n+1)}\over2n+1}
 -\sum_{n=0}^{\infty}{(1+2i)^{-(2n+1)}\over2n+1}
 ={\pi i\over4}.
\tag{3.3}
\]

Equivalently, with integers

\[
 b_0=1,\quad b_1=-1,\quad
 b_n=-6b_{n-1}-25b_{n-2}\quad(n\ge2),
\tag{3.4}
\]

the unnumbered identity on PDF p. 2 is

\[
 \sum_{n=0}^{\infty}{b_n\over(2n+1)5^{2n}}
 ={5\pi\over16},\qquad |b_n|<2\cdot5^n.
\tag{3.5}
\]

For a term with

\[
 t=2n+1=5^k m,\qquad (m,5)=1,
\tag{3.6}
\]

v2 equation (3), PDF p. 3, proposes a reduction modulo `Z[i]` with
denominator only `m`.  Section 3, PDF p. 3, then states that equation (3) is
incorrect when

\[
 2n+1>d-k.
\tag{3.7}
\]

In that range the left side has denominator

\[
 5^{2n+1-d+k}m,
\tag{3.8}
\]

whereas the proposed right side has denominator `m`.  Section 3 also says
that shortening the sum to enforce the opposite inequality does not repair
the method because no bound is then available for the fractional part of the
omitted tail.

Version 1's removed decimal paragraph multiplies by `10^d`, truncates at
`n=2d+2r-1`, and asserts the analogous unnumbered congruence with denominator
`m`.  It has the same missing factor (3.8).  There is therefore no retained
base-10 theorem in the corrected source.

### 3.3 Bailey-Crandall (2001)

Hypothesis A, PDF p. 2, is explicitly a hypothesis.  Let

\[
 r_n={p(n)\over q(n)},\qquad p,q\in\mathbb Z[X],\qquad
 0\le\deg p<\deg q,
\tag{3.9}
\]

with `q(n) != 0` for positive integers `n`.  For integer `b>=2`, define

\[
 x_0=0,\qquad x_n=(b x_{n-1}+r_n)\pmod1.
\tag{3.10}
\]

The hypothesis says that `(x_n)` either has a finite attractor or is uniformly
distributed in `[0,1)`.  Theorem 1.1, PDF p. 3, is conditional on this
hypothesis and lists pi, `log 2`, and `zeta(3)` as base-2 cases, with `log 2`
also a base-3 case and `zeta(5)` additionally requiring irrationality.  It does
not state a base-10 conclusion for pi.

The unconditional Theorem 3.1, PDF pp. 9-10, assumes (3.9), integer `b>=2`,
and defines

\[
 \alpha=\sum_{k=1}^{\infty}{p(k)\over b^kq(k)},\qquad
 x_n=\left(bx_{n-1}+{p(n)\over q(n)}\right)\pmod1.
\tag{3.11}
\]

Its exact conclusion is that `alpha` is rational if and only if `(x_n)` has a
finite attractor, equivalently a periodic attractor.  It does not conclude
anything about the other, infinite-attractor case.

The base-10 discussion, PDF pp. 16-17, calls a BBP implementation for pi in
base 10 an open question.  Its displayed pi expansion uses a recurrence
`D_(n+1)=D_n-5D_(n-1)`, not a rational-polynomial perturbation covered by
(3.9).  Finally, PDF p. 23 (printed p. 22) asks whether Hypothesis A can be
connected to Weyl sums and says that the powers `b^n` prevent easy
manipulation of the exponential sum.

### 3.4 Lagarias (2001)

Theorem 2.1, PDF p. 5, fixes integer `b>=2` and `theta in [0,1]`.  It states:

1. `theta` is digit-dense to base `b` iff its radix remainder sequence is
   dense in `[0,1]`.
2. `theta` is normal to base `b` iff that sequence is uniformly distributed.
3. `theta` has an eventually periodic base-`b` expansion iff the remainder
   sequence has finitely many limit points, iff it eventually enters a
   periodic orbit, iff `theta` is rational.

These are equivalences; they do not establish the distribution side for pi.

Theorem 3.1, PDF p. 7, assumes integer `b>=2`, real `epsilon_n -> 0`, and

\[
 \theta=\sum_{n=1}^{\infty}\epsilon_n b^{-n}.
\tag{3.12}
\]

For the associated perturbed remainder `y_n^*(theta)`, ordinary radix
remainder `x_n(theta)`, and

\[
 t_n=\sum_{j=1}^{\infty}\epsilon_{n+j}b^{-j},
\tag{3.13}
\]

it states

\[
 x_n(\theta)=y_n^*(\theta)+t_n\pmod1,
\tag{3.14}
\]

and that the two orbits approach one another on `R/Z`.  Lemma 3.2, PDF p. 8,
states that two sequences differing modulo one by `delta_n -> 0` have the same
limit points (with endpoints identified), and one is uniformly distributed iff
the other is.  Again, this transfers a property; it proves neither side has it.

Definition 4.1, PDF p. 9, calls

\[
 \theta=\sum_{n=1}^{\infty}{p(n)\over q(n)}b^{-n},
 \quad p,q\in\mathbb Z[X],\ (p,q)=1,\ q(n)\ne0,
\tag{3.15}
\]

a BBP-number to base `b`.  Theorem 4.1, PDF pp. 10-11, additionally assumes
`deg q > deg p`.  Under the separately stated Weak Dichotomy Hypothesis its
conclusion is the rational-or-digit-dense alternative; under the Strong
Dichotomy Hypothesis (Bailey-Crandall Hypothesis A) its conclusion is the
rational-or-normal alternative.  Both conclusions are conditional.

Theorem 3.3, PDF pp. 8-9, states under (3.12) that rationality is equivalent to
the perturbed remainders having finitely many limit points, and equivalent to
their approaching a periodic radix orbit residue-class by residue-class.  It
does not classify irrational orbits.

### 3.5 Bailey-Crandall (2002), the unconditional exponential-sum input

Theorem 4.6, printed pp. 12-13, is the only retained theorem that gives a
nontrivial exponential-sum bound.  For coprime integers `b,c>1`, there exist
positive constants `A,B,D`, depending only on `b,c`, such that for every
positive integer `J`, all sufficiently large `n`, and every integer `H`
satisfying

\[
 \gcd(H,c^n)<D c^n,
\tag{3.16}
\]

one has

\[
 \left|\sum_{j=0}^{J-1}
 e\left({H b^j\over c^n}\right)\right|
 <B\left(Ac^{n/2}+Jc^{-n/2}\log(c^n)\right),
\quad e(x)=\exp(2\pi i x).
\tag{3.17}
\]

Its proof uses the multiplicative order `ord(b,c^n)` and decomposes arbitrary
`J` into complete periods plus a remainder.  The hypotheses `gcd(b,c)=1` and
the rational phase are structural, not cosmetic.

Theorem 4.8, printed p. 14, concerns the paper's constructed
`(b,c,m,n)`-PRNG.  With `mu_k=m_k-m_(k-1)` and
`nu_k=n_k-n_(k-1)`, it assumes `(nu_k)` is nondecreasing and that for some
`gamma>1/2`, eventually

\[
 {\mu_k\over c^{\gamma n_k}}
 \ge {\mu_{k-1}\over c^{\gamma n_{k-1}}}.
\tag{3.18}
\]

It concludes the constructed PRNG is uniformly distributed and the specially
constructed number

\[
 \alpha_{b,c,m,n}=\sum_{k=1}^{\infty}{1\over b^{m_k}c^{n_k}}
\tag{3.19}
\]

is base-`b` normal.  Pi is not identified with (3.19), so this theorem is a
constructed-constant result, not a fixed-pi input.

## 4. The literal fixed-pi targets

Write throughout

\[
 e(x)=\exp(2\pi i x),\qquad
 S_N^\pi(h)=\sum_{t=0}^{N-1}e(h10^t\pi),\quad h\in\mathbb Z.
\tag{4.1}
\]

For a legal adjacent T26 chain node, let

\[
 C_k=h_0(10^r-1)\prod_{a<k}(10^{s_a}-1)>0,
 \quad \beta_0=C_k\pi,
 \quad s=s_k,
\tag{4.2}
\]

and

\[
 C_q=(10^s-1)C_k,\qquad \beta=C_q\pi,
 \qquad q=k+1.
\tag{4.3}
\]

Equation (4.3) is T61's checked adjacent coefficient identity.  The outgoing
shift at node `q`, denoted here `s_q`, is generally different from the incoming
shift `s` in (4.2).  Define

\[
 U_q=10^{s_q}-1,
\quad
 \delta=\min\left(E_q,{E_{q+1}\over U_q},
                         {1\over2U_q10^\ell}\right),
\quad R=\lceil\delta^{-1}\rceil,
\tag{4.4}
\]

where the previously undefined terms in (4.4) are literally

\[
 E_i=\operatorname{nodeErrorThreshold}(D,i)
 =\operatorname{inverseError}\left({1\over
   8\operatorname{densityDenominator}(D,i)^2}\right),
 \qquad
 \operatorname{inverseError}(\tau)={\arccos(\tau)\over2\pi}.
\tag{4.4a}
\]

These are the T24/T26/T38 definitions.  Write
`M_i=chain.nodeResidual(i)`; then T38's
`commonDepth(chain,q)=min(M_q,M_(q+1))`.  The checked chain requires

\[
 q=k+1<d,\qquad 1\le\ell<\min(M_q,M_{q+1}).
\tag{4.5}
\]

Put `H=R-1`,

\[
 \mathcal T_H=\{u\in\mathbb N:\lfloor H/10\rfloor<u\le H\},
 \qquad w_R(v)=1-{v\over R},
\tag{4.6}
\]

and let `nu_10(u)` be the decimal valuation of `u`.  T55 and T62 give the
literal terminal statistic

\[
 \begin{split}
 T(C_q\pi,\ell,R)
  ={}&\sum_{u\in\mathcal T_H}
      \sum_{a=0}^{\nu_{10}(u)}\sum_{j=0}^{\ell-1}
      w_R(u/10^a)\\
 &\quad\cdot e\left(C_q\pi\left((u/10^a)10^\ell-u10^j\right)\right).
 \end{split}
\tag{4.7}
\]

Every triple `(u,a,j)` remains a separate label.  In particular, coincident
integer frequencies are not merged.

Factoring the terminal endpoint in the T55 block gives, by direct finite
algebra,

\[
 \sum_{j=0}^{\ell-1}e(C_qu(10^\ell-10^j)\pi)
 =e(C_qu10^\ell\pi)S_\ell^\pi(-C_qu).
\tag{4.8}
\]

Thus (4.7) is a weighted, phase-sensitive combination of moving-frequency
`S_ell^pi(-C_q u)`, not one fixed-frequency Weyl sum.

T61's direct adjacent variance uses

\[
 m_{u,j}=u(10^\ell-10^j)
\tag{4.9}
\]

and is exactly

\[
 V=\sum_{u\in\mathcal T_H}\sum_{j=0}^{\ell-1}w_R(u)
 \left|e(C_k10^s m_{u,j}\pi)-e(C_km_{u,j}\pi)\right|^2.
\tag{4.10}
\]

The elementary telescoping identity

\[
 S_s^\pi(10f)-S_s^\pi(f)=e(f10^s\pi)-e(f\pi)
\tag{4.11}
\]

turns (4.10), without an analogy, into

\[
 \boxed{
 V=\sum_{u\in\mathcal T_H}\sum_{j<\ell}w_R(u)
 \left|S_s^\pi(10C_km_{u,j})-S_s^\pi(C_km_{u,j})\right|^2.}
\tag{4.12}
\]

The checked sufficient inequality required by T61 is

\[
 V<\ell+2A_{\rm dir}-2B_{\rm pred}-2B_{\rm end}
       -{\ell\over4R\delta^2},
\tag{4.13}
\]

where

\[
 A_{\rm dir}=\sum_{u\in\mathcal T_H}\sum_{j<\ell}w_R(u),
\tag{4.14}
\]

`B_pred` is the norm of the complete positive-depth part `a>=1` of (4.7),
and `B_end` is T55's complete source-shell endpoint budget.  No audited source
proves (4.13) for a legal fixed-pi chain.

## 5. Translation attempt from Zudilin's series

Define the rational truncation from (3.5)

\[
 \pi_K={16\over5}\sum_{n=0}^{K-1}{b_n\over(2n+1)5^{2n}}.
\tag{5.1}
\]

Using `|b_n|<2*5^n`, line by line,

\[
 \begin{aligned}
 |\pi-\pi_K|
 &\le {16\over5}\sum_{n=K}^{\infty}{2\cdot5^n\over(2n+1)5^{2n}}\\
 &\le {32\over5(2K+1)}\sum_{n=K}^{\infty}5^{-n}\\
 &= {32\over5(2K+1)}{5^{-K}\over1-1/5}\\
 &= {8\,5^{-K}\over2K+1}.
 \end{aligned}
\tag{5.2}
\]

In verifier-friendly ASCII, the last line is

```text
|pi-pi_K| <= 8*5^{-K}/(2K+1).
```

Substituting (5.1) into one target phase is exact only in the limit:

\[
 e(f\pi)=\lim_{K\to\infty}e(f\pi_K).
\tag{5.3}
\]

For a finite truncation, the elementary Lipschitz bound is

\[
 |e(x)-e(y)|\le2\pi|x-y|.
\tag{5.4}
\]

Consequently

\[
 \left|S_N^\pi(h)-\sum_{t<N}e(h10^t\pi_K)\right|
 \le {2\pi|h|(10^N-1)\over9}|\pi-\pi_K|.
\tag{5.5}
\]

This is the explicit algebraic transformation furnished by the series.  It
provides approximation of each term, not cancellation among the terms.

For the direct variance, let `V_K` be (4.10) with `pi_K` replacing pi.  Since
`| |z|^2-|z'|^2 | <= 4|z-z'|` when `|z|,|z'|<=2`, (5.4) gives

\[
 |V-V_K|
 \le8\pi C_kR^2\ell\,10^\ell(10^s+1)|\pi-\pi_K|.
\tag{5.6}
\]

Indeed, `m_(u,j)<R10^ell`, the total positive weight is less than `R*ell`,
and each endpoint difference has multiplier at most
`C_k*m_(u,j)*(10^s+1)`.  To certify (4.13) with a known strict margin `eta`, a
sufficient series precision is therefore

\[
 |\pi-\pi_K|<
 {\eta\over8\pi C_kR^2\ell\,10^\ell(10^s+1)}.
\tag{5.7}
\]

A sufficient choice of `K` obtained by combining (5.2) and (5.7) has, up to
logarithmic factors, the scale

\[
 K\gtrsim (\ell+s)\log_5 10+\log_5(C_kR^2\ell/\eta).
\tag{5.8}
\]

There is no source estimate for the sign of the strict margin `eta`, and a
finite approximation cannot manufacture one.

## 6. Modulus size and corrected decimal denominator

The denominator failure can be checked without prose.  Put `z=1-2i` and
`t=2n+1=5^k m`.  Since

\[
 z^{-t}={(1+2i)^t\over5^t},
\tag{6.1}
\]

the v1 decimal summand is

\[
 {8\,10^d\over5^km}z^{-t}
 ={8\,2^d5^{d-k-t}(1+2i)^t\over m}.
\tag{6.2}
\]

When `t>d-k`, the denominator retains

\[
 5^{t-d+k}m=5^{2n+1-d+k}m,
\tag{6.3}
\]

exactly as stated in v2 Section 3.  Reduction modulo `m` alone discards this
factor.  Worse, `(1-2i)` is not invertible modulo powers of 5 because its norm
is 5, so the omitted factor cannot be restored by applying the same modular
inverse routine at the corrected modulus.

Version 1 sums through `n_max=2d+2r-1`.  At that endpoint, the missing
5-adic exponent is

\[
 2n_{\max}+1-d+k=3d+4r-1+k.
\tag{6.4}
\]

Thus the true term modulus can contain a factor as large as
`5^(3d+4r-1+k)`, not merely the claimed odd cofactor `m`.

The condition for the claimed reduction, `2n+1<=d-k`, allows only roughly the
first half of the `d`-scale terms.  If the sum is shortened there, its omitted
tail begins near `n=d/2`; after multiplication by `10^d`, its absolute scale
before cancellation is on the order of

\[
 {10^d5^{-d/2}\over d}\asymp {2^d5^{d/2}\over d},
\tag{6.5}
\]

which grows exponentially.  This quantifies v2's statement that the original
small-tail estimate no longer applies after shortening.

For comparison, the rational number (5.1) has the following convenient,
generally nonreduced, common denominator

\[
 Q_K=5^{2K-1}\operatorname{lcm}(1,3,5,\ldots,2K-1).
\tag{6.6}
\]

This chosen common denominator is divisible by `5^(2K-1)` and hence is not
coprime to 10.  This is not a lower bound on the reduced denominator of
`pi_K`; no such lower bound is claimed.  The displayed representation is
suitable for exact rational evaluation, but it cannot itself be inserted as
the coprime pure-power modulus in Bailey-Crandall Theorem 4.6.

## 7. Orbit length and Bailey-Crandall scale

To use Theorem 4.6 for a base-10 rational phase, one must set

\[
 b=10,\qquad \text{phase}={a h10^j\over q},
\tag{7.1}
\]

with `q=c^n` and `gcd(10,c)=1`.  The modular orbit length is
`ord_q(10)<=phi(q)<=q`.  The proof of Theorem 4.6 splits a sum of length `J`
into these periods.

The corrected Zudilin modulus has the form `q=5^e m`.  It therefore fails the
theorem's literal `gcd(10,q)=1` hypothesis.  There is a transient that must not
be hidden: after `j>=e`, multiplication by `10^j` cancels the 5-power from the
reduced phase and may leave an orbit modulo a divisor of `m`.  Before that
point there is no multiplicative-group orbit modulo `q`.  If the sum length
`J<=e`, the transient consumes the whole sum.  If `J>e`, a separate argument
would still have to show that the remaining modulus is a pure power `c^n` of
one fixed `c`, that `n` is sufficiently large, and that all frequency-gcd
hypotheses below hold.  Zudilin gives no such argument.

Suppose instead that an unrelated reduced coprime rational approximation
`a/q` is introduced, with `q=c^n` for a fixed `c` coprime to 10.  Then (5.5)
yields the following sufficient transfer condition

\[
 |\pi-a/q|\le {9\varepsilon\over
  2\pi |h|(10^J-1)}
\tag{7.2}
\]

to approximate a length-`J` fixed-pi sum to error `epsilon`.  It is not a
necessary condition because errors inside the sum can cancel.  For the largest
direct-label endpoint in (4.10), this becomes at least the scale

\[
 |\pi-a/q|\ll {\varepsilon\over C_kR10^{\ell+s}}.
\tag{7.3}
\]

The source numerator in Theorem 4.6 is `H_source=a*h`.  Since `(a,q)=1`, its
gcd hypothesis becomes

\[
 \gcd(h,q)<Dq.
\tag{7.4}
\]

This must hold simultaneously for every moving frequency in (8.2)-(8.3), with
the constants attached to one fixed `c`.  No retained source verifies it.

On the other hand, when all hypotheses do hold, Theorem 4.6 gives

\[
 B(Aq^{1/2}+Jq^{-1/2}\log q).
\tag{7.5}
\]

For (7.5) merely to beat the trivial bound `J`, its first term requires roughly
`AB*q^(1/2)<J`; to produce an asymptotic `o(J)` estimate it requires
`q^(1/2)=o(J)` (with fixed source constants).  If one naively uses the explicit
nonreduced denominator `Q_K` from (6.6), then
`Q_K^(1/2)>=5^(K-1/2)` and, for the fixed source constants, the first term
eventually exceeds the short lengths `J=ell` or `J=s`.  This proves only that this direct common-denominator
implementation is useless; it does not rule out a different exceptionally
good reduced approximant.  Such an approximant would still have to satisfy
the pure-power, fixed-`c`, sufficiently-large-`n`, simultaneous gcd, accuracy,
and nontrivial-bound requirements just listed.  None is constructed or
estimated in the retained sources.

## 8. Frequency range required by T55 and T61

For `0<=j<ell` and `u in T_H`,

\[
 9u10^{\ell-1}\le m_{u,j}<u10^\ell<R10^\ell.
\tag{8.1}
\]

The terminal statistic (4.8) requires length `ell` sums at moving frequencies

\[
 |h|=C_qu<C_qR.
\tag{8.2}
\]

The direct variance (4.12) requires length `s` sums simultaneously at

\[
 h=C_km_{u,j}\quad\text{and}\quad10C_km_{u,j},
\tag{8.3}
\]

for every labeled pair `(u,j)`, with the endpoint phases reaching multipliers
of size

\[
 C_k10^sR10^\ell.
\tag{8.4}
\]

The chain supplies no parameter-independent upper bound on `C_k`, `R`, or
`s`.  A theorem for each fixed `h`, or for `|h|` polynomial in the sum length,
would therefore not cover this adaptive range without an additional uniform
estimate.  None of the retained sources states any bound over (8.2)-(8.4).

## 9. Approximation error and carries

Digit extraction and phase control have distinct error requirements.

Bailey-Borwein-Plouffe, PDF p. 2, notes the radix ambiguity between a tail of
`(b-1)` digits and a carry into trailing zeros.  Lagarias, Theorem 4.1 footnote
2 on PDF p. 10, is more explicit: their convention computes an approximation
to `b^d theta mod 1` within a specified distance; this usually determines the
digit but may fail near a digit-interval endpoint.

Thus an error bound

\[
 \|10^d\pi-x\|_{\mathbb R/\mathbb Z}<10^{-r}
\tag{9.1}
\]

alone does not certify `r` decimal digits.  Choose compatible representatives
in `[0,1)`; one also needs the computed point, including across the identified
`0/1` boundary, to be farther than the error from every relevant boundary `a/10^t`,
`1<=t<=r`.  Neither Zudilin version provides such a carry-exclusion lower
bound.  The phrase "hardly affected" in the tail discussion is not a uniform
digit certificate.

For T55/T61, decimal digits need not be read at all.  Carries can be bypassed
by the analytic phase bounds (5.4)-(5.7).  But those bounds require a known
strict margin in (4.13), and the literature supplies no cancellation estimate
creating that margin.  Finite decimal evidence cannot replace it.

## 10. Hypothesis-by-hypothesis applicability table

| source input | source hypothesis | attempted target mapping | result |
|---|---|---|---|
| BBP Theorem 1 | base-16 identity (3.1) | base 10 in (4.1) | wrong base; source explicitly leaves decimal pi open |
| Zudilin (3.3)-(3.5) | convergent pi-specific series | replace pi in each phase by (5.1) | exact only as a limit; finite error is (5.5)-(5.7); no cancellation |
| Zudilin v1 decimal congruence | implicitly discards all denominator except `m` | compute `{10^d pi}` remotely | false when (3.7) holds; missing modulus (6.3) |
| Bailey-Crandall Hypothesis A | unproved rational-polynomial dynamical dichotomy | infer behavior of decimal pi orbit | pi conclusion in source is base 2/16, not 10; hypothesis remains unproved |
| Bailey-Crandall 2001 Theorem 3.1 | rational-polynomial perturbation | classify the pi orbit | only rational iff finite attractor; no irrational-case estimate |
| Lagarias Theorem 3.1 | an existing convergent perturbed expansion | transfer behavior between two orbits | equivalence/approach only; no behavior established |
| Lagarias Theorem 4.1 | BBP expansion (3.15) plus a dichotomy hypothesis | apply to Zudilin recurrence | Zudilin coefficients are not `p(n)/q(n)` and the conclusion is conditional |
| Bailey-Crandall 2002 Theorem 4.6 | rational phase, `q=c^n` for fixed `c`, sufficiently large `n`, `gcd(b,c)=1`, and (3.16) | set `b=10`, approximate pi | Zudilin's modulus fails the literal hypotheses; unrelated approximants must satisfy (7.2)-(7.5) uniformly over moving frequencies |
| Bailey-Crandall 2002 Theorem 4.8 | constructed PRNG and growth (3.18) | identify its constant with pi | no such identity or parameter map exists |

No row supplies all hypotheses needed for (4.7), (4.12), or (4.13).

## 11. What the source does establish

The genuinely pi-specific surviving arithmetic is:

1. The exact complex arctangent identity (3.3).
2. The integer recurrence and convergent rational series (3.4)-(3.5).
3. The explicit approximation error (5.2), derived here from Zudilin's stated
   coefficient bound.

These facts permit computation of pi and, with enough precision, any fixed
finite collection of phases.  They do not bound a moving, adaptively weighted
family of phase sums.  Computational access to every summand is not an
estimate for their sum.

## 12. Precise obstruction

The following three checked failures collectively explain why the retained
sources do not provide the requested bridge:

1. **Validity obstruction.**  The only 2024 decimal claim was removed because
   its core congruence omits `5^(2n+1-d+k)`.
2. **Theorem-hypothesis obstruction.**  The available unconditional
   exponential-sum theorem requires a rational phase, a pure power `c^n` for
   one fixed `c` coprime to 10, sufficiently large `n`, and a frequency-gcd
   bound.  The corrected Zudilin representation supplies none of this package.
3. **Route-specific scale failure.**  The explicit approximation route
   (5.1), used with the convenient common denominator (6.6), makes the
   `q^(1/2)` term in the shape of Theorem 4.6 larger than the short target sum.
   This does not exclude all rational approximants; it records exactly why the
   retained Zudilin truncation plus Theorem 4.6 does not bridge the target.

This is stronger than saying the formulas merely "look different": the failed
equation, the missing source hypotheses, and the incompatible inequalities
are all displayed above.

## 13. Smallest checkable next lemma

The next useful formal statement is an elementary transfer lemma, not a claim
that suitable approximants or rational-phase cancellation exist.

**AdaptiveRationalPhaseTransfer.**  Fix legal T61 parameters
`C_k,s,ell,R` and define `V(theta)` by replacing pi with `theta` in (4.10).
For any real `theta`, rational `a/q`, and `eta>0`, prove

\[
 |\theta-a/q|<
 {\eta\over8\pi |C_k|R^2\ell10^\ell(10^s+1)}
 \quad\Longrightarrow\quad
 |V(\theta)-V(a/q)|<\eta.
\tag{13.1}
\]

This lemma is finite, has explicit constants, and is directly checkable from
(5.4).  It would isolate exactly what any future coprime-modulus
exponential-sum theorem must provide: a rational-phase upper bound beating the
right side of (4.13) by `eta`, together with an approximation satisfying
(13.1).  The current sources provide neither antecedent.

## 14. Terminal verdict

NO CURRENT BRIDGE
