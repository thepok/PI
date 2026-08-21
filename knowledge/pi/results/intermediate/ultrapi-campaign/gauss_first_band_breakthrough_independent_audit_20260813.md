# Independent audit: Gauss first-band two-ray reduction

Audit date: **2026-08-13 UTC**

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Primary report:
[`gauss_first_band_breakthrough_attack_20260813.md`](gauss_first_band_breakthrough_attack_20260813.md)

Primary checker:
[`gauss_first_band_breakthrough_attack_20260813_check.py`](gauss_first_band_breakthrough_attack_20260813_check.py)

Independent checker:
[`gauss_first_band_breakthrough_independent_check.py`](gauss_first_band_breakthrough_independent_check.py)

Original source URL: none. This is Marcel's human-authored local target, so no
external source URL is invented. The canonical quantifiers remain: every
finite decimal word, including leading zeroes, must occur contiguously in the
usual nonterminating decimal expansion of \(\pi\). In the first-band criterion,
\(n\) ranges over every positive integer; \(\delta\) is fixed before
\(n\to\infty\), and only then may \(\delta\downarrow0\).

## Verdict and exact boundary

**PASS with no correction to the primary artifacts.** Independent derivations
below confirm the one-digit Lucas congruence, reflected first-block zero
symmetry, two-ray parametrization including its unique merger, both endpoint
bounds, the quantifier order in criterion (16), the count equivalence, the CRT
gcd identity, the abstract local-statistics countermodel, and finite-field
identity (26).

The primary report establishes exact reductions but not

\[
 S_n:=\sum_{\substack{n/2<p<n\\p\ \text{odd prime}\\p\mid A_n}}\log p=o(n),
 \qquad A_m=[X^m](X^2+2X+2)^m.                              \tag{A1}
\]

The reductions remain a `proof sketch`, their bounded source audit is
`literature-checked` as of the date above, and every bounded replay is an
`experiment`. Nothing here is `machine-checked`, a `candidate resolution`, or a
`verified resolution`. Canonical V1 remains a `conjecture`.

Before this audit, and unchanged by it:

- primary report SHA-256:
  `cba7b6115efc11de85b61634e1109430b9a215eda335cd0bea1cd2345a517e23`;
- primary checker SHA-256:
  `ec046cf117145b245cb20ea6822f4a757b6eed52c54e9ac3e278f51333a73ff7`;
- canonical target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

## 1. Coefficients, identity (26), and reflection

Put \(R(X)=X+2+2X^{-1}\). Then
\(A_m=\operatorname{ct}R(X)^m\), while direct multinomial extraction gives

\[
 A_m=\sum_{0\le k\le m/2}
       {m\choose 2k}{2k\choose k}2^{m-k}.                   \tag{A2}
\]

This independently fixes the coefficient convention and positivity. Its
generating function is

\[
 \sum_{m\ge0}A_mz^m=(1-4z-4z^2)^{-1/2}.                   \tag{A3}
\]

Let \(p\) be odd and \(q=(p-1)/2\). Substituting \(z=x/2\) in (A3), and
using \(q\equiv-1/2\pmod p\), gives coefficientwise through degree \(p-1\)

\[
 F_p(x):=(1-2x-x^2)^q
       =\sum_{s=0}^{p-1}(A_s/2^s)x^s\pmod p.               \tag{A4}
\]

For \(k<p\), the generalized-binomial denominator is a \(p\)-adic unit. If
\(q<k<p\), both \({q\choose k}\) and
\({-1/2\choose k}\pmod p\) vanish. This checks the top half of (A4), where
a careless truncation argument could otherwise fail.

The reciprocal identity

\[
 x^{p-1}F_p(1/x)=(x^2-2x-1)^q=(-1)^qF_p(-x)               \tag{A5}
\]

then yields, for \(0\le s\le q\),

\[
 A_{p-1-s}\equiv(-4)^{q-s}A_s\pmod p.                     \tag{A6}
\]

The scalar is nonzero, so

\[
 p\mid A_s\quad\Longleftrightarrow\quad p\mid A_{p-1-s}.  \tag{A7}
\]

Also \(A_s=(2i)^sP_s(-i)\). Parity gives
\(P_s(i)=(-1)^sP_s(-i)\), hence

\[
 \operatorname{Res}(X^2+1,2^sP_s(X))=A_s^2.               \tag{A8}
\]

Thus the resultant is the original integer squared, not a new small-height
norm. Finally, the recurrence

\[
 (s+1)A_{s+1}=2(2s+1)A_s+4sA_{s-1}                       \tag{A9}
\]

shows that two consecutive first-block zeros would propagate backward to
\(A_0=0\), impossible. This verifies exactly the no-consecutive-zero property
used below; it does not assert stronger spacing information.

## 2. Lucas reduction and both rays

In characteristic \(p\), \(R(X)^p=R(X^p)\). For \(0\le t<p\), exponents of
\(R(X)^t\) have absolute value below \(p\), whereas exponents of \(R(X^p)\)
are multiples of \(p\). Constant-term extraction therefore factors:

\[
 A_{p+t}\equiv
 \operatorname{ct}R(X^p)\operatorname{ct}R(X)^t
 =2A_t\pmod p.                                             \tag{A10}
\]

For \(n/2<p<n\), let \(t=n-p\). Then \(1\le t<p\), and (A7)--(A10) give

\[
 p\mid A_n\Longleftrightarrow p\mid A_t
 \Longleftrightarrow p\mid A_r,\qquad
 r=\min(t,p-1-t).                                          \tag{A11}
\]

If \(t\le(p-1)/2\), then \(r=t\) and \(p=n-r\). If
\(t\ge(p-1)/2\), then \(r=p-1-t\) and
\(p=(n+1+r)/2\). In either case \(p\ge2r+1\), so
\(3r\le n-1\).

Conversely, suppose \(1\le r\le(n-1)/3\), \(p\mid A_r\), and either

\[
 p=n-r,\qquad\text{or}\qquad p=(n+1+r)/2                  \tag{A12}
\]

is an odd prime. Then \(p\ge2r+1\). The reconstructed \(t\) is respectively
\(r\) or \(p-1-r\), lies in \([1,p-1]\), and (A7)--(A10) give
\(p\mid A_n\) with \(n/2<p<n\). This proves both directions without using
finite evidence.

The candidates in (A12) coincide exactly when

\[
 n-r=(n+1+r)/2
 \Longleftrightarrow n=3r+1,\qquad p=2r+1.                \tag{A13}
\]

This is \(t=r=(p-1)/2\), so there is at most one merger for each \(n\), and
it is one selected prime rather than two copies. The independent replay
exercises actual mergers, beginning with \((n,r,p)=(46,15,31)\).

## 3. Endpoints, criterion (16), and counts

For fixed \(r\), at most the two distinct candidates in (A12) are selected,
and their product divides \(A_r\le5^r\). A selected prime has a unique minimal
index. Consequently

\[
 \sum_{r\le T}\sum_{p\ \text{selected at }r}\log p
 \le\sum_{r\le T}\log A_r
 \le{\log5\over2}\lfloor T\rfloor(\lfloor T\rfloor+1).   \tag{A14}
\]

Every \(T=o(\sqrt n)\) therefore has \(o(n)\) weight.

Fix \(0<\delta<1/6\). For \(r<\delta n\), the direct and reflected rays
occupy prime intervals of lengths \(\delta n\) and
\(\delta n/2+O(1)\). For
\((1/3-\delta)n<r\le(n-1)/3\), their two intervals adjacent to the merger
have the same lengths. The prime number theorem in Chebyshev form bounds the
four ambient weights by

\[
                         3\delta n+o_\delta(n).             \tag{A15}
\]

Endpoint overlap can only reduce the distinct-prime weight.

Let \(I_n(\delta)\) be the selected weight on
\(\delta n\le r\le(1/3-\delta)n\). Positivity gives
\(I_n(\delta)\le S_n\), and (A15) gives

\[
 \limsup_{n\to\infty}{S_n\over n}
 \le\limsup_{n\to\infty}{I_n(\delta)\over n}+3\delta.      \tag{A16}
\]

Therefore

\[
 S_n=o(n)\Longleftrightarrow
 \bigl(\forall\,\delta\in(0,1/6)\text{ fixed}\bigr)
 I_n(\delta)=o(n).                                         \tag{A17}
\]

The reverse direction first takes \(n\to\infty\) at fixed \(\delta\), then
\(\delta\downarrow0\). It does not assume uniformity for a moving
\(\delta(n)\).

If \(C_n\) counts distinct selected primes, then

\[
 C_n\log(n/2)\le S_n\le C_n\log n,                         \tag{A18}
\]

and \(\log(n/2)\sim\log n\) proves

\[
 S_n=o(n)\Longleftrightarrow C_n=o(n/\log n).              \tag{A19}
\]

## 4. CRT compression

Write

\[
 \Pi_n=\prod_{n/2<p<n}p,\qquad
 J_n=\sum_{n/2<p<n}{\Pi_n\over p}A_{n-p},                 \tag{A20}
\]

with both ranges over odd primes. Modulo a band prime \(p\), every
\(J_n\)-summand except the \(p\)-summand vanishes, while \(\Pi_n/p\) is a
unit. Hence

\[
 p\mid J_n\Longleftrightarrow p\mid A_{n-p}.               \tag{A21}
\]

Since \(\Pi_n\) is square-free,

\[
 \gcd(\Pi_n,J_n)
 =\prod_{\substack{n/2<p<n\\p\mid A_{n-p}}}p
 =\exp(S_n).                                                \tag{A22}
\]

The PNT gives \(\log\Pi_n=n/2+o(n)\), so the generic bound by \(\Pi_n\)
remains linear. Exact compression alone supplies no cancellation theorem.

## 5. Abstract one-zero countermodel

Let \(N_j=10^j\), \(j\ge3\), and for each prime

\[
                         3N_j/4<p<4N_j/5                  \tag{A23}
\]

prescribe the one minimal zero \(z_p=N_j-p\); prescribe none for other
primes. These prime intervals are disjoint as \(j\) varies. For (A23),

\[
 0<z_p<(p-1)/2<p-1-z_p<p-1,
 \qquad (p-1-z_p)-z_p=3p-2N_j-1>N_j/4-1.                  \tag{A24}
\]

Thus \(\{z_p,p-1-z_p\}\) has reflected support, one minimal zero, and no
consecutive zeros. At \(n=N_j\), every prime in (A23) lies on the direct ray
\(p=N_j-z_p\), and the PNT gives weight

\[
 \vartheta(4N_j/5)-\vartheta(3N_j/4)
                   =(1/20+o(1))N_j.                        \tag{A25}
\]

This is a countermodel only to an implication based on the uniform minimal
zero count, reflected zero support, and no-consecutive-zero property. It is
not claimed to satisfy recurrence (A9). It does not refute a theorem using
additional arithmetic relations among the actual \(A_r\bmod p\). With this
scope, the primary report's pointwise-correlation barrier is correct.

## 6. Literature, mathlib, source pins, and hygiene

The source audit was repeated on **2026-08-13 UTC**. The versioned arXiv PDFs
for Kohen, Mattarei, and Sun were downloaded again and matched the primary
pins byte for byte. Five existing downloads of the Noe PDF also matched its
pin; its Waterloo URL was readable through the literature browser, while one
new command-line retrieval returned HTTP 503. That transient availability
issue changes neither the pinned bytes nor the checked theorem text.

| Primary source | Independently checked content | SHA-256 |
|---|---|---|
| [Noe, *On the Divisibility of Generalized Central Trinomial Coefficients*](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf) | Equations (3)--(5), (13)--(14), and Theorem 8.6 give the generating function, recurrence, Legendre normalization, digit product, and nonzero-scalar reflection. | `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c` |
| [Kohen, *Density and Symmetry in the Generalized Motzkin Numbers mod p*, arXiv:2411.03681v2](https://arxiv.org/pdf/2411.03681v2) | Theorem 4 gives reflection; Proposition 7 gives fixed-prime digit multiplicativity. The no-zero-prime remark explicitly uses a probabilistic heuristic and gives no moving-prime diagonal bound. | `f4c604453c2b81a48dd3ee56aabab0ef3a6a78b0d14a21a2b323bd4818d6db42` |
| [Mattarei, *Root multiplicities and number of nonzero coefficients of a polynomial*, arXiv:math/0512239v2](https://arxiv.org/pdf/math/0512239v2) | Theorem 2 gives weight at least \(q+1=(p+1)/2\) for a nonzero root of multiplicity \(q<p\); applied to (A4), it still permits \((p-1)/2\) zero coefficients. | `5e9c4f6345a7171b112d16b6eb12b7388334c9123e8d39058d22080e4f031b9d` |
| [Sun, *Congruences involving generalized central trinomial coefficients*, arXiv:1008.3887v13](https://arxiv.org/pdf/1008.3887v13) | Fixed-prime square-sum and parametric congruences, including the \(T_k(2,2)\) specialization in Conjecture 5.4, give no pointwise cross-prime selector estimate. | `a4540dc374dc9ef0fcad856c9a69c247d345fec94127ac8a6f09353f18995eb1` |

A fresh primary-source search for A006139, generalized-central-trinomial
prime divisors, \(P_n(i)\bmod p\), and zero coefficients of finite-field
trinomial powers found analytic and fixed-characteristic results but no
theorem implying (A1) or (A17). This is a bounded negative search, not a
novelty claim.

The local mathlib search confirms ordinary binomial Lucas in
Mathlib/Data/Nat/Choose/Lucas.lean, shifted-Legendre symmetry in
Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean, and Chebyshev theta and
primorial bounds in Mathlib/NumberTheory/Chebyshev.lean. It found no
generalized-central-trinomial digit product or moving affine-selector theorem.
No formal code was changed.

Run:

    python work/ultrapi-resume/gauss_first_band_breakthrough_independent_check.py

The independent checker compares (A2) with the recurrence; reconstructs
(A4), (A6), and (A10); compares the direct first band with both rays and
selected mergers; checks exact endpoint partitions for several rational
\(\delta\)'s; replays (A22) and (A24) at bounds distinct from the primary
checker; runs the primary checker; and validates target and primary hashes,
source-pin literals, links, UTF-8, C0/DEL cleanliness, final newlines, trailing
whitespace, and explicit negative V1 boundary statements.

Its finite rows remain an `experiment`. The PNT, limit-order argument, and
logical countermodel proof are analytic, not consequences of finite scanning.

## 7. Handoff

The unsolved core is unchanged: for every fixed \(0<\delta<1/6\), prove an
\(o(n)\) pointwise bound for actual prime divisors \(p\mid A_r\) aligned with
the two rays on \(\delta n\le r\le(1/3-\delta)n\). A local theorem about each
prime's zero count, reflection, and absence of consecutive zeros cannot alone
do this. The next useful input must correlate actual zero locations across
changing characteristics. Until such an input is proved, canonical V1 remains
a `conjecture`.
