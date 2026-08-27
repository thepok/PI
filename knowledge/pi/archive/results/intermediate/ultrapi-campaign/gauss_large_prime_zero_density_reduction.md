# Gauss large-prime zeros: norm closure and a compact-core reduction

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

The remaining estimate from the exceptional-gcd audit,

\[
 W_n:=\sum_{\substack{\sqrt n<p<n\\p\ {\rm odd\ prime}\\
                    p\mid U_{n\bmod p}}}\log p=o(n),             \tag{1}
\]

has **not** been proved.  Consequently this branch does not prove the
exceptional gcd is subexponential and does not prove a decimal-cylinder hit
for \(\pi\).  Canonical V1 remains a `conjecture`.

There are two useful all-depth reductions.

First, put

\[
 A_t=2^tU_t=T_t(1,2,2)\in\mathbb Z,\qquad
 L_t(X)=2^tP_t(X)\in\mathbb Z[X],                               \tag{2}
\]

where \(P_t\) is the Legendre polynomial.  Then

\[
 \boxed{\quad
 \operatorname {Res}_X(X^2+1,L_t(X))=A_t^2.
 \quad}                                                         \tag{3}
\]

Thus the tempting Gaussian norm/resultant formulation is exact, but it is
also tautologically no stronger than divisibility of \(A_t\): it supplies no
extra small-height integer and no hidden saving in (1).

Second, every selected prime in (1) has a unique reflected minimal index.
If

\[
 a=\left\lfloor{n\over p}\right\rfloor,qquad
 s=n-ap,qquad t=\min(s,p-1-s),                                 \tag{4}
\]

then

\[
 p\mid A_t,\qquad p>2t,\qquad (2a+1)t\le n-a,                  \tag{5}
\]

and at least one of

\[
       p={n-t\over a},\qquad
       p={n+1+t\over a+1}                                     \tag{6}
\]

holds (the two formulas are the direct and reflected cases, and both hold
only at the central residue \(s=t=(p-1)/2\)).  This removes
the moving coefficient index from the congruence: the unresolved objects are
large prime factors of the fixed integers \(A_t\), sampled by the two affine
selectors in (6).

For an integer \(B\ge1\) and a real parameter \(T\ge1\), let
\(C_n(B,T)\) be the part of \(W_n\)
coming from selected primes with

\[
       \left\lfloor n/p\right\rfloor\le B,qquad t>T.           \tag{7}
\]

Writing \(\vartheta(x)=\sum_{p\le x}\log p\), there is the all-depth bound

\[
 C_n(B,T)\le W_n\le C_n(B,T)
   +\vartheta\!\left({n\over B+1}\right)
   +{\log5\over2}T(T+1).                                      \tag{8}
\]

In particular, Chebyshev's estimate \(\vartheta(x)=O(x)\) and
\(B=T=\lfloor n^{1/3}\rfloor\) give

\[
 \boxed{\quad
 W_n=C_n(\lfloor n^{1/3}\rfloor,
         \lfloor n^{1/3}\rfloor)+O(n^{2/3}).
 \quad}                                                        \tag{9}
\]

Therefore (1) is equivalent to an \(o(n)\) estimate on the compact core in
(9).  The core has the simultaneous restrictions

\[
 a\le n^{1/3},\quad n^{1/3}<t\le {n-a\over2a+1},\quad
 p\mid A_t,                                                     \tag{10}
\]

together with one of the exact affine identities (6).  This is narrower than
the original varying-characteristic formulation, but it remains a genuine
pointwise prime-factor selector problem.

Equations (3)--(9) are a `proof sketch` with a complete derivation below;
they are not yet a Lean formalization.  The bounded source search is
`literature-checked` as of the audit date.  The companion checker is an
`experiment` in its finite-search portions.  Nothing here is a
`machine-checked`, `candidate resolution`, or `verified resolution` of V1.

## 1. Exact normalization

The previous audit established

\[
 \sum_{t\ge0}U_tx^t=(1-2x-x^2)^{-1/2}.                         \tag{11}
\]

After replacing \(x\) by \(2x\),

\[
 \sum_{t\ge0}A_tx^t=(1-4x-4x^2)^{-1/2}.                       \tag{12}
\]

The generalized-central-trinomial convention gives

\[
 A_t=T_t(1,2,2)
   =[X^t](X^2+2X+2)^t.                                        \tag{13}
\]

In particular \(A_t\) is a positive integer.  Since it is one positive
coefficient of a polynomial whose coefficient sum is \(5^t\),

\[
                         1\le A_t\le5^t.                       \tag{14}
\]

The standard Legendre generating function also yields

\[
                       A_t=(2i)^tP_t(-i).                      \tag{15}
\]

No asymptotic estimate is used in the tail argument; the elementary bound
(14) is enough.

## 2. The Gaussian norm/resultant closes on itself

Legendre parity and (15) give the following exact remainder in
\(\mathbb Z[X]/(X^2+1)\):

\[
 L_t(X)\equiv
 \begin{cases}
   (-1)^{t/2}A_t,&t\text{ even},\\
   (-1)^{(t-1)/2}A_tX,&t\text{ odd}.
 \end{cases}                                                   \tag{16}
\]

One may also prove (16) directly from the integral recurrence

\[
 (t+1)L_{t+1}(X)=2(2t+1)XL_t(X)-4tL_{t-1}(X),                 \tag{17}
\]

together with the positive recurrence

\[
 (t+1)A_{t+1}=2(2t+1)A_t+4tA_{t-1}.                           \tag{18}
\]

Because \(X^2+1\) is monic, its resultant with \(L_t\) is the
product of the two values at \(i\) and \(-i\).  Equation (16) therefore
proves

\[
 \operatorname {Res}_X(X^2+1,L_t(X))
       =L_t(i)L_t(-i)=A_t^2,                                   \tag{19}
\]

which is (3).  Equivalently, for every odd prime \(p\),

\[
 p\mid A_t
 \quad\Longleftrightarrow\quad
 X^2+1\mid L_t(X)\pmod p
 \quad\Longleftrightarrow\quad
 p^2\mid\operatorname {Res}(X^2+1,L_t).                       \tag{20}
\]

The last square in (20) looks like amplification, but (19) shows that it is
exactly the square of the original divisibility.  A norm or resultant bound
cannot improve (1) unless it introduces a genuinely independent algebraic
quantity.  The middle divisibility in (20) is polynomial divisibility in
\(\mathbb F_p[X]\): it means that the Euclidean remainder is zero and remains
valid when \(p\equiv3\pmod4\), even though \(X^2+1\) then has no root in
\(\mathbb F_p\).

## 3. Reflection and the minimal-index encoding

Let \(p\) be odd and \(m=(p-1)/2\).  Frobenius applied to (11), as in the
previous audit, gives the complete first block

\[
 \sum_{s=0}^{p-1}U_sx^s=(1-2x-x^2)^m\pmod p.                  \tag{21}
\]

Set \(D(x)=1-2x-x^2\).  Reversal of the polynomial on the right gives

\[
 x^{p-1}D(1/x)^m=(x^2-2x-1)^m=(-1)^mD(-x)^m.                 \tag{22}
\]

Comparison of coefficients in (21)--(22) proves the signed reflection

\[
 U_{p-1-s}\equiv(-1)^{m+s}U_s\pmod p.                         \tag{23}
\]

Now take a prime selected in (1), and define \(a,s,t\) by (4).  Equation
(23) gives \(p\mid U_t\), equivalently \(p\mid A_t\).  The definition of
\(t\) gives \(2t\le p-1\), hence \(p>2t\).

If \(t=s\), then \(n=ap+t\), giving the first formula in (6).  If
\(t=p-1-s\), then

\[
                  n=(a+1)p-1-t,                               \tag{24}
\]

giving the second formula.  The alternatives overlap exactly when
\(s=p-1-s\).  Finally, substituting \(p\ge2t+1\) into either
\(n=ap+t\) or (24) gives in both cases

\[
                         (2a+1)t\le n-a.                       \tag{25}
\]

This proves (5)--(6).  Conversely, let \(a\ge1\) and \(t\ge0\) be integers.
If either identity in (6) holds for an odd prime \(p\), and if
\(p>2t\), \(p\mid A_t\), and the original size conditions
\(\sqrt n<p<n\) hold, then \(\lfloor n/p\rfloor=a\).  The corresponding
residue is respectively \(t\) or \(p-1-t\), and \(p>2t\) makes \(t\) its
reflected minimal index.  Equation (23) therefore reconstructs a selected
prime.  This also covers the central residue, where both identities agree.

## 4. Removing both tails

Partition the primes in (1) according to whether

1. \(a=\lfloor n/p\rfloor>B\);
2. \(a\le B\) but \(t\le T\);
3. \(a\le B\) and \(t>T\).

The third sum is \(C_n(B,T)\).  In the first sum,
\(a\ge B+1\) implies \(p\le n/(B+1)\), so its weight is at most
\(\vartheta(n/(B+1))\).

Every prime in the second sum divides at least one of
\(A_0,\ldots,A_{\lfloor T\rfloor}\).  Counting a prime more than once only
increases an upper bound, and (14) gives

\[
 \begin{split}
 \sum_{\substack{p\ {\rm selected}\\t\le T}}\log p
 &\le\sum_{0\le t\le T}\log A_t\\
 &\le {\log5\over2}T(T+1).                                   \tag{26}
 \end{split}
\]

This proves (8).  Chebyshev's classical bound
\(\vartheta(x)=O(x)\), followed by \(B=T=\lfloor n^{1/3}\rfloor\), proves
(9).

The same argument permits any integer-valued \(B=B(n)\to\infty\) and
real-valued \(T=T(n)=o(\sqrt n)\):

\[
 W_n=C_n(B,T)+O\!\left({n\over B}+T^2\right).                 \tag{27}
\]

Thus both the small-prime-quotient tail and every fixed or slowly growing
endpoint range are harmless.  What remains is the interior alignment (10),
not a failure to account for endpoint factors.

## 5. Why per-prime zero counts do not close the core

For a fixed prime define

\[
                         z(p)=\#\{0\le s<p:p\mid U_s\}.        \tag{28}
\]

Equation (23) pairs its noncentral zeros.  Also, the three-term recurrence
shows that two consecutive values cannot both vanish.  These facts give only
linear bounds for \(z(p)\).

There is a polynomial formulation of the same limitation.  The right side
of (21) has two nonzero roots, each of multiplicity \((p-1)/2\).  The standard
root-multiplicity/weight bound therefore guarantees only at least
\((p+1)/2\) nonzero coefficients, again leaving as many as
\((p-1)/2\) zeros.  Mattarei's theorem cited below contains this sharp general
weight bound in characteristic greater than the degree.

Even a much stronger estimate for \(z(p)\) would not, by itself, control the
pointwise selector in (1): one must also show that the particular residues
\(n\bmod p\), simultaneously as \(p\) varies with \(n\), rarely land in the
zero sets.  Equations (6), (9), and (10) state that missing correlation input
without hiding it in a generic “zero-density” phrase.

## 6. Finite falsification scan

The companion exact checker finds the following `experiment`:

- among odd primes \(p\le10{,}000\), the largest first-block zero count is
  eight, first attained at \(p=2777\), with zero indices
  \(309,551,1286,1382,1394,1490,2225,2467\);
- on \(5000\le n\le10{,}000\), the largest observed \(W_n/n\) is
  \(0.006701765654129378\), at \(n=5009\), and the mean is
  \(0.0007040017576365069\).

These observations are compatible with (1), but they are finite evidence
only.  In particular, the small observed values of \(z(p)\) are not promoted
to a uniform theorem.

## 7. Literature search

Search date: **2026-08-12 UTC**.  The search used the exact generalized
central-trinomial normalization, Legendre values at \(\pm i\), resultants,
Krawtchouk formulations, sparse-polynomial/root-multiplicity bounds, and
varying-prime zero sets.

- Tony D. Noe,
  [*On the Divisibility of Generalized Central Trinomial Coefficients*,
  J. Integer Sequences 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf),
  proves the generalized Lucas product and the reflected first-block
  congruence.  For \((a,b,c)=(1,2,2)\), his sequence is exactly
  \(A_t=2^tU_t\).  Thus (21) and (23) are prior art/direct specializations,
  not novelty claims.
- Nadav Kohen,
  [*Density and Symmetry in the Generalized Motzkin Numbers mod \(p\)*,
  arXiv:2411.03681v2](https://arxiv.org/pdf/2411.03681v2), develops the same
  generalized-central-trinomial reflection and relates fixed-prime densities
  to the zeros in the first \(p\) terms.  Its heuristic discussion of primes
  with no first-block zero is for the ordinary central-trinomial sequence,
  so it is thematic rather than a theorem about the exact sequence in (2);
  it does not prove the cross-prime pointwise selector estimate (1).
- Sandro Mattarei,
  [*Root multiplicities and number of nonzero coefficients of a polynomial*,
  J. Algebra Appl. 6 (2007), 469--475](https://arxiv.org/pdf/math/0512239v2),
  proves the sharp root-multiplicity lower bound for polynomial weight in the
  relevant characteristic range.  Applied to (21), it gives only the linear
  bound described in Section 5.
- Zhi-Wei Sun,
  [*Congruences involving generalized central trinomial coefficients*,
  Sci. China Math. 57 (2014), 1375--1400](https://arxiv.org/pdf/1008.3887v13),
  records
  many exact square-sum and parametric congruences for \(T_n(b,c)\).  The
  bounded search found no theorem there that bounds (1)'s varying-prime
  affine selector.

No checked primary source in this bounded search proves (1), the compact-core
estimate following (9), or a uniform all-prime bound strong enough to imply
it.  Absence from this search is not a novelty claim.

## 8. Reproduction

Run

```bash
python work/ultrapi-resume/gauss_large_prime_zero_density_check.py
```

The expected output is

```text
PASS: Gaussian remainder/resultant identity, signed reflection, and minimal-index selector encoding on 7803 selected pairs through n=10000; the two-tail premises also replay exactly
EXPERIMENT: among odd primes p<=10000 the largest first-block zero count is 8 at p=2777, with zeros [309, 551, 1286, 1382, 1394, 1490, 2225, 2467]
EXPERIMENT: dyadic (upper, maximizer, max W_n/n, mean W_n/n) = [(100, 68, 0.10771308793159606, 0.018902677932601458), (1000, 505, 0.03380773184168008, 0.005139887790901463), (10000, 5009, 0.006701765654129378, 0.0007040017576365069)]; no asymptotic claim is made
```

The checker verifies (16)--(19) in exact integer polynomial arithmetic,
checks the full signed reflection for every odd prime through 997, scans all
first-block zero sets through 10,000, replays (4)--(6) for every selected pair
with \(n\le10{,}000\), and verifies the exact cutoff and divisibility premises
for the finite instance of (8).  Its two
`EXPERIMENT` lines are not used in the proof of any all-depth statement.

## 9. Handoff

The norm/resultant avenue is closed unless a second independent small-height
integer is found: the natural resultant is exactly \(A_t^2\).  Future work on
this branch should attack the compact core (10), preferably through a theorem
on large prime divisors of \(A_t\) constrained by the two affine selectors
(6), or through genuine cross-prime selector discrepancy.  More fixed-prime
automaticity or finite zero counts will not by themselves prove (1).
