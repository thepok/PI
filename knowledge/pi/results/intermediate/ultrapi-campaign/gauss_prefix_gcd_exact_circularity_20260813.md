# Gauss prefix gcd: exact support identity and circularity boundary

Status: canonical V1 remains a `conjecture`.  The exact support theorem below
is a `proof sketch`; the bounded primary-source search is `literature-checked`
as of **2026-08-13 UTC**; and all finite rows are an `experiment`.

## Provenance and normalization

- Canonical target:
  [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
- Target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Original source URL: none.  The target is Marcel's human-authored local
  question, so no external source URL is invented.
- Audited predecessor:
  [`gauss_first_band_breakthrough_attack_20260813.md`](gauss_first_band_breakthrough_attack_20260813.md)
- Independent audit of that predecessor:
  [`gauss_first_band_breakthrough_independent_audit_20260813.md`](gauss_first_band_breakthrough_independent_audit_20260813.md)

The integer sequence in this branch is

\[
 A_m=[X^m]\,(X^2+2X+2)^m=[x^m]\,(1+2x+2x^2)^m.             \tag{1}
\]

The second equality follows by reversing the degree-\(2m\) polynomial.  The
similar expression \([x^m]\,(1+2x+4x^2)^m\) is **not** the same sequence:
at \(m=2\), (1) is \(8\), whereas that expression is \(12\).  All statements
below concern the audited sequence (1), not the coefficient with \(4x^2\).

## Outcome

For \(n\ge2\), put

\[
 R_n=\prod_{1\le r\le\lfloor(n-1)/3\rfloor}A_r,
 \qquad
 G_n=\gcd(\operatorname{odd}(A_n),\operatorname{odd}(R_n)),             \tag{2}
\]

where \(\operatorname{odd}(m)=m/2^{v_2(m)}\).  For a positive integer \(m\),
write

\[
 \operatorname{rad}_{<n}^{\rm odd}(m)
   =\prod_{\substack{p<n\\p\text{ odd prime}\\p\mid m}}p.             \tag{3}
\]

Then the proposed prefix gcd has the exact support identity

\[
 \boxed{
 \operatorname{rad}_{<n}^{\rm odd}(G_n)
   =\operatorname{rad}_{<n}^{\rm odd}(A_n).
 }                                                                       \tag{4}
\]

Consequently, if

\[
 M_n=\sum_{\substack{\sqrt n<p<n\\p\text{ odd prime}\\p\mid A_n}}
          \log p,
\]

then

\[
 0\le
 \log\operatorname{rad}_{<n}^{\rm odd}(G_n)-M_n
 \le\vartheta(\sqrt n)=o(n),                                           \tag{5}
\]

and hence

\[
 \boxed{
 \log\operatorname{rad}_{<n}^{\rm odd}(G_n)=o(n)
 \quad\Longleftrightarrow\quad M_n=o(n).
 }                                                                       \tag{6}
\]

Thus the square-free, below-\(n\) version of the prefix-gcd proposal is not a
new cross-characteristic estimate.  It is exactly the already unproved
medium-prime radical theorem, up to the elementary \(o(n)\) contribution of
primes at most \(\sqrt n\).

The untruncated integer \(G_n\) is strictly stronger and noisier than (4): it
retains prime powers and can contain common prime divisors \(p\ge n\).  For
example,

\[
 G_{226}=131\cdot263\cdot577\cdot24071,                                  \tag{7}
\]

where \(263,577,24071\ge226\); their prefix witnesses are respectively
\(r=30,36\), \(r=41\), and \(r=42\).  Also

\[
 G_{76}=17^2\cdot23\cdot97,                                               \tag{8}
\]

so the multiplicity issue is real.  A proof that \(\log G_n=o(n)\) would
still imply the needed theorem, but it asks for additional control not
present in the original prime radical.  No such bound is proved here.

## 1. Exact quantifiers

The theorem (4) holds for every integer \(n\ge2\).  Its prime quantifier is
over every odd prime \(p<n\), with the strict endpoint retained.  Equation
(6) is pointwise as \(n\to\infty\), not on average and not merely along a
subsequence.  A bounded computation cannot prove (6).

The canonical target asks whether every **finite** decimal word, including
words with leading zeroes, occurs contiguously in the usual nonterminating
decimal expansion of \(\pi\).  Nothing in this report proves the medium-prime
estimate, a fixed return, or a decimal-cylinder hit.

## 2. Proof of the support identity

Let \(p<n\) be an odd prime with \(p\mid A_n\).  Write the base-\(p\)
expansion as \(n=\sum_j d_jp^j\), where \(0\le d_j<p\).  The generalized
Lucas product gives

\[
                   A_n\equiv\prod_jA_{d_j}\pmod p.                       \tag{9}
\]

Therefore some digit \(d=d_j\) satisfies \(p\mid A_d\).  Since \(A_0=1\),
this digit is nonzero.  First-block reflection gives

\[
 p\mid A_d
 \quad\Longleftrightarrow\quad
 p\mid A_{p-1-d},                                                         \tag{10}
\]

because its scalar factor is nonzero modulo \(p\).
Together with \(A_0=1\), (10) also rules out \(d=p-1\).  Thus both
\(d\) and \(p-1-d\) are positive.

Suppose first that \(p\le 2n/3\).  With
\(r=\min(d,p-1-d)\), equations (9)--(10) give \(p\mid A_r\), and

\[
 1\le r\le{p-1\over2}\le{n-1\over3}.
\]

Thus \(p\mid R_n\).

Suppose instead that \(p>2n/3\).  Since \(p<n\), one has
\(n=p+s\) with \(1\le s<p\), and the one-digit Lucas congruence is

\[
                         A_n\equiv A_1A_s=2A_s\pmod p.                   \tag{11}
\]

Hence \(p\mid A_s\).  The strict inequality \(p>2n/3\) gives

\[
                         1\le s=n-p\le\left\lfloor{n-1\over3}\right\rfloor,
\]

so again \(p\mid R_n\).  We have proved

\[
 p<n, p\text{ odd prime}, p\mid A_n
 \quad\Longrightarrow\quad p\mid G_n.                                  \tag{12}
\]

The reverse implication for support below \(n\) is immediate from
\(G_n\mid A_n\).  This proves (4).  Notice that the two cases are exhaustive
and that neither uses finite evidence.

Equation (5) now follows because its left-hand difference is precisely the
sum of \(\log p\) over a subset of odd primes \(p\le\sqrt n\), hence is at
most \(\vartheta(\sqrt n)\).  Chebyshev's estimate already gives
\(O(\sqrt n)\); the prime number theorem is more than sufficient.  This
proves (6).

## 3. Why the full gcd does not repair the theorem

There are two independent enlargements between (4) and the full integer
\(G_n\).

1. If \(p^a\mid A_n\) and the prefix product supplies at least \(a\) copies
   of \(p\), then \(p^a\mid G_n\).  Lucas support modulo \(p\) does not by
   itself bound these valuations.
2. A prime \(p\ge n\) can divide both \(A_n\) and an earlier \(A_r\).  Such a
   prime is outside the medium-prime sum but remains in \(G_n\), as (7)
   demonstrates.

The trivial height bound \(G_n\le\operatorname{odd}(A_n)\le A_n\) is only
exponential, because

\[
 A_n=[z^n]\,(1-4z-4z^2)^{-1/2}
      =\exp\bigl((\log(2+2\sqrt2)+o(1))n\bigr).                           \tag{13}
\]

Bounding pairwise resultants or the whole prefix product does not improve
this generic linear logarithmic scale.  Moreover, replacing \(G_n\) by its
below-\(n\) radical returns exactly (6), so that truncation cannot be
advertised as an independent route.

The finite data are suggestive but logically weaker.  The checker evaluates
all \(G_n\) through \(n=3000\), verifies (4), and evaluates selected rows as
far as \(n=50000\).  At \(n=25000,30000,40000,50000\), respectively, it
finds approximately

\[
 {\log G_n\over n}=0.000639, 0.000394, 0.000302, 0.000217.              \tag{14}
\]

These rows are an `experiment`.  They do not rule out later spikes and do
not prove a little-o estimate.

## 4. Literature and mathlib audit

Search date: **2026-08-13 UTC**.  Queries covered gcds of generalized
central-trinomial coefficients, common divisors of Legendre values,
P-recursive gcd bounds, holonomic-sequence gcds, resultants of orthogonal
polynomials, and moving-prime zero sets.

- Tony D. Noe,
  [*On the Divisibility of Generalized Central Trinomial Coefficients*,
  J. Integer Sequences 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf),
  supplies the generalized Lucas product and nonzero-scalar first-block
  reflection used in (9)--(10).  The official PDF pin already independently
  checked in the predecessor is
  `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c`.
- Eric Rowland and Reem Yassawi,
  [*Automatic congruences for diagonals of rational functions*,
  arXiv:1310.8635](https://arxiv.org/abs/1310.8635), gives automata and Lucas
  products in fixed characteristic.  It supplies no uniform pointwise bound
  when the prime and index vary together.
- Zheng Xiao,
  [*Greatest common divisors for polynomials in algebraic numbers and
  applications to linear recurrence sequences*, arXiv:2110.01751v2](https://arxiv.org/abs/2110.01751v2),
  proves gcd bounds for constant-coefficient algebraic linear recurrence
  sequences using the Subspace Theorem.  The sequence (1) is P-recursive,
  not a constant-coefficient linear recurrence, and the prefix product in
  (2) is not covered by those theorems.  Frozen PDF SHA-256:
  `e631a86a1e94f172a113ed648d0841075a210527f3fba0c200adbca450f0f6ab`.

The local mathlib search reconfirmed ordinary Lucas infrastructure in
`Mathlib/Data/Nat/Choose/Lucas.lean`, shifted Legendre infrastructure in
`Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`, and Chebyshev theta
bounds in `Mathlib/NumberTheory/Chebyshev.lean`.  It found no theorem for
(4)'s generalized sequence or a P-recursive prefix-gcd estimate closing
(6).  This is a bounded negative search, not a novelty claim.

No formal code was changed.  Therefore nothing in this report is labeled
`machine-checked`, and no axiom-audit entry is claimed.

## 5. Reproduction

Run:

```bash
.venv/bin/python work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813_check.py
```

The replay checks the coefficient normalization, recurrence, Lucas and
reflection congruences, (4) through \(n=3000\), the strict extra-prime and
multiplicity examples, every full gcd through \(n=3000\), and the four
larger sampled rows in (14).  It also checks the target pin, links, UTF-8,
C0/DEL cleanliness, final newlines, and trailing whitespace.

## 6. Handoff

The prefix gcd is useful as a diagnostic but not as the missing theorem.
After the only asymptotically harmless truncation, its support is exactly the
medium-prime radical already isolated in the predecessor.  Keeping the full
gcd instead creates two extra obligations: control common primes at least
\(n\), and control valuations.  A viable continuation must establish new
cross-characteristic arithmetic for one of those quantities or return to the
two-ray selector; merely proving (4) again cannot advance canonical V1.
