# Independent audit: Gauss medium-prime radical reduction

Audit date: **2026-08-13 UTC**

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Primary report:
[`gauss_medium_prime_radical_reduction.md`](gauss_medium_prime_radical_reduction.md)

Primary checker:
[`gauss_medium_prime_radical_check.py`](gauss_medium_prime_radical_check.py)

Independent checker:
[`gauss_medium_prime_radical_independent_check.py`](gauss_medium_prime_radical_independent_check.py)

## Verdict and exact boundary

**PASS after one narrow bibliographic correction.**  I found no mathematical
error in the corrected definitions, one-digit Lucas identity, every-
\((B,n)\) error bound, little-o equivalence, fixed-band diagonal, eventual
fixed-band identity, exact first band, endpoint PNT reduction, scaled
Schur/Holt congruences, or resultant lemma.

The pre-audit report incorrectly identified Stephan Wagner's arXiv preprint as
*Journal of Integer Sequences* 15 (2012), Article 12.7.7.  That article is the
unrelated Shevelev--García-Pulgarín--Velásquez-Soto--Castillo paper
*Overpseudoprimes, and Mersenne and Fermat Numbers as Primover Numbers*.
Wagner's arXiv record has no journal reference.  I corrected only that citation
and versioned its link; the mathematical text and primary checker did not need
repair.

The exact remaining research blocker is

\[
 \sum_{\substack{\sqrt n<p<n\\p\ \mathrm{odd\ prime}\\
                   p\mid A_{n\bmod p}}}\log p=o(n),
 \qquad
 A_j=[X^j](X^2+2X+2)^j,
\]

equivalently the medium-prime radical estimate for \(A_n\), or equivalently
all fixed-band estimates in the report.  In particular, even

\[
 \sum_{\substack{n/2<p<n\\p\ \mathrm{odd\ prime}\\p\mid A_n}}\log p=o(n)
\]

is unproved.  Thus the reduction is a `proof sketch`; the bounded source audit
is `literature-checked` as of the date above; and every finite replay is an
`experiment`.  Nothing here is `machine-checked`, a `candidate resolution`, or
a `verified resolution`.  Canonical V1 remains a `conjecture`.

## Correction record

Before this audit:

- primary report SHA-256:
  `d7c4c66ab4402fe08d67e047cd274cf1aebbe5dc43c8db215ddadbca66097910`;
- primary checker SHA-256:
  `8c7909127936dc0853d34158a689675ac93271586de6b5c148cd9fa1faf2af2f`.

The corrected report now cites Wagner as
“arXiv:1205.5402v3 (2012 preprint).”  Its freshly downloaded PDF has the same
pin already recorded by the report.  The correction changes provenance only;
it supplies no new estimate and changes no equation.

## 1. Definitions and normalization

Write

\[
 A_j=2^jU_j=[X^j](X^2+2X+2)^j.
\]

The coefficient has the independent positive formula

\[
 A_j=\sum_{0\le k\le j/2}
       {j\choose 2k}{2k\choose k}2^{j-k}.                    \tag{A1}
\]

Indeed, choosing \(k\) quadratic terms forces \(j-2k\) linear
terms and \(k\) constant terms.  Formula (A1) proves integrality and
positivity.  It also agrees with the report's three-term recurrence.
Reversing a quadratic exchanges its constant and leading coefficients but
does not change its central coefficient, explaining why both the
three-parameter notation \(T_j(1,2,2)\) and
\([X^j](X^2+2X+2)^j\) give the same integer.

Because \(A_j\) is one positive coefficient and the sum of all coefficients
is \(5^j\),

\[
                         1\le A_j\le 5^j.                    \tag{A2}
\]

For an odd prime, \(p\mid A_j\) is equivalent to \(p\mid U_j\), so replacing
the original normalized coefficient by \(A_j\) loses no selected odd prime.
The strict interval \(\sqrt n<p<n\) is retained in both

\[
 W_n=\sum_{p\mid A_{n\bmod p}}\log p,
 \qquad
 M_n=\sum_{p\mid A_n}\log p,                                \tag{A3}
\]

where both sums are only over odd primes in that interval.  They are
logarithms of square-free products, not valuations with multiplicity.

## 2. Lucas identity and the exact discrepancy

There is a direct Laurent-polynomial proof independent of the primary
checker.  Put

\[
                         R(X)=X+2+2X^{-1}.
\]

Then \(A_m=\operatorname{ct}R(X)^m\).  In characteristic \(p\),
\(R(X)^p=R(X^p)\).  If \(m=ap+s\), \(0\le s<p\), every exponent in
\(R(X)^s\) has absolute value below \(p\), whereas every exponent in
\(R(X^p)^a\) is a multiple of \(p\).  A product term can therefore have
exponent zero only when both factors have exponent zero.  Hence

\[
                     A_{ap+s}\equiv A_aA_s\pmod p.           \tag{A4}
\]

This proves the identity for every \(a\ge0\), not merely the two-digit range.
Noe's equation (13) independently gives the same specialization.

For \(\sqrt n<p<n\), let \(a=\lfloor n/p\rfloor\) and
\(s=n-ap\).  The strict inequalities give \(1\le a<p\), and (A4) gives

\[
 p\mid A_n\quad\Longleftrightarrow\quad
 p\mid A_a\ \text{or}\ p\mid A_s.                           \tag{A5}
\]

Therefore \(W_n\le M_n\), and the set underlying \(M_n-W_n\) is exactly

\[
 \{p:\sqrt n<p<n,\ p\mid A_a,\ p\nmid A_s\}.                \tag{A6}
\]

The \((n,p)=(68,17)\) witness is valid:
\(a=4,s=0,A_4=136\), and \(A_0=1\).  Thus equality at finite depth is
false for the precise reason claimed.

## 3. Error bound and little-o equivalence

Fix integers \(n\ge2\) and \(B\ge1\), and let \(D_{n,B}\) be the product of
the distinct discrepancy primes in (A6).  If \(a>B\), integrality gives
\(a\ge B+1\), hence \(p\le n/(B+1)\).  If \(1\le a\le B\), the product of
all discrepancy primes having that quotient divides \(A_a\).  Consequently

\[
 D_{n,B}\le
 \prod_{p\le n/(B+1)}p\;\prod_{a=1}^{B}A_a
 \le
 \prod_{p\le n/(B+1)}p\;5^{B(B+1)/2}.                       \tag{A7}
\]

Taking logarithms proves the report's bound for **every** displayed pair
\((n,B)\), including \(B>n\).  Mathlib's explicit theorem
`Chebyshev.theta_le_log4_mul_x` even supplies
\(\vartheta(x)\le(\log4)x\) for all real \(x\ge0\).  With
\(B=\lfloor n^{1/3}\rfloor\), both terms are \(O(n^{2/3})\), so

\[
                         0\le M_n-W_n=O(n^{2/3}).             \tag{A8}
\]

Dividing by \(n\) proves the two directions of

\[
 W_n=o(n)\quad\Longleftrightarrow\quad M_n=o(n).             \tag{A9}
\]

For all sufficiently large \(n\), the product printed in the report is
exactly the square-free product whose logarithm is \(M_n\); the odd-prime
qualification is automatic because \(p>\sqrt n\ge2\).  The finitely many
smaller \(n\) do not affect (A9).

The “nonprimitive” interpretation is also correct.  For every odd \(p<n\),
(A4) puts a divisor of \(A_n\) into \(A_{\lfloor n/p\rfloor}\) or
\(A_{n\bmod p}\), both earlier terms.  The prime \(2\) already divides
\(A_1\).  One primitive divisor of \(A_n\) therefore cannot control the
moving nonprimitive radical in (A9).

## 4. Fixed-band diagonal and endpoints

The quantities \(W_{n,a}\) form a disjoint partition of \(W_n\), because
each selected prime has the unique quotient \(a=\lfloor n/p\rfloor\).
Positivity proves the forward implication in the fixed-band equivalence.

For the converse, suppose \(W_{n,a}/n\to0\) for each fixed \(a\).  For every
positive integer \(k\), choose a positive, strictly increasing threshold
\(N_k\) such that

\[
 n\ge N_k\Longrightarrow W_{n,a}/n\le k^{-2}
 \quad(1\le a\le k).                                        \tag{A10}
\]

Let \(B(n)=\max\{k:N_k\le n\}\) after the first threshold.  Strict increase
makes this maximum finite, and \(B(n)\to\infty\).  At \(k=B(n)\), (A10)
gives

\[
 \sum_{a\le B(n)}W_{n,a}\le n/B(n).                         \tag{A11}
\]

The complementary primes have \(a>B(n)\), so their total weight is at most
\(\vartheta(n/(B(n)+1))=O(n/B(n))\).  This tends to zero after division by
\(n\).  No uniform convergence in \(a\) was assumed; the report's order of
quantifiers is correct.

For fixed \(a\),

\[
 \lfloor n/p\rfloor=a
 \quad\Longleftrightarrow\quad
 {n\over a+1}<p\le {n\over a}.                              \tag{A12}
\]

Let \(P(a)\) be the largest prime divisor of the fixed positive integer
\(A_a\).  Once \(n>(a+1)P(a)\), every prime in (A12) is too large to divide
\(A_a\), and (A5) changes the selector \(p\mid A_s\) exactly into
\(p\mid A_n\).  This supplies an explicit sufficient threshold for the
report's eventual identity while retaining the original strict
\(\sqrt n<p<n\) conditions.

For \(a=1\), \(A_1=2\), so every odd candidate avoids \(A_1\) at every
depth.  Also \(n/2\ge\sqrt n\) for \(n\ge4\); the cases \(n<4\) contain no
eligible odd prime.  Thus the report may drop the square-root restriction
and keep the exact strict interval \(n/2<p<n\) with no exceptional threshold.

## 5. Endpoint PNT reduction

For a selected prime in a fixed band, put

\[
 s=n-ap,\qquad t=\min(s,p-1-s).
\]

The two branches are exactly

\[
 p={n-t\over a},\qquad p={n+1+t\over a+1}.                  \tag{A13}
\]

For \(0\le t\le\eta n\), \(0<\eta\le1/2\), they lie respectively in

\[
 \left[{(1-\eta)n\over a},{n\over a}\right],\qquad
 \left[{n+1\over a+1},{n+1+\eta n\over a+1}\right].        \tag{A14}
\]

Their combined length is
\(\eta n(1/a+1/(a+1))\).  The PNT in Chebyshev form
\(\vartheta(x)=x+o(x)\) shows that the combined logarithmic prime weight is

\[
 O_a(\eta n)+o_a(n).                                        \tag{A15}
\]

The error can be taken uniformly for \(0<\eta\le1/2\): all four positive
endpoints remain in a fixed \(a\)-dependent compact range of constant
multiples of \(n\), and \(\sup_{x\ge c_an}|\vartheta(x)-x|/x\to0\).
Endpoint inclusions alter (A15) by at most \(O(\log n)\).

Hence first taking \(n\to\infty\), then \(\eta\downarrow0\), gives zero
normalized endpoint weight.  A standard slow diagonal can additionally be
chosen with \(\eta(n)n\to\infty\).  This justifies the report's
\(t\ge\eta(n)n\) localization.  It does not estimate the remaining
proportional-index core and is not a proof of a fixed-band little-o claim.

## 6. Scaled Schur/Holt congruences

Noe defines

\[
 Q_m(x,d)=d^{m/2}P_m(x/\sqrt d).
\]

The report's integral polynomial is the exact specialization

\[
 L_m(X)=2^mP_m(X)=Q_m(2X,4).                                 \tag{A16}
\]

Noe's scaled Schur theorem, with the two base-\(p\) digits \(a,t\), gives

\[
 L_{ap+t}\equiv L_a^pL_t\pmod p
 \quad(0\le a<p,\ 0\le t<p).                               \tag{A17}
\]

For odd \(p\), scaled Holt gives

\[
 Q_{p-1-t}(2X,4)\equiv4^{(p-1)/2-t}Q_t(2X,4)
 \equiv2^{-2t}L_t\pmod p.                                  \tag{A18}
\]

Combining (A17)--(A18) proves both displayed affine congruences in the
report on its narrower domain
\(1\le t\le(p-1)/2\).  Here polynomial exponentiation is literal;
Frobenius then identifies \(L_a(X)^p\) with \(L_a(X^p)\) over
\(\mathbb F_p\).

The explicit formula

\[
 L_t(X)=\sum_{0\le k\le t/2}
 (-1)^k{t\choose k}{2t-2k\choose t}X^{t-2k}                \tag{A19}
\]

shows \(\deg L_t=t\) and
\(\operatorname{lc}(L_t)={2t\choose t}\).  Since \(2t<p\), that leading
coefficient is a \(p\)-adic unit.  All domain conditions needed later are
therefore present.

## 7. Resultant lemma and diagnostic table

The elementary lemma is valid with the following exact domain:

> Let \(f,g\in\mathbb Z[X]\), let \(p\) be prime, let
> \(\deg f=t\), and assume \(p\nmid\operatorname{lc}(f)\).  If the reduction
> of \(f\) divides the reduction of \(g\) in \(\mathbb F_p[X]\), then
> \(p^t\mid\operatorname{Res}(g,f)\).

Over \(\mathbb Z_p\), scale \(f\) by its unit leading coefficient to make it
monic.  Division writes \(g=qf+r\) with every coefficient of \(r\) in
\(p\mathbb Z_p\).  The quotient algebra
\(\mathbb Z_p[X]/(f)\) is free of rank \(t\), and multiplication by \(r\)
has a matrix all of whose entries lie in \(p\mathbb Z_p\).  Its determinant
is divisible by \(p^t\).  The relevant resultant differs from this norm only
by powers of the unit leading coefficient and a sign, proving the assertion.

Applying this to \(f=L_t\) and either affine \(g\), using (A17)--(A19), gives
the two universal \(p^t\) divisibilities.  Selection by \(p\mid A_t\) is not
used.  A separate integer Sylvester matrix with fraction-free Bareiss
elimination reproduced the four sharp valuations:

| \(n\) | \(t\) | \(p\) | branch | \(p\mid A_t\)? | valuation |
|---:|---:|---:|:---|:---:|---:|
| 20 | 3 | 17 | direct | no | 3 |
| 21 | 4 | 17 | direct | yes | 4 |
| 29 | 4 | 17 | reflected | yes | 4 |
| 30 | 7 | 23 | direct | yes | 7 |

Thus the forced factor can be sharp on both sides of the selector.  The
two-Legendre resultant does not distinguish the desired primes.

## 8. Primary-checker coverage

The primary checker is internally consistent and its printed finite counts
reproduce exactly.  Its coverage is narrower than the mathematical report,
as it should be for an `experiment`:

- it builds \(A_n\) only from the recurrence; the independent checker also
  uses the direct coefficient formula (A1);
- it compares Lucas prediction with direct integer \(A_n\) only through
  \(n=300\); for the scan through \(10{,}000\), both \(W\) and \(M\) are then
  selected from the same first-block/Lucas tables rather than direct
  \(A_n\) divisibility;
- it tests the error-bound premises only at
  \(B=\lfloor n^{1/3}\rfloor\), not every finite \(B\);
- it does not test the fixed-band diagonal or the PNT, which are analytic
  arguments rather than finite identities;
- it tests the scaled congruences for \(p\le31,a\le2\), and checks the four
  resultants with SymPy.

None of these limits invalidates a report claim: the report does not present
finite checking as proof of an asymptotic.  The independent checker closes
the most useful finite coverage gaps without sharing primary-checker code.
It verifies:

- the coefficient formula and recurrence through depth 360;
- 16,069 exact Lucas instances and 12,459 direct medium-prime pairs;
- 130,317 exponentiated integer forms of the error bound for every
  \(2\le n\le360\) and every \(1\le B\le363\);
- 359 exact band partitions, 1,475 instances beyond explicit fixed-band
  thresholds, the exact first band at every checked depth, and 426 rational
  endpoint-selector containments;
- 470 scaled Schur/Holt congruence and divisibility instances, including
  \(a=p-1\) boundary cases;
- the four resultants with a custom determinant and 16 additional instances
  of the general resultant lemma.

Those bounded checks remain an `experiment`.  In particular, the decreasing
ratios printed by the primary checker have no proof status.

## 9. Literature and source-pin audit

The following primary PDFs were fetched afresh on **2026-08-13 UTC**.

| Source | Claim actually checked | SHA-256 |
|---|---|---|
| [Tony D. Noe, *On the Divisibility of Generalized Central Trinomial Coefficients*](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf), JIS 9 (2006), Article 06.2.7 | Equations (1)--(5), (11)--(14), Lemma 9.4, and Theorem 9.1 support the coefficient convention, scaled Holt relation, and full Lucas/Schur product. | `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c` |
| [Stephan Wagner, *Asymptotics of generalised trinomial coefficients*, arXiv:1205.5402v3](https://arxiv.org/pdf/1205.5402v3) | Gives asymptotic expansions for \([x^n](x^2+bx+c)^n\).  It controls the total size of \(A_n\), not its moving prime-factor window.  It is a preprint, not JIS Article 12.7.7. | `5b4696abb4b9c40ef48203dda749f4c290a3ba215dcb1de2c12bb5eb78bdec28` |
| [Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers mod \(p\)*, arXiv:2411.03681v2](https://arxiv.org/pdf/2411.03681v2) | Proposition 7 is a fixed-prime digit product; Theorem 4 is first-block reflection.  Its no-zero-prime discussion is explicitly heuristic and concerns the ordinary central-trinomial sequence. | `f4c604453c2b81a48dd3ee56aabab0ef3a6a78b0d14a21a2b323bd4818d6db42` |
| [Zhi-Wei Sun, *New observations on primitive roots modulo primes*, arXiv:1405.0290](https://arxiv.org/pdf/1405.0290), Nanjing Univ. J. Math. Biquarterly 36 (2019), 108--133 | Conjecture 5.6 proposes primitive divisors for the ordinary central-trinomial and Motzkin sequences.  It is conjectural, concerns different sequences, and one primitive divisor would not imply this radical estimate. | `ff6a4d164e54f32e86d9a52c3446dd70dd847791c6e631a6ac42cc032e0a2fdb` |
| [Jovan Mikić, *On new divisibility properties of generalized central trinomial coefficients and Legendre polynomials*, arXiv:2311.14623v1](https://arxiv.org/pdf/2311.14623v1) | Theorem 8 concerns the highest power of the fixed parameter \(b\) dividing \(T_n(a,b)\) and assumes \(\gcd(a,b)=1\).  Here \(A_n=T_n(2,2)\), so the hypothesis fails; a fixed-parameter valuation would not control moving primes \(p\asymp n\) anyway. | `ecd46f987961a8bfc821d652bd94d123ce2f374f3c7e96198100ed976fdccee6` |

Searches also covered `A006139`, generalized-central-trinomial prime
divisors, primitive and nonprimitive parts, largest prime factors, moving
prime windows, holonomic sequences, and Legendre resultants.  The local
mathlib search found the explicit Chebyshev bound, binomial Lucas theorem,
and general resultant infrastructure, but no theorem for this generalized
central-trinomial moving radical.

No checked source proves \(M_n=o(n)\), any fixed-band little-o estimate, or
the first-band estimate.  This is a bounded negative search result, not a
novelty claim.

## 10. Reproduction, hygiene, and frozen pins

Run:

```bash
python work/ultrapi-resume/gauss_medium_prime_radical_check.py
python work/ultrapi-resume/gauss_medium_prime_radical_independent_check.py
```

The independent checker's exact output begins:

```text
PASS: independent definitions, central coefficients, one-digit Lucas identity, and W/M containment on 12459 medium-prime pairs; 130317 exact integer exponentiations of the every-(n,B) error bound passed
PASS: 359 band partitions, 1475 eventual fixed-band instances, 426 exact endpoint-selector containments, 470 scaled Schur/Holt divisibility checks, and 16 resultant-lemma instances passed
BOUNDARY: exact resultant table = [(20, 3, 17, 3, False, 'direct'), (21, 4, 17, 4, True, 'direct'), (29, 4, 17, 4, True, 'reflected'), (30, 7, 23, 7, True, 'direct')]
EXPERIMENT: 16069 finite Lucas congruences were replayed exactly; finite data prove no little-o estimate, no exceptional-gcd bound, and no V1 claim
```

Final frozen pins:

- target:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`;
- corrected primary report:
  `32b2c01875d03f2ae2c683622fde1a199af2b220d92c3db1b1633313bf4e98d6`;
- unchanged primary checker:
  `8c7909127936dc0853d34158a689675ac93271586de6b5c148cd9fa1faf2af2f`;
- independent checker:
  `06406bb8e3fd4ea048a095e00fdaea4dee586820d22efcb5407b1d92c4a02f14`;
- this audit: compute SHA-256 with the literal token
  `INDEPENDENT_AUDIT_SHA256` left in this line, avoiding a self-hash paradox.

The audit passes the reduction, not the missing asymptotic.  The exact
remaining blocker is the pointwise medium-prime radical (or already its
first fixed band), and there is no V1 resolution claim.
