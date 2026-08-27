# Independent audit: Gauss prefix-gcd support identity

Audit date: **2026-08-13 UTC**

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Primary report:
[`gauss_prefix_gcd_exact_circularity_20260813.md`](gauss_prefix_gcd_exact_circularity_20260813.md)

Primary checker:
[`gauss_prefix_gcd_exact_circularity_20260813_check.py`](gauss_prefix_gcd_exact_circularity_20260813_check.py)

Independent checker:
[`gauss_prefix_gcd_exact_circularity_independent_check_20260813.py`](gauss_prefix_gcd_exact_circularity_independent_check_20260813.py)

Original source URL: none. The canonical target is Marcel's human-authored local
question, so no external source URL is invented.

## Verdict

**PASS on the mathematics, with one bibliographic correction and one source-pin
addition recorded below.** I first tried to break the coefficient convention, both
prime cases, the strict endpoint, the generalized Lucas step at indices exceeding
\(p^2\), the radical equality, and the claimed asymptotic equivalence. None of those
attempts produced a counterexample or a gap.

The independently rederived result is exactly

\[
 \operatorname{rad}_{<n}^{\rm odd}
 \gcd\!\left(\operatorname{odd}(A_n),
       \operatorname{odd}\!\prod_{1\le r\le\lfloor(n-1)/3\rfloor}A_r\right)
 =\operatorname{rad}_{<n}^{\rm odd}(A_n)                  \tag{A1}
\]

for every integer \(n\ge2\), where

\[
                       A_m=[x^m]\,(1+2x+2x^2)^m.           \tag{A2}
\]

It follows that the logarithm of the left side in (A1) is \(o(n)\) if and
only if

\[
 M_n=\sum_{\substack{\sqrt n<p<n\\p\ {\rm odd\ prime}\\p\mid A_n}}
       \log p=o(n).                                       \tag{A3}
\]

This is an exact repackaging of the previously isolated medium-prime radical,
not a proof of (A3). The full gcd is only a sufficient, strictly enlarged target:
it also retains valuations and common primes at least \(n\). Canonical V1 remains
a `conjecture`; (A1)--(A3) are a `proof sketch`; the bounded source audit is
`literature-checked` as of the date above; and all finite replay output is an
`experiment`. Nothing here is `machine-checked`, a `candidate resolution`, or a
`verified resolution`.

Frozen inputs were unchanged during this audit:

- primary report SHA-256:
  `e7faee8c575b526e79bc7488ae61d3b7fb88012a2257ec60c6a442eabe6a083e`;
- primary checker SHA-256:
  `7d2f857c8c35c4d5a8783dd885ba2e20c8a100624ad197ffc2130eee2d72b8de`;
- canonical target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

## 1. Refutation attempts and normalization

Reversal of the degree-\(2m\) polynomial gives

\[
 [X^m]\,(X^2+2X+2)^m=[x^m]\,(1+2x+2x^2)^m.
\]

Choosing \(k\) quadratic terms forces \(m-2k\) linear terms and \(k\)
constant terms. Thus

\[
 A_m=\sum_{0\le k\le m/2}
      {m\choose k}{m-k\choose m-2k}2^k2^{m-2k}
    =\sum_{0\le k\le m/2}{m\choose2k}{2k\choose k}2^{m-k}. \tag{A4}
\]

This gives \(A_0=1,A_1=2,A_2=8\). Replacing \(2x^2\) by \(4x^2\)
instead gives \(12\) at \(m=2\); the primary report correctly excludes that
normalization.

With \(L(x)=x+2+2x^{-1}\), one also has
\(A_m=\operatorname{ct}L(x)^m\).
Constant-term summation yields

\[
 \sum_{m\ge0}A_mz^m=(1-4z-4z^2)^{-1/2},                  \tag{A5}
\]

and differentiating (A5) gives

\[
 (m+1)A_{m+1}=2(2m+1)A_m+4mA_{m-1}.                     \tag{A6}
\]

The positive dominant singularity of (A5) is

\[
 \rho={\sqrt2-1\over2}={1\over2+2\sqrt2}.
\]

The other zero of \(1-4z-4z^2\) has larger modulus. The standard simple
square-root singularity estimate therefore gives

\[
 A_m=\Theta\!\left({(2+2\sqrt2)^m\over\sqrt m}\right),
 \qquad
 \log A_m=m\log(2+2\sqrt2)+O(\log m).                    \tag{A7}
\]

Thus the primary exponential-scale statement is exact. It supplies only a
linear bound for \(\log G_n\), not the required little-o bound.

## 2. Lucas product and reflection, derived independently

Let \(p\) be odd and write \(m=ap+s\), \(0\le s<p\). In characteristic
\(p\), the Frobenius identity gives

\[
 L(x)^{ap+s}=L(x^p)^aL(x)^s.
\]

Every exponent in \(L(x)^s\) lies strictly between \(-p\) and \(p\), while
every exponent in \(L(x^p)^a\) is a multiple of \(p\). A product term has
exponent zero only when the exponent in each factor is zero. Hence

\[
                         A_{ap+s}\equiv A_aA_s\pmod p.     \tag{A8}
\]

Iteration proves the full base-\(p\) product

\[
 m=\sum_jd_jp^j
 \quad\Longrightarrow\quad
                         A_m\equiv\prod_jA_{d_j}\pmod p.  \tag{A9}
\]

This argument includes arbitrarily many digits; it is not restricted to
\(m<p^2\).

For the reflection, put \(q=(p-1)/2\). Coefficientwise through degree
\(p-1\), generalized binomial coefficients give

\[
 (1-2y-y^2)^q
   \equiv\sum_{s=0}^{p-1}{A_s\over2^s}y^s\pmod p.         \tag{A10}
\]

The potentially dangerous upper half is valid: when \(q<k<p\), both
\({q\choose k}\) and \({-1/2\choose k}\) vanish modulo \(p\), the latter
because its numerator contains the factor \(-p/2\). The reciprocal identity

\[
 y^{p-1}(1-2/y-y^{-2})^q
 =(y^2-2y-1)^q=(-1)^q(1+2y-y^2)^q                       \tag{A11}
\]

then gives, for \(0\le s\le q\),

\[
                 A_{p-1-s}\equiv(-4)^{q-s}A_s\pmod p.    \tag{A12}
\]

Its scalar is nonzero, so divisibility is invariant under
\(s\leftrightarrow p-1-s\). This agrees with Noe's discriminant
\(d=2^2-4(1)(2)=-4\).

## 3. Exact support identity and all boundaries

Fix \(n\ge2\), an odd prime \(p<n\), and suppose \(p\mid A_n\). By (A9),
some base-\(p\) digit \(d\) of \(n\) satisfies \(p\mid A_d\). Since
\(A_0=1\), \(d\ne0\). Equation (A12) and \(A_0=1\) also rule out
\(d=p-1\).

If \(p\le2n/3\), set \(r=\min(d,p-1-d)\). Then \(p\mid A_r\) and

\[
 1\le r\le{p-1\over2}\le{n-1\over3},                    \tag{A13}
\]

so \(p\) divides the prefix product.

If \(p>2n/3\), then \(p<n<3p/2<2p\), so \(n=p+s\) with
\(1\le s<p\). Equation (A8) becomes

\[
                         A_n\equiv A_1A_s=2A_s\pmod p.    \tag{A14}
\]

Because \(2\) is a unit and \(3s=3(n-p)<n\), one gets

\[
               p\mid A_s,
 \qquad 1\le s\le\left\lfloor{n-1\over3}\right\rfloor. \tag{A15}
\]

The two cases are exhaustive. They include the integer rounding in (A13)--(A15);
no equality or parity case is omitted. The endpoint \(p=n\) is intentionally absent,
and in fact (A8) gives \(A_p\equiv A_1=2\pmod p\) for every odd prime.
The prime \(2\) is intentionally removed by `odd`. Conversely, every odd prime
in the gcd already divides \(A_n\). These observations prove (A1) with exactly
the displayed strict condition \(p<n\).

## 4. Medium-prime equivalence and the circularity boundary

Let \(E_n\) be the logarithm of either side of (A1). Removing from \(E_n\)
the terms with \(\sqrt n<p<n\) leaves exactly a subset of the odd primes at
most \(\sqrt n\). Therefore

\[
                     0\le E_n-M_n\le\vartheta(\sqrt n).   \tag{A16}
\]

Chebyshev's elementary bound \(\vartheta(x)=O(x)\) already implies that the
right side is \(o(n)\). Positivity and (A16) prove both directions of

\[
                         E_n=o(n)\Longleftrightarrow M_n=o(n). \tag{A17}
\]

This is the precise sense in which the truncated radical proposal is
circular: it is equivalent, up to a proved \(o(n)\) term, to the existing
unproved target. It is not a logically circular proof, because no proof of
either side is claimed.

The full integer gcd is different. The independent replay confirms

\[
 G_{226}=131\cdot263\cdot577\cdot24071,
 \qquad
 G_{76}=17^2\cdot23\cdot97.                               \tag{A18}
\]

For the first row, the primes \(263,577,24071\ge226\) have prefix witnesses
\(r=30,36\), \(r=41\), and \(r=42\), respectively. The second row confirms
that a repeated prime survives. Thus \(\log G_n=o(n)\) would imply (A3), but
it additionally requires control of prime powers and common primes at least
\(n\). The finite small ratios in the primary report are only an `experiment`
and cannot establish this pointwise asymptotic.

## 5. Primary-source and mathlib audit

The mathematical source claims are supported, but the primary report has a
non-mathematical title error: Zheng Xiao's frozen v2 paper is titled
*Greatest common divisors for polynomials in almost units and applications to
linear recurrence sequences*, not “polynomials in algebraic numbers.” Its
abstract describes gcd bounds and applications to linear recurrence sequences;
Definition 2.3 explicitly defines those recurrences with constant coefficients,
and Theorem 1.5 gives the application. This does not cover the P-recursive sequence
(A2) or its growing prefix product.

The checked source records are:

| Source | Exact locator used | Independently checked PDF SHA-256 |
|---|---|---|
| [Tony D. Noe, *On the Divisibility of Generalized Central Trinomial Coefficients*](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf), JIS 9 (2006), Article 06.2.7 | Equations (1)--(4) fix the coefficient, generating function, and recurrence; equations (13)--(14), Theorem 8.6, Lemma 9.4, and Theorem 9.1 give the Lucas and nonzero-scalar reflection laws. | `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c` |
| [Eric Rowland and Reem Yassawi, *Automatic congruences for diagonals of rational functions*, arXiv:1310.8635v2](https://arxiv.org/pdf/1310.8635v2) | Section 5.1, especially Theorems 5.1--5.2 and the paragraph following Theorem 5.2, gives fixed-characteristic automata and Lucas products, including Noe's family. It gives no moving-prime pointwise estimate. | `17ff14e22d4dce2c8f0723dc9273ee888239b853d3cf0c556134da089a868c4d` |
| [Zheng Xiao, *Greatest common divisors for polynomials in almost units and applications to linear recurrence sequences*, arXiv:2110.01751v2](https://arxiv.org/pdf/2110.01751v2) | Abstract, Theorem 1.5, and Definition 2.3. The Subspace Theorem machinery concerns constant-coefficient linear recurrences, not (A2). | `e631a86a1e94f172a113ed648d0841075a210527f3fba0c200adbca450f0f6ab` |

The Noe pin matches two separately retained frozen copies from earlier source
audits; the official JIS landing page confirms the author, title, volume, year,
and article number. A fresh official PDF request returned HTTP 503 during this
audit, so that failed request was not treated as a new pin. The Rowland--Yassawi
v2 pin above fills the primary report's missing version/pin. Xiao v2 was freshly
downloaded and matched the primary report's recorded hash.

The local mathlib paths named by the primary report exist. The Lucas file proves
ordinary binomial Lucas congruences, the shifted-Legendre file develops shifted
Legendre polynomials, and `Mathlib/NumberTheory/Chebyshev.lean` contains
`Chebyshev.theta_le_log4_mul_x`. A bounded symbol search found no ready theorem
for the generalized sequence (A2), identity (A1), or a P-recursive prefix-gcd
little-o estimate. This is a bounded negative search, not a novelty claim.

## 6. Reproduction and handoff

Run the frozen primary checker and the independent implementation:

```bash
.venv/bin/python work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813_check.py
.venv/bin/python work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_independent_check_20260813.py
```

The independent implementation does not import or execute the primary checker. It
recomputes the sequence from the differential recurrence, checks a direct
multinomial formula, exercises the full Lucas product and scalar reflection, tests
both witness branches and exact support through \(n=1200\), and recomputes (A18).

The useful handoff is negative but exact: the below-\(n\), square-free prefix gcd
cannot be advertised as a new cross-characteristic estimate. Any genuine advance
must bound the medium-prime radical itself or exploit the additional valuation and
large-common-prime structure of the untruncated gcd. No formal code changed, so no
new axiom-audit entry or `scripts/check.ps1` claim is made.
