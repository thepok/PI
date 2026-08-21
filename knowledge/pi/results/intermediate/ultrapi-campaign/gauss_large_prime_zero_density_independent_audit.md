# Independent audit: Gauss large-prime zero-density reduction

Audit date: **2026-08-12 UTC**

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Primary artifact:
[`gauss_large_prime_zero_density_reduction.md`](gauss_large_prime_zero_density_reduction.md)

Primary checker:
[`gauss_large_prime_zero_density_check.py`](gauss_large_prime_zero_density_check.py)

Independent checker:
[`gauss_large_prime_zero_density_independent_check.py`](gauss_large_prime_zero_density_independent_check.py)

## Verdict and claim status

**PASS after five narrow corrections.**  I found no mathematical error in
the corrected normalization, Gaussian resultant identity, signed reflection,
two affine selectors, compact-core restriction, or integer-parameter tail
bound.  Equations (3)--(9) are a `proof sketch`; the finite replays are an
`experiment`; and the bounded primary-source audit is `literature-checked`
as of the date above.

The estimate

\[
 \sum_{\substack{\sqrt n<p<n\\p\ {\rm odd\ prime}\\
                  p\mid U_{n\bmod p}}}\log p=o(n)
\]

is not proved.  Therefore the odd exceptional gcd is not proved
subexponential, no decimal cylinder is proved to be hit, and canonical V1
remains a `conjecture`.  This work is not `machine-checked`, a `candidate
resolution`, or a `verified resolution`.

## Corrections made during this audit

The pre-audit primary report had SHA-256
`dfe56e53ddd7570b91a774a808ca6a7749173498e362ef3b804a7449e1627ecf`;
the pre-audit checker had SHA-256
`039014ee19646089f9bf96cccc4873cba452bf5a96f3804034da79c529e609db`.
The following corrections are included in the final pins below.

1. The report formerly quantified \(B\) as real in (8).  Its proof used
   \(a>B\Rightarrow a\ge B+1\), which is false for nonintegral \(B\), for
   example \(B=3/2,a=2\).  The corrected theorem requires an integer
   \(B\ge1\), as does (27).  The advertised choice
   \(B=\lfloor n^{1/3}\rfloor\) was already integral, so (9) and the
   compact-core equivalence are unchanged.  An alternative valid real
   formulation would replace \(B+1\) by \(\lfloor B\rfloor+1\).
2. Two carriage-return control bytes had corrupted `\rm` in displayed
   formulas.  They were removed, and a full C0-byte scan is now clean.
3. The primary checker used `round(n ** (1 / 3))` and floating logarithms in
   assertions described as exact.  It now computes the floor cube root by
   integer comparisons and checks the tail premises through exact cutoff
   membership and prime-product divisibility.  Floating logarithms remain
   only in output explicitly labelled `experiment`.
4. Sun's paper was incorrectly cited as an Acta Arithmetica article.  Its
   correct publication is *Science China Mathematics* 57 (2014),
   1375--1400.  The citation and versioned arXiv link are corrected.  The
   Kohen entry now says explicitly that its no-zero-prime heuristic concerns
   the ordinary central-trinomial sequence, not the exact sequence here.
5. The report now makes the converse selector's integer domains explicit and
   clarifies that \(X^2+1\mid L_t\) in (20) is divisibility in
   \(\mathbb F_p[X]\).  It remains valid for \(p\equiv3\pmod4\); no root of
   \(X^2+1\) in \(\mathbb F_p\) is being assumed.

These corrections narrow domains, repair provenance and formatting, and make
the computation match its description.  They do not supply the missing
asymptotic estimate.

## 1. Normalization: equations (11)--(15)

The generating-function rescaling is exact:

\[
 \sum_{t\ge0}2^tU_tx^t
 =F(2x)=(1-4x-4x^2)^{-1/2}.
\]

Noe's generalized-central-trinomial formula at parameters \((1,2,2)\) gives

\[
 A_t=\sum_{0\le k\le t/2}
 {t\choose2k}{2k\choose k}2^{t-k}
 =[X^t](X^2+2X+2)^t.
\]

Reversing the quadratic swaps its first and last coefficients but leaves the
central coefficient unchanged, so this agrees with Noe's convention.  Every
summand is a positive integer, and the chosen coefficient is at most the sum
of all coefficients, \(5^t\), proving (14).

From

\[
 (1-2zq+q^2)^{-1/2}=\sum_{t\ge0}P_t(z)q^t
\]

with \(z=-i,q=2ix\), one gets
\(A_t=(2i)^tP_t(-i)\), including both signs in (15).  The independent checker
also expands the central coefficient directly through depth 48 and compares
it with a separately generated recurrence table.

## 2. Gaussian remainder and resultant: equations (16)--(20)

Put \(L_t=2^tP_t\).  Equation (15) gives

\[
 L_t(-i)=(-i)^tA_t,
 \qquad L_t(i)=i^tA_t.
\]

These two evaluations are equivalent to the stated remainder

\[
 L_t(X)\equiv
 \begin{cases}
 (-1)^{t/2}A_t,&t\text{ even},\\
 (-1)^{(t-1)/2}A_tX,&t\text{ odd}
 \end{cases}
 \pmod{X^2+1}.
\]

Since the first polynomial in the resultant is monic,

\[
 \operatorname{Res}(X^2+1,L_t)=L_t(i)L_t(-i)=A_t^2.
\]

For every odd prime \(p\), the Euclidean remainder above is zero modulo \(p\)
exactly when \(p\mid A_t\).  This is equivalent to polynomial divisibility by
\(X^2+1\) in \(\mathbb F_p[X]\) whether that quadratic splits or is irreducible.
Finally, \(p^2\mid A_t^2\) is exactly equivalent to \(p\mid A_t\), establishing
all three terms of (20).  The independent checker explicitly exercises every
odd prime through 251, including 29 primes congruent to 3 modulo 4.

The report's negative conclusion is correctly limited: this natural
resultant is precisely the square of the original quantity and provides no
independent height saving.

## 3. Frobenius block and reflection: equations (21)--(23)

Let \(D=1-2x-x^2\), \(m=(p-1)/2\), and
\(F=D^{-1/2}\).  In \(\mathbb F_p[[x]]\),

\[
 H=D^mF(x^p)
 \quad\Longrightarrow\quad
 H^2={D^{p-1}\over D(x^p)}=D^{-1}=F^2.
\]

Both series have constant coefficient one, while \(H+F\) has unit constant
coefficient two, so \(H=F\).  Because \(D^m\) has degree \(p-1\), its coefficients
are exactly \(U_0,\ldots,U_{p-1}\) modulo \(p\), proving (21).

Also

\[
 x^{p-1}D(1/x)^m=(-1)^mD(-x)^m.
\]

Comparing the coefficient of \(x^s\) gives

\[
 U_{p-1-s}\equiv(-1)^{m+s}U_s\pmod p,
\]

with no missing sign.  This was checked against direct polynomial powers
through \(p=257\) and against an independently generated full recurrence block
for every odd prime through 10,000.

## 4. Selector equivalence and boundary audit: equations (4)--(6), (24)--(25)

For a selected prime, strict inequalities \(\sqrt n<p<n\) imply
\(1\le a=\lfloor n/p\rfloor<p\).  Write \(n=ap+s\) and
\(t=\min(s,p-1-s)\).  Reflection gives \(p\mid U_t\), and oddness of \(p\) makes
this equivalent to \(p\mid A_t\).  The definition gives
\(0\le t\le(p-1)/2\), hence the strict integer inequality \(p>2t\).

If \(t=s\), then \(n=ap+t\); if \(t=p-1-s\), then
\(n=(a+1)p-1-t\).  These give the two exact quotients in (6).  They hold
simultaneously exactly when \(2t=p-1\), the central residue.  Substituting
\(p\ge2t+1\) into either expression gives

\[
 (2a+1)t\le n-a.
\]

The converse also holds with the corrected explicit domains.  For integers
\(a\ge1,t\ge0\), either affine identity and \(p>2t\) produce respectively the
residue \(t\) or \(p-1-t\), both in \([0,p-1]\); therefore
\(\lfloor n/p\rfloor=a\) and \(t\) is the reflected minimum.  The hypothesis
\(p\mid A_t\), signed reflection, odd primality, and the original strict size
conditions then reconstruct selection.  The independent checker exhausts
1,371 such affine candidates through \(n=1800\), including direct-only,
reflected-only, and central cases.  It also checks all 7,803 forward selected
pairs through \(n=10{,}000\).  The strict boundaries \(p^2=n\) and \(p=n\) are
excluded exactly as required.

## 5. Tail inequality and floors: equations (8)--(10), (26)--(27)

For integer \(B\), the quotient tail satisfies

\[
 a>B\Longrightarrow a\ge B+1
 \Longrightarrow p\le {n\over B+1}.
\]

Its logarithmic weight is therefore at most
\(\vartheta(n/(B+1))\).  For the endpoint tail, group selected primes by their
unique reflected index \(t\).  The product of the distinct primes in the
\(t\)-group divides \(A_t\), hence its logarithmic weight is at most
\(\log A_t\).  For real \(T\ge1\),

\[
 \sum_{0\le t\le T}\log A_t
 \le\log5\sum_{t=0}^{\lfloor T\rfloor}t
 \le {\log5\over2}T(T+1).
\]

This proves the corrected (8), including all floors.  Chebyshev's
\(\vartheta(x)=O(x)\) and \(B=T=\lfloor n^{1/3}\rfloor\) give

\[
 0\le W_n-C_n(B,T)=O(n^{2/3}),
\]

so (9) and its equivalence to an \(o(n)\) compact-core estimate are valid.
In that core, integer \(t>\lfloor n^{1/3}\rfloor\) implies
\(t>n^{1/3}\), while (25) gives the upper bound in (10).  More generally,
integer-valued \(B\to\infty\) and real-valued \(T=o(\sqrt n)\) give (27).

The independent checker exercises 66,797 combinations of \((n,B,T)\) with exact
cutoff and prime-product divisibility assertions.  It also contains the
explicit arithmetic counterexample to the withdrawn real-\(B\) proof step.

## 6. Fixed-prime zero counts

In the algebraic closure of \(\mathbb F_p\), \(D^m\) has two distinct nonzero
roots, each of multiplicity \(m\), because \(p\) is odd.  Mattarei's
root-multiplicity/weight theorem gives weight at least \(m+1\), hence at most
\((p-1)/2\) zero coefficients among the first \(p\) values.  Equivalently, the
normalized three-term recurrence and nonzero last coefficient rule out two
consecutive zeros.  Neither argument is sublinear in \(p\), as the report says.

More importantly, any fixed-prime bound counts all zero residues for that
one prime, whereas \(W_n\) samples the single diagonal residue \(n\bmod p\) while
\(p\) varies with \(n\).  The report correctly refuses to infer a pointwise
cross-prime estimate from fixed-prime automaticity or finite zero counts.

## 7. Literature audit

The following primary sources were fetched afresh on **2026-08-12 UTC**.

| Primary source | Relevant content checked | PDF SHA-256 |
|---|---|---|
| [Noe, *On the Divisibility of Generalized Central Trinomial Coefficients*](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf), J. Integer Sequences 9 (2006), Article 06.2.7 | Equations (1)--(5), (11)--(14), and Theorem 8.6 give the normalization, Legendre representation, Lucas product, and reflected divisibility symmetry. | `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c` |
| [Kohen, *Density and Symmetry in the Generalized Motzkin Numbers mod p*, v2](https://arxiv.org/pdf/2411.03681v2) | Theorem 4 gives generalized-central-trinomial reflection; Proposition 12 and Corollary 13 reduce fixed-prime densities to first-block data.  The no-zero-prime discussion is explicitly heuristic and concerns the ordinary sequence. | `f4c604453c2b81a48dd3ee56aabab0ef3a6a78b0d14a21a2b323bd4818d6db42` |
| [Mattarei, *Root multiplicities and number of nonzero coefficients of a polynomial*, v2](https://arxiv.org/pdf/math/0512239v2), J. Algebra Appl. 6 (2007), 469--475 | Theorem 2 specializes to weight at least \(m+1\) when \(m<p\); the introduction records the degree-below-characteristic form used here. | `5e9c4f6345a7171b112d16b6eb12b7388334c9123e8d39058d22080e4f031b9d` |
| [Sun, *Congruences involving generalized central trinomial coefficients*, v13](https://arxiv.org/pdf/1008.3887v13), Sci. China Math. 57 (2014), 1375--1400 | Definition, recurrence, square-sum congruences, and parametric congruences for \(T_n(b,c)\); no theorem located there controls this varying-prime affine selector. | `a4540dc374dc9ef0fcad856c9a69c247d345fec94127ac8a6f09353f18995eb1` |

No checked source supplies \(W_n=o(n)\) or an equivalent compact-core estimate.
That bounded negative search result is not a novelty claim.

## 8. Reproduction, pins, and final boundary

Run:

```bash
python work/ultrapi-resume/gauss_large_prime_zero_density_check.py
python work/ultrapi-resume/gauss_large_prime_zero_density_independent_check.py
```

The independent checker prints:

```text
PASS: independent normalization/resultant/reflection and both selector directions on 7803 selected pairs; 1371 converse candidates and 66797 exact tail instances
BOUNDARY: X^2+1 divisibility is in F_p[X] and includes p=3 mod 4; the corrected tail theorem requires integer B
EXPERIMENT: first-block zero record and all three reported W_n/n statistics independently reproduced; no o(n), exceptional-gcd, or V1 claim
```

Final frozen pins:

- target:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- corrected primary report:
  `e7a73b52d5bbf9d8b8f5137f5efd2f4de8267fbf5f355630334b04b97f3b4422`
- corrected primary checker:
  `a48b25ac75b1058140351448baf31f75da6ea81208e56334aeb9005014ef3b5d`
- independent checker:
  `7f04ce2f7a15fb257ea9f28698295dbbb245c6f62db710ea672fcc52b01c14c7`

The strongest audited conclusion is the exact resultant closure and the
integer-parameter compact-core reduction.  It remains a pointwise
large-prime-factor selector problem, not a proof of the required asymptotic
and not a proof that every finite decimal word occurs in \(\pi\).
