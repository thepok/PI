# Gauss compact core: a medium-prime radical and fixed-band reduction

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

The remaining estimate

\[
 W_n:=\sum_{\substack{\sqrt n<p<n\\p\ {\rm odd\ prime}\\
                       p\mid A_{n\bmod p}}}\log p=o(n),       \tag{1}
\]

where

\[
 A_j=2^jU_j=T_j(1,2,2)=[X^j](X^2+2X+2)^j,                   \tag{2}
\]

has **not** been proved.  Consequently the exceptional Gauss--Lambert gcd
has not been proved subexponential, and this route proves no fixed-sixteen
return and no decimal-cylinder hit.  Canonical V1 remains a `conjecture`.

The compact-core selector can, however, be removed completely up to an
unconditional sublinear error.  Define the medium-prime radical weight

\[
 M_n:=\sum_{\substack{\sqrt n<p<n\\p\ {\rm odd\ prime}\\
                       p\mid A_n}}\log p.                    \tag{3}
\]

Then for every integer \(B\ge1\) and every integer \(n\ge2\),

\[
 \boxed{
  0\le M_n-W_n\le
  \vartheta\!\left({n\over B+1}\right)
  +{\log5\over2}B(B+1),
 }                                                           \tag{4}
\]

where \(\vartheta(x)=\sum_{p\le x}\log p\).  In particular, with
\(B=\lfloor n^{1/3}\rfloor\), Chebyshev's estimate gives

\[
                    M_n=W_n+O(n^{2/3}).                       \tag{5}
\]

Thus the missing statement has the exact equivalent form

\[
 \boxed{
 W_n=o(n)
 \quad\Longleftrightarrow\quad
 \log\!\prod_{\substack{\sqrt n<p<n\\p\mid A_n}}p=o(n).
 }                                                           \tag{6}
\]

This is a pointwise theorem about the square-free part of one integer
\(A_n\) contributed by primes between \(\sqrt n\) and \(n\).  It is not a
fixed-prime zero-density statement and is not implied by a largest-prime-
factor theorem.

There is a second equivalent localization.  For each integer \(a\ge1\), put

\[
 W_{n,a}:=
 \sum_{\substack{\sqrt n<p<n\\p\ {\rm odd\ prime}\\
                   \lfloor n/p\rfloor=a\\p\mid A_{n\bmod p}}}
       \log p.                                               \tag{7}
\]

Then

\[
 \boxed{
 W_n=o(n)
 \quad\Longleftrightarrow\quad
 \text{for every fixed }a\ge1,\quad W_{n,a}=o(n).
 }                                                           \tag{8}
\]

For each fixed \(a\), the Lucas congruence also makes (7), for all
sufficiently large \(n\), exactly the \(a\)-th prime-factor band of \(A_n\):

\[
 W_{n,a}=
 \sum_{\substack{n/(a+1)<p\le n/a\\p\ {\rm odd\ prime}\\
                   \sqrt n<p<n\\p\mid A_n}}\log p.          \tag{9}
\]

In the first band there is no exceptional threshold at all, because
\(A_1=2\):

\[
 \boxed{
 W_{n,1}=\sum_{\substack{n/2<p<n\\p\ {\rm odd\ prime}\\
                           p\mid A_n}}\log p.
 }                                                           \tag{10}
\]

Consequently even the irreducible first task is already the pointwise claim
that the prime divisors of \(A_n\) in \((n/2,n)\) have logarithmic weight
\(o(n)\).  No proof of (10)'s little-o estimate was found.

Equations (4)--(10) and the resultant lemma below are a `proof sketch` with
all quantifiers exposed and complete derivations.  They are not yet a Lean
formalization.  The bounded primary-source search is `literature-checked` as
of the date above.  The companion exact replay is an `experiment` in its
finite-search portions.  Nothing here is a `machine-checked`, `candidate
resolution`, or `verified resolution` of V1.

## 1. Exact statement and ambiguous quantifiers

The canonical target asks whether every **finite** word over
\(\{0,\ldots,9\}\), including words with leading zeroes, occurs contiguously
in the usual nonterminating decimal expansion of \(\pi\).  The immutable
source distinguishes this from infinite contiguous words and from arbitrary
subsequences.  This note changes none of those quantifiers.

The quantifiers in the arithmetic claim are:

- (1), (3), (5), (6), and (8) concern every integer \(n\to\infty\), not a
  subsequence or an average over \(n\);
- the parameter \(B\) in (4) is an integer and (4) holds for every pair
  \(n\ge2,B\ge1\);
- “for every fixed \(a\)” in (8) means that \(a\) is held constant before
  \(n\to\infty\); it is not a uniform assertion for \(a\le\sqrt n\);
- all prime intervals in (1), (3), and (7)--(10) retain their displayed
  strict or weak endpoints exactly.

Finite factorization data cannot prove any of the little-o statements.

## 2. The one-digit Lucas identity

The positive coefficient formula in (2) gives

\[
                         1\le A_j\le5^j.                     \tag{11}
\]

For every odd prime \(p\), every integer \(a\ge0\), and every
\(0\le s<p\), Noe's generalized Lucas congruence specializes to

\[
                         A_{ap+s}\equiv A_aA_s\pmod p.       \tag{12}
\]

It also follows directly from the previously established Lucas congruence
for \(U_j\).  Indeed,
\(U_{ap+s}\equiv U_aU_s\pmod p\), and Fermat's theorem gives

\[
 2^{ap+s}U_{ap+s}\equiv2^{a+s}U_aU_s
                    \equiv A_aA_s\pmod p.
\]

Now fix \(n\ge2\) and an odd prime \(\sqrt n<p<n\), and write

\[
                        n=ap+s,\qquad0\le s<p.               \tag{13}
\]

The strict bounds imply \(1\le a<p\).  Equations (12)--(13) give

\[
 p\mid A_n\quad\Longleftrightarrow\quad
 p\mid A_a\ \text{ or }\ p\mid A_s.                         \tag{14}
\]

Since membership in (1) is exactly \(p\mid A_s\), (14) immediately proves
\(W_n\le M_n\).  More precisely,

\[
 \{p:M_n\setminus W_n\}
 =\{p:\sqrt n<p<n,\ p\mid A_a,\ p\nmid A_s\}.              \tag{15}
\]

The equality \(M_n=W_n\) is false at finite depth.  At \(n=68\), for
example, \(p=17\) has \(a=4,s=0\), with
\(17\mid A_4=136\) but \(17\nmid A_0=1\).  Thus it contributes to \(M_{68}\)
but not to \(W_{68}\).  The error estimate must account for precisely these
earlier-index factors.

## 3. Proof of the medium-radical error bound

Split the primes in (15) according to whether \(a>B\) or \(a\le B\).
If \(a>B\), integrality gives \(a\ge B+1\), and hence

\[
                         p\le {n\over B+1}.                  \tag{16}
\]

Their total logarithmic weight is at most
\(\vartheta(n/(B+1))\).

For a fixed \(1\le a\le B\), all the remaining distinct primes divide the
single positive integer \(A_a\).  Their product therefore divides \(A_a\),
and (11) gives

\[
 \sum_{\substack{p\ {\rm in}\ (15)\\\lfloor n/p\rfloor=a}}
       \log p
 \le\log A_a\le a\log5.                                    \tag{17}
\]

Summing (17) over \(a\le B\), and adding (16), proves (4).

Chebyshev's theorem supplies absolute constants \(C_\vartheta,x_0>0\) such
that \(\vartheta(x)\le C_\vartheta x\) for all \(x\ge x_0\).  With
\(B=\lfloor n^{1/3}\rfloor\), equation (4) is therefore bounded by

\[
 C_\vartheta{n\over B+1}+{\log5\over2}B(B+1)=O(n^{2/3}),    \tag{18}
\]

with an absolute implied constant and for every sufficiently large integer
\(n\).  This proves (5), and division by \(n\) proves (6).

Another exact interpretation is useful.  Every prime \(p<n\) dividing
\(A_n\) is nonprimitive for the sequence \((A_j)\): equation (14) puts it in
\(A_a\) or \(A_s\) at a smaller index.  Thus (6) asks for a subexponential
bound on one specified part of the nonprimitive radical of \(A_n\).  Merely
proving that \(A_n\) has one primitive prime divisor would be far weaker.

## 4. Proof of the fixed-band equivalence

The implication from (1) to every assertion on the right of (8) follows
from positivity, since \(0\le W_{n,a}\le W_n\).

Conversely, assume that for each fixed positive integer \(a\),
\(W_{n,a}/n\to0\).  For fixed \(k\), the finite sum

\[
                 D_n(k):=\sum_{1\le a\le k}W_{n,a}          \tag{19}
\]

also satisfies \(D_n(k)/n\to0\).  Recursively choose a strictly increasing,
hence unbounded, sequence of integers \(N_k\) so large that

\[
 n\ge N_k\quad\Longrightarrow\quad
 {W_{n,a}\over n}\le {1\over k^2}
 \quad(1\le a\le k).                                       \tag{20}
\]

For \(n\ge N_1\), define \(B(n)\) to be the largest \(k\) with
\(N_k\le n\); define it arbitrarily for the finitely many earlier \(n\).
Then \(B(n)\to\infty\), and (20) gives, for \(n\ge N_1\),

\[
                         D_n(B(n))\le {n\over B(n)}.         \tag{21}
\]

Every prime in the complementary bands has \(a>B(n)\), hence by (16) its
weight is at most \(\vartheta(n/(B(n)+1))=O(n/B(n))\).
Equations (21) and Chebyshev's bound prove \(W_n=o(n)\), establishing (8).
This is an existence diagonal; it does not assume uniform convergence in
\(a\).

For (9), fix \(a\).  The primes with \(\lfloor n/p\rfloor=a\) lie in

\[
                         {n\over a+1}<p\le {n\over a}.       \tag{22}
\]

As \(n\to\infty\), the lower endpoint tends to infinity.  Eventually none
of these primes divides the fixed nonzero integer \(A_a\).  Equation (14)
then says \(p\mid A_n\) if and only if \(p\mid A_s\), proving (9), with the
original \(\sqrt n<p<n\) restrictions retained.  When \(a=1\), the only
prime divisor of \(A_1=2\) is excluded from the odd-prime sum, so the same
argument is exact without an eventual threshold and gives (10).

The affine reflection from the preceding audit can additionally remove an
\(o(n)\)-sized endpoint portion of each fixed band.  For fixed \(a\), the
direct and reflected selectors are

\[
                 p={n-t\over a},\qquad
                 p={n+1+t\over a+1}.                         \tag{23}
\]

For \(0\le t\le\eta n\), their primes lie in two intervals of total relative
length \(O_a(\eta)\).  The prime number theorem gives, for every fixed
\(a\) and fixed \(\eta>0\), total logarithmic weight
\(O_a(\eta n)+o_a(n)\).  Taking \(n\to\infty\) and then
\(\eta\downarrow0\), or choosing a sufficiently slow diagonal
\(\eta(n)\downarrow0\), makes this endpoint contribution \(o(n)\).  The
unresolved portion of each fixed band can therefore be required to have
\(t\ge\eta(n)n\); it still contains the genuine proportional-index core.

## 5. Why the second Legendre resultant does not separate selected primes

Let

\[
                         L_j(X)=2^jP_j(X)\in\mathbb Z[X],    \tag{24}
\]

where \(P_j\) is the Legendre polynomial.  A tempting continuation is to
combine the already known identity
\(\operatorname{Res}(X^2+1,L_t)=A_t^2\) with a resultant between
\(L_t\) and the affine-depth polynomial \(L_n\).  There is a universal
factor which makes this ineffective.

For every odd prime \(p\), every \(0\le a<p\), and every
\(1\le t\le(p-1)/2\), the scaled Schur congruence gives

\[
                         L_{ap+t}\equiv L_a^pL_t\pmod p.     \tag{25}
\]

Here the superscript \(p\) denotes polynomial exponentiation; equivalently,
\(L_a(X)^p=L_a(X^p)\) over \(\mathbb F_p\).  The scaled Holt reflection is
\(L_{p-1-t}\equiv2^{-2t}L_t\pmod p\), so similarly

\[
             L_{ap+p-1-t}\equiv
             2^{-2t}L_a^pL_t\pmod p.                         \tag{26}
\]

Because \(2t<p\), the leading coefficient
\(\binom{2t}{t}\) of \(L_t\) is a \(p\)-adic unit.  The elementary
resultant lemma

\[
 f\mid g\pmod p,\quad\deg f=t,\quad p\nmid\operatorname{lc}(f)
 \quad\Longrightarrow\quad p^t\mid\operatorname{Res}(g,f) \tag{27}
\]

therefore proves

\[
 \boxed{
 p^t\mid\operatorname{Res}(L_{ap+t},L_t),\qquad
 p^t\mid\operatorname{Res}(L_{ap+p-1-t},L_t).
 }                                                           \tag{28}
\]

For completeness, (27) follows by dividing \(g\) by \(f\) over
\(\mathbb Z_p[X]\).  The remainder has every coefficient in
\(p\mathbb Z_p\), and the resultant is, up to a \(p\)-adic unit, the
determinant of multiplication by that remainder on the free rank-\(t\)
algebra \(\mathbb Z_p[X]/(f)\).  Every matrix entry is divisible by \(p\),
so its determinant is divisible by \(p^t\).

Crucially, (28) uses neither \(p\mid A_t\) nor \(p\mid X^2+1\) in any
quotient algebra.  It holds for every affine candidate.  Exact examples show
that the baseline can be sharp on both sides of the selector:

| \(n\) | \(t\) | \(p\) | branch | \(p\mid A_t\)? | \(v_p\operatorname{Res}(L_n,L_t)\) |
|---:|---:|---:|:---|:---:|---:|
| 20 | 3 | 17 | direct | no | 3 |
| 21 | 4 | 17 | direct | yes | 4 |
| 29 | 4 | 17 | reflected | yes | 4 |
| 30 | 7 | 23 | direct | yes | 7 |

Thus dividing out the forced \(p^t\) leaves no extra factor even in these
selected cases.  The natural two-Legendre resultant does not distinguish the
primes in (1), so it supplies no bound for (6) or (10).

## 6. Finite falsification and interpretation

The companion checker supplies the following `experiment` through
\(n=10{,}000\):

- it finds 7,803 \(W\)-pairs and 13,053 medium-radical pairs;
- all 5,250 discrepancies have exactly the earlier-index source in (15);
- at the dyadic upper endpoints \(100,1000,10000\), the largest observed
  \(M_n/n\) on the upper half intervals is respectively
  \(0.14937799005006983\), \(0.04120263576814949\), and
  \(0.007668862297463097\).

The decreasing finite ratios are consistent with (6) but prove no
asymptotic statement.  The exact witness at \(n=68\) also falsifies the
stronger proposed identity \(M_n=W_n\), while (4) explains why that failure
is asymptotically harmless if only a sublinear error is needed.

The reduction changes the best next question.  More fixed-prime automatic
zero counts are not enough.  A successful continuation must prove a
pointwise estimate for the medium-prime radical of \(A_n\), or at minimum
prove the fixed-band estimates in (8), beginning with the explicit first
band (10).

## 7. Literature search

Search date: **2026-08-12 UTC**.  Queries included the exact sequence
`A006139`, generalized central trinomial prime divisors, primitive and
nonprimitive parts, greatest prime factors, Legendre-polynomial resultants,
and prime divisors of holonomic sequences.

- Tony D. Noe,
  [*On the Divisibility of Generalized Central Trinomial Coefficients*,
  J. Integer Sequences 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf),
  proves the generalized Schur/Lucas and Holt congruences used in (12),
  (25), and (26).  PDF SHA-256:
  `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c`.
- Stephan Wagner,
  [*Asymptotics of generalised trinomial coefficients*,
  arXiv:1205.5402v3 (2012 preprint)](https://arxiv.org/pdf/1205.5402v3),
  gives coefficient asymptotics for this class.  Those asymptotics control
  \(\log A_n\), not the moving prime-factor window (3).  PDF SHA-256:
  `5b4696abb4b9c40ef48203dda749f4c290a3ba215dcb1de2c12bb5eb78bdec28`.
- Nadav Kohen,
  [*Density and Symmetry in the Generalized Motzkin Numbers mod \(p\)*,
  arXiv:2411.03681v2](https://arxiv.org/pdf/2411.03681v2), studies the first
  \(p\) generalized-central-trinomial coefficients for a **fixed** prime and
  explicitly treats related no-zero observations heuristically.  It does not
  prove the pointwise cross-prime radical estimate (6).  PDF SHA-256:
  `f4c604453c2b81a48dd3ee56aabab0ef3a6a78b0d14a21a2b323bd4818d6db42`.
- Zhi-Wei Sun,
  [*New observations on primitive roots modulo primes*,
  Nanjing Univ. J. Math. Biquarterly 36 (2019), 108--133](https://arxiv.org/pdf/1405.0290),
  states primitive-prime-divisor assertions even for the ordinary central
  trinomial and several neighboring combinatorial sequences as conjectures.
  This is contextual only: those are different sequences, and existence of
  one primitive divisor would not prove (6).  PDF SHA-256:
  `ff6a4d164e54f32e86d9a52c3446dd70dd847791c6e631a6ac42cc032e0a2fdb`.

No checked primary source in this bounded search proves (6), any one of the
fixed-band little-o estimates in (8), or the first-band estimate following
(10).  Absence from this search is not a novelty claim.

## 8. Reproduction

Run

```bash
python work/ultrapi-resume/gauss_medium_prime_radical_check.py
```

The expected output begins

```text
PASS: W_n is contained in the medium-prime radical M_n on 6369374 strict prime/depth pairs through n=10000; all 5250 M\W pairs came from A_floor(n/p), and 5250 exact cutoff/product groups passed
PASS: one-digit Lucas zeros matched direct integer A_n divisibility on 10027 cases; 444 full direct/reflected Legendre congruences (and divisibility checks) plus the exact resultant table passed
```

The checker generates \(A_n\), prime tables, and every first characteristic
block independently.  It checks (12)--(17) on the stated finite ranges, the
strict \(n=68\) discrepancy, polynomial divisibility on both affine branches,
the full congruences (25)--(26), and the four exact resultant valuations
above.  Floating-point logarithms
occur only in output explicitly labelled `experiment`.

## 9. Handoff

The strongest conclusion is the exact equivalence (6), together with the
fixed-band criterion (8) and exact first band (10).  The remaining Gauss
problem is no longer hidden behind a moving remainder or a compact
two-parameter selector: it is the pointwise medium-prime radical of
\(A006139\).  Neither a generic resultant nor fixed-prime automaticity
controls it.  Until one proves (6), or the weaker numerical constant actually
needed by the Padé obstruction, this branch remains a `proof sketch` and
does not resolve V1.
