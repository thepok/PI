# Gauss first band: two-ray localization and a pointwise-correlation barrier

Status: `conjecture` for canonical V1; the reductions below are a `proof
sketch`, the bounded source search is `literature-checked` as of **2026-08-13
UTC**, and the companion finite replay is an `experiment`.

## Provenance

- Canonical target:
  [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
- Target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Original source URL: none.  The target is Marcel's human-authored local
  question, and no external URL is invented.
- Primary predecessor:
  [`gauss_medium_prime_radical_reduction.md`](gauss_medium_prime_radical_reduction.md)
- Independently audited predecessor:
  [`gauss_medium_prime_radical_independent_audit.md`](gauss_medium_prime_radical_independent_audit.md)

## Outcome

No unconditional proof was found of

\[
 S_n:=\sum_{\substack{n/2<p<n\\p\text{ odd prime}\\p\mid A_n}}\log p=o(n),
 \qquad
 A_m=[X^m](X^2+2X+2)^m.                                    \tag{1}
\]

Thus this attack does not prove the exceptional Gauss--Lambert gcd
subexponential and does not prove a decimal-cylinder hit for \(\pi\).
Canonical V1 remains a `conjecture`.

There are nevertheless three exact advances.

1. The first band is exactly the union of two affine prime-factor rays from
   the **minimal reflected index** \(r\le(n-1)/3\):

   \[
       p=n-r,
       \qquad\text{or}\qquad
       p={n+1+r\over2},
       \qquad p\mid A_r.                                   \tag{2}
   \]

2. Both ends of the \(r\)-interval are harmless.  The already known
   small-\(r\) product bound removes every \(r\le T=o(\sqrt n)\), and the
   prime number theorem also removes a shrinking relative neighborhood of
   the **previously unisolated merger point** \(r=n/3\).  Consequently (1)
   is equivalent to proving the estimate on every fixed proportional core

   \[
              \delta n\le r\le(1/3-\delta)n,
              \qquad 0<\delta<1/6.                          \tag{3}
   \]

3. A rigorous obstruction shows what cannot close (3).  Even hypothetical
   zero sets having at most **one** minimal zero for every prime, together
   with the exact reflection symmetry and no-consecutive-zero property, can
   be arranged to give linear pointwise weight along infinitely many
   depths.  Therefore any proof based only on per-prime zero counts,
   reflection, and zero spacing is logically insufficient.  A genuinely
   cross-prime correlation theorem for the affine rays (2) is needed.

The first-band radical also has an exact one-integer CRT encoding in (18)
below.  Its ambient primorial has logarithm \((1/2+o(1))n\), explaining why
mere CRT packaging or a size bound still stops at linear scale.

## 1. Exact statement and quantifiers

The canonical question is whether every **finite** word over
\(\{0,\ldots,9\}\), including words with leading zeroes, occurs contiguously
in the usual nonterminating decimal expansion of \(\pi\).  It is not a claim
about infinite words or arbitrary subsequences.

This note attacks only the necessary arithmetic estimate (1).  Its
quantifiers are pointwise:

- \(n\) ranges through every positive integer and tends to infinity;
- the prime interval in (1) retains both strict endpoints;
- in (3), \(\delta\) is fixed before \(n\to\infty\), and only afterward may
  \(\delta\downarrow0\);
- an `experiment` at bounded depth cannot establish any little-o statement.

## 2. Lucas reduction and exact two-ray parametrization

For an odd prime \(p\) and \(0\le t<p\), the one-digit generalized Lucas
congruence gives

\[
                         A_{p+t}\equiv A_1A_t=2A_t\pmod p.  \tag{4}
\]

For a prime in (1), write \(t=n-p\).  Then \(0<t<p\), and (4) proves

\[
                         p\mid A_n\quad\Longleftrightarrow\quad p\mid A_t.
                                                                    \tag{5}
\]

The first-block reflection congruence has a nonzero scalar on the right, so

\[
                         p\mid A_t
          \quad\Longleftrightarrow\quad p\mid A_{p-1-t}.    \tag{6}
\]

Put

\[
                         r=\min(t,p-1-t).                    \tag{7}
\]

Then \(0\le r\le(p-1)/2\), \(p\mid A_r\), and exactly one of

\[
 t=r,\quad p=n-r;
 \qquad\text{or}\qquad
 t=p-1-r,\quad p={n+1+r\over2}                              \tag{8}
\]

holds, except at \(t=r=(p-1)/2\), where both descriptions coincide.  Since
\(p\ge2r+1\), either formula in (8) yields

\[
                              3r\le n-1.                    \tag{9}
\]

Conversely, suppose \(1\le r\le(n-1)/3\), \(p\mid A_r\), and either number
in (8) is an odd prime.  Inequality (9) gives \(p\ge2r+1\).  In the direct
case \(n=p+r\); in the reflected case \(n=2p-1-r\).  Thus \(n/2<p<n\), and
(5)--(6) reconstruct \(p\mid A_n\).  The case \(r=0\) contributes nothing
because \(A_0=1\).

Define

\[
\begin{aligned}
 D_n&=\{r:1\le r\le(n-1)/3,\ n-r\text{ prime},\ n-r\mid A_r\},\\
 R_n&=\{r:1\le r\le(n-1)/3,\ (n+1+r)/2\text{ an odd prime},
                                  \ (n+1+r)/2\mid A_r\}.
\end{aligned}                                                \tag{10}
\]

The maps in (10) are injective.  Their images intersect only at the central
candidate

\[
                     r={n-1\over3},\qquad p={2n+1\over3},    \tag{11}
\]

when those quantities are integral and selected.  Equations (8)--(11) are
therefore an exact, duplicate-free encoding of (1).

## 3. Removing both ends of the minimal-index interval

### 3.1 Absolute small-index removal

For a fixed \(n,r\), there are at most two candidate primes in (8).  If both
are distinct and selected, their product divides \(A_r\); at the merger
point there is only one prime.  Since \(1\le A_r\le5^r\), for every real
\(T\ge1\),

\[
 \sum_{\substack{p\text{ selected in }(1)\\r(p)\le T}}\log p
 \le\sum_{1\le r\le T}\log A_r
 \le {\log5\over2}\lfloor T\rfloor(\lfloor T\rfloor+1).   \tag{12}
\]

Hence every \(T=T(n)=o(\sqrt n)\) contributes \(o(n)\).  This uses integer
divisibility, not a probabilistic model for the prime factors.

### 3.2 Relative neighborhoods of all three prime endpoints

Fix \(0<\delta<1/6\).  For \(r<\delta n\), the two rays lie in

\[
 (1-\delta)n<p<n,
 \qquad
 {n\over2}<p<{(1+\delta)n\over2}+1.                         \tag{13}
\]

For \((1/3-\delta)n<r\le(n-1)/3\), they lie in

\[
 {2n+1\over3}\le p<(2/3+\delta)n,
 \qquad
 (2/3-\delta/2)n<p\le{2n+1\over3}.                         \tag{14}
\]

The prime number theorem in Chebyshev form,
\(\vartheta(x)=x+o(x)\), bounds the total logarithmic weight in (13) by
\((3\delta/2)n+o_\delta(n)\), and that in (14) by the same quantity.
Endpoint conventions cost only \(O(\log n)\).  Thus all four pieces together
have weight

\[
                             \le3\delta n+o_\delta(n).       \tag{15}
\]

Let \(I_n(\delta)\) be the selected weight from both rays with the range (3),
counting distinct primes and therefore counting the merger prime only once.
Positivity and (15) prove the exact criterion

\[
 \boxed{
 S_n=o(n)
 \quad\Longleftrightarrow\quad
 I_n(\delta)=o(n)\text{ for every fixed }0<\delta<1/6.
 }                                                           \tag{16}
\]

The forward implication is immediate from \(0\le I_n(\delta)\le S_n\).  For
the reverse implication, take \(n\to\infty\) at fixed \(\delta\) in (15),
obtaining \(\limsup S_n/n\le3\delta\), and then let
\(\delta\downarrow0\).  This order of limits is essential.

Every selected prime satisfies \(\log(n/2)\le\log p\le\log n\).  If \(C_n\)
denotes the number of distinct selected primes, then

\[
 C_n\log(n/2)\le S_n\le C_n\log n,
 \qquad
 S_n=o(n)\Longleftrightarrow C_n=o(n/\log n).                \tag{17}
\]

Thus the remaining problem is a pointwise upper bound on the number of
affine prime-factor collisions in the proportional core, not a question
about the total size of \(A_r\).

## 4. Exact CRT compression and why size alone remains linear

Let

\[
 \mathcal P_n=\{p:n/2<p<n,\ p\text{ an odd prime}\},\qquad
 P_n=\prod_{p\in\mathcal P_n}p,
\]

and define the integer

\[
                  J_n=\sum_{p\in\mathcal P_n}{P_n\over p}A_{n-p}. \tag{18}
\]

For \(p\in\mathcal P_n\), every summand indexed by \(q\ne p\) is divisible
by \(p\), while \(P_n/p\) is a \(p\)-adic unit.  Consequently

\[
 p\mid J_n\Longleftrightarrow p\mid A_{n-p},
 \qquad
 \boxed{\ \exp(S_n)=\gcd(P_n,J_n).\ }                       \tag{19}
\]

This is a genuine single-integer version of the entire first band.  It does
not by itself save anything: the PNT gives

\[
                   \log P_n=\vartheta(n)-\vartheta(n/2)+O(\log n)
                           ={n\over2}+o(n).                  \tag{20}
\]

Reducing \(J_n\) to its least residue modulo \(P_n\) preserves (19), but the
generic inequality \(\gcd(P_n,J_n)\le P_n\) still gives only a linear
exponent.  Any CRT continuation must therefore establish special
cancellation or nonconcentration for the actual residues \(A_{n-p}\); CRT
orthogonality and height alone cannot prove (1).

## 5. A rigorous local-statistics obstruction

For an actual prime \(p\), let its minimal first-block zero set be

\[
 Z_p=\{0\le r\le(p-1)/2:p\mid A_r\}.                        \tag{21}
\]

Reflection reconstructs the full zero set from \(Z_p\), and the three-term
recurrence forbids two consecutive full-block zeros.  It is tempting to seek
a bound such as \(|Z_p|=O(1)\) and infer (1).  The following abstract
construction proves that this inference is invalid even with the strongest
possible nonempty bound \(|Z_p|=1\).

Let \(N_j=10^j\) for \(j\ge3\).  The intervals

\[
                         {3N_j\over4}<p<{4N_j\over5}         \tag{22}
\]

are pairwise disjoint.  For each prime in (22), prescribe the single minimal
zero

\[
                         z_p=N_j-p,                          \tag{23}
\]

and prescribe no minimal zero for any other prime.  The reflected full set is
\(\{z_p,p-1-z_p\}\).  For all these primes,

\[
 0<z_p<{p-1\over2},\qquad
 (p-1-z_p)-z_p=3p-2N_j-1>{N_j\over4}-1.                    \tag{24}
\]

Thus the model has one minimal zero per prime, exact reflection symmetry,
and no consecutive zeros (indeed the paired zeros are macroscopically
separated).  Nevertheless, at depth \(n=N_j\), every prime in (22) lies on
the direct ray because \(p=N_j-z_p\).  Its selected weight is at least

\[
 \vartheta(4N_j/5)-\vartheta(3N_j/4)
                         =\left({1\over20}+o(1)\right)N_j.   \tag{25}
\]

This construction is **not** claimed to be realizable by the recurrence for
\(A_r\).  Its exact logical content is narrower and important: no theorem
using only a uniform bound on \(|Z_p|\), reflection, and zero spacing can
imply the pointwise diagonal estimate (1).  A successful theorem must use
additional arithmetic structure linking the locations \(Z_p\) for different
primes to the same depth \(n\).

This also explains the quantifier gap in a conventional large-sieve attack.
Per-prime sparsity can control averages over \(n\), once a sufficiently strong
average bound for \(|Z_p|\) is available, but a large-sieve mean square does
not automatically give the **every-\(n\)** estimate in (1).  No such average
bound for the actual sequence was found here either.

## 6. Checked approaches and exact stopping points

### Finite-field Legendre/Krawtchouk identities

The identity \(A_r=(2i)^rP_r(-i)\) makes \(p\mid A_r\) equivalent to
\(X^2+1\mid 2^rP_r(X)\) over \(\mathbb F_p\).  The corresponding resultant is
exactly \(A_r^2\), so it contains no independent small-height norm.  The
first-block coefficient representation

\[
 \sum_{s=0}^{p-1}(A_s/2^s)x^s
        =(1-2x-x^2)^{(p-1)/2}\pmod p                       \tag{26}
\]

recovers reflection and coefficient-zero questions, but the general
root-multiplicity/weight theorem gives only a linear upper allowance for the
number of zero coefficients.  More importantly, Section 5 proves that even a
uniform constant zero count would not settle the pointwise affine alignment.

### Bivariate resultants

The natural resultant between \(X^2+1\) and the Legendre polynomial is the
square of the original integer.  The natural resultant between two Legendre
depths contains a universal \(p^r\) factor for every affine candidate,
selected or not, as established and independently audited in the predecessor.
Neither resultant separates (2)'s selected primes.

### Size, smoothness, and largest-prime-factor estimates

After removing the exact power of two, the odd part of \(A_r\) still has
positive exponential rate.  Therefore the elementary product bound permits
\(\asymp r/\log r\) prime factors of size \(\asymp r\); it cannot yield the
little-o count in (17).  A theorem asserting merely one very large or one
primitive prime factor is also too weak: it need not consume most of the
logarithmic mass.  The bounded literature search found no theorem giving the
needed near-linear-prime radical estimate for this sequence.

### Large sieve

The selector at fixed \(n\) is \(n-p\in Z_p\).  Standard large-sieve input
controls an average over the external variable; it does not bound the maximum
over every \(n\).  The construction (22)--(25) is an explicit witness to this
quantifier failure at the level of local zero-set hypotheses.

## 7. Literature and mathlib audit

Search date: **2026-08-13 UTC**.  Queries covered `A006139`, generalized
central-trinomial prime divisors, greatest and primitive prime factors,
Legendre values \(P_r(i)\bmod p\), Krawtchouk/hypergeometric identities,
zero coefficients of powers of trinomials over finite fields, large sieve
selector bounds, and moving prime windows of holonomic sequences.

| Primary source | What was checked | Frozen PDF SHA-256 |
|---|---|---|
| [Tony D. Noe, *On the Divisibility of Generalized Central Trinomial Coefficients*, JIS 9 (2006), Article 06.2.7](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf) | The generalized Lucas product and first-block reflection specialize to (4) and (6). | `971d271f35eb4400ac223f7e3536cdc7ac28e14393caa03c1204bc16d30a094c` |
| [Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers mod p*, arXiv:2411.03681v2](https://arxiv.org/pdf/2411.03681v2) | Theorem 4 gives the generalized-central-trinomial reflection.  Its discussion of no-zero primes is heuristic and fixed-prime; it supplies no cross-prime diagonal estimate. | `f4c604453c2b81a48dd3ee56aabab0ef3a6a78b0d14a21a2b323bd4818d6db42` |
| [Sandro Mattarei, *Root multiplicities and number of nonzero coefficients of a polynomial*, arXiv:math/0512239v2](https://arxiv.org/pdf/math/0512239v2) | The sharp general polynomial-weight theorem leaves a linear number of possible zero coefficients in (26). | `5e9c4f6345a7171b112d16b6eb12b7388334c9123e8d39058d22080e4f031b9d` |
| [Zhi-Wei Sun, *Congruences involving generalized central trinomial coefficients*, arXiv:1008.3887v13](https://arxiv.org/pdf/1008.3887v13) | Square-sum and parametric congruences give global fixed-prime identities, not a pointwise affine selector bound. | `a4540dc374dc9ef0fcad856c9a69c247d345fec94127ac8a6f09353f18995eb1` |

No checked primary source proves (1), (16), or a cross-prime theorem strong
enough to imply them.  This is a bounded negative search result, not a
novelty claim.

The local mathlib search found:

- `Mathlib/Data/Nat/Choose/Lucas.lean` for ordinary binomial Lucas;
- `Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean` for integral shifted
  Legendre polynomials and their symmetry;
- `Mathlib/NumberTheory/Chebyshev.lean`, including
  `Chebyshev.theta_le_log4_mul_x` and primorial identities;
- no generalized-central-trinomial Lucas/reflection theorem and no theorem
  directly expressing the moving affine prime-factor selector.

No formal code was changed, so no theorem from this note is labeled
`machine-checked` and no axiom-audit entry is claimed.

## 8. Reproduction

Run:

```bash
python work/ultrapi-resume/gauss_first_band_breakthrough_attack_20260813_check.py
```

Expected output:

```text
PASS: exact Lucas/reflection/two-ray first-band encoding on 309017 prime-depth pairs through n=3000, with 339 selected pairs
PASS: CRT gcd package on 417 depths and small-r product bound on 271 depths
EXPERIMENT: largest first-band collision multiplicity through n=3000 is 3 at n=2772, primes=[2383, 2671, 2689]
EXPERIMENT: abstract symmetric one-minimal-zero construction used 508 distinct primes; rows (N, hits, weighted_ratio)=[(1000, 7, 0.04652985520836395), (10000, 57, 0.05102929687736916), (100000, 444, 0.04998541544326285)]
BOUNDARY: finite replays prove no little-o estimate, no exceptional-gcd bound, and no decimal-cylinder hit
```

The first two lines replay only finite algebraic identities.  The third and
fourth lines are expressly an `experiment`; the asymptotic statement (25)
comes from the PNT, not from those rows.

## 9. Handoff

The exact unresolved theorem can now be stated without a moving Legendre
index, band endpoint, or local-zero-count ambiguity:

> For every fixed \(0<\delta<1/6\), prove that the logarithmic weight of
> primes on the two rays (2), with \(\delta n\le r\le(1/3-\delta)n\) and
> \(p\mid A_r\), is \(o(n)\), uniformly pointwise as \(n\to\infty\).

The new obstruction (22)--(25) rules out treating per-prime sparsity as the
missing theorem.  A viable continuation needs arithmetic correlation across
different characteristics—such as a nontrivial bound on the indegree of the
actual shifted-prime-divisor graph—not another fixed-prime zero-density or
resultant reformulation.  Until that cross-prime input is proved, the branch
remains a `proof sketch` and V1 remains a `conjecture`.
