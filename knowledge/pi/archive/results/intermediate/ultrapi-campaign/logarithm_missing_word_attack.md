# Logarithm-of-an-algebraic-number attack on decimal disjunctivity of pi

Audit date: **2026-08-12 UTC**  
Status: `literature-checked` bounded applicability audit, with local `proof sketch`
separators  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

No theorem found in the primary literature implies that the decimal expansion
of \(\pi\) is disjunctive.  Euler's identity gives the unusually rigid exact
representation

\[
  \pi=-i\operatorname{Log}(-1),
\]

and classical work gives effective transcendence measures for every fixed
logarithm of an algebraic number.  Those theorems bound how closely \(\pi\)
can approach algebraic numbers or polynomial zero sets.  Absence of a decimal
word says instead that the single expanding orbit

\[
  \bigl\{10^n\pi\bigr\}\pmod 1
\]

avoids one interval forever.  Repulsion from the interval's endpoints does
not force an entry into its interior.

This is a genuine logical gap, not just a bad numerical constant.  For every
finite word \(w\), a nine-symbol decimal Cantor subset of the \(w\)-avoiding set
contains:

1. transcendental badly approximable numbers of irrationality exponent
   exactly two; and
2. transcendental numbers satisfying an explicit polynomial
   degree--height lower bound of the same general functional shape as the
   classical Cijsouw measure for logarithms of algebraic numbers.

Thus neither transcendence, an optimal scalar irrationality exponent, nor a
classical-style transcendence measure can by itself exclude a missing word.
The special identity \(e^{i\pi}=-1\) would have to be coupled to a new theorem
that detects a decimal survivor interval, and no such bridge was located.

The canonical target remains a `conjecture`.  This file contains no candidate
resolution and no claim about finite computations of digits.

## 1. Exact target and the logarithmic representations

The target is the following quantifier order:

\[
  \forall m\geq1\ \forall w\in\{0,\ldots,9\}^m\
  \exists n\geq0:\quad
  d_{n+1}(\pi)\cdots d_{n+m}(\pi)=w.                 \tag{1}
\]

Leading zeros in \(w\) are permitted, and only the fractional decimal digits
are in scope.  Lagarias calls (1) *digit-density*.  His Definition 2.1 and
Theorem 2.1(1) identify it exactly with density of the base-10 remainder
orbit.  Normality is stronger and is not being substituted for (1).

There are two exact logarithmic presentations worth separating.

First, for the principal branch,

\[
  \operatorname{Log}(-1)=i\pi.                      \tag{2}
\]

Second, put

\[
  \alpha_q={q+i\over q-i}.
\]

Since \(\operatorname{Log}(\alpha_q)=2i\arctan(1/q)\) for \(q>0\),
Machin's identity gives

\[
  i\pi=8\operatorname{Log}(\alpha_5)
        -2\operatorname{Log}(\alpha_{239}).          \tag{3}
\]

The numbers \(-1,\alpha_5,\alpha_{239}\) are algebraic.  Consequently (2)
and (3) lie squarely inside the theory of logarithms of algebraic numbers.
That theory proves nonvanishing, transcendence, and quantitative lower
bounds for suitable logarithmic forms.  None of those conclusions contains
an expanding-orbit or cylinder-hitting assertion.

## 2. What the classical logarithm measure actually gives

Cijsouw's Theorem 2 is especially useful because its hypotheses and output
can be compared directly with (1).  If \(\alpha\ne0,1\) is algebraic and a
branch \(L=\log\alpha\) is fixed, then there is an effective constant
\(C(\alpha)>0\) such that every nonconstant \(P\in\mathbb Z[X]\), of degree
at most \(D\) and height at most \(H\), satisfies

\[
  |P(L)|>
  \exp\!\left(-C(\alpha)D^2(D+\log H)(1+\log D)^2\right).       \tag{4}
\]

This is [Cijsouw 1974, Theorem 2, p. 164](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf).
Taking \(\alpha=-1\) gives a measure for \(i\pi\).  It also gives a measure of
the same shape for \(\pi\) itself: for an integer polynomial \(P\), apply (4)
to

\[
  Q(Y)=P(-iY)P(iY)\in\mathbb Z[Y],
\]

at \(Y=i\pi\), and use
\(Q(i\pi)=P(\pi)P(-\pi)\) together with the elementary upper bound on
\(|P(-\pi)|\).  More explicitly, \(\deg Q\leq2D\),
\(H(Q)\leq(D+1)H^2\), and
\(|P(-\pi)|\leq(D+1)H\max(1,\pi)^D\), so the changes are absorbed into the
same degree--height shape as (4).  Cijsouw later published a measure
specifically for \(\pi\), but the reduction above already shows exact
applicability of the logarithm theorem.

The critical point is the direction of (4).  It says that once a polynomial
\(P\) has been supplied, its value at \(\pi\) is not too small.  The
hypothesis that a word is absent supplies nested interval inequalities, not a
family of integer polynomials with values smaller than (4).  A
transcendence measure is therefore not a digit-distribution theorem.

### 2.1 The universal decimal truncations are much too coarse

Let

\[
  q_N=10^N,\qquad p_N=\lfloor q_N\pi\rfloor.
\]

Then every real number, independently of its digits, satisfies

\[
  0<\pi-{p_N\over q_N}<q_N^{-1}.                    \tag{5}
\]

Word avoidance restricts which numerator \(p_N\) can occur, but does not
improve the exponent one in (5).  The best currently published scalar bound
found in the fresh search is

\[
  \mu(\pi)\leq7.103205334137\ldots,                  \tag{6}
\]

from Zeilberger--Zudilin.  Thus, for every fixed \(\varepsilon>0\), all
sufficiently large rational approximations obey a lower bound of order
\(q^{-7.103205334137\ldots-\varepsilon}\).  The interval between that lower
bound and the universal upper bound \(q^{-1}\) is enormous, and omission of
one word does not shrink it.  Even the hypothetical optimum \(\mu(\pi)=2\)
would not exclude a missing word; Section 5 gives an exact separator.

### 2.2 Exponentiating the truncation does not rescue Euler's identity

Equation (2) turns (5) into the exact small exponential form

\[
 \left|e^{ip_N/q_N}+1\right|
 =2\left|\sin\!\left({\pi-p_N/q_N\over2}\right)\right|
 <q_N^{-1}.                                          \tag{7}
\]

This is a linear form in exponentials of algebraic numbers: the exponents
are \(ip_N/q_N\) and \(0\).  Huang's effective
Lindemann--Weierstrass bound, Theorem 1.2, applies.  With the number of terms
and algebraic degrees fixed while
\(h(ip_N/q_N)=O(\log q_N)\), a crude simplification of that explicit theorem
has the form

\[
  \left|e^{ip_N/q_N}+1\right|
  \geq \exp\!\bigl(-\exp(q_N^{C_0})\bigr)             \tag{8}
\]

for an effective constant \(C_0>0\).  Bound (8) is vastly smaller than
\(q_N^{-1}\), so (7) is completely compatible with it.  The specialized
irrationality bound (6) is much stronger than this general-purpose estimate,
but Section 5.1 shows that even the optimal scalar exponent would not imply
word coverage.

The homogeneous logarithmic form (3) exhibits the same obstruction in a
different notation.  The error in a decimal rational approximation is

\[
  i\left(\pi-{p\over q}\right)
  =8\log\alpha_5-2\log\alpha_{239}-{ip\over q}.       \tag{9}
\]

The last additive algebraic term is not the logarithm of an algebraic
number.  Writing it as \(\log(e^{ip/q})\) introduces a transcendental base.
Effective Lindemann--Weierstrass theory handles the exponentiated version,
but only at the weak height-dependent scale illustrated by (8).

## 3. A direct digit consequence of restricted-denominator bounds

Rivoal's paper is a direct test of the tempting idea that a very sharp
logarithm measure at denominators \(b^m\) should reveal digits.  For certain
positive rationals \(r=1-a/b\) with \(0<|a/b|<1\), his Theorem 1 proves
restricted-denominator inequalities

\[
  \left|\log r-{u\over B^m}\right|\geq B^{-(\Lambda+\varepsilon)m}.
                                                               \tag{10}
\]

The introduction, equations (1.1)--(1.2), spells out the digit consequence.
If \(e_1<e_2<\cdots\) are the nonzero base-\(B\) digit positions, then (10)
gives only

\[
  e_{j+1}\leq\Lambda e_j+O(1),\qquad
  \#\{j:e_j\leq N\}\geq {\log N\over\log\Lambda}+O(1).          \tag{11}
\]

That is a logarithmic lower bound on the number of nonzero digits, not an
occurrence theorem for any prescribed block.  The published hypotheses also
do not contain \(\log(-1)\): \(r\) is positive and \(0<|a/b|<1\).  Extending
the Pad\'e argument to the two complex logarithms in (3) would still leave the
combinatorial gap in (11).

The 2026 theorem of Fischler--Rivoal is current confirmation of the same
boundary.  Their Theorem 2 proves, for suitable positive values of strict
E-functions,

\[
  \left|\ln(f(\xi))-{a\over b}\right|
  \geq \exp(-c b^d).                                  \tag{12}
\]

It implies that the value is not ultra-Liouville.  It neither applies to the
complex value \(\operatorname{Log}(-1)\) in its quantitative part nor gives a
base-expansion cylinder hit.  The universal truncation error \(b^{-1}\) is
again much larger than the right side of (12).

## 4. Why one forbidden word supplies no anomalously small form

Fix a word \(w\) of length \(m\).  Its avoiding strings form a finite-state
language with Perron eigenvalue \(\lambda_w<10\).  Thus the missing-word
hypothesis gives an entropy defect and places \(\{\pi\}\) in the survivor set

\[
  K_w=\{x:T_{10}^n x\notin I_w\text{ for all }n\geq0\}.          \tag{13}
\]

This is a point-location condition.  It does not choose a low-degree
polynomial, a repeated decimal prefix, or a rational approximation with
exponent greater than one.

The combinatorial scale explains why.  There can be
\(\asymp\lambda_w^L\) different allowed blocks of length \(L\).  A collision
forced only by pigeonhole therefore occurs at a location exponential in
\(L\), whereas Subspace-Theorem rational approximations need a repeated
portion whose length is proportional to its starting position.  A positive
entropy subshift does not supply that proportional repetition.

The August 2026 refinement of this circle of ideas makes the quantifiers
particularly clear.  Nguyen's Theorem A says that a coefficient word with
sufficiently large *refined Diophantine exponent* gives a value which is in
the ground field or transcendental; Theorem B adds a transcendence measure
under stronger recurrence hypotheses.  The input is quantitative
near-periodicity of the one chosen word.  Membership in a forbidden-word
subshift supplies no such input.  Conversely, knowing that \(\pi\) is already
transcendental does not imply the recurrence hypothesis.  Applying the
theorem backwards would reverse a one-way implication.

Status of the reduction in this section: `proof sketch`.  It identifies the
missing premise; it does not prove (1).

## 5. Exact separators for scalar and polynomial measures

The following constructions show that the gap survives very strong
Diophantine information.

### 5.1 Optimal scalar approximation coexists with a missing digit

Choose a decimal digit \(d\) occurring in \(w\), put
\(A=\{0,\ldots,9\}\setminus\{d\}\), and define

\[
  K_A=\left\{\sum_{n\geq1}a_n10^{-n}:a_n\in A\right\}.           \tag{14}
\]

Every irrational member of \(K_A\) has a unique decimal expansion which
omits \(d\), and hence avoids \(w\).  This is the attractor of nine
similarities \(x\mapsto(x+a)/10\), satisfies the open set condition, and is
irreducible.  Fishman's Corollary 3 therefore gives

\[
  \dim_H(K_A\cap\mathrm{BA})=\dim_H K_A={\log9\over\log10}>0,    \tag{15}
\]

where \(\mathrm{BA}\) is the set of badly approximable real numbers.
Removing the countable algebraic numbers leaves the dimension unchanged.
Consequently there are transcendental \(\xi\in K_A\cap\mathrm{BA}\).

For such a \(\xi\), there is \(c(\xi)>0\) with

\[
  \left|\xi-{p\over q}\right|>{c(\xi)\over q^2}
  \quad(p\in\mathbb Z,\ q\geq1).                     \tag{16}
\]

Dirichlet's theorem supplies infinitely many approximations at exponent
two, so \(\mu(\xi)=2\) exactly.  Thus an optimal irrationality exponent is
compatible with omitting even one digit.  This rigorously blocks any upgrade
from a hypothetical proof \(\mu(\pi)=2\) to V1.

### 5.2 A classical-shape transcendence measure also coexists with omission

Here is a second, independent separator.  It is recorded as a local
`proof sketch`; all estimates are displayed so that no probabilistic slogan
is doing hidden work.

Let

\[
  s={\log9\over\log10}
\]

and let \(\nu\) be the uniform self-similar probability measure on \(K_A\).
An elementary level-cylinder count gives a constant
\(C_A\) (for example \(C_A=4\cdot10^s\) suffices) such that

\[
  \nu(B(x,r))\leq C_A r^s\qquad(x\in\mathbb R,r>0).   \tag{17}
\]

Indeed, for \(0<r<1\), choose \(n\) with
\(10^{-(n+1)}<r\leq10^{-n}\).  A real interval of length \(2r\) meets at
most four level-\(n\) decimal grid cells, each relevant cylinder has mass
\(9^{-n}=(10^{-n})^s<(10r)^s\), and the claim follows.  For \(r\geq1\)
it is immediate.  This also verifies (17) when the center is not in
\(K_A\), as needed below.

For integers \(D\geq1\), \(k\geq0\), let

\[
  M_{D,k}=(2^{k+1}+1)^{D+1},\qquad
  r_{D,k}=
  \left({2^{-D-k-4}\over C_A D M_{D,k}}\right)^{1/s}.             \tag{18}
\]

There are at most \(M_{D,k}\) integer polynomials of degree at most
\(D\) and height at most \(2^k\).  Remove from \(K_A\), for every such
nonzero polynomial, the real points within \(r_{D,k}\) of any of its complex
roots.  A nonreal root has an empty real \(r_{D,k}\)-neighborhood when its
imaginary part is at least \(r_{D,k}\); otherwise its intersection with the
real axis is contained in a real ball of radius \(r_{D,k}\).  Hence each of
the at most \(D\) roots contributes at most \(C_A r_{D,k}^s\) by (17), and
(17)--(18) bound the removed measure by

\[
  \sum_{D\geq1}\sum_{k\geq0}2^{-D-k-4}={1\over8}.     \tag{19}
\]

Choose \(\eta\) in the positive-measure remainder.  It is not a root of any
nonzero integer polynomial, hence is transcendental, and it still omits
\(d\).  If \(P\in\mathbb Z[X]\) has exact degree \(D\geq1\) and height
\(H\geq1\), take \(k=\lceil\log_2H\rceil\).  Then \(H\leq2^k<2H\).
Factoring \(P\) over \(\mathbb C\) and using its nonzero integral leading
coefficient gives

\[
\begin{split}
 |P(\eta)|
 &\geq r_{D,k}^{D}\\
 &\geq
 \left(
 {2^{-D-5}\over C_A D\,6^{D+1}H^{D+2}}
 \right)^{D/s}.                                      \tag{20}
\end{split}
\]

In particular, after enlarging an absolute constant depending only on
\(A\), (20) implies

\[
  |P(\eta)|\geq
  \exp\!\left(-C'_A D^2(D+\log H)(1+\log D)^2\right).             \tag{21}
\]

The functional shape in (21) is the same as, and in its displayed
degree--height dependence actually weaker than the explicit estimate (20),
while matching the form of Cijsouw's logarithm measure (4).  Constants are
not asserted to be the same.  The conclusion is precise: the *existence and
functional strength class* of a classical transcendence measure cannot
imply digit coverage.  A successful logarithm proof must use more than the
lower-bound output of that theory.

## 6. What a successful logarithm route would still have to prove

At least one new pointwise bridge of the following kind is required.

1. **Survivor exclusion.**  Prove directly that
   \(\{\pi\}\notin K_w\) for every finite \(w\).  This is exactly V1 in
   dynamical language.
2. **Digit-to-form conversion.**  Starting from \(\{\pi\}\in K_w\), construct
   explicit nonzero integer polynomials or exponential/logarithmic forms
   whose smallness beats (4), (6), or an improved bound.  The universal
   truncations (5) and (7) do not.
3. **Pointwise entropy or Fourier input.**  Prove full topological entropy,
   orbit density, or cylinder-scale Fourier cancellation for the named
   orbit \(\{10^n\pi\}\).  Averaging over all logarithms, all survivor paths,
   or all admissible numerators is insufficient.

The first and third items are essentially reformulations or strong
sufficient conditions for V1.  The second is the only genuinely different
transcendence route, and the missing construction is now isolated exactly:
one must convert an interval-avoidance statement into anomalous arithmetic
smallness while retaining the special relation \(e^{i\pi}=-1\).

## 7. Primary-source ledger and exact applicability

Status of this table: `literature-checked` on **2026-08-12 UTC**.  It records
a bounded primary-source search, not a claim to have exhausted all
mathematical literature.

| Source | Exact locator | What is proved | Why it does not prove V1 |
|---|---|---|---|
| [Cijsouw, *Transcendence measures of exponentials and logarithms of algebraic numbers* (1974)](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf) | Theorem 2, printed p. 164 | Effective bound (4) for a fixed \(\log\alpha\). | It lower-bounds a supplied polynomial value; word omission supplies no anomalously small polynomial. |
| Cijsouw, *A transcendence measure for \(\pi\)* (1977) | Baker--Masser volume, pp. 93--100; [bibliographic record](https://research.tue.nl/en/publications/a-transcendence-measure-for-pi/) | A direct transcendence measure for \(\pi\). | Same pointwise-polynomial versus orbit-hitting mismatch. |
| [Lagarias, *On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055) | Introduction p. 1; Definition 2.1 and Theorem 2.1, pp. 4--5; Theorem 5.3, pp. 14--15 | Exact digit-density/orbit-density equivalence; Baker theory gives rational-or-transcendental dichotomies for certain G-values. | The normality mechanism is explicitly conditional on Bailey--Crandall Hypothesis A; transcendence is not density. |
| [Rivoal, *Convergents and irrationality measures of logarithms*](https://doi.org/10.4171/RMI/519) | Introduction equations (1.1)--(1.2), pp. 931--933; Theorems 1--4, pp. 933--936 | Restricted-denominator measures for \(\log(1-a/b)\), with the logarithmic nonzero-digit consequence (11). | Positive-real and small-argument hypotheses exclude \(\log(-1)\); even a hypothetical extension gives digit counts, not prescribed blocks. |
| [Fishman, *Schmidt's game, badly approximable matrices and fractals*](https://doi.org/10.1016/j.jnt.2009.02.005) | Section 4, Corollary 3, pp. 19--20 of [arXiv:0809.2065](https://arxiv.org/abs/0809.2065) | Badly approximable points have full relative dimension in irreducible self-similar sets satisfying OSC. | Supplies the exact missing-digit, \(\mu=2\) separator (15)--(16). |
| [Zeilberger--Zudilin, *The irrationality measure of pi is at most 7.103205334137...*](https://doi.org/10.2140/moscow.2020.9.407) | Title theorem and Introduction, p. 1 | Current rigorous scalar upper bound found in the dated search. | Decimal truncation has exponent one; omission does not force an approximation beyond the bound. |
| [Huang, *Explicit Bounds for Linear Forms in the Exponentials of Algebraic Numbers*](https://doi.org/10.1145/3476446.3536170) | Theorem 1.2, pp. 2--3 of [arXiv:2112.05004](https://arxiv.org/abs/2112.05004) | Effective Lindemann--Weierstrass lower bound used in (8). | Height grows with \(p_N/q_N\); the resulting lower bound is vastly smaller than the universal truncation error. |
| [Fischler--Rivoal, *Transcendence of values of logarithms of E-functions* (2026)](https://doi.org/10.1007/s00208-026-03374-z) | Corollary 1 and Theorem 2, equations around (1.1); [arXiv:2409.18537](https://arxiv.org/abs/2409.18537) | Transcendence of many log E-values and the measure (12) in the positive-real strict case. | Quantitative hypotheses do not cover \(\operatorname{Log}(-1)\), and the conclusion is non-ultra-Liouville rather than cylinder hitting. |
| [Nguyen, *Transcendence and measures via the refined Diophantine exponent*](https://arxiv.org/abs/2605.30606v2) | Theorems A and B, pp. 3--5; version dated 1 Aug. 2026 | Strong recurrence of a coefficient word implies transcendence/measure statements at algebraic bases. | A forbidden-word language has positive entropy and does not give the required recurrence for its chosen path; the implication cannot be reversed from transcendence of \(\pi\). |

The search also checked the 2025--2026 fixed-number complexity papers already
catalogued in [`ultrapi.md`](../../ultrapi.md).  Their linear or superlinear
factor-complexity conclusions are exponentially below the \(10^m\) coverage
required at length \(m\), and none specializes a logarithm theorem to decimal
disjunctivity of \(\pi\).

Exact PDF pins used for this audit (SHA-256, fetched 2026-08-12 UTC):

| Source | SHA-256 |
|---|---|
| Cijsouw 1974 | `fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a` |
| Lagarias, arXiv v2 | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Rivoal 2007 author PDF | `05eb82730fca2dfa6cf60f1f581e87442c98cf17a5e36106b342448e63802b7e` |
| Fishman, arXiv:0809.2065v1 | `3778e06391c3aacde0012f7145a11549ee1311353bbd4bd8d28546f4b02963e5` |
| Zeilberger--Zudilin, arXiv:1912.06345 | `b922ee68a427ad5b74617bd2ac6b6a549824eb2d5a8c97eed0d34b2de984155f` |
| Huang, arXiv:2112.05004 | `050006233128531e25866579b13f599abb0d4e486b1a3959aad0b3c35fad95f2` |
| Fischler--Rivoal, arXiv:2409.18537 | `bddfb2aa7226ca4758efc284e284b96e4824ed205beb180a8985c9bdd9f43a86` |
| Nguyen, arXiv:2605.30606v2 | `2cfb651d65a9960bc0385a2658005752dd899bb4a8919b08d91c8319a18a87b2` |

## Bottom line

The logarithmic identity explains why \(\pi\) is transcendental and supports
strong quantitative nonapproximation theorems.  It does not currently
control the sign, location, entropy, or Fourier distribution of
\(\{10^n\pi\}\).  The separators above show that the generic scalar
nonapproximation outputs audited here coexist with missing digits.  The
route remains open only at the genuinely new bridge from decimal survivor
dynamics to a \(\pi\)-specific anomalously small logarithmic or exponential
form.

No finite checker was added: the new conclusions are symbolic inequalities
and a literature applicability audit, and finite digit computation would
carry no proof leverage for V1.
