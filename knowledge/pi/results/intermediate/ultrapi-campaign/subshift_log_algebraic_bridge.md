# Finite-type decimal avoidance versus the algebraic logarithm of −1

Audit date: **2026-08-12 UTC**  
Status: `literature-checked` bounded primary-source audit with local
`proof sketch` reductions  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

No unconditional bridge was found which excludes \(\pi\) from every proper
finite-type decimal subshift.  The exact special relation

\[
  e^{i\pi}=-1,\qquad i\pi=\operatorname{Log}(-1),                 \tag{1}
\]

does put \(\pi\) under effective logarithm and E-function-zero estimates.
Those estimates lower-bound a polynomial or exponential form after that form
has been supplied.  Omitting one word supplies instead an infinite sequence of
interval memberships.  The fresh exponent ledgers below show where the most
direct conversions lose:

1. finite-type pigeonhole repetition occurs at an exponential return scale
   and yields only an approximation exponent tending to one;
2. a polynomial containing every allowed prefix has exponential degree and is
   not small after denominators are cleared;
3. multiplying genuinely small selected-tail factors gives degree \(O(N)\),
   height \(\exp(O(N^2))\), and value only \(\exp(-O(N))\), while the applicable
   Cijsouw lower bound is of order \(\exp(-O(N^4\log^2N))\).

There is an exact separator for a tempting strengthening: every
single-forbidden-word survivor contains an explicit selected-path Mahler
number which is
transcendental and has irrationality exponent exactly two.  Thus
finite-state membership, selected-path automatic/Mahler structure,
transcendence, and optimal scalar rational approximation can all coexist with
word omission.  What this separator deliberately does **not** have is a known
algebraic exponential.  The remaining possible theorem is therefore sharply
identified:

> exclude a logarithm of an algebraic number, specifically
> \(\operatorname{Log}(-1)=i\pi\), from a prescribed positive-entropy decimal
> survivor by a digit-sensitive estimate.

No such theorem was located in the bounded search.  The canonical statement
remains a `conjecture`; this report is not a candidate resolution.

## 1. Exact negation and the amount of structure it supplies

Write

\[
 \pi=3+\theta,\qquad
 \theta=0.d_1d_2\ldots=\sum_{n\geq1}d_n10^{-n}.
\]

The target permits leading zeros and asserts

\[
 \forall m\geq1\ \forall w\in\{0,\ldots,9\}^m\ \exists k\geq1:
 d_kd_{k+1}\cdots d_{k+m-1}=w.                     \tag{2}
\]

Fixing one word \(w\) of length \(m\), its negation is that the digit path
belongs to the one-sided subshift of finite type

\[
 X_w=\{(a_n):w\text{ occurs at no position of }(a_n)\}.          \tag{3}
\]

Equivalently, with

\[
 x_n=\{10^n\pi\}=10^n\pi-\lfloor10^n\pi\rfloor
\]

and with \(I_w\) the half-open decimal cylinder for \(w\),

\[
 x_n\notin I_w\qquad(n\geq0).                                  \tag{4}
\]

This is a controlled path, not a deterministic finite-state output.  Choose
any digit \(c\) occurring in \(w\).  Every sequence over the nine-symbol
alphabet

\[
 A_c=\{0,\ldots,9\}\setminus\{c\}                              \tag{5}
\]

lies in \(X_w\).  Consequently \(X_w\) contains a full nine-shift and can
carry arbitrary choices at every position.

The entropy bounds make the gap quantitative.  If \({\cal L}_L(w)\) is the
set of length-\(L\) words avoiding \(w\), then

\[
 9^L\leq |{\cal L}_L(w)|.
\]

Writing \(L=qm+r\), \(0\leq r<m\), and partitioning into aligned
length-\(m\) blocks gives

\[
 |{\cal L}_L(w)|
 \leq 10^r(10^m-1)^q.                                           \tag{6}
\]

Hence

\[
 \log9\leq h(X_w)\leq {1\over m}\log(10^m-1)<\log10.           \tag{7}
\]

The survivor is proper but still has positive entropy extremely close to
full entropy when \(m\) is large.  By contrast, (2) is equivalent to maximal
factor entropy \(\log10\): if even one length-\(m\) word is missing, factor
submultiplicativity gives the strict upper bound in (7).

Status of this section: local `proof sketch`; the aligned-block count is an
elementary upper bound, not a novelty claim.

## 2. SFT, automatic, and low-complexity are different quantifiers

Three objects that look finite-state on paper must be separated.

1. A **regular language** recognizes all finite legal prefixes in (3).
2. A **subshift of finite type** is the set of all infinite legal paths.  It
   need not choose one outgoing digit at any state.
3. A **\(q\)-automatic sequence** is one selected sequence whose \(n\)-th
   symbol is output by a finite automaton reading the base-\(q\) expansion of
   \(n\).  It has only \(O(L)\) length-\(L\) factors.

The full nine-shift in (5) proves that the first two notions do not imply the
third: \(X_w\) has uncountably many paths and contains paths with \(9^L\)
distinct length-\(L\) factors, while there are only countably many finite
automata.

The regular language does have a rational length generating function and an
all-path transfer-matrix/Mahler system.  Those functions sum over all legal
paths.  They do not give a Mahler equation for the path formed by the digits
of \(\pi\).  Applying an automatic-number theorem to the transfer matrix
would therefore change the quantifier from one selected path to an aggregate
of all paths.

Even adding selected-path automaticity would not finish.  Adamczewski--
Bugeaud prove that an irrational number with an automatic digit word is
transcendental, and Adamczewski--Faverjon prove the
coefficient-field-or-transcendental alternative for a Mahler function at an
algebraic point inside the unit disk where the function has no pole.
Since \(\pi\) is already transcendental, both conclusions are compatible with
\(\pi\).  The 2026 Adamczewski--Faverjon Liouville-type inequality further
shows that Mahler values are not U-numbers; this is still polynomial
degree--height separation, not a theorem about the exponential of a Mahler
value or about decimal cylinders.

The bounded search found no primary theorem of the form

\[
 \xi\text{ is a nonrational Mahler value}
 \quad\Longrightarrow\quad e^{i\xi}\text{ is transcendental}.  \tag{8}
\]

Such a statement would in any event concern a selected-path Mahler value,
which (3) alone does not supply.

## 3. Exact repetition exponent ledger

Let \(M_L=|{\cal L}_L(w)|\), and let \(d_1d_2\ldots\) be any irrational path
in \(X_w\).  Among the \(M_L+1\) length-\(L\) factors beginning at positions
\(0,1,\ldots,M_L\), two agree.  Write their starting positions as
\(i<j\), and put \(r=j-i\).  Then

\[
 d_{i+1}\cdots d_{i+L}=d_{j+1}\cdots d_{j+L}.                  \tag{9}
\]

Let \(U=d_1\cdots d_i\), \(B=d_{i+1}\cdots d_j\), and let \([U]\),
\([B]\) denote their base-10 integer values.  The ultimately periodic
rational

\[
 y_L={ [U]\over10^i}+{[B]\over10^i(10^r-1)}                    \tag{10}
\]

agrees with \(\theta\) through digit \(j+L\), including when the two copies
in (9) overlap.  Here the repeating representation is used if the period is
all nines; the alternative terminating representation has the same rational
value and does not affect the following error bound.  Therefore

\[
 |\theta-y_L|\leq10^{-(j+L)},\qquad
 Q_L:=10^i(10^r-1)<10^j.                                      \tag{11}
\]

In unreduced-denominator notation, (11) is only

\[
 |\theta-y_L|<Q_L^{-\left(1+L/j\right)}.                       \tag{12}
\]

Pigeonhole gives \(j\leq M_L\), so the weak exponent that this construction
guarantees uniformly is

\[
 1+{L\over M_L}.
\]

Since \(M_L\geq9^L\), this guaranteed exponent is at most
\(1+L/9^L\), hence tends to one exponentially fast.  It is weaker than the
exponent two available for every irrational number from continued fractions.
De Bruijn cycles on the nine-symbol subsystem also show at each fixed \(L\)
that a first repeated \(L\)-block can be delayed to exponential scale.  Thus
finite-type avoidance alone does not hide a linear-scale repetition theorem.

This ledger explains the hypothesis mismatch in Subspace-Theorem and refined
Diophantine-exponent results.  Those theorems require a long repeated portion
relative to the location/period of the repeat.  Equation (6) supplies only an
exponential location for a length-\(L\) repeat.  Nguyen's 2026 theorems take
strong near-periodicity of the selected coefficient word as an input; they
cannot be reversed from membership in \(X_w\), nor from the already-known
transcendence of \(\pi\).

Status: local `proof sketch`.  The overlap case in (9)--(11) was checked
separately; equality of the two blocks makes the intervening segment
\(r\)-periodic for exactly the range used in (10).

## 4. An explicit automatic/Mahler separator inside every survivor

The distinction above can be made exact rather than categorical.  Let
\((t_n)_{n\geq0}\) be the Thue--Morse word,

\[
 t_0=0,\qquad t_{2n}=t_n,\qquad t_{2n+1}=1-t_n,
\]

and choose distinct digits \(a<b\), both different from the digit \(c\) in
(5).  Put

\[
 \tau_{10}=\sum_{n\geq0}t_n10^{-n-1},\qquad
 \eta_w={a\over9}+(b-a)\tau_{10}.                              \tag{13}
\]

Termwise addition in (13) has digits at most nine, so there are no carries.
The Thue--Morse word is not eventually constant, hence this is not the
ambiguous eventually-nine decimal expansion.  The decimal digits of
\(\eta_w\) are therefore exactly

\[
 a+(b-a)t_n\in\{a,b\}.
\]

They omit \(c\), hence avoid \(w\).  The selected digit path is 2-automatic.
Its generating function

\[
 T(z)=\sum_{n\geq0}t_nz^n
\]

satisfies the genuine selected-path Mahler equation

\[
 T(z)=(1-z)T(z^2)+{z\over1-z^2}.                               \tag{14}
\]

Bugeaud proves that the Thue--Morse--Mahler number
\(\sum t_n10^{-n}\) has irrationality exponent exactly two.  Rational affine
changes preserve that exponent, so

\[
 \mu(\eta_w)=2.                                                \tag{15}
\]

The word is not eventually periodic, so \(\eta_w\) is irrational.  Its
factor complexity is \(O(L)\), as for every automatic word, and Theorem 1 of
Adamczewski--Bugeaud therefore makes \(\eta_w\) transcendental (equivalently,
their automatic-number Theorem 2 applies).  Thus one and the same
explicit point in \(X_w\) has all of the following:

\[
 \text{selected-path automatic/Mahler structure}
 +\text{ transcendence}+\mu=2.                                \tag{16}
\]

Independently, Fishman's theorem gives a full-relative-dimension set of
badly approximable points in the nine-digit Cantor subset of \(X_w\).
Removing the countable algebraic points leaves transcendental members of
\(X_w\) with \(\mu=2\).  Hence (15) is not an isolated automatic artifact.

The limitation is essential and explicit: no claim is made that
\(e^{i\eta_w}\) is algebraic.  The separator refutes arguments based only on
finite-state language, automatic/Mahler structure, transcendence, or scalar
irrationality.  It does not refute a genuinely mixed theorem using an
algebraic exponential, which is exactly the unresolved possibility in (1).

## 5. Euler's identity at decimal truncations is the original orbit

Let

\[
 q_n=10^n,\qquad p_n=\lfloor q_n\pi\rfloor,qquad
 x_n=q_n\pi-p_n\in(0,1).
\]

Equation (1) gives the exact identity

\[
 e^{ip_n/q_n}+1=1-e^{-ix_n/q_n},
\qquad
 \left|e^{ip_n/q_n}+1\right|\leq {x_n\over q_n}<q_n^{-1}.      \tag{17}
\]

At the first-order normalized scale,

\[
 q_n\bigl(e^{ip_n/q_n}+1\bigr)=ix_n+O(q_n^{-1}).                \tag{18}
\]

But omission of \(w\) is precisely the assertion \(x_n\notin I_w\) for all
\(n\).  Thus normalization of the small exponential form recovers the same
unproved orbit, rather than an independent quantity.  Effective
Lindemann--Weierstrass estimates see the ordinary height of \(p_n/q_n\), not
the regular language containing \(p_n\), and are far below the universal
\(q_n^{-1}\) upper bound in (17).

There is also a structural reason Baker's linear-forms theorem does not apply
directly to the useful difference:

\[
 i(q_n\pi-p_n)=q_n\operatorname{Log}(-1)-ip_n.                  \tag{19}
\]

The second term is algebraic, not a logarithm of an algebraic number.
Writing \(ip_n=p_n\operatorname{Log}(e^i)\) introduces the transcendental
base \(e^i\).  Exponentiating (19) returns (17).

## 6. Two polynomial ledgers

### 6.1 All allowed prefixes: exponential degree, no small integer value

Let \(A_w(n)\) be the zero-padded length-\(n\) integers avoiding \(w\), and
put \(R_n=|A_w(n)|\).  Under the omission hypothesis,

\[
 a_n=\lfloor10^n\theta\rfloor\in A_w(n).
\]

The most direct language polynomial is

\[
 B_n(X)=\prod_{a\in A_w(n)}\bigl(10^n(X-3)-a\bigr)\in\mathbb Z[X]. \tag{20}
\]

It has degree \(R_n\) and leading coefficient \(10^{nR_n}\), so

\[
 \log H(B_n)\geq nR_n\log10.                                  \tag{21}
\]

At \(X=\pi\), the selected factor is \(x_n<1\), while every other factor can
have size comparable with \(10^n\).  The guaranteed upper bound is only

\[
 |B_n(\pi)|<(10^n)^{R_n-1},                                   \tag{22}
\]

which is large.  Dividing (20) by \(10^{nR_n}\) produces a small normalized
product but destroys integrality; clearing denominators returns exactly
(20)--(22).  Regular-language sparsity reduces \(R_n\) from \(10^n\) to
roughly \(\lambda_w^n\), but it does not make the integer polynomial value
small.

### 6.2 Selected tails: a small value with the wrong degree--height scale

A complementary construction does produce small integer polynomial values.
Set

\[
 A_n=\lfloor10^n\pi\rfloor,qquad F(Z)=Z(1-Z),
\]

and

\[
 P_N(X)=\prod_{n=1}^N F(10^nX-A_n)\in\mathbb Z[X].              \tag{23}
\]

Since \(F(x_n)\in(0,1/4]\),

\[
 0<P_N(\pi)\leq4^{-N}.                                        \tag{24}
\]

This smallness is universal; it already holds without word omission.  More
importantly, its cost is exact.  Put \(t=10^n\).  Since \(0<A_n<4t\),

\[
 F(tX-A_n)
 =-t^2X^2+t(1+2A_n)X-A_n(1+A_n)
\]

has coefficient \(\ell^1\)-norm at most \(30t^2\).  Therefore

\[
 \deg P_N=2N,qquad
 H(P_N)\leq30^N10^{N(N+1)},qquad
 \log H(P_N)=O(N^2).                                           \tag{25}
\]

Cijsouw's logarithm measure transfers explicitly from
\(\operatorname{Log}(-1)=i\pi\) to integer polynomials in \(\pi\).  Indeed,
for \(P\in\mathbb Z[X]\) of degree \(D\geq1\) and height \(H\geq1\), put

\[
 Q(Y)=P(-iY)P(iY)\in\mathbb Z[Y].
\]

Then \(Q\ne0\), \(\deg Q\leq2D\),
\(H(Q)\leq(D+1)H^2\), and
\(Q(i\pi)=P(\pi)P(-\pi)\).  Since
\(|P(-\pi)|\leq(D+1)H\max(1,\pi)^D\), Cijsouw's Theorem 2, with these
parameter changes absorbed into its effective constant, gives the shape

\[
 |P(\pi)|>
 \exp\!\left[-C D^2(D+\log H)(1+\log D)^2\right]               \tag{26}
\]

for every nonconstant \(P\in\mathbb Z[X]\) of degree \(D\) and height \(H\).
For (25), one may use the explicit estimate
\(\log H(P_N)\leq9N^2\) for \(N\geq1\).  Thus the exponent on the
right of (26) is at most a constant times
\(44N^4(1+\log(2N))^2\), and substituting (25) gives only

\[
 |P_N(\pi)|>\exp\bigl(-O(N^4\log^2N)\bigr),                    \tag{27}
\]

fully compatible with the upper bound \(\exp(-N\log4)\) in (24).

Replacing \(F(x_n)\) by any fixed univariate polynomial factor that is
uniformly contracted on the survivor changes \(-N\log4\) to another constant
times \(-N\); the same substitution \(x_n=10^nX-A_n\) retains the
degree-\(O(N)\), log-height-\(O(N^2)\) scale.  A nonzero fixed polynomial
cannot vanish on the whole survivor, because that set is uncountable and has
accumulation points.  Allowing the factor degree to grow within this same
direct-product scheme makes both total degree and coefficient height grow as
well.  These
observations audit this product construction only: they do not prove that
every growing-degree construction must worsen (26).  A viable auxiliary-form
proof therefore needs a new compression mechanism, not a sharper constant in
the existing measure.

Status of Sections 5--6: local `proof sketch`; these are exact algebraic and
size ledgers, not a proof that every conceivable auxiliary construction must
fail.

## 7. Primary-literature applicability audit

The following bounded search was rechecked on **2026-08-12 UTC**.  It covered
combinations of *logarithm of an algebraic number*, *automatic/Mahler value*,
*finite-type subshift*, *forbidden word*, *digit complexity*, *restricted
numerator*, *refined Diophantine exponent*, and 2025--2026 follow-ups.

| Primary source | Applicable theorem | Exact boundary here |
|---|---|---|
| [Cijsouw, *Transcendence measures of exponentials and logarithms of algebraic numbers* (1974)](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf), Theorem 2 | Polynomial degree--height measure for a fixed algebraic logarithm; applies to \(i\pi=\operatorname{Log}(-1)\). | Gives (26); omission does not supply a polynomial small enough to beat it. |
| [Adamczewski--Bugeaud, *On the complexity of algebraic numbers I*](https://annals.math.princeton.edu/2007/165-2/p04), Theorems 1--2 | Irrational automatic numbers are transcendental; irrational algebraic digits have superlinear complexity. | \(\pi\) is transcendental already; a proper SFT can have exponential complexity. |
| [Waldschmidt, *Words and Transcendence*](https://arxiv.org/abs/0908.4034) | Survey of the exact word-complexity/Subspace-Theorem boundary. | Records how far even algebraic-number digit occurrence was from normality; it supplies no algebraic-logarithm survivor exclusion. |
| [Bugeaud, *On the rational approximation to the Thue--Morse--Mahler numbers*](https://doi.org/10.5802/aif.2666), main theorem | \(\mu(\sum t_nb^{-n})=2\) for every integer \(b\geq2\). | Supplies the explicit separator (13)--(16), not an algebraic exponential. |
| [Fishman, *Schmidt's game, badly approximable matrices and fractals*](https://arxiv.org/abs/0809.2065), Corollary 3 | Badly approximable points have full relative dimension in the relevant irreducible self-similar sets. | Optimal scalar nonapproximation coexists with omission. |
| [Adamczewski--Faverjon, *Méthode de Mahler...*](https://doi.org/10.1112/plms.12038), Corollary 1.8 | A Mahler value at an algebraic point is in the coefficient number field or is transcendental. | Does not treat \(e^{i f(\alpha)}\) and does not select a path from an SFT. |
| [Adamczewski--Faverjon, *A Liouville-Type Inequality for Values of Mahler M-Functions* (2026)](https://arxiv.org/abs/2604.08208), Theorems 1.1--1.2 and Corollary 5.2 | Polynomial measure for arbitrary M-values; no M-value is a U-number. | Still a polynomial degree--height output; no mixed exponential or cylinder theorem. |
| [Fischler--Rivoal, *Transcendence of values of logarithms of E-functions* (2026)](https://doi.org/10.1007/s00208-026-03374-z), consequence after Theorem 3 | For \(\pi\), \(|\pi-a/b|\geq\exp(-cb^d)\) via the simple zero of \(\sin z\). | At \(b=10^N\), exponentially weaker than the universal truncation error \(10^{-N}\), and numerator-language blind. |
| [Nguyen, *Transcendence and measures via the refined Diophantine exponent* (2026)](https://arxiv.org/abs/2605.30606v2), Theorems A--B | Strong selected-word near-periodicity implies transcendence and, under stronger hypotheses, measures. | Positive-entropy SFT membership does not imply the recurrence hypothesis; the implication cannot be reversed from transcendence. |
| [Chow--Varjú--Yu, *Counting rationals and Diophantine approximation in missing-digit Cantor sets*](https://arxiv.org/abs/2402.18395v2), Theorems 1.2, 1.4, 1.8 | Aggregate rational counts and metric/dimension results in missing-digit sets. | Does not decide membership of the fixed named point \(\pi\); one forbidden word is more general than one missing digit. |
| [Bugeaud--Kim, arXiv:2510.02059v2](https://arxiv.org/abs/2510.02059v2) and [Bugeaud--Kaneko--Kim, arXiv:2510.17177v3](https://arxiv.org/abs/2510.17177v3) | Current linear factor-complexity bounds from restricted irrationality exponents near two. | The known \(\pi\) bound is outside their useful ranges, and even their conclusions are exponentially below \(10^m\) coverage. |

Exact PDF pins (SHA-256; fetched or reverified 2026-08-12 UTC):

| Source/version | SHA-256 |
|---|---|
| Cijsouw 1974 | `fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a` |
| Adamczewski--Bugeaud, arXiv:math/0511674 | `e3bd2934800e94dd27930d43d47abc44f760de7e90320d1d014b372b681be9a0` |
| Waldschmidt, arXiv:0908.4034 | `735e483213db56fb0a7c07a5293d63b22d23f1f47ae5d2c83b488b8caaff42c3` |
| Bugeaud, Thue--Morse--Mahler journal PDF | `6d7607e8a70e8524630daa45001192113487d9af1f1588c96556283445c7460c` |
| Fishman, arXiv:0809.2065v1 | `3778e06391c3aacde0012f7145a11549ee1311353bbd4bd8d28546f4b02963e5` |
| Adamczewski--Faverjon, arXiv:1508.07158v2 | `d44bec7a6c2b016d4a65971e60e583a9d013e8389948c52393911f5b12b7e7dd` |
| Adamczewski--Faverjon, arXiv:2604.08208v1 | `c428a9a555b8d7abeb25f3e8a02c8f7880c640e7fe6a2f85c411ca1b68f1945c` |
| Fischler--Rivoal, final Math. Ann. 2026 PDF | `86669c0103d2a589c9a45970734a9ebac47c737382c015fa026b546960c0301d` |
| Nguyen, arXiv:2605.30606v2 | `2cfb651d65a9960bc0385a2658005752dd899bb4a8919b08d91c8319a18a87b2` |
| Chow--Varjú--Yu, arXiv:2402.18395v2 | `5bb31a65f491bd85a72864938f610cddf04e45bac6e6f635e508ff6cf70b67bf` |
| Bugeaud--Kim, arXiv:2510.02059v2 | `fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330` |
| Bugeaud--Kaneko--Kim, arXiv:2510.17177v3 | `c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01` |

This is a bounded search, not a claim to have exhausted all literature.

## 8. Strongest remaining theorem and bottom line

The genuinely new bridge would have to be at least one of the following.

1. **Algebraic-logarithm survivor exclusion:** for every proper decimal SFT
   \(X\), prove that the base-10 word of
   \(-i\operatorname{Log}(-1)=\pi\) does not lie in \(X\).
2. **Language-sensitive exponential separation:** for every forbidden word
   \(w\), prove a lower bound for
   \(|e^{ip/10^n}+1|\) which is stronger specifically for
   \(p\) whose zero-padded decimal prefix avoids \(w\), at the \(10^{-n}\)
   scale needed to contradict (17).
3. **Compressed auxiliary form:** turn all survivor constraints into a
   nonzero integer polynomial or logarithmic/exponential form with
   smallness beating (26), while avoiding the degree and height costs in
   (20)--(27).

The first statement is essentially V1 in logarithmic language.  The second
and third are the only potentially different arithmetic routes isolated by
this audit.  Existing automatic/Mahler, irrationality-measure, Subspace-
Theorem, E-zero, and metric Cantor-set results stop strictly before them.

Accordingly, this branch produces a falsified obstruction and an exact
exponent ledger, but no complete proof of (2).
