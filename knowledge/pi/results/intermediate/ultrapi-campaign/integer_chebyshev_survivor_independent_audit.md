# Independent audit: integer--Chebyshev survivor attack

Audit date: **2026-08-12 UTC**

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Audited report:
[`integer_chebyshev_survivor_attack.md`](integer_chebyshev_survivor_attack.md)

Audited report SHA-256:
`27252531f03e8a8826fdb6cd471bd447990c89ff881bcd5e24f357f307eb5192`

Audited checker:
[`integer_chebyshev_survivor_attack_check.py`](integer_chebyshev_survivor_attack_check.py)

Audited checker SHA-256:
`89f4114b0faedc312b08e9338d94f944ac91de4f3febdb4b3804664e27ad766a`

Independent checker:
[`integer_chebyshev_survivor_independent_check.py`](integer_chebyshev_survivor_independent_check.py)

Independent checker SHA-256:
`f03e9f5affb008e0a4b8557355c6bc80adfc2e49d1f11e6ee16937701d8ad4fd`

## Verdict

**PASS for the report's stated negative conclusion and quantified method
separator.  No proof of V1 follows.**

The survivor/capacity argument, integer-Chebyshev bracket, real-orbit product
ledger, Dickson trace lift, minimum monomial clearing, Euler-power family,
Cijsouw substitutions, and sufficient compression criterion all survive
independent derivation.  The branch correctly concludes that its explicit
auxiliary-polynomial families do not contradict the available transcendence
measures.

One narrow wording defect was found and corrected in the primary report and
checker before their hashes above were taken.  The finite boxed minimax search
uses decimal prefixes evaluated as terminating rational numbers.  Such nodes
need not belong to the infinite survivor \(K_w\); for \(w=0\), for example,
the prefix \(11\) gives \(0.11000\ldots\), which contains the forbidden digit,
and its alternative expansion \(0.10999\ldots\) also contains it.  The files
now call them **admissible-prefix truncation nodes** and explicitly retain the
output at status `experiment`.  This correction does not affect any
proof-relevant identity or the negative verdict.

The analytic reductions remain a `proof sketch`; they are not in the Lean
verified track.  The bounded primary-source audit is `literature-checked` as
of the date above.  The canonical V1 statement remains a `conjecture`.  This
work is neither a candidate resolution nor a verified resolution.

## 1. Survivor and capacity derivation

Assume one nonempty word \(w\) is omitted and define \(K_w\) as the continuous
decimal image of the compact symbolic survivor.  For
\(p_j=\lfloor 10^j\pi\rfloor\),

\[
 x_j=10^j\pi-p_j
\]

is the decimal tail beginning after digit \(j\), so \(x_j\in K_w\) for every
\(j\geq0\).  Irrationality of \(\pi\) removes the terminating-expansion
ambiguity for this conditional inclusion.

Choose a digit \(c\) occurring in \(w\), then choose two distinct
\(a,b\in\{2,3,6,7\}\setminus\{c\}\).  Every sequence on \(\{a,b\}\) omits
\(c\), hence omits \(w\), and its decimal image \(C_{a,b}\) is contained in
\(K_w\).  The two maps

\[
 x\longmapsto {a+x\over10},\qquad
 x\longmapsto {b+x\over10}
\]

have disjoint images and common ratio \(1/10\).  The fair Bernoulli measure
therefore has a Frostman bound \(\mu(B(x,r))\leq C_s r^s\) for every
\(s<\log2/\log10\).  The layer-cake calculation

\[
 \iint\log^+{1\over|x-y|}\,d\mu(x)d\mu(y)
 =\int_0^\infty
   (\mu\times\mu)\{|x-y|<e^{-t}\}\,dt
 \leq C_s\int_0^\infty e^{-st}\,dt
\]

is finite.  Thus \(C_{a,b}\), and by monotonicity \(K_w\), have positive
logarithmic capacity.

On \([2/9,7/9]\), the derivative magnitude of \(2\cos x\) lies between
\(2\sin(2/9)>0\) and \(2\sin(7/9)<2\).  The restriction is bi-Lipschitz, so
the pushed-forward Cantor measure again satisfies a positive-exponent
Frostman bound.  Hence the cosine image \(J_w\) has positive capacity.  The
interval formula \(\operatorname{cap}([A,B])=(B-A)/4\) gives

\[
 0<\operatorname{cap}(K_w)\leq{1\over4},\qquad
 0<\operatorname{cap}(J_w)
 \leq{1-\cos1\over2}<{1\over4}.
\]

The last strict inequality follows from \(1<\pi/3\), hence
\(\cos1>1/2\).  No finite digit computation is used.

## 2. Integer-Chebyshev bracket

Let \(M_D(E)\) be the infimum of \(\lVert P\rVert_E\) over nonzero integer
polynomials of degree at most \(D\).  If \(P\) has exact degree \(d\geq1\)
and leading coefficient \(a_d\), divide it by \(a_d\).  If \(\tau_d(E)\)
is the degree-\(d\) monic Chebyshev norm, submultiplicativity and the
Chebyshev-capacity theorem give

\[
 \tau_d(E)^{1/d}\geq\operatorname{cap}(E).
\]

Since \(|a_d|\geq1\),

\[
 \lVert P\rVert_E\geq\operatorname{cap}(E)^d
 \geq\operatorname{cap}(E)^D
\]

when \(0<\operatorname{cap}(E)<1\).  A nonzero constant integer has norm at
least one, so it satisfies the same final bound.  Taking infima, \(D\)-th
roots, and the limit proves

\[
 t_{\mathbb Z}(E)\geq\operatorname{cap}(E)>0.
\]

Pritsker's Theorem 2.1 with weight \(1\) states the matching Hilbert--Fekete
upper bound

\[
 t_{\mathbb Z}(E)\leq\sqrt{\operatorname{cap}(E)}.
\]

Both \(K_w\) and \(J_w\) are compact real sets, so the theorem applies.  Since
their capacities are below one, the full bracket in the primary report is
correct.  In particular, the lower bound
\(\lVert P_D\rVert_E\geq\operatorname{cap}(E)^D\) really does rule out
uniform \(\exp[-\omega(D)]\) smallness for nonzero integer polynomials of
degree at most \(D\).

## 3. Real decimal-orbit product

For fixed \(R(X)=\sum_{k=0}^d r_kX^k\in\mathbb Z[X]\setminus\{0\}\), put

\[
 F_{N,R}(X)=\prod_{j=0}^{N-1}R(10^jX-p_j).
\]

Every factor is nonzero, so the product is a nonzero integer polynomial.
Transcendence of \(\pi\) implies \(F_{N,R}(\pi)\ne0\).  If
\(\rho=\lVert R\rVert_{K_w}<1\), the omission hypothesis gives the exact
upper bound \(|F_{N,R}(\pi)|\leq\rho^N\).

The leading term is obtained independently as

\[
 \operatorname{lc}(F_{N,R})
 =r_d^N\prod_{j=0}^{N-1}10^{jd}
 =r_d^N10^{dN(N-1)/2}.
\]

For coefficient length \(L\), using \(p_j<4\cdot10^j\),

\[
\begin{aligned}
 L(R(10^jX-p_j))
 &\leq\sum_{k=0}^d|r_k|(10^j+p_j)^k\\
 &\leq L(R)(5\cdot10^j)^d,
\end{aligned}
\]

and length is submultiplicative.  This proves the report's degree, leading
coefficient, and height bounds.  For fixed \(R\), the logarithmic height is
both \(\Omega_R(N^2)\), from the leading coefficient, and \(O_R(N^2)\), from
the length bound.

## 4. Exact Cijsouw transfer for \(\pi\)

The primary report abbreviates the passage from Cijsouw's logarithm theorem
to an integer polynomial in \(\pi\).  The passage is sound, and the omitted
ledger is as follows.

Let \(P\in\mathbb Z[X]\) have degree \(D\geq1\) and height \(H\), and set

\[
 Q(X)=P(-iX)P(iX).
\]

The odd powers cancel, so \(Q\in\mathbb Z[X]\),
\(\deg Q=2D\), and

\[
 H(Q)\leq L(Q)\leq L(P)^2\leq((D+1)H)^2.
\]

For the fixed branch \(\operatorname{Log}(-1)=i\pi\),

\[
 Q(i\pi)=P(\pi)P(-\pi).
\]

Cijsouw's Theorem 2 applied to \(Q\), followed by

\[
 |P(-\pi)|\leq(D+1)H\max(1,\pi)^D,
\]

gives, after enlarging the fixed effective constant,

\[
 |P(\pi)|>
 \exp\!\left[-C D^2(D+\log H)(1+\log D)^2\right].
\]

For \(D=dN\) and fixed \(R\), the orbit-product height ledger therefore
produces only

\[
 |F_{N,R}(\pi)|>
 \exp[-O_R(N^4\log^2N)],
\]

which is compatible with the certified \(\rho^N\) upper bound.  If the
detector degree varies, positive capacity permits certified uniform
smallness only on the \(\exp[-\Theta_w(d)]\) scale, whereas the leading
coefficient already places the Cijsouw penalty on at least the
\(d^3N^4(1+\log(dN))^2\) scale.  This is a method comparison, not a
contradiction and not a universal no-go theorem for all auxiliary forms.

## 5. Dickson trace lift and minimum monomial clearing

The recurrence

\[
 C_0=2,\quad C_1=X,\quad C_{n+1}=XC_n-C_{n-1}
\]

gives by induction

\[
 C_n(Z+Z^{-1})=Z^n+Z^{-n}.
\]

For \(j\geq1\), \(10^j\) is even, so

\[
 C_{p_j}(e^i+e^{-i})=2\cos p_j=2\cos x_j.
\]

The shifted Laurent product

\[
 G_{N,R}(Z)=Z^{d\sum p_j}
 \prod_{j=1}^N R(Z^{p_j}+Z^{-p_j})
\]

is in \(\mathbb Z[Z]\), has degree exactly \(2d\sum p_j\) when \(R\) has
exact degree \(d\), and satisfies

\[
 L(G_{N,R})\leq(2^dL(R))^N.
\]

The report states the weaker degree inequality, so it is sound.  At \(e^i\),
its modulus is at most \(\rho^N\); nonvanishing follows because \(e^i\) is
transcendental.

For \(R(Y)=Y-2\), each Laurent factor has endpoint exponents \(-p, p\)
with nonzero coefficients.  Its support span is \(2p\), and

\[
 Z^p(Z^p+Z^{-p}-2)=(Z^p-1)^2.
\]

Endpoint coefficients in the product do not cancel, so the combined support
span is \(2\sum p_j\).  Thus the report's clearing has minimum degree among
monomial shifts of this Laurent product.  The report correctly limits this
claim to the chosen detector; it is not a lower bound for every conceivable
determinant or auxiliary construction.

The elementary prefix bounds

\[
 3\cdot10^j\leq p_j<4\cdot10^j
\]

sum to the stated bounds on \(s_N=\sum_{j=1}^Np_j\).  Hence
\(\deg G_N=\Theta(10^N)\), while \(H(G_N)\leq4^N\).  Cijsouw's Theorem 1
for the fixed algebraic exponent \(i\) gives

\[
 |P(e^i)|>\exp[-C D^2(D+\log H)],
\]

so this family receives only a lower bound of order
\(\exp[-O(10^{3N})]\), fully compatible with its
\(\exp[-\Theta(N)]\) certified upper bound.

## 6. Euler-power family

The identity \(C_3(X)=X^3-3X\) gives

\[
 Z^3(C_3(Z+Z^{-1})+2)=(Z^3+1)^2.
\]

Consequently \(S_D(Z)=(Z^3+1)^{2D}\) has degree \(6D\), length \(4^D\),
and height \(\binom{2D}{D}\).  Euler's identity and
\(0<\pi-3<1/7\) give

\[
 |e^{3i}+1|=2\sin((\pi-3)/2)<\pi-3<1/7,
\]

hence \(0<|S_D(e^i)|<49^{-D}\).  Cijsouw supplies only
\(\exp[-O(D^3)]\), so the inequalities are compatible.  This family is a
power of one fixed nonzero value and contains no survivor-specific
information.

## 7. Sufficient compression criterion

For a nonconstant \(P_N\in\mathbb Z[Z]\), Cijsouw's Theorem 1 implies

\[
 -\log|P_N(e^i)|
 < C_0(\deg P_N)^2(\deg P_N+\log H(P_N))
\]

for a fixed effective \(C_0\).  Therefore the parameter-free condition

\[
 { -\log|P_N(e^i)|
  \over
   (\deg P_N)^2(\deg P_N+\log H(P_N))}
 \longrightarrow\infty
\]

is indeed sufficient for a contradiction.

The report's more concrete lemma is also sufficient.  If
\(\deg P_N\leq C_wN\) and \(\log H(P_N)\leq C_wN\), then

\[
 (\deg P_N)^2(\deg P_N+\log H(P_N))
 \leq2C_w^3N^3.
\]

An upper bound \(|P_N(e^i)|\leq\exp(-N^{3+\varepsilon_w})\) contradicts
Cijsouw for all sufficiently large \(N\).  A nonzero constant polynomial
cannot satisfy this small-value condition, so the lemma does not need a
separate nonconstant hypothesis once \(N\) is large.

This compression lemma remains a `conjecture`.  Neither positive-capacity
Chebyshev minimization nor the two audited orbit products prove it.

## 8. Primary-source check

The following primary sources were fetched again on **2026-08-12 UTC** and
their hashes independently reproduced.

| Primary source | Statement checked | SHA-256 |
|---|---|---|
| [Pritsker, *Small polynomials with integer coefficients*](https://arxiv.org/abs/math/0101166), equations (1.3), (1.5)--(1.10), Theorem 2.1 and Remark 2.2 | Definition of \(t_{\mathbb Z}\), equality of classical Chebyshev constant and capacity, and \(t_{\mathbb Z}(E)\leq\sqrt{\operatorname{cap}(E)}\) for compact real \(E\). | `8685ecf5001fe76271c5fd2a9b50783967d2c1a708e6ace52d215b2231cbc8c2` |
| [Borwein--Pinner--Pritsker, *Monic integer Chebyshev problem*](https://arxiv.org/abs/1307.5362), equations (1.1)--(1.9), Proposition 1.2 | Confirms the distinction between classical, nonmonic integer, and monic integer Chebyshev constants and the capacity threshold quoted by the report. | `d703e1d94a115b86ba510549c599dbf01845dc153cc83fd77a40594a43761d27` |
| [Cijsouw, *Transcendence measures of exponentials and logarithms of algebraic numbers*](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf), Theorems 1--2, printed p. 164 | With \(S=D+\log H\), Theorem 1 gives \(\exp(-C D^2S)\) for \(e^\alpha\); Theorem 2 gives \(\exp(-C D^2S(1+\log D)^2)\) for a fixed \(\log\alpha\). | `fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a` |

The hypotheses match the two applications: \(i\) is nonzero algebraic for
Theorem 1, and \(-1\) is algebraic and neither zero nor one, with fixed branch
\(\operatorname{Log}(-1)=i\pi\), for Theorem 2.  This bounded source audit is
`literature-checked`; it does not claim that all related literature has been
exhausted.

## 9. Independent deterministic check

Exact command:

```text
.venv/bin/python work/ultrapi-resume/integer_chebyshev_survivor_independent_check.py
```

Output:

```text
PASS: independent capacity skeleton, orbit/trace algebra, height ledgers, Cijsouw transfer/scales, Euler powers, and compression threshold
SCOPE: admissible-prefix truncations are not generally points of K_w; their boxed minimax output remains experiment only
VERDICT: no contradiction and no proof of V1
```

The checker independently reconstructs the Dickson recurrence, general trace
lift, minimum clearing for \(Y-2\), real-orbit leading coefficient and length
bounds, the integer polynomial \(Q(X)=P(-iX)P(iX)\), Euler-power coefficients,
Cijsouw parameter scales, and the cubic compression threshold.  Its finite
checks are `experiment`; the analytic proof inputs are the arguments and
primary sources recorded above.

## 10. Final claim status

The audited branch establishes a useful `proof sketch` separator:
positive-capacity survivor information yields only exponential-in-degree
uniform integer-polynomial contraction, the direct real orbit pays quadratic
log-height, and the exact \(e^i\) lift pays exponential degree.  Those facts
explain precisely why the three displayed constructions do not reach the
sufficient compression ratio.

They do **not** exclude every possible auxiliary determinant, interpolation
scheme, or digit-sensitive cancellation.  Most importantly, they do not show
that a word-omitting decimal expansion of \(\pi\) is impossible.  V1 therefore
does not follow and remains a `conjecture`.
