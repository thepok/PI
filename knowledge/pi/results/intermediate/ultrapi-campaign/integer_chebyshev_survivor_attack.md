# Integer-Chebyshev and capacity attack on a decimal survivor

Audit date: **2026-08-12 UTC**
Status: `literature-checked` bounded primary-source audit with local
`proof sketch` reductions and finite `experiment` checks
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

No contradiction, and hence no proof of V1, was obtained from integer
Chebyshev polynomials, logarithmic capacity, Dickson--Chebyshev trace
polynomials, or the direct fixed-\(e^i\) lift.

The branch does give a sharp structural separator.  For every nonempty
forbidden word \(w\), its compact decimal survivor \(K_w\), and also its
cosine image

\[
 J_w=\{2\cos x:x\in K_w\},
\]

have positive logarithmic capacity.  Their nonmonic integer Chebyshev
constants satisfy

\[
 0<\operatorname{cap}(E)\le t_{\mathbb Z}(E)
 \le\sqrt{\operatorname{cap}(E)}<1,
 \qquad E=K_w,J_w.                                      \tag{1}
\]

Thus optimized integer polynomials can be uniformly small on a survivor,
but only at an exponential-in-degree rate; positive capacity rules out a
uniform superexponential gain.

Two exact auxiliary ledgers show why that rate does not cross a known
transcendence measure.

1. An optimized fixed detector \(R\) applied to the first \(N\) decimal
   tails gives an integer polynomial in \(\pi\) of degree \(dN\), unavoidable
   log-height \(\Omega(dN^2)\), and value at most \(\rho^N\).  Cijsouw's
   algebraic-logarithm measure then gives only
   \(\exp[-O_R(N^4\log^2N)]\), compatible with \(\rho^N\).
2. The minimum-degree Laurent clearing of the corresponding fixed-\(e^i\)
   Chebyshev detector is

   \[
     G_N(Z)=\prod_{j=1}^N(Z^{p_j}-1)^2,
     \qquad p_j=\lfloor10^j\pi\rfloor.                 \tag{2}
   \]

   It has degree \(2\sum p_j=\Theta(10^N)\), height at most \(4^N\), and
   \(0<|G_N(e^i)|\le[4\sin^2(1/2)]^N\).  Cijsouw's fixed-exponential
   measure is only \(\exp[-O(10^{3N})]\) at that degree.

Even the unusually cheap exact family

\[
 S_D(Z)=(Z^3+1)^{2D}                                   \tag{3}
\]

has degree \(6D\), exact height \(\binom{2D}{D}\), and

\[
 0<|S_D(e^i)|<49^{-D};                                  \tag{4}
\]

the applicable lower bound deteriorates as \(\exp[-O(D^3)]\).  Powering a
single already-small nonzero value supplies no contradiction.

The canonical statement therefore remains a `conjecture`.  This report is
not a candidate resolution.

This branch is independent of both the T68 simultaneous-primary Hutton
theorem and the Furstenberg fixed-multiplier return reduction recorded in
`ultrapi.md`.  T68 studies exact prime-power denominator layers of rational
Hutton truncations; the fixed-return branch studies
\(\|(10^N-c)\pi\|\).  Here there are no Hutton truncations, multiplicative
returns, or BBP residues: the sole conditional input is membership of every
decimal tail in one compact survivor, and the sole arithmetic special value
is \(e^{i\pi}=-1\) (equivalently \(e^i\) or
\(\operatorname{Log}(-1)=i\pi\)).

## 1. Exact statement and conditional survivor

Write the unique nonterminating decimal expansion

\[
 \pi=3+\alpha,
 \qquad
 \alpha=\sum_{n\ge1}d_n10^{-n},
 \qquad d_n\in\{0,\ldots,9\}.
\]

The canonical V1 statement is

\[
 \forall m\ge1\ \forall w\in\{0,\ldots,9\}^m\ \exists k\ge1:
 d_kd_{k+1}\cdots d_{k+m-1}=w.                       \tag{5}
\]

Leading zeroes in \(w\) are significant and occurrences are contiguous.
This branch assumes the exact negation for one fixed nonempty word \(w\).
It does not address either infinite-string reading of the original wording:
V2 (an arbitrary infinite word occurs as a contiguous tail) or V3 (an
arbitrary infinite word occurs as a subsequence).  Thus every quantifier in
this report is for canonical finite-word V1.
Let \(X_w\) be the closed set of infinite digit sequences avoiding \(w\),
and let

\[
 K_w=\left\{\sum_{n\ge1}a_n10^{-n}:(a_n)\in X_w\right\}\subset[0,1].
                                                               \tag{6}
\]

This symbolic-image definition makes \(K_w\) compact even at the countably
many points with two decimal representations.  Since \(\alpha\) is
irrational, no representation ambiguity affects the conditional inclusion
\(\alpha\in K_w\).

Put

\[
 p_j=\lfloor10^j\pi\rfloor,
 \qquad x_j=10^j\pi-p_j=\{10^j\alpha\}.               \tag{7}
\]

The omission hypothesis gives

\[
 x_j\in K_w\qquad(j\ge0).                              \tag{8}
\]

This is the full information supplied by word avoidance: every tail lies in
the same positive-entropy survivor, but the finite automaton does not choose
which outgoing digit occurs.

## 2. The survivor has positive capacity

Choose a digit \(c\) occurring in \(w\).  Every sequence omitting \(c\)
avoids \(w\).  From the four digits \(\{2,3,6,7\}\), choose two distinct
digits \(a,b\ne c\).  The two-digit Cantor set

\[
 C_{a,b}=\left\{\sum_{n\ge1}\varepsilon_n10^{-n}:
                  \varepsilon_n\in\{a,b\}\right\}                 \tag{9}
\]

is contained in \(K_w\), lies in \([2/9,7/9]\), and has Hausdorff
dimension \(\log2/\log10>0\).  This last assertion follows directly from
the two disjoint similarities \(x\mapsto(a+x)/10\) and
\(x\mapsto(b+x)/10\).

For completeness, positive logarithmic capacity needs no black-box
dimension theorem here.  The fair Bernoulli measure on \(C_{a,b}\) obeys,
for every \(s<\log2/\log10\),

\[
 \mu(B(x,r))\le C_s r^s.                               \tag{10}
\]

Integrating the shell bound in (10) makes
\(\iint\log^+(1/|x-y|)\,d\mu(x)d\mu(y)\) finite.  Hence
\(\operatorname{cap}(C_{a,b})>0\), and monotonicity gives

\[
 0<\operatorname{cap}(K_w)\le\operatorname{cap}([0,1])={1\over4}.
                                                               \tag{11}
\]

The map \(x\mapsto2\cos x\) is bi-Lipschitz on \([2/9,7/9]\), so the
image of \(C_{a,b}\) again has positive Hausdorff dimension and positive
capacity.  Since cosine decreases on \([0,1]\),

\[
 0<\operatorname{cap}(J_w)
 \le \operatorname{cap}([2\cos1,2])
 ={1-\cos1\over2}<{1\over4}.                         \tag{12}
\]

The interval-capacity formula used in (11)--(12) is
\(\operatorname{cap}([A,B])=(B-A)/4\).

Status: local `proof sketch`; every estimate is exposed above.  No digit
calculation for \(\pi\) is used.

## 3. What optimized integer Chebyshev polynomials can supply

For an infinite compact real set \(E\), define the nonmonic integer
Chebyshev constant

\[
 t_{\mathbb Z}(E)=
 \lim_{D\to\infty}
 \inf_{\substack{0\ne P\in\mathbb Z[X]\\\deg P\le D}}
 \|P\|_E^{1/D}.                                      \tag{13}
\]

The Hilbert--Fekete bound gives

\[
 t_{\mathbb Z}(E)\le\sqrt{\operatorname{cap}(E)}.     \tag{14}
\]

The reverse elementary inequality needed here is
\(t_{\mathbb Z}(E)\ge\operatorname{cap}(E)\).  Indeed, if \(P\) has
exact degree \(d\le D\), its leading coefficient is a nonzero integer.
After dividing by that coefficient, the defining monic Chebyshev inequality
gives

\[
 \|P\|_E\ge\operatorname{cap}(E)^d
          \ge\operatorname{cap}(E)^D,                \tag{15}
\]

because the capacities in (11)--(12) are below one.  Equations
(11)--(15) prove (1).

This answers the capacity question at the scale relevant to the attack:

* optimized integer polynomials do tend uniformly to zero on \(K_w\) and
  \(J_w\);
* their best asymptotic scale is \(\exp[-\Theta_w(D)]\);
* no uniform family on the entire survivor can have
  \(\|P_D\|_E=\exp[-\omega(D)]\).

That last point is important.  Capacity can improve a constant in an
auxiliary upper bound, but it cannot manufacture the superlinear exponent
needed to challenge the degree dependence of present transcendence measures.

Status: `literature-checked` for (13)--(14) and the capacity/Chebyshev
identification; (15) is the standard one-line monic comparison.

## 4. Exact real-orbit product ledger

Let

\[
 R(X)=\sum_{k=0}^d r_kX^k\in\mathbb Z[X]\setminus\{0\},
 \qquad
 L(R)=\sum_{k=0}^d|r_k|,
 \qquad
 \rho=\|R\|_{K_w}<1.                                \tag{16}
\]

Here \(R\) may be a degree-\(d\) integer-Chebyshev optimizer or any
explicit detector.  Under (8), define

\[
 F_{N,R}(X)=\prod_{j=0}^{N-1}R(10^jX-p_j)\in\mathbb Z[X].       \tag{17}
\]

At the target point,

\[
 0<|F_{N,R}(\pi)|=\prod_{j=0}^{N-1}|R(x_j)|\le\rho^N.          \tag{18}
\]

Strict nonvanishing follows because \(F_{N,R}\) is a nonzero integer
polynomial and \(\pi\) is transcendental.

The cost is exact.  Since \(p_j<4\cdot10^j\),

\[
\begin{aligned}
 \deg F_{N,R}&=dN,\\
 |\operatorname{lc}F_{N,R}|
   &=|r_d|^N10^{dN(N-1)/2},                                      \tag{19}\\
 H(F_{N,R})&\le L(F_{N,R})\\
 &\le L(R)^N5^{dN}10^{dN(N-1)/2}.                                \tag{20}
\end{aligned}
\]

Equation (19) proves that the quadratic log-height term is not an artifact
of a loose coefficient estimate; it is already present in the leading
coefficient.  Equation (20) follows from

\[
 L(R(10^jX-p_j))
 \le L(R)(10^j+p_j)^d
 \le L(R)(5\cdot10^j)^d.                         \tag{21}
\]

Cijsouw's Theorem 2 gives, for every nonconstant
\(P\in\mathbb Z[X]\) of degree \(D\) and height \(H\),

\[
 |P(\pi)|>
 \exp\!\left[-C D^2(D+\log H)(1+\log D)^2\right],              \tag{22}
\]

after the fixed algebraic change from
\(i\pi=\operatorname{Log}(-1)\) to a polynomial in \(\pi\).
Substituting (19)--(20), for fixed \(R\), yields only

\[
 |F_{N,R}(\pi)|>\exp[-O_R(N^4\log^2N)].                         \tag{23}
\]

This is fully compatible with (18), whose exponent is merely linear in
\(N\).  More quantitatively, if a capacity-scale optimizer has
\(-\log\rho=\Theta_w(d)\), then the **certified** upper-bound exponent is
\(A^{\rm cert}_{N,d}=\Theta_w(dN)\), whereas the exponent paid in (22),
using the unavoidable leading-coefficient height (19), is

\[
 B_{N,d}=\Omega_w\!\left(
     d^3N^4(1+\log(dN))^2
   \right).                                             \tag{23a}
\]

The ratio \(A^{\rm cert}_{N,d}/B_{N,d}\) is therefore at most
\(O_w((d^2N^3(1+\log(dN))^2)^{-1})\), tending to zero.  Taking a
higher-degree Chebyshev optimizer makes this comparison worse rather than
better.  Positive capacity forbids a superlinear uniform gain in \(d\).

The special choice \(R(X)=X(1-X)\) recovers the universal selected-tail
product already audited in
[`subshift_log_algebraic_bridge.md`](subshift_log_algebraic_bridge.md).
The new point here is that replacing that factor by a survivor-optimized
integer Chebyshev detector cannot change the linear smallness scale, while
(19) shows the orbit-substitution height cost is intrinsic.

Status: local `proof sketch`; the identities and bounds are checked exactly
by the companion program.

## 5. Dickson--Chebyshev lift to the fixed exponential

Let \(C_n\in\mathbb Z[X]\) be the trace/Dickson polynomial

\[
 C_0=2,\qquad C_1=X,\qquad C_{n+1}=XC_n-C_{n-1}.                  \tag{24}
\]

It satisfies the exact identity

\[
 C_n(Z+Z^{-1})=Z^n+Z^{-n}.                         \tag{25}
\]

Set \(u=e^i+e^{-i}=2\cos1\).  For \(j\ge1\), \(10^j\) is even, so

\[
 C_{p_j}(u)=2\cos p_j
 =2\cos(10^j\pi-x_j)=2\cos x_j\in J_w.             \tag{26}
\]

Take \(R\in\mathbb Z[Y]\) of degree \(d\), length \(L(R)\), and
\(\|R\|_{J_w}\le\rho<1\).  With \(s_N=\sum_{j=1}^Np_j\), the exact
Laurent clearing is

\[
 G_{N,R}(Z)=Z^{ds_N}
 \prod_{j=1}^N R(Z^{p_j}+Z^{-p_j})\in\mathbb Z[Z].                \tag{27}
\]

It obeys

\[
\begin{aligned}
 \deg G_{N,R}&\le2ds_N,\\
 H(G_{N,R})&\le L(G_{N,R})\le(2^dL(R))^N,                         \tag{28}\\
 0<|G_{N,R}(e^i)|&\le\rho^N.                                    \tag{29}
\end{aligned}
\]

For (28), expand each \((Z^p+Z^{-p})^k\): its Laurent coefficient
length is \(2^k\).  Nonvanishing in (29) follows from Lindemann's theorem,
because \(e^i\) is transcendental and (27) is a nonzero integer polynomial.

The degree is the fatal cost.  Since

\[
 {10\over3}(10^N-1)
 \le s_N
 <{40\over9}(10^N-1),                              \tag{30}
\]

the polynomial degree in (28) is exponential in the number of controlled
decimal tails.

### 5.1 Minimum-degree clearing for the simplest detector

The explicit integer detector

\[
 R(Y)=Y-2,
 \qquad
 \|R\|_{J_w}\le2(1-\cos1)<1                         \tag{31}
\]

already contracts on the whole ambient interval, independently of \(w\).
For one exponent \(p\), its Laurent support is \(\{-p,0,p\}\), of span
\(2p\).  Therefore every monomial clearing has polynomial degree at least
\(2p\), and

\[
 Z^p(Z^p+Z^{-p}-2)=(Z^p-1)^2                       \tag{32}
\]

attains that minimum.  For all \(N\), (27) becomes exactly (2); its Laurent
support has span \(2s_N\), so the global clearing is again minimum-degree.
Moreover,

\[
\begin{aligned}
 \deg G_N&=2s_N,\\
 H(G_N)&\le L(G_N)\le4^N,                            \tag{33}\\
 |G_N(e^i)|
 &=\prod_{j=1}^N4\sin^2(x_j/2)
 \le[4\sin^2(1/2)]^N.                               \tag{34}
\end{aligned}
\]

This is the requested optimized ledger: (32) proves the chosen Laurent
detector has been cleared with the least possible degree, rather than with a
loose resultant bound.

Cijsouw's Theorem 1 gives, for a nonzero integer polynomial of degree \(D\)
and height \(H\),

\[
 |P(e^i)|>\exp[-C D^2(D+\log H)].                    \tag{35}
\]

Substitution of (30), (33) gives only

\[
 |G_N(e^i)|>\exp[-O(10^{3N})],                       \tag{36}
\]

again compatible with the \(\exp[-\Theta(N)]\) upper bound (34).  A
word-specific extremal \(R\) can improve the constant in (29), but (1)
keeps the gain exponential in \(d\), while (30) remains unchanged.

The exponent deficit is especially stark in this fixed-exponential form.
For fixed \(d\), the survivor information certifies only

\[
 -\log|G_{N,R}(e^i)|\ge
 A_N^{\rm cert}:=-N\log\rho=\Theta_w(N),
\]

while (35) pays

\[
 B_N=\Theta_w(10^{3N})                                      \tag{36a}
\]

up to its ineffective fixed constant.  Thus the construction is short by a
factor of order \(10^{3N}/N\) in its **guaranteed** exponent.  If \(d\) is
allowed to grow, capacity gives at most
\(A^{\rm cert}_{N,d}=O_w(dN)\), whereas
\(D=\Theta(d10^N)\) makes the leading lower-bound penalty
\(B_{N,d}=\Omega_w(d^3 10^{3N})\); the ratio is at most
\(O_w(N/(d^2 10^{3N}))\).

Status: local `proof sketch`; (24)--(34) are exact identities or elementary
bounds and are checked on finite symbolic instances.

## 6. The cheapest exact Euler power still does not cross

The first prefix gives an even cleaner test of whether a very small
fixed-\(e^i\) value can be amplified.  Since

\[
 C_3(X)=X^3-3X,
 \qquad
 Z^3(C_3(Z+Z^{-1})+2)=(Z^3+1)^2,                    \tag{37}
\]

the \(D\)-th power produces (3).  Its exact arithmetic ledger is

\[
 \deg S_D=6D,
 \qquad
 H(S_D)=\binom{2D}{D}\le4^D,
 \qquad
 L(S_D)=4^D.                                        \tag{38}
\]

Put \(\alpha=\pi-3\).  Euler's identity and the elementary bound
\(\pi<22/7\) give

\[
\begin{aligned}
 |e^{3i}+1|
 &=|e^{3i}-e^{i\pi}|\\
 &=2\sin(\alpha/2)<\alpha<{1\over7}.                \tag{39}
\end{aligned}
\]

Equations (38)--(39) prove (4).  On the other hand, (35) gives only

\[
 |S_D(e^i)|>\exp[-O(D^3)].                           \tag{40}
\]

There is no sign conflict: for large \(D\), the right side of (40) is far
smaller than \(49^{-D}\).  Algebraically, (3) is merely the \(2D\)-th
power of the fixed nonzero number \(e^{3i}+1\).  Its apparent smallness is
not a growing family of independent arithmetic cancellations.

Status: local `proof sketch`; the coefficient, height, and trace identities
are exact.

## 7. Why capacity and resultants stop here

The audited variants now have distinct, explicit failures.

1. **Uniform potential theory.**  Classical and integer Chebyshev
   minimization can supply \(\exp[-c_wD]\), but (1) proves it cannot supply
   \(\exp[-\omega(D)]\) uniformly on the survivor.
2. **All decimal tails in the real variable.**  The product has economical
   degree \(dN\), but its leading coefficient already has quadratic
   log-height (19); the algebraic-logarithm measure lands at (23).
3. **Exact conversion to the fixed exponential.**  The Dickson trace
   identity removes analytic approximation altogether, but integer
   frequencies \(p_j\asymp10^j\) become polynomial degree.  The optimized
   clearing (32) proves this degree loss is intrinsic for the chosen
   detector.
4. **A resultant instead of Laurent clearing.**  A resultant can encode the
   same relation, but for (31) it cannot reduce the exponent span below
   \(2s_N\).  The direct lift (27) is already cheaper and has controlled
   coefficient length.
5. **Powering or multiplicities.**  Smallness, degree, and log-height all
   scale linearly in the power, while the known lower-bound exponent is
   cubic (and for logarithms also carries \((1+\log D)^2\)).  Powering makes
   the comparison worse.

These are separators for the explicit families above, not a theorem that
every possible determinant, resultant, or auxiliary construction must fail.
A surviving loophole would require a genuinely compressed, digit-sensitive
form whose smallness exponent grows faster than its degree/height penalty.
Neither logarithmic capacity nor the exact trace lift supplies such a form.

An exact polynomial identity cannot secretly provide the compression.  If
\(Q_N(e^i)=G_{N,R}(e^i)\) for integer polynomials \(Q_N,G_{N,R}\), then
the transcendence of \(e^i\) forces \(Q_N=G_{N,R}\).  Hence a successful
low-degree form must arise from a new cancellation or auxiliary determinant,
not from rewriting the Laurent product (27).

## 8. Exact checker and finite optimization

Companion:
[`integer_chebyshev_survivor_attack_check.py`](integer_chebyshev_survivor_attack_check.py)

It checks exactly:

* the target SHA-256;
* \(C_n(Z+Z^{-1})=Z^n+Z^{-n}\) for finite symbolic instances;
* the minimum Laurent-span clearing (32);
* the degree, exact coefficient length, and height ledgers (37)--(38);
* the general trace-lift degree/length bound (28);
* the exact leading coefficient (19) and the product length bound (20);
* an exhaustive finite integer-Chebyshev search for degree at most four,
  coefficient absolute value at most two, and level-two admissible-prefix
  truncation nodes for \(w=0,31,9\).

Exact run:

```text
PASS: exact trace lifts, minimal Laurent clearing, auxiliary ledgers, orbit heights, and finite boxed optimizations
EXPERIMENT: degree<=4, |coefficient|<=2 finite-node minimizers are the universal [x(1-x)]^2 for w=0, w=31, and w=9
```

The boxed minimax calculation is an `experiment`.  These truncation nodes
need not themselves belong to \(K_w\): appending zeroes may create a forbidden
word across or after the truncation boundary (for example when \(w=0\)).  Its
finite prefix sample and coefficient box therefore do not determine
\(t_{\mathbb Z}(K_w)\) and give no evidence for V1.

## 9. Primary-literature audit

The bounded search was performed on **2026-08-12 UTC** over combinations of
*integer Chebyshev constant*, *logarithmic capacity*, *Cantor set*,
*subshift of finite type*, *algebraic logarithm*, *polynomial at an
exponential*, *resultant*, and *digit restriction*.  Only primary papers are
used below.

| Primary source | Exact use | Boundary for this attack |
|---|---|---|
| [Pritsker, *Small polynomials with integer coefficients*](https://arxiv.org/abs/math/0101166), Theorem 2.1 | Hilbert--Fekete inequality \(t_{\mathbb Z}(E)\le\sqrt{\operatorname{cap}(E)}\), including the weighted generalization. | Gives exponentially small uniform polynomials, not superexponential smallness. |
| [Borwein--Pinner--Pritsker, *Monic integer Chebyshev problem*](https://arxiv.org/abs/1307.5362), equations (1.1)--(1.9) and Proposition 1.2 | Definitions, interval capacity, distinction between monic and nonmonic integer constants, and the capacity threshold. | Monic and nonmonic constants must not be conflated; neither gives a digit-sensitive value estimate at \(\pi\). |
| [Cijsouw, *Transcendence measures of exponentials and logarithms of algebraic numbers*](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf), Theorems 1--2 | Bounds (22) and (35) for \(\operatorname{Log}(-1)=i\pi\) and \(e^i\). | Their degree dependence is cubic after the present substitutions; exponential Chebyshev smallness cannot cross it. |

Exact PDF pins (SHA-256; fetched 2026-08-12 UTC):

| Source/version | SHA-256 |
|---|---|
| Pritsker, arXiv:math/0101166 | `8685ecf5001fe76271c5fd2a9b50783967d2c1a708e6ace52d215b2231cbc8c2` |
| Borwein--Pinner--Pritsker, arXiv:1307.5362 | `d703e1d94a115b86ba510549c599dbf01845dc153cc83fd77a40594a43761d27` |
| Cijsouw 1974 | `fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a` |

No primary theorem was found which excludes a fixed algebraic logarithm or
fixed exponential value from every positive-capacity decimal finite-type
survivor.  This is a bounded `literature-checked` audit, not a claim that all
literature has been exhausted.

## 10. Claim status and exact missing input

* The capacity bracket (1), the product ledgers (17)--(21), the Dickson lift
  (24)--(34), and the power ledger (37)--(40) are local `proof sketch`
  results; none has been added to the verified Lean track.
* The source applicability table is `literature-checked` through the stated
  date and scope.
* The companion output is a finite `experiment` validating identities and a
  boxed minimax search only.
* Nothing in this file is `machine-checked`, a candidate resolution, or a
  verified resolution.

For this route to prove V1, one needs at least one input not present here.
The following single precise statement would suffice.

> **Survivor--exponential compression lemma (conjectural).**  For every
> nonempty decimal word \(w\), there exist constants \(C_w>0\) and
> \(\varepsilon_w>0\) such that, if all decimal tails of \(\pi\) lie in
> \(K_w\), then for every sufficiently large \(N\) there is a nonzero
> \(P_N\in\mathbb Z[Z]\) satisfying
> \[
>   \deg P_N\le C_wN,\qquad
>   \log H(P_N)\le C_wN,
>   \qquad
>   0<|P_N(e^i)|\le\exp(-N^{3+\varepsilon_w}).       \tag{41}
> \]

Indeed, Cijsouw's Theorem 1 would give from the first two bounds
\(|P_N(e^i)|>\exp(-C'_wN^3)\), contradicting the last bound for large
\(N\).  A parameter-free sufficient condition is

\[
 { -\log|P_N(e^i)|
  \over
   (\deg P_N)^2(\deg P_N+\log H(P_N))}
 \longrightarrow\infty.                              \tag{42}
\]

Positive capacity says a uniform one-variable Chebyshev polynomial cannot
prove this lemma by itself.  Decimal-orbit products pay quadratic height in
the real variable, and the exact fixed-\(e^i\) trace lift pays exponential
degree.  The direct lift's ratio in (42), when its certified survivor
smallness is substituted, is only \(O_w(N/10^{3N})\), which tends to zero
in the opposite direction.  Exceptional extra smallness of the actual
factors is not supplied by word omission and would itself require a new
\(\pi\)-specific Diophantine input.
Accordingly, this branch records a clean obstruction, a quantified sharp
deficit for these constructions, and one exact missing lemma, but not a proof
of (5).
