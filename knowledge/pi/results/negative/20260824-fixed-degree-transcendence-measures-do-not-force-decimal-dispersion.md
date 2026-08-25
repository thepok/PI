# Fixed-degree transcendence measures do not force decimal dispersion

Status: `proof sketch`

Date: 2026-08-24 UTC

External input: Beresnevich--Nesharim--Yang,
[*Winning property of badly approximable points on curves*, Corollary 1.7](https://arxiv.org/abs/2005.02128).

## Result

Even simultaneous Dirichlet-optimal polynomial lower bounds at every fixed
degree do not imply the canonical entropy, moving-mesh uniform-integrability,
collision, target-cell, or V1 conclusions.

For \(d\ge1\), let

\[
 \mathcal B_d=\left\{\xi:\exists c_d(\xi)>0\ \forall\,0\ne P\in
 \mathbb Z[X],\ \deg P\le d,\quad
 |P(\xi)|\ge c_d(\xi)H(P)^{-d}\right\}.
\]

Let

\[
 K_{01}=\left\{\sum_{j\ge1}\varepsilon_j10^{-j}:
 \varepsilon_j\in\{0,1\}\right\},\qquad
 \delta=\log_{10}2,\qquad \gamma=1-\delta=\log_{10}5.
\]

The fair Bernoulli measure on \(K_{01}\) is \(\delta\)-Ahlfors regular.
BNY Corollary 1.7 therefore gives

\[
 \dim_H\left(K_{01}\cap\bigcap_{d\ge1}\mathcal B_d\right)=\delta.
\]

In particular, there are transcendental \(\alpha\in K_{01}\) satisfying the
displayed optimal fixed-degree bound for every \(d\). BNY also supplies the
corresponding lower bounds against real algebraic approximants of every fixed
degree. For any such \(\alpha=\sum_{j\ge1}\varepsilon_j10^{-j}\), exact decimal
dynamics gives

\[
 \{10^n\alpha\}=\sum_{j\ge1}\varepsilon_{n+j}10^{-j}\in K_{01}
 \qquad(n\ge0).
\]

Thus the orbit is permanently confined to the digits \(0,1\); in particular,
the digit \(2\) never occurs.

## Quantitative failures of the live premises

For every orbit block, canonical depth \(k\), block length \(L\ge1\), and
starting time \(A\ge0\), at most \(2^k\) depth-\(k\) decimal cells are occupied.
Hence its entropy \(H_{A,L}(k)\) and deficit \(D_{A,L}(k)\) obey

\[
 H_{A,L}(k)\le k\log2,
 \qquad
 D_{A,L}(k)=k\log10-H_{A,L}(k)\ge k\log5.
\]

For an arbitrary equal \(q\)-cell mesh, the interval covering number of
\(K_{01}\) gives at most \(4q^\delta\) occupied cells. If \(n(a)\) are the
occupancies and

\[
 T_{A,L,q}(M)=\frac1L\sum_{n(a)>ML/q}n(a),
\]

then the mass outside the tail is supported on at most \(4q^\delta\) cells,
and therefore

\[
 T_{A,L,q}(M)\ge1-4M q^{-\gamma}.
\]

Consequently the moving-mesh UI tail tends to one, rather than zero, as
\(q\to\infty\). Cauchy--Schwarz on the occupied cells also gives

\[
 \sum_a n(a)^2\ge\frac{L^2}{4q^\delta},
 \qquad
 \frac{\sum_a n(a)^2}{L^2/q+L}
 \ge \frac{q^\gamma}{4(1+q/L)}.
\]

Thus bounded \(q/L\) forces the normalized collision quotient to diverge.

## Scope

This is a generic separator, not a result about \(\pi\), and it proves no part
of V1 for \(\pi\). The constants \(c_d(\alpha)\) are existential and have no
controlled dependence on \(d\); a genuinely growing-degree estimate with
quantitative constants could escape the example. The fixed-degree
transcendence-measure route was not the named active frontier, so this note
only closes a plausible strengthening of the already recorded effective-
irrationality route. No literature novelty is claimed beyond verifying and
applying the cited source; the deductions above have not been checked in Lean.

## Growing-degree quantitative supplement

Status: `proof sketch`. This subsection records a self-contained generic
separator and coding obstruction; it is not a statement about the digits of
π.

Fix a decimal digit $c$, let $A_c=\{0,\ldots,9\}\setminus\{c\}$, and let
$\mu_c$ be the fair Bernoulli measure on

\[
 K_c=\left\{3+\sum_{n\ge1}a_n10^{-n}:a_n\in A_c\right\},
 \qquad \delta=\frac{\log9}{\log10}.
\]

Discard the $\mu_c$-null set of ambiguous eventually-$9$ representations.
For $H\ge1$, put $h=\lfloor\log_2 H\rfloor$ and

\[
 F_9(d,H)=\frac d\delta\log\!\left(
  24d\,2^{d+1}(h+1)(h+2)
  (3\cdot2^{h+1})^{d+1}\right).
\]

There is $E_c\subseteq K_c$ with $\mu_c(E_c)\ge1/2$ such that,
simultaneously for every $\alpha\in E_c$, $d\ge1$, and nonzero
$P\in\mathbb Z[X]$ with $\deg P\le d$ and naive polynomial height
$H(P)=\max_i|a_i|=H\ge1$,

\[
 |P(\alpha)|\ge \exp(-F_9(d,H)). \tag{G1}
\]

Indeed, $\mu_c(I)\le12|I|^\delta$ for real intervals $I$ of length below
one, hence a complex-root covering argument gives

\[
 \mu_c\{x:|P(x)|<\varepsilon\}\le24d\varepsilon^{\delta/d}.
\]

There are at most $(3\cdot2^{h+1})^{d+1}$ coefficient vectors in the
$(d,h)$ dyadic class. Choosing the threshold encoded by $F_9$ makes the
sum of all bad-class measures at most
$\sum_{d\ge1}2^{-(d+1)}
\sum_{h\ge0}((h+1)(h+2))^{-1}=1/2$.
The complement therefore satisfies (G1) in every degree and height and
consists of transcendental numbers.

Every $\alpha\in E_c$ omits $c$. Its decimal orbit occupies at most
$9^r$ canonical depth-$r$ cells, so every block has entropy deficit

\[
 D_{A,L}(r)\ge r\log(10/9).
\]

On an equal $q$-cell moving mesh, the orbit occupies fewer than
$18q^\delta$ cells. Consequently

\[
 T_{A,L,q}(M)\ge1-18M q^{-(1-\delta)},
\]

which tends to one for every fixed $M$. Thus explicit simultaneous
all-degree polynomial repulsion coexists with linear canonical entropy
deficit and maximal failure of the retained moving-mesh UI premise.

Here is the precise uniform-bridge obstruction. For a nonempty decimal word
$w$, let $Y_w\subset[3,4)$ be the reals whose canonical decimal expansion
omits $w$. For integers $d,H\ge1$, define

\[
 K(d,H)=d\bigl((2H+1)^{d+1}-1\bigr),\qquad
 N^*(d,H)=\lfloor\log_9K(d,H)\rfloor+1,
\]
\[
 T_{\rm alg}=\log3+N^*\log10,\qquad
 T_{\rm poly}=dT_{\rm alg}.
\]

For algebraic $\beta$, $H(\beta)$ below means the naive height of its
primitive irreducible minimal polynomial. If fixed $d,H,T$ have the literal
uniform property

\[
 \forall y\in Y_w\ \exists\beta_y:\quad
 \deg\beta_y\le d,\ H(\beta_y)\le H,\ |y-\beta_y|<e^{-T},
\]

then $T\le T_{\rm alg}(d,H)$. Likewise, if

\[
 \forall y\in Y_w\ \exists\,0\ne P_y\in\mathbb Z[X]:\quad
 \deg P_y\le d,\ H(P_y)\le H,\ |P_y(y)|<e^{-T},
\]

then $T\le T_{\rm poly}(d,H)$. To see this, choose a digit $c$ occurring
in $w$ and $9^N$ digit-$c$-omitting codepoints with a common tail. They
are $10^{-N}$-separated. There are at most
$(2H+1)^{d+1}-1$ nonzero coefficient vectors and at most $d$ relevant
roots per vector. Balls of radius $10^{-N}/3$, followed in the polynomial
case by the elementary implication
$|P(y)|<(10^{-N}/3)^d\Rightarrow y$ lies within $10^{-N}/3$ of a
root, give the stated bounds at $N=N^*$. This theorem concerns only the
displayed universal statements; it does not constrain a π-specific bridge
using additional arithmetic information.

For each fixed $d$, as $H\to\infty$,

\[
 F_9(d,H)=\frac{d(d+1)}\delta\log H+O_d(\log\log H),
 \qquad
 T_{\rm poly}(d,H)=\frac{d(d+1)}\delta\log H+O_d(1).
\]

Thus the direct-polynomial separator and codebook obstruction match only at
the fixed-$d$ leading scale. The algebraic codebook scale is
$(d+1)\log H/\delta+O_d(1)$.

Bugeaud records, and attributes to Waldschmidt, the π transcendence-measure
formula

\[
 |P(\pi)|\ge
 \exp\{-240d(\log H+d\log d)(1+\log d)\}
\]

for nonzero integer polynomials of degree at most $d$ and naive height at
most $H$: see [Bugeaud, *Approximation by Algebraic Numbers*, Chapter
8](https://www.cambridge.org/core/books/approximation-by-algebraic-numbers/other-classifications-of-real-and-complex-numbers/ED51F082B43AC7ACAF3F6F7DEE976EE4)
and Waldschmidt's [*Transcendence measures for exponentials and
logarithms*](https://doi.org/10.1017/S1446788700021431). The recorded theorem
only says that $d$ and $H$ are sufficiently large; it supplies no numerical
starting range.

Accordingly, $d=1965$ is only the first integer at which the leading
coefficients in this formal comparison satisfy

\[
 \frac{d+1}{\delta}>240(1+\log d).
\]

Conditional on the external estimate being valid at that degree, a relaxed
necessary comparison gives $\log_{10}H>45{,}415{,}673.08$. Neither number is
a theorem-backed threshold without the missing starting range. This
supplement proves no π entropy or UI estimate, has not been checked in Lean,
and makes no `literature-checked` or novelty claim.

## Denominator hole for uniform bounded-polynomial covers

Status: `proof sketch`. This closes only a scale-wise, language-uniform
covering mechanism; it is not a statement about a polynomial constructed
specifically at π.

Let $w$ be a nonempty decimal word. For every $d,H\ge1$ there is a reduced
rational $x_{w,H}=p/q\in[3,4)$ whose canonical fractional decimal expansion
avoids $w$, such that

\[
 H<q\le10H,
 \qquad
 |P(x_{w,H})|\ge(10H)^{-d}                                      \tag{G2}
\]

for every nonzero $P\in\mathbb Z[X]$ with $\deg P\le d$ and naive height
$H(P)\le H$.

To construct it, choose a digit $c$ occurring in $w$ and
$a\in\{1,7\}\setminus\{c\}$. Let $m\ge0$ be least such that
$q=9\cdot10^m>H$. For $m=0$, take the fractional part $0.\overline a=a/9$.
For $m\ge1$, choose an even digit
$b\in\{0,2,4,6,8\}\setminus\{c\}$ with
$4b+a\not\equiv0\pmod5$, and take

\[
 0.\underbrace{aa\ldots a}_{m-1\text{ digits}}b\overline a
   =\frac{9U+a}{9\cdot10^m},
\]

where $U$ is the integer represented by the first $m$ digits. Such a $b$
exists because exactly one even digit fails the congruence and excluding $c$
removes at most one more choice. The numerator $9U+a$ is odd, is nonzero
modulo $5$ by construction, and is congruent to $a\equiv1\pmod3$; hence the
displayed denominator is reduced. All fractional digits omit $c$, while the
eventual digit $a\in\{1,7\}$ removes terminating-tail ambiguity. Adding $3$
preserves the denominator and puts the result in $[3,4)$. Minimality of $m$
gives $H<q\le10H$.

If a positive-degree $P$ in (G2) vanished at $p/q$, the rational-root theorem
would make $q$ divide its leading coefficient, impossible because $q>H$.
The constant case is immediate. Thus $q^dP(p/q)$ is a nonzero integer, so
$|P(p/q)|\ge q^{-d}\ge(10H)^{-d}$.

For comparison, Theorem 2 of Nesterenko--Waldschmidt,
[*On the approximation of the values of exponential function and logarithm by
algebraic numbers*](https://arxiv.org/abs/math/0002047), gives for every
$d\ge1$, $L\ge3$, and nonzero integer polynomial with $\deg P\le d$ and
coefficient length $L(P)=\sum_j|a_j|\le L$,

\[
 |P(\pi)|\ge
 \exp\{-2\cdot10^6d(\log L+d\log d)(1+\log d)\}.                \tag{G3}
\]

Since $L(P)\le(d+1)H(P)$, put $L_0=\max\{3,(d+1)H\}$ and denote the
right-hand side of (G3) by $\varepsilon_\pi(d,H)$. For all $d,H\ge1$,

\[
 \varepsilon_\pi(d,H)< (10H)^{-d},
\]

because $L_0\ge2H$ and $2\cdot10^6\log(2H)>\log(10H)$. Therefore the strict
sublevel sets $\{|P(x)|<\varepsilon_\pi(d,H)\}$, over all nonzero polynomials
of degree at most $d$ and height at most $H$, do not cover the full
$w$-avoiding language at any scale $(d,H)$. This strengthens the preceding
uniform codebook obstruction in the growing-degree regime. It does not rule
out a nonuniform bridge that uses arithmetic information specific to π, and
it proves no π cancellation, entropy estimate, UI estimate, or part of V1.
No Lean or novelty claim is made.

## Fixed-target T139 and finite-differencing separator

Status: `proof sketch`. This is a target-specific sharpening of the same
generic separator, not a statement about π.

Fix $k\ge1$, $q=10^k$, and $0\le A<q$, and choose a digit $c$ occurring in the
length-$k$ word for $A$, with leading zeros retained. Choose

\[
 (d_0,d_1)=
 \begin{cases}
  (1,2),&c=0,\\
  (0,2),&c=1,\\
  (0,1),&c\ge2,
 \end{cases}
 \qquad s=d_1-d_0.
\]

Take

\[
 \beta\in K_{01}\cap\bigcap_{d\ge1}\mathcal B_d,
 \qquad
 \xi=3+\frac{d_0}{9}+s\beta.
\]

The decimal digits of ξ are exactly $d_0$ and $d_1$, with no carry, so
its decimal orbit omits the prescribed target cylinder. The affine change
also preserves the simultaneous optimal fixed-degree estimates. Indeed, with
$A_0=27+d_0$, for nonzero $Q\in\mathbb Z[X]$ of degree at most $d$,

\[
 \widetilde Q(Y)=9^dQ\!\left(\frac{A_0+9sY}{9}\right)
 \in\mathbb Z[Y],
 \qquad
 H(\widetilde Q)\le(d+1)46^dH(Q),
\]

and $\widetilde Q(\beta)=9^dQ(\xi)$. Thus, for a suitable $c_d(\xi)>0$,

\[
 |Q(\xi)|\ge c_d(\xi)H(Q)^{-d}
 \qquad(d\ge1).
\]

The degree-one case gives a uniform optimal linear estimate. If $R$ is the
nearest integer to $M\xi$, then $\beta\in[0,1/9]$ and $s\le2$ give the
height estimate omitted by the first draft:

\[
 |9R-A_0M|
 \le |9R-9M\xi|+|9M\xi-A_0M|
 \le\frac92+9sM\beta
 \le\frac{13}{2}M<18M.
\]

Applying the β estimate to
$9sM X-(9R-A_0M)$ therefore yields

\[
 \lVert M\xi\rVert_{\mathbb R/\mathbb Z}
 \ge \frac{c_1(\beta)}{162M}.
\]

This repulsion survives every finite van der Corput expansion of the complete
primitive polynomial. If its current frequencies $m_1,m_2$ are not
divisible by ten, a lag-ℓ correlation has frequency

\[
 10^\ell m_1-m_2\equiv-m_2\pmod {10},
\]

so it is again nonzero and primitive. Iterating this recurrence covers the
cross terms of the full polynomial; for one character it specializes to
$m\prod_j(10^{\ell_j}-1)$. Hence every finite leaf enjoys the displayed
linear repulsion, despite the permanent missing target.

Finally, put $e(t)=\exp(2\pi i t)$ and
$\mathcal P_q=\{1\le u\le2q-1:10\nmid u\}$, and let
$p_{q,A}(u)$, $E_q$, and

\[
 Z_{q,A}^{\xi}(N)=
 \sum_{u\in\mathcal P_q}p_{q,A}(u)
 \sum_{n<N}e(u10^n\xi)
\]

denote the complete T139 primitive coefficients, exact endpoint budget, and
generic-orbit primitive sum; write $\alpha_q(0)$ for its positive zero mode.
Since the boundary-matched kernel is nonpositive
outside the target cylinder, its exact Fourier expansion and the T139
primitive-ray endpoint identity give, at every $N\ge1$,

\[
 -\frac2N\operatorname{Re}Z_{q,A}^{\xi}(N)
 +\frac{4E_q}{N}\ge\alpha_q(0).
\]

Thus the strict T139 sufficient condition fails at every horizon even though
ξ has simultaneous Dirichlet-optimal polynomial repulsion in each fixed
degree and optimal linear repulsion at every frequency generated by arbitrary
finite differencing. This rules out deductions based only on such lower
repulsion; it does not rule out signed or off-diagonal information special to
π, and it proves no T139 premise or part of V1. No Lean or novelty claim is
made.
