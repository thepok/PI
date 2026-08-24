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
