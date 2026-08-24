# Entropy-deficit hierarchy below moving-mesh collision

Status: `proof sketch`

Recorded: 2026-08-24 UTC

Admission-policy fit: item 2 — a strict weakening of an existing sufficient
premise, with explicit exact-dynamics separators for both new implications.

Source frontier: branch `pi-core-consolidation`, parent commit
`3733305a2e85f57c91d669b7acaad47f5bee3299`.

## Result

The existing moving-mesh collision premise is stronger than necessary in two
separate senses.

For the exact decimal orbit of π, a sublinear Shannon-entropy deficit along any
unbounded sequence of decimal word lengths already implies canonical V1. For a
general approximate times-ten orbit, a uniformly bounded entropy deficit forces
Haar block limits. The former is strictly weaker than bounded entropy deficit,
and the latter is strictly weaker than the existing quadratic collision bound,
even inside exact base-ten dynamics.

No entropy estimate of either strength is proved here for π. V1 remains open.

## Notation

Let

\[
 x_n=\{10^n\pi\}\in\mathbb T,
 \qquad q_j=10^{k_j},
\]

and let `B_j` be a nonempty finite contiguous block of orbit indices. Partition
the circle into the canonical half-open `q_j`-mesh cells

\[
 I_{j,a}=[a/q_j,(a+1)/q_j),\qquad 0\le a<q_j.
\]

Write

\[
 p_{j,a}={1\over |B_j|}\#\{n\in B_j:x_n\in I_{j,a}\},
\]

and use the convention `0 log 0 = 0`. Define the Shannon entropy and its
deficit from the uniform `q_j`-cell law by

\[
 H_j=-\sum_{a<q_j}p_{j,a}\log p_{j,a},
 \qquad
 D_j=\log q_j-H_j
     =\sum_{a<q_j}p_{j,a}\log(q_jp_{j,a}).
\]

Thus `D_j` is the Kullback--Leibler divergence from the uniform cell law.

## 1. Sublinear entropy deficit implies V1

### Statement

Assume `k_j -> infinity` and

\[
 {D_j\over k_j}\longrightarrow0. \tag{E1}
\]

Then every finite decimal word occurs in π.

The index blocks `B_j` need not begin at zero, need not be nested, and need not
contain all `q_j` cells.

### Proof

Let `p_π(k)` be the number of distinct length-`k` factors in the decimal digit
stream of π. Because π is irrational, the canonical `10^k` mesh cell of
`x_n` is exactly the length-`k` decimal factor beginning at `n`. Therefore

\[
 |\operatorname{supp}p_j|\le p_\pi(k_j).
\]

Entropy is bounded by the logarithm of support size, so

\[
 H_j\le\log |\operatorname{supp}p_j|
     \le\log p_\pi(k_j).
\]

Since `log q_j = k_j log 10`, this gives

\[
 1-{D_j\over k_j\log10}
 \le {\log p_\pi(k_j)\over k_j\log10}
 \le1. \tag{1}
\]

The middle expression is the canonical factor-entropy ratio along `k_j`. Its
full sequence has a limit by the machine-checked submultiplicativity/Fekete
argument in
[`T1CanonicalEntropy.lean`](../../../../TheoryLib/PiPositiveDecimalFactorEntropy/T1CanonicalEntropy.lean).
By (E1), the subsequence in (1) converges to one, so the full factor entropy is
one. The machine-checked theorem
`pi_entropy_eq_one_iff_every_finite_decimal_word_occurs` then gives V1.

This criterion is asymptotic. It gives no quantitative first-occurrence bound
and does not assert that every cell is occupied at any displayed scale.

## 2. Bounded entropy deficit implies Haar block limits

### Statement

Let `x_n in T` be any sequence, let `Sx=10x`, and let the empirical measures on
blocks `[A_j,A_j+M_j)` be

\[
 \mu_j={1\over M_j}\sum_{n=A_j}^{A_j+M_j-1}\delta_{x_n}.
\]

Let `q_j -> infinity`, let `p_{j,a}` be the associated equal-cell law, and
assume

\[
 \sup_j D_j<\infty, \tag{E2}
\]

and

\[
 {1\over M_j}\sum_{n=A_j}^{A_j+M_j-1}
 d_{\mathbb T}(x_{n+1},Sx_n)\longrightarrow0. \tag{E3}
\]

Then `mu_j` converges weakly to Haar measure. Consequently every fixed nonempty
open interval, including every decimal-cylinder interior, is hit by every
sufficiently late selected block.

No separate assumption on `q_j/M_j` is needed: since an empirical law on
`M_j` samples has support at most `M_j`,

\[
 D_j=\log q_j-H_j\ge\log(q_j/M_j),
\]

so (E2) already bounds `q_j/M_j` and forces `M_j -> infinity`.

### Proof

Spread each atom uniformly over its mesh cell. The resulting probability has
density

\[
 g_j(x)=q_jp_{j,a}\quad\text{on }I_{j,a},
\]

and

\[
 \int g_j\log g_j\,dx=D_j. \tag{2}
\]

For `M>1`, the negative part of `t log t` on `[0,1]` is at most `1/e`.
Therefore (2) gives

\[
 \int_{\{g_j>M\}}g_j\,dx
 \le {\sup_jD_j+1/e\over\log M}. \tag{3}
\]

Hence the densities are uniformly integrable. More explicitly, for every
measurable `E`,

\[
 \int_E g_j\,dx
 \le M\,|E|+{\sup_jD_j+1/e\over\log M}. \tag{4}
\]

The atom-to-cell coupling changes the integral of a continuous test function
by at most its modulus of continuity at `1/q_j`. Thus the smoothed measures and
`mu_j` have the same weak subsequential limits. Formula (4), outer regularity,
and Portmanteau show that every such limit is absolutely continuous with
respect to Haar measure.

For a Lipschitz test function `phi`, (E3) and the two block endpoints give

\[
 \left|\int\phi\circ S\,d\mu_j-\int\phi\,d\mu_j\right|
 \le \operatorname{Lip}(\phi){1\over M_j}
      \sum_{n=A_j}^{A_j+M_j-1}d(x_{n+1},Sx_n)
      +{2\|\phi\|_\infty\over M_j}\to0.
\]

Every weak limit is therefore `S`-invariant. If `d\mu=f\,dx`, then invariance
gives

\[
 \widehat f(h)=\widehat f(10h),\qquad h\in\mathbb Z.
\]

Since `f in L^1`, the Riemann--Lebesgue lemma makes
`hat f(10^r h) -> 0` for every nonzero `h`. Hence every nonzero Fourier
coefficient vanishes, so `mu` is Haar. All subsequential limits are Haar, which
forces convergence of the full selected sequence.

Compared with the previous
[`collision-to-Haar note`](20260823-moving-mesh-collision-haar-consumer.md),
square summability is not needed: absolute continuity gives an `L^1` density,
and Riemann--Lebesgue is already sufficient for the times-ten Fourier-ray
argument.

## 3. The old collision premise implies bounded entropy deficit

Let `n_a=M p_a`. The previous consumer assumes

\[
 \sum_{a<q}n_a^2\le C_0(M^2/q+M)
 \quad\text{and}\quad q/M\le K.
\]

Jensen's inequality with weights `p_a` gives

\[
 D(p\|u_q)
 =\sum_ap_a\log(qp_a)
 \le\log\!\left(q\sum_ap_a^2\right).
\]

The collision premise therefore yields

\[
 D(p\|u_q)\le\log(C_0(1+K)).
\]

Thus the implication hierarchy is

```text
quadratic collision bound
          => bounded entropy deficit
          => sublinear entropy deficit
          => V1 for the exact decimal π orbit.
```

The first two implications are strict, not merely syntactically weaker.

## 4. Exact-times-ten separators

The strictness can be realized by genuine decimal orbits, not only by abstract
probability vectors.

For each large `k`, put `q=10^k`. Choose a cyclic decimal de Bruijn word of
order `k` and linearize it to a digit string of length `q+k-1`; its `q`
consecutive length-`k` windows contain every decimal word exactly once.
Prepend a zero run of length `z+k-1` and sample the next

\[
 M=q+z+k-1
\]

starting positions. At least `z` starts give `0^k`, exactly `q` starts give the
uniform de Bruijn law, and only `k-1` transition starts remain. Therefore

\[
 p=(1-\alpha)u_q+\alpha r,
 \qquad
 \alpha={z+k-1\over M}
\]

for some probability law `r`. Convexity of relative entropy gives

\[
 D(p\|u_q)\le\alpha\log q. \tag{5}
\]

Also `p(0^k)>=z/M`, so

\[
 q\sum_ap_a^2\ge q\,p(0^k)^2. \tag{6}
\]

These finite stages can be placed at disjoint, rapidly growing digit positions
of one nonterminating decimal expansion. Its orbit satisfies
`x_(n+1)=10x_n mod 1` exactly. By choosing the stage positions recursively, the
sampled stages can also have the literal form `[L_j,2L_j)`.

### Separator A: sublinear does not imply bounded

Take `z=floor(q/sqrt(k))`. Then (5) gives

\[
 D(p\|u_q)=O(\sqrt{k})=o(k).
\]

On the other hand, coarse-graining to the events `{0^k}` and its complement
gives

\[
 D(p\|u_q)\ge
 p(0^k)\log(qp(0^k))-1/e,
\]

which tends to infinity. Thus the sublinear-deficit V1 criterion does not
require bounded entropy deficit. Equation (6) also gives
`q sum p_a^2 -> infinity`.

### Separator B: bounded does not imply collision

Take `z=floor(q/k)`. Then (5) gives a uniform entropy-deficit bound,

\[
 D(p\|u_q)\le\log10+o(1),
\]

while (6) gives

\[
 q\sum_ap_a^2\gg q/k^2\longrightarrow\infty.
\]

Hence no constant can satisfy the previous normalized collision estimate on
these blocks, even though the entropy premise is bounded and the dynamics is
exact.

## Fixed-π research target

The weakest retained target from this note is now:

> Find `k_j -> infinity` and nonempty finite blocks of the exact decimal π
> orbit for which the canonical `10^k_j`-cell entropy satisfies
>
> `H_j = k_j * log 10 - o(k_j)`.

This is strictly weaker than the existing collision target. A stronger but
still weaker-than-collision route is to prove `D_j=O(1)` and use the Haar
consumer above.

A finite computation can falsify a proposed uniform entropy law, identify
where the deficit concentrates, or compare scaling models. It cannot establish
the required asymptotic statement.

## Reproducible finite check

The companion experiment
[`entropy_deficit_separator.py`](../../../../workflows/research/pi/experiments/entropy_deficit_separator.py)
constructs decimal de Bruijn stages for orders 2 through 5, checks the exact
window counts and de Bruijn coverage, and records numerical entropy and
collision diagnostics. Reproduce the retained CSV with

```bash
python workflows/research/pi/experiments/entropy_deficit_separator.py \
  --max-order 5 --format csv > \
  knowledge/pi/results/intermediate/20260824-entropy-deficit-separator-results.csv
```

The retained output is
[`20260824-entropy-deficit-separator-results.csv`](20260824-entropy-deficit-separator-results.csv).
This finite computation is an `experiment`; the asymptotic separator is the
mathematical argument above, not an extrapolation from the table.

## Claim boundary

- This note proves no entropy bound for π.
- It provides no first-occurrence rate and no quantitative C1 deadline.
- The Haar conclusion needs bounded deficit; sublinear deficit alone gives V1
  through factor entropy and does not imply Haar convergence of the displayed
  blocks.
- No novelty claim is attached to the entropy inequalities or de Bruijn
  separators.
- The result is not yet integrated into Lean and is therefore `proof sketch`,
  not `machine-checked`.

V1 remains open.
