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
unbounded sequence of decimal word lengths implies more than canonical V1: on
consecutive selected blocks it forces every fixed-depth word law to converge to
uniform, and hence forces the selected empirical measures to converge to Haar.
For a general approximate times-ten orbit, a uniformly bounded entropy deficit
also forces Haar block limits. Sublinear deficit is strictly weaker than
canonical-mesh uniform integrability in exact base-ten dynamics; bounded
deficit is strictly weaker than the existing quadratic collision bound.

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
`mu_j` have the same weak subsequential limits. Formula (4) gives uniform
absolute continuity: for a Haar-null compact set, place it inside an open set
of arbitrarily small Haar measure, bound a continuous cutoff between their
indicators, and pass its integrals to the weak limit. Inner regularity then
shows that every such limit is absolutely continuous with respect to Haar
measure.

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

For decimal meshes `q_j=10^k_j` with `k_j -> infinity` on the exact pi orbit,
the implication hierarchy is

```text
quadratic collision bound
          => bounded entropy deficit
          => sublinear entropy deficit
          => V1 for the exact decimal π orbit.
```

The first two implications are strict, not merely syntactically weaker. The
general Haar consumer of Section 2 does not by itself assert the final
pi-specific implication; that step additionally uses the exact decimal coding
and the factor-entropy theorem from Section 1.

## 4. Exact-times-ten separators

The strictness can be realized by genuine generic decimal orbits, not only by
abstract probability vectors. These separators are not estimates for pi.

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

## 5. Finite entropy stationarization in exact canonical dynamics

This strengthening uses two hypotheses that must not be dropped: the mesh is
the canonical `b^k` digit mesh, and the points form consecutive blocks of one
exact orbit under `T_b(x)=b*x mod 1`. It is not a statement for arbitrary
moving meshes or for pseudo-orbits.

Let `b >= 2`, let `x_(n+1)=T_b(x_n)`, and let

\[
 B=[A,A+L),\qquad L\ge1.
\]

For `s >= 1`, let `p_(B,s)` be the empirical law of the canonical half-open
`b^s` cells on this block, and put

\[
 H_s(B)=-\sum_{a<b^s}p_{B,s}(a)\log p_{B,s}(a),
 \qquad D_s(B)=s\log b-H_s(B).
\]

For laws `P,Q` on `M` symbols, use the convention

\[
 d_{\rm TV}(P,Q)={1\over2}\sum_{a=1}^M|P(a)-Q(a)|.
\]

For `M >= 2` and `t >= 0`, define

\[
 \tau_M(t)=\min\left\{t,1-{1\over M}\right\},
 \qquad
 \Omega_M(t)=h_2(\tau_M(t))+\tau_M(t)\log(M-1), \tag{7}
\]

where `h_2(u)=-u log u-(1-u)log(1-u)` with `0 log 0=0`.
Thus `Omega_M` is the monotone Fannes--Audenaert envelope: if
`d_TV(P,Q) <= t`, then

\[
 |H(P)-H(Q)|\le\Omega_M(t). \tag{8}
\]

The clamp at `1-1/M` is intentional. For larger `t`, `Omega_M(t)=log M`,
the universal entropy-difference bound.

### Finite stationarization theorem

For integers `k >= r >= 1`, put

\[
 m=\left\lfloor{k\over r}\right\rfloor,
 \qquad M=b^r.
\]

Then every finite block above satisfies

\[
 \boxed{
 D_r(B)\le {D_k(B)\over m}
 +{1\over m}\sum_{u=0}^{m-1}
   \Omega_M\!\left({ur\over L}\right).} \tag{9}
\]

In particular,

\[
 \boxed{
 D_r(B)\le {D_k(B)\over m}
 +\Omega_M\!\left({(m-1)r\over L}\right).} \tag{10}
\]

Since the empirical `k`-cell law has support at most `L`, one also has

\[
 L\ge b^k e^{-D_k(B)}, \tag{11}
\]

and therefore the length-free bound

\[
 \boxed{
 D_r(B)\le {D_k(B)\over m}
 +\Omega_{b^r}\!\left(
 { (m-1)r e^{D_k(B)}\over b^k}
 \right).} \tag{12}
\]

To prove (9), choose `N` uniformly in `B` and let
`Y_t=floor(b*x_(N+t))` for `0 <= t < k`. Exact dynamics and the canonical
half-open convention identify `(Y_0,...,Y_(k-1))` with the `k`-cell of `x_N`,
so its entropy is `H_k(B)`. Split its first `m*r` coordinates into `m`
successive `r`-blocks `Z_u`, and write

\[
 \Delta_u=r\log b-H(Z_u).
\]

Entropy subadditivity, with the remaining fewer than `r` digits bounded by
their full entropy, gives

\[
 \sum_{u=0}^{m-1}\Delta_u\le D_k(B). \tag{13}
\]

The law of `Z_u` is the canonical `r`-cell law on the shifted block `B+ur`.
The two length-`L` index blocks differ only at their endpoints, so

\[
 d_{\rm TV}(p_{B,r},p_{B+ur,r})
 \le\min\left\{1,{ur\over L}\right\}. \tag{14}
\]

Since `Delta_0=D_r(B)`, (8) gives
`D_r(B) <= Delta_u+Omega_M(ur/L)`. Averaging over `u` and using (13) proves
(9); monotonicity gives (10). Finally,
`H_k(B) <= log L` proves (11), whose substitution into (10) gives (12).

There is also an exact finite simultaneous-hitting certificate. If any one of
the `b^r` cells is absent, then

\[
 D_r(B)\ge\log{b^r\over b^r-1}. \tag{15}
\]

Consequently every length-`r` base-`b` word occurs at a starting index in `B`
whenever the right side of (12) is strictly smaller than the threshold in
(15). Pinsker also gives, for each such word `w`,

\[
 p_{B,r}(w)\ge b^{-r}-\sqrt{D_r(B)/2}. \tag{16}
\]

## 6. Sublinear canonical deficit forces Haar block limits

Let `B_j=[A_j,A_j+L_j)` be nonempty consecutive blocks of one exact base-`b`
orbit. If `k_j -> infinity` and

\[
 {D_{k_j}(B_j)\over k_j}\longrightarrow0, \tag{17}
\]

then, for every fixed `r >= 1`,

\[
 D_r(B_j)\longrightarrow0,
 \qquad
 d_{\rm TV}(p_{B_j,r},u_{b^r})\longrightarrow0. \tag{18}
\]

Indeed, `m_j=floor(k_j/r)` makes the first term in (10) tend to zero. From
(11),

\[
 {k_j\over L_j}
 \le k_j\exp(D_{k_j}(B_j)-k_j\log b)\longrightarrow0, \tag{19}
\]

so its endpoint term also tends to zero. Pinsker yields the total-variation
claim.

For the block empirical measures

\[
 \mu_j={1\over L_j}\sum_{n\in B_j}\delta_{x_n},
\]

this fixed-depth convergence implies `mu_j => lambda`. Precisely, if
`omega_phi` is the modulus of continuity of a continuous test function, then

\[
 \left|\int\varphi\,d\mu_j-\int\varphi\,d\lambda\right|
 \le 2\omega_\varphi(b^{-r})
 +2\|\varphi\|_\infty
   d_{\rm TV}(p_{B_j,r},u_{b^r}). \tag{20}
\]

First let `j -> infinity` and then `r -> infinity`.

For `b=10` and `x_n={10^n*pi}`, (18) says that every fixed decimal word has
frequency tending to `10^-r` along the selected blocks. Hence every fixed word
occurs in every sufficiently large **stage** `j`. This does not say that those
occurrences are arbitrarily late in the decimal expansion unless one also
assumes `A_j -> infinity`. In either case, occurrence in at least one selected
block implies V1.

Thus the earlier factor-complexity implication is strengthened to

```text
sublinear canonical entropy deficit on exact consecutive orbit blocks
          => fixed-depth total-variation convergence
          => selected-block Haar convergence
          => V1 for the exact decimal pi orbit.
```

## 7. Canonical UI is strictly stronger

For the canonical `b^k_j` mesh, let `f_j=b^k_j*p_(B_j,k_j)(a)` on cell `a`.
Then

\[
 D_{k_j}(B_j)=\int f_j\log f_j\,d\lambda.
\]

Because `0 <= f_j <= b^k_j`, for every `R>1`,

\[
 D_{k_j}(B_j)
 \le \log R+k_j\log b
       \int_{\{f_j>R\}}f_j\,d\lambda. \tag{21}
\]

Canonical-mesh uniform integrability therefore implies
`D_(k_j)(B_j)=o(k_j)`. This implication uses only the canonical mesh; the Haar
conclusion additionally uses exact dynamics and consecutive blocks.

The converse fails within one exact global orbit. For `j >= 2`, set

\[
 k_j=j^2,\qquad \ell_j=j,\qquad r_j=j^2-j,
 \qquad P_j=b^{r_j}.
\]

Choose a cyclic base-`b` de Bruijn word `W_j` of order `r_j`. At pairwise
disjoint digit positions in one infinite base-`b` expansion, embed
`P_j+k_j-1` digits of `W_j` repeated periodically, and let `B_j` be the `P_j`
starting positions spanning one full period. The `P_j` length-`k_j` windows
are distinct because their first `r_j` digits are the distinct cyclic
`r_j`-windows. Hence their `k_j`-cell law is uniform on exactly `P_j` cells and

\[
 D_{k_j}(B_j)=j\log b=o(k_j). \tag{22}
\]

On every occupied fine cell the smoothed density is `b^j`; all mass lies on
those cells. Thus, for every finite `R`,

\[
 \sup_j\int_{\{f_j>R\}}f_j\,d\lambda=1, \tag{23}
\]

so UI fails maximally. Nevertheless every fixed `s <= r_j` word occurs
exactly `b^(r_j-s)` times in the stage. The separator is therefore an exact
global orbit, not an abstract histogram or pseudo-orbit.

On canonical meshes and exact consecutive-block dynamics, the revised strict
hierarchy is

```text
quadratic collision + bounded mesh ratio
          => uniform integrability
          =>(strict) sublinear entropy deficit
          => selected-block Haar convergence
          => V1 for the exact decimal pi orbit.
```

This hierarchy does not compare sublinear deficit with UI on arbitrary meshes,
and it gives no analogous stationarization theorem for pseudo-orbits.

## Fixed-π research target

The weakest retained target from this note is now:

> Find `k_j -> infinity` and nonempty finite blocks of the exact decimal π
> orbit for which the canonical `10^k_j`-cell entropy satisfies
>
> `H_j = k_j * log 10 - o(k_j)`.

This is strictly weaker than canonical-mesh UI and therefore than the existing
collision target. On exact consecutive blocks it already gives Haar limits;
there is no need to strengthen it to `D_j=O(1)` for that conclusion.

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
- Sublinear canonical deficit gives Haar convergence only for consecutive
  blocks of exact base-ten dynamics. The stationarization theorem does not
  cover arbitrary meshes or pseudo-orbits.
- "Every fixed word occurs in every sufficiently large `j`" refers to the
  stage index; it means arbitrarily late decimal positions only if `A_j ->
  infinity` is assumed.
- No literature or novelty claim is attached to the entropy inequalities or
  de Bruijn separators.
- No pi-specific entropy estimate, T128/T124 Fourier estimate, BBP estimate,
  or carry-flow estimate is proved or advanced here.
- The result is not yet integrated into Lean and is therefore `proof sketch`,
  not `machine-checked`.

V1 remains open.
