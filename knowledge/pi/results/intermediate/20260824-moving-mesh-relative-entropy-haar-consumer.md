# Relative-entropy moving-mesh control implies Haar block limits

Status: `proof sketch`

Independently audited: 2026-08-24 UTC

## Intermediate sufficient premise

The moving-mesh consumer in
[`20260823-moving-mesh-collision-haar-consumer.md`](20260823-moving-mesh-collision-haar-consumer.md)
uses a uniform `L^2` bound on the mesh step densities, obtained from

\[
  \sum_{a<q_j} n_j(a)^2 \le C\left(\frac{L_j^2}{q_j}+L_j\right)
\]

together with bounded `q_j/L_j`. The `L^2` input is stronger than the Haar
argument needs. Uniform integrability is enough to make every block limit
absolutely continuous, and a bounded mesh relative entropy gives an explicit
finite condition implying that uniform integrability.

This strictly weakens the older collision premise, but it is stronger than the
already reviewed uniform-integrability condition. It is therefore a useful
explicit intermediate premise, not the active weakest moving-mesh frontier.
It does not prove the premise for the decimal orbit of pi or for the sampled
BBP orbit.

## Statement

Let \(x_n\in\mathbb T=\mathbb R/\mathbb Z\), let \(Sx=10x\), and let
\(L_j,q_j\to\infty\) through positive integers. On the block
\([L_j,2L_j)\), set

\[
 \mu_j=\frac1{L_j}\sum_{n=L_j}^{2L_j-1}\delta_{x_n},\qquad
 n_j(a)=\#\{n\in[L_j,2L_j):x_n\in I_{j,a}\},
\]

where \(I_{j,a}=[a/q_j,(a+1)/q_j)\), and put
\(p_j(a)=n_j(a)/L_j\). Define the mesh relative entropy, using the natural
logarithm and the convention \(0\log 0=0\), by

\[
 D_j=\sum_{a<q_j}p_j(a)\log\bigl(q_jp_j(a)\bigr).
 \tag{E}
\]

Assume

\[
 \sup_j D_j<\infty
 \tag{1}
\]

and

\[
 \frac1{L_j}\sum_{n=L_j}^{2L_j-1}
 d_{\mathbb T}(x_{n+1},Sx_n)\longrightarrow0.
 \tag{2}
\]

Then \(\mu_j\) converges weakly to Haar measure on \(\mathbb T\). Hence every
fixed nonempty open interval meets every sufficiently late selected block.
In particular, if (1) holds along selected blocks of the exact decimal orbit
of pi, then the existing cylinder bridge would imply V1.

No separate hypothesis on \(q_j/L_j\) is needed.

## Proof

Define a step density \(g_j\) by

\[
 g_j(x)=q_jp_j(a)\quad(x\in I_{j,a})
\]

and let \(\nu_j=g_j\,dx\). The measures \(\mu_j\) and \(\nu_j\) assign the
same mass to each mesh cell. For every continuous \(\varphi\), coupling each
atom of \(\mu_j\) to normalized Lebesgue measure on its cell gives

\[
 \left|\int\varphi\,d\mu_j-\int\varphi\,d\nu_j\right|
 \le \omega_\varphi(1/q_j),
 \tag{3}
\]

so the two sequences have the same weak subsequential limits.

The entropy is exactly

\[
 D_j=\int_{\mathbb T} g_j\log g_j\,dx
    =\int_{\mathbb T}\Phi(g_j)\,dx,
 \qquad \Phi(t)=t\log t-t+1,
 \tag{4}
\]

with \(\Phi(0)=1\). The function \(\Phi\) is nonnegative and superlinear.
More explicitly, for \(R>e\),

\[
 \int_{\{g_j>R\}}g_j\,dx
 \le \frac{D_j}{\log R-1}.
 \tag{5}
\]

Together with
\(\int_A g_j\le R|A|+\int_{\{g_j>R\}}g_j\), this proves uniform
integrability of \(\{g_j\}\).

Take any weakly convergent subsequence of \(\nu_j\), with limit \(\nu\).
Uniform integrability makes \(\nu\) absolutely continuous with respect to Haar
measure. Indeed, given a Haar-null compact set \(K\), put it inside an open
set \(O\) of arbitrarily small Haar measure, choose a continuous cutoff equal
to one on \(K\) and supported in \(O\), and use (5) before passing to the weak
limit. Thus \(d\nu=f\,dx\) for some \(f\in L^1(\mathbb T)\).

Condition (2) makes every weak block limit \(S\)-invariant. For continuous
\(\varphi\), insert \(\varphi(x_{n+1})\) between
\(\varphi(Sx_n)\) and \(\varphi(x_n)\). Uniform continuity and (2) control
the averaged first difference, while the second difference telescopes to

\[
 \frac{\varphi(x_{2L_j})-\varphi(x_{L_j})}{L_j}\longrightarrow0.
\]

Consequently \(\int\varphi\circ S\,d\nu=\int\varphi\,d\nu\).

For the Fourier coefficients of \(f\), invariance gives

\[
 \widehat f(h)=\widehat f(10h)\qquad(h\in\mathbb Z).
\]

If \(h\ne0\), iteration and the Riemann--Lebesgue lemma yield

\[
 \widehat f(h)=\widehat f(10^rh)\longrightarrow0.
\]

Hence every nonzero Fourier coefficient vanishes, while
\(\widehat f(0)=1\). Uniqueness of Fourier coefficients gives \(f=1\) almost
everywhere. Every subsequential limit is therefore Haar, so the full selected
sequence converges to Haar. The open-interval conclusion follows from
Portmanteau.

## The old collision premise implies the entropy premise

For one mesh write \(p(a)=n(a)/L\). Jensen's inequality, applied to the
probability weights \(p(a)\), gives the order-one/order-two Renyi comparison

\[
 \sum_a p(a)\log(qp(a))
 \le \log\left(q\sum_a p(a)^2\right).
 \tag{6}
\]

Thus the old assumptions

\[
 \sum_a n(a)^2\le C\left(\frac{L^2}{q}+L\right),
 \qquad \frac qL\le K,
\]

imply

\[
 D\le \log\bigl(C(1+K)\bigr).
\]

Conversely, bounded entropy already absorbs the mesh-ratio condition. Since
\(p\) has support of size at most \(L\),

\[
 D=\log q-H(p)\ge \log(q/L),
\]

and hence \(q/L\le e^D\).

## Strict separator

The entropy control does not imply the quadratic collision control, even after
retaining `q/L = 1` and the averaged pseudo-orbit hypothesis.

For each integer \(m\ge2\), set

\[
 k_m=10^m,\qquad q_m=L_m=10^{k_m},\qquad r_m=10^{k_m-m}.
\]

First consider the occupancy profile

\[
 n_m(0)=r_m,
 \qquad n_m(a)=1\text{ on }q_m-r_m\text{ other cells},
 \qquad n_m(a)=0\text{ on the remaining cells}.
 \tag{7}
\]

Its entries sum to \(L_m\). The only nonzero entropy contribution comes from
the heavy cell, because every singleton cell has \(q_mp_m(a)=1\). Hence

\[
 D_m=10^{-m}\log(10^{k_m-m})
     =\left(1-\frac{m}{10^m}\right)\log 10<\log 10.
 \tag{8}
\]

On the other hand,

\[
 \frac{\sum_a n_m(a)^2}{L_m^2/q_m+L_m}
 =\frac12\left(10^{k_m-2m}+1-10^{-m}\right)
 \longrightarrow\infty.
 \tag{9}
\]

Thus no fixed collision constant covers (7).

The profiles can be realized while preserving the dynamical hypothesis. A
cyclic decimal de Bruijn word of order \(k_m\) gives a period-\(q_m\) orbit of
\(S\) that visits every decimal \(q_m\)-cell exactly once. Such a word is
obtained from an Euler circuit in the directed graph of \(k_m-1\)-digit
words. Choose the cyclic starting point immediately after the unique visit to
the zero cell and take \(q_m-r_m\) consecutive orbit points; these visit
distinct nonzero cells. Build the selected block by taking \(r_m\) copies of
the fixed point zero, then those \(q_m-r_m\) de Bruijn-orbit points. There is
only one non-dynamical transition inside the block, from zero to the chosen
periodic orbit. All other transitions are exact, and \(x_{2L_m}\) can be
chosen as the next orbit point. Therefore

\[
 \frac1{L_m}\sum_{n=L_m}^{2L_m-1}d_{\mathbb T}(x_{n+1},Sx_n)
 \le \frac{1}{2L_m}\longrightarrow0.
\]

Since \(2L_m<L_{m+1}\), these blocks can be inserted disjointly into one global
sequence, with arbitrary values in the gaps. This sequence satisfies the new
entropy and pseudo-orbit premises but violates every uniform quadratic
collision bound. It is a generic separator, not a fixed-pi example and not
an exact global orbit.

The mechanism is exactly the one missed by quadratic energy: a cell carrying
mass \(\varepsilon\) at density \(M\) costs order
\(\varepsilon M\) in the `L^2` quantity but only
\(\varepsilon\log M\) in relative entropy. Rare high-multiplicity islands
can therefore destroy collision bounds without destroying the compactness
needed by the Haar argument. This explicitly escapes, rather than ignores,
the sparse-periodic-island obstruction recorded in
`T19T19SparsePeriodicIslands.lean`.

## Optional stronger fixed-pi target

One sufficient fixed-pi target is to prove that there are unbounded selected
blocks and meshes for which

\[
 \sup_j\sum_{a<q_j}\frac{n_j(a)}{L_j}
  \log\left(\frac{q_jn_j(a)}{L_j}\right)<\infty.
\]

No such estimate is proved here for the decimal orbit of pi or the sampled BBP
orbit. The weakest retained Haar target remains uniform integrability; bounded
relative entropy is one stronger way to establish it. The result does not
prove V1, density, normality, or fixed-pi Fourier cancellation, and it makes no
novelty or literature-optimality claim. Its mathematical gain is the strict
replacement of the `L^2` collision premise by an `L log L` compactness premise
with an explicit generic pseudo-orbit separator. The existing exact-global-
orbit de Bruijn separator is stronger than this separator.

Relevant checked and archived context:

- `TheoryLib/PiLongLagBlockCollisionDecay/T1T1LongLagBlockCollisionDecay.lean`
- `TheoryLib/PiLongLagBlockCollisionDecay/T3T3CollisionDecayImpliesDisjunctive.lean`
- `TheoryLib/PiLongLagBlockCollisionDecay/T19T19SparsePeriodicIslands.lean`
- `TheoryLib/PiPositiveLowerBlockDensity/T19T19MinimalDeBruijnFlow.lean`
- `knowledge/pi/results/negative/t120_t119_metric_nearpair_and_forcing_obstructions_20260822.md`
