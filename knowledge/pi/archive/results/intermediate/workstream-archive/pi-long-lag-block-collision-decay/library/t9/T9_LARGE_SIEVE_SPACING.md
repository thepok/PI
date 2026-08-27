# T9: pointwise irrationality and the T8 spectral energy

Status: `proof sketch` (rigorous prose, not machine-checked).

## 1. Scope and normalized statement

The immutable canonical question is
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`, SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

Its canonical quantifier order is: for every real `s` with `0 < s < 1`,
there is one `C_s >= 1` which works for every pair of positive integers
`m,N`. Pairs in the canonical collision count are ordered, the lag cutoff is
`|i-j| >= m`, and the right side is
`C_s(N+N^2 10^(-sm))`.

This note does **not** prove that statement. It studies the conditional T8
spectral target, which is attached to the residual/near-return reductions A12
and A13. In T8 notation, after fixing the arithmetic parameters `(mu,c) =
(8,1)` and an onset `Q0`, the target asks whether one constant `K >= 0`
exists before all positive `m,N` such that

\[
 E(m,N):=\sum_{h=1}^{10^m}|S_h(m,N)|^2
 \le K\,10^m N^2.                                      \tag{T8}
\]

Here

\[
 S_h(m,N)=\sum_{q\in Q(8,1,Q_0,m,N)}e(hx_q),\qquad
 e(t)=\exp(2\pi i t),                                    \tag{1}
\]

and `Q` is T8's collision-independent ordered domain, audited exactly below.

### Quantifier and interpretation ambiguities resolved here

1. `Q0` is fixed before `m,N`; it is not allowed to vary with scale.
2. The same `K` in (T8) must work for every positive `m,N`.
3. Frequencies are the inclusive positive interval `1 <= h <= 10^m`; there
   are exactly `10^m` frequencies and no zero frequency in `E`.
4. `Q` is a set of ordered pair records. The associated points on
   `R/Z` are shown distinct below, so applying a set-form large sieve does
   not silently discard multiplicity.
5. The premise `mu(pi) < 8` is external literature input. T4 represents it by
   the explicit hypothesis `IrrationalityMeasureBelow Real.pi 8`; neither T4
   nor this note proves that source theorem internally.

## 2. The exact T8 domain at `(mu,c)=(8,1)`

T8 represents a member by an orientation and a core `(r,n)`. Its membership
theorem says exactly

\[
 0<r,\quad m\le r<N,\quad 0\le n<N-r,\quad
 \neg\operatorname{ArithmeticExcluded}(8,1,Q_0,m,n,r).   \tag{2}
\]

The two orientations represent `(a,b)=(n,n+r)` and `(n+r,n)`. The imported
definition of `ArithmeticExcluded` is in
`TheoryLib.PiPositiveLowerBlockDensity.T25T25ResidualPairReduction`, lines
48--56. It uses

\[
 d(n,r)=10^n(10^r-1)
\]

and, at `(8,1)`, says

\[
 Q_0\le d(n,r)\quad\hbox{and}\quad
 10^{-m}\le d(n,r)\,d(n,r)^{-8}=d(n,r)^{-7}.              \tag{3}
\]

For every positive `m` and every `r >= m`, this predicate is false. Indeed,
`d(n,r) >= 10^r-1 >= 10^m-1`; for `m >= 1`,

\[
 d(n,r)^7\ge(10^m-1)^7>10^m,
\]

because `10^m-1 >= 9` and already `(10^m-1)^2 > 10^m`.
Thus `d(n,r)^{-7}<10^{-m}`, contradicting the second clause of (3),
independently of its first clause.

Consequently, for every `Q0` and all positive `m,N`, the exact domain is

\[
 Q(m,N)=\{(a,b):0\le a,b<N,\ |a-b|\ge m\}.                \tag{4}
\]

It is empty when `m >= N`. If `1 <= m < N`, put `d=N-m`. Counting each
positive lag in both orientations gives

\[
 |Q(m,N)|=2\sum_{r=m}^{N-1}(N-r)=d(d+1)
          =(N-m)(N-m+1)\le N^2.                           \tag{5}
\]

This is sharper than T8's general coarse bound `|Q| <= 2N^2`.

For `q=(a,b)` define

\[
 D_q=10^a-10^b,\qquad x_q=D_q\pi\pmod 1.                 \tag{6}
\]

This is literally T8's `orderedPhaseArgument` and therefore (1) is literally
T8's `spectralSum`, not a collision-selected substitute.

The map `(a,b) -> D_q` is injective on unequal ordered pairs. To see this,
the sign of `D_q` determines the orientation. In the positive orientation
`a>b`,

\[
 D_q=10^b(10^{a-b}-1),                                   \tag{7}
\]

and the second factor is divisible by neither `2` nor `5`. Hence the exact
power of `10` dividing `D_q` recovers `b`, after which (7) recovers `a-b`.
The negative orientation follows after changing sign. In particular, for
distinct `q,q'`, `k=D_q-D_{q'}` is a nonzero integer. If `N >= 2`, then

\[
 1\le |k|\le B_N:=2(10^{N-1}-1).                          \tag{8}
\]

The upper endpoint is exact for the full domain whenever `m<N`, using
`(a,b)=(N-1,0)` and its reverse.

## 3. Named dual large-sieve inequality

We use the sharp analytic large sieve of Montgomery and Vaughan in dual form.
The normalization is stated in full because changing the length convention
changes the `-1`.

**Dual Montgomery--Vaughan large sieve.** Let `J` be a finite set, let
`x_j in R/Z` be pairwise `delta`-separated in circle distance,

\[
 \|x_j-x_{j'}\|_{\mathbb R/\mathbb Z}\ge\delta
 \quad(j\ne j'),\qquad 0<\delta\le\tfrac12.              \tag{9}
\]

For every integer `M`, every positive integer `H`, and every family of
complex numbers `(b_j)`,

\[
 \sum_{h=M+1}^{M+H}\left|\sum_{j\in J}b_j e(hx_j)\right|^2
 \le (H-1+\delta^{-1})\sum_{j\in J}|b_j|^2.              \tag{10}
\]

This is the dual, by equality of the operator norms of a matrix and its
adjoint, of the sharp large-sieve inequality with the same constant. The
source is H. L. Montgomery and R. C. Vaughan, *The large sieve*,
Mathematika 20 (1973), 119--134,
DOI <https://doi.org/10.1112/S0025579300004708>. Publisher metadata and the
article extract are at
<https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0025579300004708>.
The publisher currently places the full PDF behind access control; no
unverified PDF copy is retained with this note.

For T8 take `M=0`, `H=10^m`, `J=Q(m,N)`, and every `b_q=1`. Then (10) says

\[
 E(m,N)\le(10^m-1+\delta^{-1})|Q(m,N)|.                  \tag{11}
\]

All subsequent losses therefore occur in the spacing input, not in an
unstated large-sieve constant.

## 4. Strongest spacing supplied by `mu(pi)<8`

T4's source-level premise expands as follows: there are `mu_0<8` such that
for every `epsilon>0` there is `Q(epsilon)` for which, for every positive
integer `q>=Q(epsilon)` and every integer `p`,

\[
 q^{-(\mu_0+\epsilon)}<|\pi-p/q|.                        \tag{12}
\]

There are two useful consequences, and it is important not to conflate them.

### 4.1 Strongest logical consequence of the strict inequality

Choose any `nu` with

\[
 \max(1,\mu_0)<\nu<8,
\]

which exists because `mu_0<8`, and apply (12) with
`epsilon=nu-mu_0`. Put

\[
 \beta=\nu-1,\qquad 0<\beta<7,\qquad Q_\beta=Q(\nu-\mu_0).
\]

Multiplying (12) by `q` and choosing a nearest integer `p` gives

\[
 \|q\pi\|_{\mathbb R/\mathbb Z}>q^{-\beta}
 \quad(q\ge Q_\beta).                                   \tag{13}
\]

Thus the strict premise supplies *some* exponent `beta<7`. It does not, from
the proposition `mu(pi)<8` alone, name a numerical margin `7-beta`.

### 4.2 T4's completely explicit specialization

T4 instead takes `epsilon=8-mu_0`. Its machine-checked implication yields one
onset `Q0` such that

\[
 |\pi-p/q|>q^{-8}\quad(q\ge Q_0,
 \ q>0,\ p\in\mathbb Z),                                 \tag{14}
\]

and hence

\[
 \|q\pi\|_{\mathbb R/\mathbb Z}>q^{-7}.                 \tag{15}
\]

Equation (15) is weaker than (13) but has the explicit exponent and coefficient
used by the T8 parameters `(8,1,Q0)`.

### 4.3 Exact finite-prefix constant at scale `N`

For either `(beta,Q_beta)` from (13), including `(7,Q0)` from (15), and for
`N>=2`, define

\[
 \kappa_{\beta,Q_\beta}(N)
 =\min\left(\{1/2\}\cup
   \{\|q\pi\|:1\le q<Q_\beta,\ q\le B_N\}\right)>0.    \tag{16}
\]

The set is finite and nonempty because of the inserted `1/2`; every other
entry is positive because (12) implies that pi is irrational. Formula (16)
also handles `Q_beta<=1` without an empty-minimum convention. Restricting the
finite minimum to `q<=B_N` is essential for the strongest bound at the given
scale: larger coefficients cannot occur in (8). Once `B_N>=Q_beta-1`, this
quantity stabilizes at the scale-independent positive constant obtained by
omitting `q<=B_N`.

For distinct `q,q' in Q(m,N)`, apply (13) to `|D_q-D_{q'}|` when that integer
is at least `Q_beta`, and (16) otherwise. Equations (8), (13), and (16) give
the uniform separation

\[
 \|x_q-x_{q'}\|\ge
 \delta_{\beta,Q_\beta}(N)
 :=\begin{cases}
 \kappa_{\beta,Q_\beta}(N),&B_N<Q_\beta,\\
 \min\{\kappa_{\beta,Q_\beta}(N),B_N^{-\beta}\},
     &Q_\beta\le B_N.
 \end{cases}                                             \tag{17}
\]

The first branch is necessary for the strongest finite-scale statement: if
`B_N<Q_beta`, no coefficient difference reaches the asymptotic range (13).

Consequently

\[
 A_{\beta,Q_\beta}(N):=\delta_{\beta,Q_\beta}(N)^{-1}
 =\begin{cases}
 \kappa_{\beta,Q_\beta}(N)^{-1},&B_N<Q_\beta,\\
 \max\{\kappa_{\beta,Q_\beta}(N)^{-1},B_N^\beta\},
     &Q_\beta\le B_N.
 \end{cases}                                             \tag{18}
\]

This is the strongest uniform minimum-spacing statement obtained from the
pointwise irrationality premise without additional information about the
special difference set `D_q-D_{q'}`. In the fully explicit T4 specialization,
replace `beta` by `7` throughout.

## 5. Propagation through the large sieve

When `m>=N`, `Q` is empty and `E(m,N)=0`. Suppose henceforth that
`1<=m<N`; then `N>=2`. Substituting (5) and (18) into (11) gives

\[
\boxed{
 E(m,N)\le
 \left(10^m-1+A_{\beta,Q_\beta}(N)\right)
 (N-m)(N-m+1).}                                          \tag{19}
\]

For T4's explicit exponent this becomes

\[
 E(m,N)\le
 \left(10^m-1+A_{7,Q_0}(N)\right)
 (N-m)(N-m+1).                                           \tag{20}
\]

There are no hidden asymptotic constants in (19) or (20).

To compare (19) literally with (T8), abbreviate

\[
 A_\beta(N)=A_{\beta,Q_\beta}(N),
 \qquad L(m,N)=(N-m)(N-m+1).
\]

Since `L(m,N)<=N^2`, (19) implies

\[
 E(m,N)\le 10^mN^2+A_\beta(N)L(m,N).                     \tag{21}
\]

Thus this route would yield (T8) with a fixed `K>1` only if it could make

\[
 A_\beta(N)L(m,N)\le(K-1)10^mN^2                       \tag{22}
\]

uniformly over every nonempty scale `1<=m<N`.

## 6. Explicit insufficiency regime

Take the legal nonempty regime `m=1` and let `N>=2` tend to infinity. Then

\[
 H=10,\qquad L(1,N)=N(N-1),\qquad
 B_N=2(10^{N-1}-1)\ge10^{N-1}.                           \tag{23}
\]

For all sufficiently large `N`, one has `Q_beta<=B_N`, so (18) gives
`A_beta(N)>=B_N^beta`. Comparing the right side of (19), not the unknown actual
energy, with `K 10 N^2` then requires

\[
 K\ge {N-1\over10N}
 \left(9+A_\beta(N)\right)
 \ge {N-1\over10N}\,10^{\beta(N-1)}.                    \tag{24}
\]

For every `beta>0` supplied above, the last expression tends to infinity.
For the explicit T4 exponent `beta=7`, it is

\[
 {N-1\over10N}\,10^{7(N-1)}.                            \tag{25}
\]

Hence the single global minimum-spacing estimate furnished by `mu(pi)<8`,
inserted directly into the sharp dual large sieve, cannot certify one `K` for
all positive `m,N`. This is a demonstrated insufficiency of that precise
global-spacing application in the explicit scaling regime `m=1`,
`N -> infinity`. It is **not** a lower bound for `E(m,N)`, and therefore is not
a disproof of the T8 hypothesis. It also does not rule out partitioning the
points and proving scale-sensitive local-density bounds; such arguments would
use aggregate information beyond the one global minimum.

The exponent conflict is structural: nonempty T8 scales have `m<N`, whereas
the pointwise T4 specialization introduces the reciprocal-spacing scale
approximately `10^{7N}` against only `H=10^m`. Even retaining the logically
stronger unknown `beta<7` leaves `10^{beta N}` at fixed `m`.

## 7. One explicit remaining aggregate estimate

Minimum spacing replaces the entire point set by its single closest pair. A
sufficient aggregate estimate that preserves the distribution of all pair
differences is the following precise statement.

**Remaining estimate.** Prove that there is a real constant `C_agg>=0`, fixed
before `m,N`, such that for all positive integers `m,N`, with `H=10^m`,

\[
 \sum_{\substack{q,q'\in Q(m,N)\\q\ne q'}}
 \min\left\{H,{1\over2\|x_q-x_{q'}\|_{\mathbb R/\mathbb Z}}\right\}
 \le C_{\rm agg}\,H N^2.                                \tag{26}
\]

This is explicitly sufficient for T8. Indeed,

\[
 E(m,N)=\operatorname{Re}\sum_{q,q'\in Q(m,N)}
          \sum_{h=1}^{H}e(h(x_q-x_{q'})).                \tag{27}
\]

(Equivalently, (27) is an equality in `C` after embedding the real number on
the left; the full double sum is real by pairing `(q,q')` with `(q',q)`.)

For `t` nonzero modulo one, the geometric sum and
`|sin(pi t)|>=2||t||` give

\[
 \left|\sum_{h=1}^{H}e(ht)\right|
 \le\min\left\{H,{1\over2\|t\|}\right\}.              \tag{28}
\]

The diagonal in (27) is exactly `H|Q(m,N)|<=HN^2`; applying the triangle
inequality and (26) to the off-diagonal gives

\[
 E(m,N)\le(1+C_{\rm agg})HN^2.                           \tag{29}
\]

Thus (26), an aggregate truncated reciprocal-spacing estimate for the exact
T8 points, is the one explicit input left by this note. It asks for average
control of close differences rather than a stronger pointwise irrationality
exponent.

## 8. Conclusion and claim boundary

The outcome is an **insufficiency regime**, not a parameter-range proof of the
spectral hypothesis. Equations (19)--(25) show with explicit constants that
the direct single-global-spacing application of T4's pointwise irrationality
information to the sharp Montgomery--Vaughan dual large sieve loses uniformity
already at `m=1`, `N -> infinity`. Equation (26) is the precise remaining
aggregate estimate.

No claim is made that (26) holds for pi. No claim is made that the T8 uniform
spectral energy hypothesis, C1, normality, or decimal disjunctivity holds or
fails for pi.

## Sources and verification trail

1. Canonical statement URL (local source identifier):
   `knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`; verified SHA-256
   `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
2. T8 exact definitions and machine-checked endpoint audit:
   `TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction`.
   This note reuses those verified definitions and does not treat T8's
   conditional spectral hypothesis as proved.
3. Imported definitions of `structuredDenominator`, `EffectiveIrrationality`,
   and `ArithmeticExcluded`:
   `TheoryLib.PiPositiveLowerBlockDensity.T25T25ResidualPairReduction`,
   especially lines 28--56. The simplification in (3)--(4) is derived in this
   proof sketch; it is not claimed as an existing Lean theorem.
4. T4 source normalization and machine-checked conditional specialization:
   `TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset`.
5. D. Zeilberger and W. Zudilin, *The Irrationality Measure of Pi is at most
   7.103205334137...*, Moscow Journal of Combinatorics and Number Theory 9
   (2020), 407--419, DOI <https://doi.org/10.2140/moscow.2020.9.407>.
   The knowledge-library publisher PDF has SHA-256
   `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
   The numerical result is external literature evidence; this note only uses
   the explicit T4 premise `IrrationalityMeasureBelow Real.pi 8`.
6. H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20
   (1973), 119--134, DOI
   <https://doi.org/10.1112/S0025579300004708>. The exact theorem normalization
   used here is displayed in (9)--(10). Crossref and Cambridge publisher
   metadata were checked on 2026-07-24. Attempts to retrieve the publisher PDF
   through Wiley and Cambridge reached access controls, so no PDF hash is
   claimed.
