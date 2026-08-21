# T10: coefficient-difference multiplicities for the T8 spectrum

Status: `proof sketch` (rigorous prose, not machine-checked).

## Provenance

- Canonical source identifier:
  `knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`.
- Canonical source SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- T8 `machine-checked` definitions and conditional reductions:
  `TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction`.
- T9 exploratory note: `T9_LARGE_SIEVE_SPACING.md`, status `proof sketch`.
  No assertion from T9 is used as a proved premise below.
- The multiplicity bound below is new within this theory program. No claim of
  novelty in the research literature is made.
- External arithmetic premise: D. Zeilberger and W. Zudilin, *The
  Irrationality Measure of Pi is at most 7.103205334137...*, Moscow Journal of
  Combinatorics and Number Theory 9 (2020), 407-419,
  DOI <https://doi.org/10.2140/moscow.2020.9.407>. The retained publisher PDF
  in the knowledge library has SHA-256
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
  Its numerical theorem is external; this note does not prove it.

## Exact statement and claim boundary

The canonical question asks whether, for every real `s` with `0 < s < 1`,
there is one `C_s >= 1` such that for all positive integers `m,N`,

\[
 R_\pi(m,N)\le C_s\bigl(N+N^2 10^{-sm}\bigr).             \tag{C1}
\]

Here `R_pi` counts ordered pairs of equal decimal blocks whose starting
indices lie in `{0,...,N-1}` and whose absolute lag is at least `m`. This note
does **not** prove (C1). It studies T8's conditional spectral sufficient
condition, which belongs to the residual/near-return siblings A12-A13 of the
canonical question.

The result proved here is a partial spectral range: after the external premise
`mu(pi) < 8` supplies T8's fixed arithmetic parameters, one constant works at
every positive scale satisfying

\[
       (\max\{N-m,0\})^2\le N.                             \tag{R}
\]

This range is not T8's all-scale hypothesis and is not presented as (C1).

## 1. Normalized T8 domain

Fix positive integers `m,N`. T8 represents an ordered pair by an orientation
and a core `(r,n)`, where

\[
  0<r,\qquad m\le r<N,\qquad 0\le n<N-r,                  \tag{1.1}
\]

and retains the core when
`not ArithmeticExcluded(8,1,Q0,m,n,r)`. The two orientations are the ordered
pairs `(n,n+r)` and `(n+r,n)`.

The imported definitions are

\[
 d(n,r)=10^n(10^r-1)                                     \tag{1.2}
\]

and

\[
 \operatorname{ArithmeticExcluded}(8,1,Q_0,m,n,r)
 \Longleftrightarrow
 Q_0\le d(n,r)\ \hbox{ and }\ 10^{-m}\le d(n,r)^{-7}.     \tag{1.3}
\]

All powers and inequalities in (1.3) are real after coercing the positive
integer `d(n,r)`.

**Lemma 1 (the exclusion is empty).** For every integer `Q0 >= 0` and all
`m,N,r,n` satisfying (1.1), (1.3) is false.

**Proof.** Since `r >= m >= 1`,

\[
 d(n,r)\ge 10^r-1\ge 10^m-1\ge9.                         \tag{1.4}
\]

Put `A=10^m-1`. Direct expansion gives

\[
 A^2-10^m=10^{2m}-3\,10^m+1
          =10^m(10^m-3)+1>0.                             \tag{1.5}
\]

As `A>=9`, (1.5) implies `d(n,r)^7 >= A^7 > A^2 > 10^m`.
Taking positive reciprocals gives `d(n,r)^(-7) < 10^(-m)`,
which contradicts the second conjunct in (1.3). This does not depend on the
first conjunct or on `Q0`. QED.

It follows, without using T9, that T8's domain at `(mu,c)=(8,1)` is exactly

\[
 Q_{m,N}=\{(a,b)\in\{0,\ldots,N-1\}^2:|a-b|\ge m\}.       \tag{1.6}
\]

This is a set of ordered pairs. Put

\[
 d=d(m,N):=\max\{N-m,0\}.                                \tag{1.7}
\]

If `m>=N`, then `d=0` and `Q_(m,N)` is empty. If `m<N`, each
gap `r in {m,...,N-1}` contributes `N-r` pairs in each orientation. Therefore

\[
 |Q_{m,N}|=2\sum_{r=m}^{N-1}(N-r)
           =(N-m)(N-m+1)=d(d+1).                         \tag{1.8}
\]

For later use, define the exact gap fiber

\[
 Q_{m,N}(r)=\{(a,b)\in Q_{m,N}:|a-b|=r\}.                 \tag{1.9}
\]

It is empty unless `m <= r < N`, and in that range

\[
 |Q_{m,N}(r)|=2(N-r).                                    \tag{1.10}
\]

## 2. Coefficients and ordered multiplicities

For `q=(a,b) in Q_(m,N)`, define the integer

\[
 \lambda_q=\lambda_{a,b}=10^a-10^b.                      \tag{2.1}
\]

The map `q -> lambda_q` is injective. Indeed, the sign determines whether
`a>b` or `a<b`. In the positive case,

\[
 \lambda_{a,b}=10^b(10^{a-b}-1),                         \tag{2.2}
\]

and `10^(a-b)-1` is divisible by neither 2 nor 5. Hence the largest power of
10 dividing `lambda_(a,b)` recovers `b`, and division then recovers `a-b`.
The negative case follows after changing sign.

Define the ordered off-diagonal pair domain

\[
 \mathcal P_{m,N}
 =\{(q,q')\in Q_{m,N}\times Q_{m,N}:q\ne q'\}.            \tag{2.3}
\]

It has exactly

\[
 |\mathcal P_{m,N}|=d(d+1)\bigl(d(d+1)-1\bigr)            \tag{2.4}
\]

elements. Injectivity shows that
`lambda_q-lambda_(q')` is nonzero on this domain.

For every nonzero integer `k`, the **ordered coefficient-difference
multiplicity** is

\[
 M_{m,N}(k)
 =|\{(q,q')\in\mathcal P_{m,N}:
           \lambda_q-\lambda_{q'}=k\}|.                  \tag{2.5}
\]

The order matters: interchanging `q,q'` changes `k` to `-k`. In particular,

\[
 M_{m,N}(-k)=M_{m,N}(k),\qquad
 \sum_{k\in\mathbb Z\setminus\{0\}}M_{m,N}(k)
 =|\mathcal P_{m,N}|.                                    \tag{2.6}
\]

The sum in (2.6) is finite: every occurring `k` satisfies, for `N>=2`,

\[
  1\le |k|\le B_N:=2(10^{N-1}-1).                        \tag{2.7}
\]

When `N=1`, `Q_(m,N)` and `P_(m,N)` are empty for every positive `m`.

## 3. A uniform multiplicity theorem

For `q=(a,b)` and `q'=(c,d)`, define the signed digit vector on the finite
index set `{0,...,N-1}` by

\[
 C_i(q,q')={\bf1}_{i=a}-{\bf1}_{i=b}
            -{\bf1}_{i=c}+{\bf1}_{i=d}.                  \tag{3.1}
\]

Then every `C_i` belongs to `{-2,-1,0,1,2}` and

\[
 \lambda_q-\lambda_{q'}=\sum_{i=0}^{N-1}C_i(q,q')10^i.   \tag{3.2}
\]

**Lemma 2 (short signed decimal uniqueness).** If two vectors
`u,w in {-2,-1,0,1,2}^N` have the same base-10 sum, then `u=w`.

**Proof.** Their difference `z=u-w` has entries in
`{-4,-3,...,4}` and satisfies `sum_i z_i 10^i=0`. If it is nonzero, let `L`
be its largest nonzero index. The leading term has absolute value at least
`10^L`, whereas all lower terms together have absolute value at most

\[
 4\sum_{i=0}^{L-1}10^i={4(10^L-1)\over9}<10^L.           \tag{3.3}
\]

They cannot cancel the leading term, a contradiction. QED.

Thus a fixed integer `k` determines the entire vector `(C_i)` in every
representation (3.2). To count the representations, regard `{a,d}` as a
two-element multiset of positive tokens and `{b,c}` as a two-element multiset
of negative tokens. Write their multiplicities as `p_i,n_i`; then

\[
 \sum_i p_i=\sum_i n_i=2,\qquad p_i-n_i=C_i.              \tag{3.4}
\]

Let `ell=sum_i min(p_i,n_i)` be the number of common, canceled tokens. If
`ell=2`, then `p_i=n_i` for every `i`, so `k=0`. Therefore a representation
of a nonzero `k` has `ell=0` or `ell=1`.

The vector `C` determines which of these two cases occurs, because

\[
 \sum_i\max\{C_i,0\}
 =\sum_i\bigl(p_i-\min\{p_i,n_i\}\bigr)=2-\ell.           \tag{3.4a}
\]

In particular, representations of one fixed nonzero `k` cannot occur in both
the `ell=0` and `ell=1` cases: Lemma 2 fixes `C`, and (3.4a) then fixes `ell`.

If `ell=0`, the vector `C` uniquely specifies both token multisets. There are
at most two ways to assign the positive tokens to the labeled positions
`(a,d)`, and at most two ways to assign the negative tokens to `(b,c)`, hence
at most four ordered representations.

If `ell=1`, the vector `C` specifies the unmatched positive and negative
tokens. The one common token may have any exponent `t in {0,...,N-1}`. Once
`t` is chosen, (3.4) specifies both multisets, and again there are at most
`2*2=4` assignments to the labeled positions. Hence there are at most `4N`
representations. Requiring `(a,b),(c,d)` to lie in the smaller set `Q_(m,N)`
can only remove representations.

**Theorem 3 (explicit ordered multiplicity bound).** For all positive integers
`m,N` and every nonzero integer `k`,

\[
             \boxed{M_{m,N}(k)\le4N.}                    \tag{3.5}
\]

More precisely, a coefficient vector with no common canceled token has
multiplicity at most `4`; a vector with one common canceled token has
multiplicity at most `4N`. The constants count labeled ordered roles and do
not suppress an orientation factor.

## 4. Valuation, gap, and dyadic strata

This section gives an exact finite decomposition, not an asymptotic shorthand.

For a nonzero integer `k`, define its base-10 valuation `v_10(k)` as the unique
nonnegative integer `v` such that

\[
 10^v\mid |k|\quad\hbox{and}\quad10^{v+1}\nmid |k|.       \tag{4.1}
\]

For an occurring difference with signed vector `C`, Lemma 2 gives

\[
 v_{10}(k)=\min\{i\in\{0,\ldots,N-1\}:C_i\ne0\}.          \tag{4.2}
\]

Indeed, after factoring out `10^v`, the remaining integer is congruent to
`C_v in {+/-1,+/-2}` modulo 10. In particular every occurring valuation lies
in `{0,...,N-1}`.

For `m <= r,s < N`, define the gap-refined multiplicity

\[
 M_{m,N}^{r,s}(k)=
 |\{(q,q')\in\mathcal P_{m,N}:
      q\in Q_{m,N}(r),\ q'\in Q_{m,N}(s),
      \lambda_q-\lambda_{q'}=k\}|.                       \tag{4.3}
\]

Then, with all sums finite by (2.7),

\[
 M_{m,N}(k)=\sum_{r=m}^{N-1}\sum_{s=m}^{N-1}
             M_{m,N}^{r,s}(k).                            \tag{4.4}
\]

An upper endpoint smaller than its lower endpoint means an empty sum. This
convention covers `m>=N` throughout.

We now introduce circle-distance bins. Write

\[
 \|x\|_{\mathbb R/\mathbb Z}=\min_{z\in\mathbb Z}|x-z|.
\]

The external premise `mu(pi)<8` is represented in T4 by the explicit
hypothesis `IrrationalityMeasureBelow pi 8`. T4 provides only the
`machine-checked` conditional implication that this hypothesis supplies an
integer `Q0` such that

\[
 |\pi-p/q|>q^{-8}
 \quad(q\ge Q_0,\ q>0,\ p\in\mathbb Z).                  \tag{4.5}
\]

The publication, not Lean and not this note, supplies the hypothesis.

For `N>=2`, define the finite-prefix constant

\[
 \kappa_{Q_0}(N)=
 \min\left(\{1/2\}\cup
   \{\|k\pi\|:k\in\mathbb N,\ 1\le k\le B_N,\ k<Q_0\}\right)>0
                                                                  \tag{4.6}
\]

and

\[
 \delta_{Q_0}(N)=\min\{\kappa_{Q_0}(N),B_N^{-7}\}>0.     \tag{4.7}
\]

The positivity in (4.6) follows from the irrationality implied by (4.5): if
`pi=p0/q0`, sufficiently large positive multiples of `q0` contradict (4.5).
The inserted `1/2` makes the finite minimum nonempty even when `Q0<=1`.

For every integer `k` with `1<=|k|<=B_N`,

\[
 \|k\pi\|\ge\delta_{Q_0}(N).                              \tag{4.8}
\]

For `|k|<Q0` this is (4.6). For `|k|>=Q0`, choose a nearest integer `p`;
(4.5) gives

\[
 \|k\pi\|/|k|=|\pi-p/|k||>|k|^{-8},
\]

so `||k*pi||>|k|^(-7)>=B_N^(-7)`. Signs do not affect circle distance.

Let `J_(Q0)(N)` be the least positive integer `J` such that

\[
                 2^{-(J+1)}<\delta_{Q_0}(N).              \tag{4.9}
\]

It exists because `delta_(Q0)(N)>0`. For `1<=j<=J_(Q0)(N)`, define the exact
finite incidence stratum

\[
\begin{split}
 A_{m,N,Q_0}(v,r,s,j)=|\{(q,q')\in\mathcal P_{m,N}:{}&
   v_{10}(\lambda_q-\lambda_{q'})=v,\\
  &q\in Q_{m,N}(r),\ q'\in Q_{m,N}(s),\\
  &2^{-(j+1)}<
    \|(\lambda_q-\lambda_{q'})\pi\|
       \le2^{-j}\}|.                                     \tag{4.10}
\end{split}
\]

The intervals `(2^(-(j+1)),2^(-j)]`, `j>=1`, are pairwise disjoint and
partition `(0,1/2]`. Equations (4.8)-(4.9) show that no occurring pair lies in
a bin with `j>J_(Q0)(N)`. Therefore, for `N>=2`, the following is an exact
finite partition identity:

\[
\boxed{
 |\mathcal P_{m,N}|=
 \sum_{v=0}^{N-1}\sum_{r=m}^{N-1}\sum_{s=m}^{N-1}
 \sum_{j=1}^{J_{Q_0}(N)}A_{m,N,Q_0}(v,r,s,j).}            \tag{4.11}
\]

For `N=1`, the separately defined domain `P_(m,1)` is empty; equations
(4.6)-(4.11) are not invoked because `B_1=0` and no off-diagonal difference
exists. Thus (4.11) audits every valuation, first gap, second gap, and dyadic
bin whenever there is a possible nonempty off-diagonal domain.

For an equivalent coefficient-level decomposition, let

\[
 \mathcal K_{N,Q_0}(v,j)=\{k\in\mathbb Z:
  1\le|k|\le B_N,\ v_{10}(k)=v,
  2^{-(j+1)}<\|k\pi\|\le2^{-j}\}.                        \tag{4.12}
\]

For `N>=2`, `0<=v<N`, `m<=r,s<N`, and
`1<=j<=J_(Q0)(N)`, one has

\[
 A_{m,N,Q_0}(v,r,s,j)
 =\sum_{k\in\mathcal K_{N,Q_0}(v,j)}M_{m,N}^{r,s}(k),    \tag{4.13}
\]

and Theorem 3 gives `M_(m,N)^(r,s)(k) <= M_(m,N)(k) <= 4N`
for every summand. No estimate for the cardinality of the special set
`K_(N,Q0)(v,j)` is asserted here.

## 5. Exact spectral expansion and the incidence scale

Put `H=10^m` and `e(x)=exp(2*pi*i*x)`. Reindex T8's orientation/core records
by the explicit bijection sending `(false,(r,n))` to `(n,n+r)` and
`(true,(r,n))` to `(n+r,n)`. Under this reindexing, T8's sum is

\[
 S_h(m,N)=\sum_{q\in Q_{m,N}}e(h\lambda_q\pi),
 \qquad 1\le h\le H,                                     \tag{5.1}
\]

and its positive-frequency energy is

\[
 E(m,N)=\sum_{h=1}^{H}|S_h(m,N)|^2.                       \tag{5.2}
\]

Expansion gives

\[
 E(m,N)=H|Q_{m,N}|+
 \operatorname{Re}\sum_{(q,q')\in\mathcal P_{m,N}}
 \sum_{h=1}^{H}e(h(\lambda_q-\lambda_{q'})\pi).          \tag{5.3}
\]

For `0<||x||<=1/2`, the finite geometric sum and
`|sin(pi*x)|>=2||x||` imply

\[
 \left|\sum_{h=1}^{H}e(hx)\right|
 \le\min\left\{H,{1\over2\|x\|}\right\}.              \tag{5.4}
\]

For `N>=2`, grouping (5.3) by the exact partition (4.11), and noting that a
member of bin `j` has `1/(2||x||)<2^j`, yields the fully explicit upper bound

\[
 E(m,N)\le H|Q_{m,N}|+
 \sum_{v=0}^{N-1}\sum_{r=m}^{N-1}\sum_{s=m}^{N-1}
 \sum_{j=1}^{J_{Q_0}(N)}
   \min\{H,2^j\}A_{m,N,Q_0}(v,r,s,j).                    \tag{5.5}
\]

For `N=1`, the domain `Q_(m,1)` is empty for every positive `m`, so
`E(m,1)=0`; the cutoff `J_(Q0)(1)` and (5.5) are not invoked.

Equation (5.5) is derived here, not imported from T9. The T9 note's
reciprocal-spacing discussion is only sketch-level motivation for recording
these bins. Theorem 3 controls repeated coefficient differences, but it does
not by itself control how many distinct coefficients enter a close circle
bin; (4.13) displays that remaining distinction exactly.

## 6. A proved nonempty uniform range for T8

The triangle inequality in (5.1) gives, for every `h`,

\[
 |S_h(m,N)|\le|Q_{m,N}|=d(d+1).                           \tag{6.1}
\]

Consequently, at every positive `m,N`,

\[
 E(m,N)\le H\,d^2(d+1)^2.                                \tag{6.2}
\]

Assume the range condition `d^2<=N`. If `d=0`, the energy is zero. If
`d>=1`, then `d<=d^2<=N`, and hence

\[
 d(d+1)=d^2+d\le2N.                                      \tag{6.3}
\]

Substitution in (6.2) proves

\[
 \boxed{E(m,N)\le4\,10^mN^2
 \quad\text{whenever }m,N\ge1\text{ and }
       (\max\{N-m,0\})^2\le N.}                          \tag{6.4}
\]

The constant `4` is chosen before `m,N`. This is not merely the empty regime
`m>=N`: for every integer `t>=2`, take

\[
 N=t^2,\qquad m=t^2-t.                                   \tag{6.5}
\]

Then `m>=1`, `m<N`, `d=t`, `d^2=N`, and
`|Q_(m,N)|=t(t+1)>0`. Thus (6.4) is a nontrivial infinite uniform parameter
range for the exact T8 energy.

Now state the role of the external premise precisely. If the published
`mu(pi)<8` result is accepted as the hypothesis
`IrrationalityMeasureBelow pi 8`, T4 conditionally supplies one `Q0` with
`EffectiveIrrationality pi 8 1 Q0`. For that fixed `Q0`, Lemma 1 identifies
T8's domain with (1.6), and (6.4) holds uniformly on (R). The estimate itself
does not need (4.5); the external premise is used only to place it inside the
arithmetic branch required by T8's conditional route to C1.

T8's `machine-checked` conditional sufficient theorem requires one constant
for **all** positive `m,N`, not only those satisfying (R). Therefore (6.4)
does not instantiate T8's `UniformSpectralEnergyBound`, does not imply T2, and
does not prove C1.

## 7. What remains outside the proved range

For `d^2>N`, the trivial estimate (6.2), normalized by T8's target scale, is

\[
 {E(m,N)\over10^mN^2}\le
 {d^2(d+1)^2\over N^2}.                                  \tag{7.1}
\]

At the explicit legal scales `m=1`, `N>=2`, one has `d=N-1`, so the right
side is

\[
 {(N-1)^2N^2\over N^2}=(N-1)^2.                          \tag{7.2}
\]

Thus cardinality alone loses a factor growing quadratically. Theorem 3 does
not erase this loss: it bounds the number of representations of each fixed
integer coefficient difference, while (5.5) also depends on the number of
distinct differences in each dyadic circle bin.

A strictly range-restricted incidence question left by this note is whether
there is a constant `C>=0`, fixed before `m,N`, such that only on the
unresolved scales `m<N` and `(N-m)^2>N`,

\[
 \sum_{v=0}^{N-1}\sum_{r=m}^{N-1}\sum_{s=m}^{N-1}
 \sum_{j=1}^{J_{Q_0}(N)}
  \min\{10^m,2^j\}A_{m,N,Q_0}(v,r,s,j)
 \le C\,10^mN^2.                                         \tag{7.3}
\]

This is narrower than an all-scale aggregate target because (6.4) has already
settled every scale with `(N-m)^2<=N`. No claim is made that (7.3) holds.

## 8. Ambiguities and verification checklist

1. `m,N` are positive integers everywhere. `Q0` is a nonnegative integer
   fixed before `m,N`.
2. `Q_(m,N)` and `P_(m,N)` are ordered domains; no factor of two is hidden.
3. The lag endpoints are `m <= |a-b| <= N-1`.
4. The coefficient difference excludes `q=q'`; injectivity then excludes
   `k=0`.
5. `M_(m,N)(k)` counts ordered representations of the signed integer `k`.
6. The valuation index in (4.11) is `0,...,N-1`, although individual strata
   may be empty; gaps range over exactly `m,...,N-1`.
7. Dyadic bins are left-open and right-closed. They start at `j=1`, partition
   `(0,1/2]`, and terminate at the explicit finite `J_(Q0)(N)` from (4.9).
8. The multiplicity constant is exactly `4N`; the partial spectral constant
   is exactly `4`.
9. The external assertion `mu(pi)<8` is not proved here. T9 remains a
   `proof sketch` and supplies no premise.
10. The proved range (R) is a partial T8 result only. C1 remains open.

## Conclusion

The exact coefficient multiset has substantially less additive repetition
than the ambient `N^4` ordered quadruple count suggests: every nonzero integer
difference occurs at most `4N` times, with the entire loss arising from one
freely inserted canceled decimal exponent. The valuation, two exponent gaps,
and circle-distance bin give the exact finite decomposition (4.11). On the
nonempty uniform range `(max{N-m,0})^2<=N`, exact domain cardinality alone
proves T8's spectral normalization with constant `4`. Extending this to all
scales requires distributional control of distinct coefficient differences,
not merely pointwise irrationality or multiplicity control. No conclusion
about C1 is drawn.
