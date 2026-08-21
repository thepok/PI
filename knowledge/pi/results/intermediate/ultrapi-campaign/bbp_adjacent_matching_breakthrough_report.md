# BBP adjacent matching: infinite support replaces collision anti-concentration

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Primary input:
[bbp_adjacent_shift_matching_attack.md](bbp_adjacent_shift_matching_attack.md),
independently audited in
[bbp_adjacent_shift_matching_independent_audit.md](bbp_adjacent_shift_matching_independent_audit.md).

## Outcome and claim boundary

No asymptotic matching and no fixed-sixteen return was proved. Consequently
no proof that every finite decimal word occurs in pi was obtained; canonical
V1 remains a conjecture.

There is nevertheless a genuine reduction. The close-pair condition in the
primary input forces the limiting measure to be nonatomic, but the
Furstenberg step never needs that much. It only needs the common invariant
support to be **infinite**. For the actual BBP row, infinitude is equivalent
to a sequence of one-row, fixed-lag noncollapse tests:

\[
 \forall P\geq1:\quad
 \liminf_{j\to\infty}{1\over N_j}
 \sum_{n=1}^{N_j}
 \operatorname{dist}(u_{n+P},u_n)^2>0.                 \tag{I}
\]

For each fixed \(P\), this differs by \(O_P(N_j^{-1})\) from the exactly
rational periodic-defect average

\[
 {1\over N_j}\sum_{n=1}^{N_j}
 \bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{\,2}.          \tag{II}
\]

Thus the original two-point close-pair energy over all \(N_j^2\) pairs can be
replaced by the assertion that the row does not become density-one
approximately periodic with any one fixed decimal period. This replacement
is strictly weaker: it permits atoms and even measures with a large atomic
part. The reduction and its strictness are recorded as a proof sketch.

Neither (I) for pi nor the adjacent-row matching is proved. The companion
checker performs exact identities and bounded diagnostics only; those outputs
are an experiment.

## 1. Exact statement and quantifiers

Canonical V1 is

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists n\geq0\ \forall i<m:\quad d_{n+i}(\pi)=w_i.    \tag{1}
\]

Leading zeroes are allowed, occurrence is contiguous, and the empty word is
vacuous. Pi is irrational, so the eventually-nine decimal ambiguity does
not arise. The two noncanonical readings in the source record remain
separate: an arbitrary infinite word cannot be a suffix, while arbitrary
infinite words as subsequences reduce to every digit recurring infinitely
often. This note addresses only V1.

Retain the primary input's definitions

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_n=\sum_{k=0}^n{a(k)\over16^k},\qquad
 u_n=\{10^nB_n\},                                      \tag{2}
\]

and

\[
 \widetilde B_n={1\over30}+\sum_{k=0}^n{a(k+1)\over16^k},
 \qquad v_n=\{10^n\widetilde B_n\}.                    \tag{3}
\]

For \(n\geq1\), the already audited exact relation and recurrence are

\[
 v_n=T_{16}u_n+a(n+1)(5/8)^n,\qquad
 u_{n+1}=T_{10}u_n+\epsilon_{n+1},\quad
 \epsilon_{n+1}=a(n+1)(5/8)^{n+1},                    \tag{4}
\]

with all equalities on the circle. Put

\[
 \eta_N={1\over N}\sum_{n=1}^N\delta_{u_n},\qquad
 \xi_N={1\over N}\sum_{n=1}^N\delta_{v_n}.             \tag{5}
\]

The matching quantifiers below are exactly

\[
 \exists C\geq1\ \exists(N_j,G_j,\sigma_j,\delta_j)_j:
 \quad N_j\to\infty,\quad\delta_j\to0,                 \tag{6}
\]

where \(G_j\subseteq\{1,\ldots,N_j\}\) and
\(\sigma_j:G_j\to\{1,\ldots,N_j\}\),

\[
 {|G_j|\over N_j}\to1,\qquad
 \max_m|\sigma_j^{-1}(m)|\leq C,\qquad
 \max_{n\in G_j}\operatorname{dist}
       (v_n,u_{\sigma_j(n)})\leq\delta_j.              \tag{7}
\]

In (I) and (II), \(P\) is fixed before \(j\to\infty\); the positive lower
bound may depend on \(P\). No uniformity in \(P\) is asserted.

## 2. Infinite-support matching criterion

**Proposition 2.1 (proof sketch).** If (6)--(7) hold and, on the same
sequence \(N_j\), (II) has positive liminf for every fixed integer \(P\geq1\),
then \(K_\pi=\mathbb T\), and hence V1 holds.

**Proof.** Pass to a further subsequence on which
\(\eta_{N_j}\Rightarrow\mu\). The audited BBP tail comparison makes
\(\mu\) a \(T_{10}\)-invariant probability with

\[
 A:=\operatorname{supp}\mu\subseteq K_\pi.             \tag{8}
\]

The adjacent identity gives
\(\xi_{N_j}\Rightarrow(T_{16})_*\mu\). The density-one,
bounded-congestion matching gives, for every continuous \(f\geq0\),

\[
 \int f\,d(T_{16})_*\mu\leq C\int f\,d\mu.             \tag{9}
\]

Therefore

\[
                  T_{16}A\subseteq A.                  \tag{10}
\]

Invariance of \(\mu\) gives \(T_{10}A=A\).

For fixed \(P\), put
\(g_P(x)=\operatorname{dist}(T_{10}^Px,x)^2\). This is a bounded continuous
circle function, so weak convergence gives

\[
 \lim_{j\to\infty}{1\over N_j}\sum_{n=1}^{N_j}
 \bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{\,2}
 =\int_A\operatorname{dist}(T_{10}^Px,x)^2\,d\mu(x).  \tag{11}
\]

The limit in (11) exists for each fixed \(P\) along this weakly convergent
further subsequence, and it is at least the liminf along the original
\(N_j\). Hence it is \(D_P(\mu)>0\). Countability of \(P\geq1\) causes no
diagonal-subsequence loss: one weakly convergent subsequence already gives
(11) simultaneously for every bounded continuous \(g_P\).

If \(A\) were finite, the equality \(T_{10}A=A\) would make
\(T_{10}:A\to A\) a permutation. Some common positive power \(P\) would fix
every point of \(A\), making the right side of (11) zero. The assumed
positive liminf excludes this. Thus \(A\) is infinite.

It remains to record precisely why infinite support is enough. The closed
set \(A\) is forward invariant under the non-lacunary semigroup generated by
10 and 16. If it contains an irrational point, Furstenberg's Theorem IV.1
makes that point's semigroup orbit dense, hence \(A=\mathbb T\). If every
point of \(A\) were rational, then \(A-A\) would be countable. But a sequence
of distinct points \(a_r\in A\) has, by compactness, a convergent subsequence
\(a_{r_s}\to a\in A\); the nonzero differences
\(a_{r_s}-a_{r_{s+1}}\in A-A\) tend to zero. Thus zero is a non-isolated
point of the closed semigroup-invariant set \(A-A\). Furstenberg's Lemma IV.2
would give \(A-A=\mathbb T\), contradicting countability. So the
irrational-point case must occur, and

\[
                  \mathbb T=A\subseteq K_\pi.          \tag{12}
\]

The audited decimal-cylinder bridge now gives V1. \(\square\)

The last paragraph is also a useful standalone corollary of Furstenberg:
an infinite closed circle set forward invariant under both multiplication by
10 and multiplication by 16 is the whole circle. The primary proof used
nonatomicity only to manufacture an irrational support point; (12) shows
that support infinitude already does so.

## 3. Exact characterization by periodic defects

For a \(T_{10}\)-invariant probability \(\mu\) on the circle, define

\[
 D_P(\mu)=\int\operatorname{dist}(T_{10}^Px,x)^2\,d\mu(x).
                                                               \tag{13}
\]

Then

\[
 \boxed{\operatorname{supp}\mu\text{ is infinite}
 \quad\Longleftrightarrow\quad
 D_P(\mu)>0\text{ for every }P\geq1.}                  \tag{14}
\]

Indeed, \(D_P(\mu)=0\) implies that the nonnegative continuous integrand
vanishes on the support, so

\[
 \operatorname{supp}\mu\subseteq
 \operatorname{Fix}(T_{10}^P)
 =\{x:(10^P-1)x=0\},                                   \tag{15}
\]

a finite set. Conversely, invariance means
\((T_{10})_*\mu=\mu\). For a continuous map on a compact space this gives
\(T_{10}(\operatorname{supp}\mu)=\operatorname{supp}\mu\): the forward
inclusion follows by pulling neighborhoods back, and the reverse inclusion
uses compactness of the support image. If that support is finite, this
surjection is a permutation and a common positive power fixes it pointwise.
This proves (14) without an entropy or ergodicity assumption.

There is an equivalent sparse spectral test. With
\(\widehat\mu(q)=\int e(qx)\,d\mu(x)\),

\[
 \operatorname{supp}\mu\text{ is infinite}
 \quad\Longleftrightarrow\quad
 |\widehat\mu(10^P-1)|<1\quad\hbox{for every }P\geq1.  \tag{16}
\]

If equality in modulus holds, equality in the triangle inequality confines
the support to one finite fibre of \(x\mapsto e((10^P-1)x)\). In the other
direction, a common period \(P\) for a finite invariant support makes the
character identically one. Unlike Fourier equidistribution, (16) asks only
for a nonzero gap from complete concentration at the special frequencies
\(10^P-1\).

## 4. Fixed-lag BBP form and an exact error bound

Iterating (4) for fixed \(P\geq1\) gives

\[
 u_{n+P}=T_{10}^Pu_n+E_{n,P},\qquad
 E_{n,P}=\sum_{r=1}^P10^{P-r}\epsilon_{n+r}.            \tag{17}
\]

The function \(x\mapsto\|x\|_{\mathbb T}^2\) is
one-Lipschitz on the circle. Hence

\[
 \left|
 \operatorname{dist}(u_{n+P},u_n)^2
 -\bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{\,2}
 \right|\leq E_{n,P}.                                  \tag{18}
\]

Since \(a(k)<k^{-2}\leq1\) for \(k\geq1\), Tonelli's theorem for
nonnegative series and a geometric sum give the endpoint-safe bound

\[
 \begin{aligned}
 \sum_{n\geq1}E_{n,P}
 &\leq\sum_{r=1}^P10^{P-r}\sum_{n\geq1}(5/8)^{n+r}\\
 &= {5\over3}\sum_{r=1}^P10^{P-r}(5/8)^r
  ={10^P\over9}(1-16^{-P})<\infty.                    \tag{19}
 \end{aligned}
\]

In particular, for every \(N\geq1\),

\[
 \left|{1\over N}\sum_{n=1}^N
 \left\{\operatorname{dist}(u_{n+P},u_n)^2
 -\bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{\,2}\right\}\right|
 \leq {10^P(1-16^{-P})\over9N}.                       \tag{19a}
\]

There is no missing right endpoint: the infinite BBP row defines
\(u_{N+P}\), and (17) uses exactly the forcing indices \(n+1,\ldots,n+P\).
Therefore the averages in (I) and (II) differ by \(O_P(N^{-1})\). The new
support condition is consequently a fixed-lag recurrence target on the one
actual BBP row. It does not ask for separation of all pairs, a decay rate in
\(P\), or cancellation of every Fourier mode.

This reformulation is exact but does not prove (I). For a sparse irrational
decimal orbit, almost every adjacent \(P\)-lag pair may still shadow the same
periodic orbit; irrationality and an infinite omega-limit set do not prevent
the average in (I) from tending to zero.

## 5. Why the replacement is strictly weaker

The primary close-pair condition makes every weak limit nonatomic, so it
automatically implies infinite support and (I)--(II). The converse fails
even among measures invariant under both maps. Let

\[
                  \mu={1\over2}\delta_0+{1\over2}m,
                                                               \tag{20}
\]

where \(m\) is normalized Lebesgue measure. It is invariant under
\(T_{10}\) and \(T_{16}\), and its support is the whole circle. For every
\(P\geq1\), multiplication by \(10^P-1\) preserves \(m\), so

\[
 D_P(\mu)={1\over2}\int_{-1/2}^{1/2}t^2\,dt={1\over24}>0. \tag{21}
\]

But the atom at zero contributes \(1/4\) to the limiting small-scale
close-pair energy. Thus the old condition fails while the new one succeeds.
This is strict logical weakening, not a claim about the empirical measure of
pi.

Finite bad supports are not a vacuous edge case. For every \(Q\geq2\) with
\(\gcd(Q,10)=1\), the rational grid

\[
                       A_Q=Q^{-1}\mathbb Z/\mathbb Z   \tag{22}
\]

is permuted by both \(T_{10}\) and \(T_{16}\). If \(P\) is the
multiplicative order of 10 modulo \(Q\), then \(D_P(\mu)=0\) for every
probability supported on \(A_Q\) and invariant under \(T_{10}\). The
quantifier over all fixed \(P\) in (I) cannot be replaced by checking a few
small periods.

## 6. A second reduction: positive-mass matching under ergodicity

There is also a transport weakening, although it adds an ergodicity
hypothesis.

**Proposition 6.1 (proof sketch).** Suppose
\(\eta_{N_j}\Rightarrow\mu\), the limit \(\mu\) is \(T_{10}\)-ergodic,
(I) holds for every \(P\), and there are
\(G_j\subseteq\{1,\ldots,N_j\}\), maps
\(\sigma_j:G_j\to\{1,\ldots,N_j\}\), a fixed congestion bound \(C\), and
\(\delta_j\to0\) such that

\[
 \liminf_j{|G_j|\over N_j}>0,
 \qquad\max_m|\sigma_j^{-1}(m)|\leq C,
 \qquad\max_{n\in G_j}d(v_n,u_{\sigma_j(n)})\leq\delta_j. \tag{23}
\]

Then V1 holds.

To see this, first pass to a further subsequence on which
\(|G_j|/N_j\to\gamma>0\). Put mass \(1/N_j\) on every matched pair
\((v_n,u_{\sigma_j(n)})\), obtaining a subprobability \(\lambda_j\) on
\(\mathbb T^2\) of total mass tending to \(\gamma\). Compactness supplies
\(\lambda_j\Rightarrow\lambda\). Its first marginal is bounded by
\(\xi_{N_j}\), so \((\mathrm{pr}_1)_*\lambda\leq(T_{16})_*\mu\); its second
marginal is bounded by \(C\eta_{N_j}\), so
\((\mathrm{pr}_2)_*\lambda\leq C\mu\). The distances of all matched pairs
are at most \(\delta_j\to0\). Therefore
\(\int d(x,y)\,d\lambda_j\leq\delta_j|G_j|/N_j\to0\).
The distance is continuous and bounded on the compact square, so weak
convergence gives \(\int d(x,y)\,d\lambda=0\). Thus \(\lambda\) is carried
by the diagonal and its two marginals agree with a nonzero measure
\(\rho\). Consequently

\[
 0\ne\rho\leq(T_{16})_*\mu,\qquad \rho\leq C\mu,       \tag{23a}
\]

which rigorously rules out mutual singularity; no almost-everywhere orbit
claim is used. The pushforward is also \(T_{10}\)-ergodic because
\(T_{10}\) and \(T_{16}\) commute, a fact already machine-checked in T39.
T39 also machine-checks that distinct ergodic invariant probabilities for a
common map are mutually singular. Hence

\[
                         (T_{16})_*\mu=\mu.             \tag{24}
\]

Condition (I) makes the support infinite by (14), and the Furstenberg
argument finishes. This version needs only a fixed positive fraction of
matched points, not density one. It does not prove that an ergodic empirical
limit or the positive matching exists for the BBP row; it is an alternative
finite target, closely aligned with the already machine-checked conditional
T70 interface.

## 7. One more exact adjacent identity—and why it does not close the gap

The endpoint correction also yields, for every \(n\geq1\),

\[
                         \boxed{T_5v_n=T_8u_{n+1}}.     \tag{25}
\]

Indeed, before taking fractional parts the \(B_{n+1}\) contributions are
both \(80\,10^nB_{n+1}\), while the remaining difference is
\(-2505\,10^{n-1}\), an integer. This identity is exact and the companion
checker replays it with rational arithmetic.

It does not imply overlap of the two rows. At the weak-limit level, with
\(\nu=(T_{16})_*\mu\), (25) becomes

\[
 (T_5)_*\nu=(T_{80})_*\mu=(T_8)_*(T_{10})_*\mu
                         =(T_8)_*\mu,                  \tag{26}
\]

which follows already from \(T_{10}\)-invariance. Multiplication by 5 and
8 is many-to-one on the circle, so equality after these factors cannot be
cancelled. The identity is useful normalization, not the missing matching.

## 8. Attempts to discharge the new targets

The following checks did not prove (7), (I), or (23).

1. **Coefficient recurrence.** Equation (18) shows that the BBP forcing is
   summably erased even in the new fixed-lag averages. It transfers (I) to
   the actual decimal lag statistic; it does not create a positive main term.
2. **Finite irrationality measure.** This cannot rule out density-one
   approximate periodicity. The decimal Kempner--Fredholm separator already
   recorded in the one-character audit has irrationality exponent two while
   its decimal empirical measure is \(\delta_0\).
3. **Infinite topological limit set.** Lagarias's Theorem 3.3 rules out an
   actually finite limit set for irrational pi, and Chen--Ye--Zheng give
   stronger progression-slice dispersion for
   \((10^n-16)\pi\). Neither result gives positive Cesaro mass to the
   exceptional limit points. A density-zero family of excursions can keep
   every average in (I) at zero.
4. **Pair-correlation literature.** Available lacunary pair-correlation
   theorems are metric statements for almost every multiplier. They cannot
   be specialized to the fixed value pi. Such a specialization would also
   give much more than (I).
5. **Sparse matching separator.** For
   \(\beta=\sum_{r\geq1}10^{-2^r}\), remove starts whose next \(L\) digits
   see a power of two. At most
   \(L(1+\lfloor\log_2(N+L)\rfloor)\) starts are removed, and on every
   remaining start the indexwise distance between \(T_{16}T_{10}^n\beta\)
   and \(T_{10}^n\beta\) is at most \((5/3)10^{-L}\). Taking
   \(L\to\infty\) slowly proves density-one \(C=1\) matching, while the
   empirical limit is still \(\delta_0\). This confirms that matching alone
   cannot supply even the weaker support condition.

The exact unresolved route is now:

\[
 \boxed{\text{prove (7) and prove (I) for every fixed }P
        \text{ on the same }N_j.}                       \tag{27}
\]

Or, through Proposition 6.1, prove an ergodic empirical limit, a
positive-mass adjacent matching, and the same fixed-period noncollapse.
Neither route is currently closed.

## 9. Literature, mathlib, and replay audit

Status of this bounded source search: literature-checked on
**2026-08-13 UTC**.

| source | exact applicability |
|---|---|
| Furstenberg, [Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation](https://doi.org/10.1007/BF01692494), Lemma IV.2 and Theorem IV.1 | the infinite-common-support argument; local PDF SHA-256 cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358 |
| Lagarias, [On the Normality of Arithmetical Constants](https://arxiv.org/abs/math/0101055v2), Theorems 3.1 and 3.3 and the remarks after Theorem 3.3 | BBP shadowing and the finite-limit-set rationality criterion; the paper explicitly does not prove density-one digit agreement; local PDF SHA-256 a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9 |
| Chen--Ye--Zheng, [Distribution modulo one of linear recurrent sequences](https://arxiv.org/abs/2604.14036v1), Theorem 1.3 | topological limit-set and residue-slice dispersion, not Cesaro noncollapse; local v1 PDF SHA-256 a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d |
| Technau--Rudnick, [The metric theory of the pair correlation function of real-valued lacunary sequences](https://arxiv.org/abs/2001.08820v1) | almost-every-multiplier pair correlation; not applicable to fixed pi; local v1 PDF SHA-256 364164f781a31ad5267b3c43d91b0593418744e8ac9073407e24581981b887b2 |
| local [T39 ergodic-affinity rigidity](../../TheoryLib/PiPositiveDecimalFactorEntropy/T39T39ErgodicAffinityRigidity.lean) and [T70 empirical-rigidity bridge](../../TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean) | machine-checked commutation, pushforward ergodicity, and common-ergodic nonsingularity implication; SHA-256 respectively f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09 and f8ecbfd2d9f8a13216e75d5ebb3732b98f7844147776b30de7f2666fc7ddec55 |

Fresh searches for “BBP adjacent coefficient empirical measure”,
“perturbed b-transformation finite support empirical measure”, “fixed
irrational lacunary pair correlation”, and “times p times q quasi-invariant
support” found no primary theorem proving (7), (I), or (23) for pi. This is a
dated bounded search, not an exhaustive absence or novelty claim.

A local mathlib search found Measure.support_mono,
Measure.AbsolutelyContinuous.support_mono, and
Measure.MutuallySingular. These cover the elementary measure-order pieces
of Propositions 2.1 and 6.1. No Lean declaration is added here, and neither
proposition is machine-checked.

The companion
[bbp_adjacent_matching_breakthrough_check.py](bbp_adjacent_matching_breakthrough_check.py)
uses exact rational arithmetic to replay 192 adjacent identities, 192
instances of (25), 2,016 fixed-lag comparisons (18), and 1,279 finite common
invariant-grid checks. Its \(N=48,96,192\), \(P=1,\ldots,6\) periodic-defect
values are only an experiment; they are not extrapolated. It also checks
the exact \(1/24\) versus \(1/4\) strictness example, source pins, mathlib
markers, and the sparse matching separator. Its output explicitly sets all
asymptotic-matching, pi-periodic-defect, fixed-return, and V1 assertion flags
to false.

## Bottom line

The collision-energy obligation in the audited adjacent-shift criterion is
not intrinsic. It can be replaced, exactly and strictly, by fixed-lag
noncollapse (I) for every decimal period. Under ergodicity, the matching can
also be reduced from density one to any fixed positive proportion. These are
smaller, inspectable targets, and (25) adds one exact coefficient-specific
identity. None of the new asymptotic targets has been proved for pi, so the
fixed-sixteen return and canonical V1 remain open.
