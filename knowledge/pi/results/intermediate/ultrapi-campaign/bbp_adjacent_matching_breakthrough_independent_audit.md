# Independent audit: BBP adjacent matching infinite-support reduction

Audit date: **2026-08-13 UTC**

Canonical target:
[problems/local/pi-digits.txt](../../problems/local/pi-digits.txt), SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Primary artifact:
[bbp_adjacent_matching_breakthrough_report.md](bbp_adjacent_matching_breakthrough_report.md)

Primary checker:
[bbp_adjacent_matching_breakthrough_check.py](bbp_adjacent_matching_breakthrough_check.py)

Independent checker:
[bbp_adjacent_matching_breakthrough_independent_check.py](bbp_adjacent_matching_breakthrough_independent_check.py)

## Verdict and claim boundary

**PASS after two narrow quantifier/source-reproducibility corrections.** The
density-one domination argument, the same-subsequence periodic-defect
criterion, the exact infinite-support characterization, the rational-support
use of Furstenberg's Lemma IV.2, the irrational-point use of Furstenberg's
Theorem IV.1, the fixed-lag endpoint constant, the strict weakening example,
and the positive-mass ergodic matching argument all rederive.

The infinite arguments remain a **proof sketch**. The bounded source audit is
**literature-checked** on the audit date. Both replay programs report only an
**experiment** for their bounded BBP values. No adjacent matching, no positive
periodic-defect lower bound for pi, no fixed-sixteen return, and no instance of
canonical V1 has been proved. Canonical V1 remains a **conjecture**; this is not
a **candidate resolution** or a **verified resolution**.

The exact unresolved alternatives are:

1. On one sequence \(N_j\), prove the density-one bounded-congestion matching
   (6)--(7) and, for every fixed \(P\geq1\), prove the positive-liminf
   fixed-lag condition (I).
2. Or prove that one empirical limit is \(T_{10}\)-ergodic, prove the same
   fixed-lag conditions, and match a fixed positive proportion with uniformly
   bounded congestion and vanishing error as in (23).

Every quantifier above is essential. Neither alternative is discharged in the
primary artifact or here.

## Corrections recorded

The live pre-correction primary report and checker had SHA-256 respectively
10102a8ac95f41eae04eb2e4437bc0f5bad82e6d6ba709d4fde0fbe403f2d and
44aea3c1e64a3dc005033958b1232a02cc94c855e6d6ba709d4fde0fbe403f2d.
Their corrected hashes are recorded below.

1. The report now types both matching maps explicitly as
   \(\sigma_j:G_j\to\{1,\ldots,N_j\}\), once in the global quantifier block and
   again in Proposition 6.1. The intended codomain was recoverable from the
   preceding audited report, but leaving it implicit made the congestion
   maximum and second marginal formally ambiguous.
2. The source table and primary checker now pin the local Chen--Ye--Zheng and
   Technau--Rudnick v1 PDFs and, crucially, the T39 Lean file that contains the
   ergodic-measure dichotomy used in Proposition 6.1. Pinning only T70 did not
   freeze its imported T39 dependency. The Technau--Rudnick URL is now also
   explicitly versioned to match the local PDF.

Neither correction changes a mathematical conclusion.

## Frozen artifact and source pins

| file | SHA-256 |
|---|---|
| problems/local/pi-digits.txt | 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825 |
| bbp_adjacent_shift_matching_attack.md | 2764624665fcb2bd4f7a7f8d4a1c4d1094e9459297e018cb095e0a76ff0feba6 |
| bbp_adjacent_shift_matching_independent_audit.md | 2a4027b9a33806425903c5d5a460349230ad716f3e9672f19300f0874b2a4866 |
| bbp_adjacent_matching_breakthrough_report.md | 2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042 |
| bbp_adjacent_matching_breakthrough_check.py | 2844f28d7ecdf13c02c623a3ba17c43dcde347efa4e8c4e864d48530eac873e9 |
| bbp_adjacent_matching_breakthrough_independent_check.py | f7bca90e7dedd923c5b1a95ecf177905a23dbd3878d472625b43098286e2ce00 |
| Furstenberg 1967 local PDF | cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358 |
| Lagarias arXiv v2 local PDF | a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9 |
| Chen--Ye--Zheng arXiv v1 local PDF | a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d |
| Technau--Rudnick arXiv v1 local PDF | 364164f781a31ad5267b3c43d91b0593418744e8ac9073407e24581981b887b2 |
| T39T39ErgodicAffinityRigidity.lean | f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09 |
| T70T70EmpiricalRigidityBridge.lean | f8ecbfd2d9f8a13216e75d5ebb3732b98f7844147776b30de7f2666fc7ddec55 |

The independent checker pins every row except itself. Its displayed hash
freezes the checked bytes without a self-referential pin.

## 1. Definitions, indices, and adjacent identities

The previously audited definitions are

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_n=\sum_{k=0}^n\frac{a(k)}{16^k},\qquad
 u_n=\{10^nB_n\},
\]

and

\[
 \widetilde B_n=\frac1{30}+\sum_{k=0}^n\frac{a(k+1)}{16^k},
 \qquad v_n=\{10^n\widetilde B_n\}.
\]

The pole combination and rational form agree exactly. For \(k\geq1\),

\[
 \frac1{k^2}-a(k)=
 \frac{392k^4+873k^3+665k^2+194k+15}
 {k^2(2k+1)(4k+3)(8k+1)(8k+5)}>0.             \tag{A1}
\]

The endpoint arithmetic \(a(0)=47/15\) and
\(16a(0)-1/30=501/10\) gives, for \(n\geq1\),

\[
 v_n=T_{16}u_n+a(n+1)(5/8)^n.                       \tag{A2}
\]

The inclusive-index recurrences are

\[
 u_{n+1}=T_{10}u_n+a(n+1)(5/8)^{n+1},\qquad
 v_{n+1}=T_{10}v_n+a(n+2)(5/8)^{n+1}.               \tag{A3}
\]

The independent checker constructs every \(u_n\) and \(v_n\) directly from
the two rational partial sums rather than importing either recurrence. It
then replays 149 instances of (A2), 298 instances of (A3), and 149 instances
of the extra identity

\[
                         T_5v_n=T_8u_{n+1}.           \tag{A4}
\]

For (A4), the two unreduced real expressions differ by exactly

\[
 10^n\left(\frac16-\frac{80\cdot47}{15}\right)
 =-2505\,10^{n-1},
\]

which is an integer precisely for the stated range \(n\geq1\). Thus no
endpoint is silently extended to \(n=0\).

## 2. Density-one matching and measure domination

Fix a weakly convergent further subsequence
\(\eta_{N_j}\Rightarrow\mu\). The already audited tail comparison transfers
the exact decimal orbit's telescoping \(T_{10}\)-invariance to \(\mu\), and
\(\operatorname{supp}\mu\subseteq K_\pi\). Equation (A2) gives synchronously

\[
                  \xi_{N_j}\Rightarrow\nu:=(T_{16})_*\mu.       \tag{A5}
\]

For continuous \(f\geq0\), the typed matching map and its congestion bound
give

\[
\begin{aligned}
 \int f\,d\xi_{N_j}
 &\leq \frac1{N_j}\sum_{n\in G_j}f(u_{\sigma_j(n)})
      +\omega_f(\delta_j)
      +\|f\|_\infty\frac{N_j-|G_j|}{N_j}\\
 &\leq C\int f\,d\eta_{N_j}+o(1).
\end{aligned}                                                    \tag{A6}
\]

The direction of congestion is correct: every target index is counted at
most \(C\) times. Density one removes the unmatched first-marginal mass.
Taking limits for all nonnegative continuous \(f\) yields

\[
                           \nu\leq C\mu.              \tag{A7}
\]

For a continuous map on a compact space,
\(\operatorname{supp}(F_*\mu)=F(\operatorname{supp}\mu)\). Therefore (A7)
implies

\[
 T_{16}(\operatorname{supp}\mu)\subseteq\operatorname{supp}\mu. \tag{A8}
\]

No surjectivity of the matching map, equality of measures, or hidden
ergodicity assumption is used.

## 3. Same-subsequence defects and exact support characterization

For fixed \(P\geq1\), let

\[
 g_P(x)=\operatorname{dist}(T_{10}^Px,x)^2.
\]

This is bounded and continuous. Weak convergence of the one selected
subsequence therefore gives

\[
 \frac1{N_j}\sum_{n=1}^{N_j}\|(10^P-1)u_n\|_{\mathbb T}^2
 \longrightarrow D_P(\mu):=\int g_P\,d\mu.           \tag{A9}
\]

This holds for every fixed \(P\) on the same subsequence. There is no
diagonal-subsequence defect: the definition of weak convergence already
tests every continuous function against the one convergent sequence. Since
the original liminf is positive for each fixed \(P\), every further
subsequence limit in (A9) remains positive.

For a \(T_{10}\)-invariant probability,

\[
 \operatorname{supp}\mu\text{ is infinite}
 \quad\Longleftrightarrow\quad
 D_P(\mu)>0\text{ for every }P\geq1.                 \tag{A10}
\]

If \(D_P(\mu)=0\), continuity and nonnegativity make \(g_P\) vanish on the
support, so that support lies in
\(\operatorname{Fix}(T_{10}^P)\), a set of \(10^P-1\) points. Conversely,
\(T_{10}\)-invariance and compactness imply

\[
 T_{10}(\operatorname{supp}\mu)=\operatorname{supp}\mu.
\]

On a finite support this is a permutation. The least common multiple of its
cycle lengths supplies one \(P\geq1\) fixing the support pointwise, and hence
\(D_P(\mu)=0\). This proves both directions with no entropy or ergodicity.

The Fourier variant also rederives:

\[
 \operatorname{supp}\mu\text{ is infinite}
 \quad\Longleftrightarrow\quad
 |\widehat\mu(10^P-1)|<1\text{ for every }P\geq1.    \tag{A11}
\]

Equality in the triangle inequality confines the support to one finite fibre
of \(x\mapsto e((10^P-1)x)\). A finite invariant support has a common period
and makes the relevant character identically one.

## 4. Why infinite common support is sufficient

Let \(A=\operatorname{supp}\mu\). Invariance gives \(T_{10}A=A\), while
(A8) gives \(T_{16}A\subseteq A\). The multiplicative semigroup generated by
10 and 16 is non-lacunary in Furstenberg's Definition IV.1: the two generators
cannot both be powers of one integer, as their prime valuations are
incompatible.

If \(A\) contains an irrational \(z\), Furstenberg's Theorem IV.1 says the
semigroup orbit of \(z\) is dense. Forward invariance and closedness then give
\(A=\mathbb T\).

Suppose instead that every point of the infinite compact set \(A\) is
rational. Then \(A-A\) is compact, hence closed; it is forward invariant under
both generators; and it is countable. Choose a sequence of distinct points of
\(A\) converging in \(A\). Consecutive nonzero differences tend to zero, so
zero is non-isolated in \(A-A\). Furstenberg's Lemma IV.2 applies and gives
\(A-A=\mathbb T\), contradicting countability. Thus the irrational case must
occur.

The source locator is exact: Definition IV.1 is on journal page 47, Lemma
IV.2 spans pages 47--48, and Theorem IV.1 is on page 48 of the pinned local
PDF. Both the lemma and theorem require a closed forward-invariant set for a
non-lacunary semigroup, exactly the hypotheses established above. They do not
require invertibility or two-sided invariance.

It follows that

\[
                       \mathbb T=A\subseteq K_\pi,
\]

so the audited decimal-cylinder bridge gives V1 conditionally on the two
unresolved premises.

## 5. Fixed-lag identity and endpoint bound

Iterating (A3) gives exactly

\[
 u_{n+P}=T_{10}^Pu_n+E_{n,P},\qquad
 E_{n,P}=\sum_{r=1}^P10^{P-r}a(n+r)(5/8)^{n+r}.       \tag{A12}
\]

The function \(x\mapsto\|x\|_{\mathbb T}^2\) is one-Lipschitz: if
\(s,t\in[0,1/2]\), then
\(|s^2-t^2|=|s-t|(s+t)\leq|s-t|\). Therefore

\[
 \left|
  \operatorname{dist}(u_{n+P},u_n)^2
  -\|(10^P-1)u_n\|_{\mathbb T}^2
 \right|\leq E_{n,P}.                                \tag{A13}
\]

Using \(a(k)<k^{-2}\leq1\) and summing first over \(n\geq1\),

\[
\begin{aligned}
 \sum_{n\geq1}E_{n,P}
 &\leq\frac53\sum_{r=1}^P10^{P-r}(5/8)^r\\
 &=\frac{10^P}{9}(1-16^{-P}).                         \tag{A14}
\end{aligned}
\]

Dividing by \(N\) proves the displayed \(O_P(N^{-1})\) comparison. There is
no lost right endpoint because the infinite row defines every \(u_{N+P}\),
and the forcing indices in (A12) are exactly \(n+1,\ldots,n+P\).

The independent replay verifies 1,235 exact rational instances for
\(N=31,79,137\) and \(P=1,2,3,5,8\), including both the finite partial forcing
sum and the universal constant (A14). Those bounded values are an
**experiment**, not evidence for a positive asymptotic liminf.

## 6. Strict weakening

For

\[
                         \mu=\tfrac12\delta_0+\tfrac12m,
\]

both \(T_{10}\) and \(T_{16}\) preserve \(\mu\), and its support is the whole
circle. Since integer multiplication preserves normalized Lebesgue measure,

\[
 D_P(\mu)=\frac12\int_{-1/2}^{1/2}t^2\,dt=\frac1{24}
\]

for every \(P\geq1\). The atom at zero contributes \(1/4\) to the limiting
small-scale pair mass. Thus infinite support and every periodic-defect test
can hold while the nonatomic close-pair obligation fails. The replacement is
strict at the measure-property level and does not claim that this is pi's
empirical measure.

The finite counterexamples also rederive. If \(Q\geq2\) and
\(\gcd(Q,10)=1\), then the grid \(Q^{-1}\mathbb Z/\mathbb Z\) is permuted by
both maps. If \(P\) is the order of 10 modulo \(Q\), every grid point is fixed
by \(T_{10}^P\), so \(D_P=0\) for every measure on that grid. The independent
checker exhausts 2,643 grid points through \(Q=113\). This is a finite replay
of the elementary identity, not a substitute for its proof.

## 7. Positive-mass ergodic matching

Assume now that \(\eta_{N_j}\Rightarrow\mu\), that \(\mu\) is
\(T_{10}\)-ergodic, and that (23) holds. Passing to a further subsequence gives
\(|G_j|/N_j\to\gamma>0\). Define

\[
 \lambda_j=\frac1{N_j}\sum_{n\in G_j}
             \delta_{(v_n,u_{\sigma_j(n)})}.
\]

This is a subprobability of mass tending to \(\gamma\). Compactness supplies a
further weak limit \(\lambda\). At finite \(j\), its first marginal is at most
\(\xi_{N_j}\), while the congestion bound makes its second marginal at most
\(C\eta_{N_j}\). Measure order passes to weak limits on the compact circle, so

\[
 (\operatorname{pr}_1)_*\lambda\leq(T_{16})_*\mu,
 \qquad
 (\operatorname{pr}_2)_*\lambda\leq C\mu.            \tag{A15}
\]

Moreover,

\[
 \int d(x,y)\,d\lambda_j\leq
 \delta_j\frac{|G_j|}{N_j}\longrightarrow0.
\]

Continuity of the distance makes \(\lambda\) diagonal. Its two marginals are
therefore one common nonzero measure \(\rho\), of mass \(\gamma\), satisfying

\[
                  0\ne\rho\leq(T_{16})_*\mu,
                  \qquad \rho\leq C\mu.              \tag{A16}
\]

This really rules out mutual singularity. If \(\mu\perp(T_{16})_*\mu\), any
finite measure absolutely continuous with respect to both would be zero;
(A16) supplies a nonzero such measure. No pointwise orbit-overlap inference is
made.

The pinned T39 file machine-checks that \(T_{10}\) and \(T_{16}\) commute,
that \(T_{10}\)-ergodicity passes to \((T_{16})_*\mu\), and that two probability
measures ergodic for one map are equal or mutually singular. Hence (A16)
gives

\[
                             (T_{16})_*\mu=\mu.        \tag{A17}
\]

The same fixed-lag hypotheses yield infinite support by (A9)--(A10), and the
Furstenberg argument finishes. This validates Proposition 6.1. It does not
prove the ergodic limit, positive matching mass, or periodic-defect bounds for
the actual BBP row.

## 8. Extra identity and failed cancellation

Taking weak limits in (A4) gives, with
\(\nu=(T_{16})_*\mu\),

\[
 (T_5)_*\nu=(T_{80})_*\mu=(T_8)_*(T_{10})_*\mu
                         =(T_8)_*\mu.                 \tag{A18}
\]

This is already forced by \(T_{10}\)-invariance. Neither \(T_5\) nor \(T_8\)
is injective on the circle, so they cannot be cancelled to infer
\(\nu=\mu\). The report correctly labels (A4) as exact normalization rather
than the missing matching.

## 9. Literature and replay audit

The bounded literature conclusions are supported by the pinned sources:

| source | checked locator and scope |
|---|---|
| Furstenberg, [Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation](https://doi.org/10.1007/BF01692494) | Definition IV.1, Lemma IV.2, and Theorem IV.1 on journal pages 47--48 support exactly the topological step used here. |
| Lagarias, [On the Normality of Arithmetical Constants](https://arxiv.org/abs/math/0101055v2) | Theorem 3.1 is the BBP-shadowing result; Theorem 3.3 states the finite-limit-set/rationality equivalence and explicitly warns that density-one digit agreement is unproved. |
| Chen--Ye--Zheng, [Distribution modulo one of linear recurrent sequences](https://arxiv.org/abs/2604.14036v1) | Theorem 1.3 gives an infinite topological limit set and progression-slice spread under its hypotheses, not positive Cesaro mass. |
| Technau--Rudnick, [The metric theory of the pair correlation function of real-valued lacunary sequences](https://arxiv.org/abs/2001.08820v1) | Theorem 1.1 is for Lebesgue-almost-every multiplier, so it cannot be specialized to fixed pi. |
| local [T39](../../TheoryLib/PiPositiveDecimalFactorEntropy/T39T39ErgodicAffinityRigidity.lean) and [T70](../../TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean) | The exact machine-checked commutation, pushforward-ergodicity, ergodic dichotomy, and conditional bridge interfaces are present and axiom-audited. |

Fresh primary-source searches on the audit date for fixed-irrational lacunary
pair correlation, BBP adjacent empirical measures, perturbed
\(b\)-transformation finite supports, and times-\(p\)/times-\(q\)
quasi-invariant supports found no theorem discharging either unresolved
alternative for pi. This is a dated bounded search, not an exhaustive absence
or novelty claim.

The primary checker passes. The independently written checker also passes and
reports:

- 149 adjacent identities from direct partial sums;
- 298 recurrence identities and 149 instances of (A4);
- 1,235 fixed-lag rational comparisons at different depths from the primary
  checker;
- 2,643 finite invariant-grid point checks;
- exact \(1/24\) and \(1/4\) values for the strictness example;
- separate sparse-separator counts, all labeled **experiment**;
- all source pins, required Lean declaration markers, local Markdown links,
  UTF-8 decoding, C0 hygiene, tabs, and trailing whitespace.

Both checker outputs explicitly set the asymptotic matching,
pi-periodic-defect, fixed-sixteen-return, and V1 flags to false. No formal file
was changed, so no new theorem required registration in
audit/AxiomAudit.lean and no formal verification gate was rerun for this
audit.

## Bottom line

The primary reduction is correct as a **proof sketch**: close-pair
anti-concentration can be replaced by the strictly weaker demand that every
fixed decimal period retain positive Cesaro defect, and ergodicity permits the
matching density to be lowered from one to any positive limit mass. The
positive-mass subprobability argument has no hidden orbit or marginal gap.
The actual matching and fixed-period noncollapse for pi remain unproved, so
canonical V1 remains a **conjecture**.
