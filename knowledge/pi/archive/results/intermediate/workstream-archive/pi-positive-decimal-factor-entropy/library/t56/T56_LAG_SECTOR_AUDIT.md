# T56: exact sparse lag sectors

Status: `machine-checked` for the Lean theorems listed in Section 10;
`experiment` for the replayed abstract instances; **INSUFFICIENT** as an
unconditional route to C7. No assertion of C7, C2, C1, or any new property of
the digits of pi is made.

## 1. Provenance and normalized task

The canonical question was formulated locally, so it has no original source
URL. The byte-exact statement is delivered as
`pi-positive-decimal-factor-entropy.txt`; its checked SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

That question asks whether one `eta>0` works in
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`. T56 does not answer
it. T56 audits the conditional C7 frontier isolated by kernel-checked T27.

For every integer `n>=1`, set

```text
L_n := 10^(n/2),
```

where `/` is natural-number division, hence the exponent is `floor(n/2)`.
Write `rho(x)` for circle distance to the nearest integer. The count under
audit is

```text
Q_pi(n,L_n)
 = |{(i,j): 0<=i,j<L_n,
       rho((10^j-10^i)*pi) < 10^(-n)}|.              (1.1)
```

The pairs are ordered, all `L_n` diagonal pairs are included, and the cutoff
is strict. The desired `O(L_n)` statement has the literal quantifiers

```text
exists A>0, exists N>=1, for every n>=N,
Q_pi(n,L_n) <= A*L_n.                                (1.2)
```

T27 machine-checks that (1.2) is equivalent to C7, and that (1.2) with
constant `A` implies the C7 energy bound with constant `17*A`. Conversely,
C7 with constant `C` implies (1.2) with constant `pi^2*C/4`. These are
implications between explicit hypotheses, not proofs of either hypothesis.

### Ambiguities fixed

1. `10^(n/2)` never means the real number `10^(n/2)` with real division.
2. Lag `r` is positive; `j` is the smaller index; the reverse orientation is
   restored by a factor two.
3. A kernel-checked conditional theorem certifies its implication only. It
   does not certify that its fixed-pi premise holds.
4. "Long" means `n<=r<L_n`; "short" means `0<r<n`.
5. The arithmetic-excluded/residual split partitions incidences at every lag,
   not merely the set of lag values.
6. The finite obstruction below is abstract. It is not a computed sample of
   pi and gives no evidence that pi realizes those incidences.

## 2. Exact diagonal-inclusive lag identity

For `n>=1`, the exact identity is

```text
Q_pi(n,L_n)
 = L_n
   + 2 * sum_(1<=r<=L_n-1)
       |{j: 0<=j<L_n-r,
          rho(10^j*(10^r-1)*pi) < 10^(-n)}|.         (2.1)
```

This includes every pair exactly once: the first term is the diagonal; an
ordered off-diagonal pair has a unique positive lag `r=|i-j|`, a unique
smaller index `j`, and one of two orientations. The factorization is exact:

```text
(10^(j+r)-10^j)*pi = 10^j*(10^r-1)*pi.              (2.2)
```

The inner range `j<L_n-r` is equivalent to `j+r<L_n`; the outer interval
`1<=r<=L_n-1` is equivalent to `0<r<L_n`. No endpoint is dropped.

Theorem `sparse_Q_exact_lag_decomposition` in `T56LagSectorAudit.lean`
machine-checks (2.1), importing the accepted generic decomposition rather
than duplicating it. The theorem
`sparse_repunit_eq_structuredDenominator_cast` identifies (2.2) with T25's
natural denominator `10^j*(10^r-1)`.

## 3. Exhaustive sectors

Fix real `mu,c` and natural `Q0`. T25 defines

```text
ArithmeticExcluded(mu,c,Q0,n,j,r)
 iff Q0 <= 10^j*(10^r-1)
 and 10^(-n) <= 10^j*(10^r-1)
                     * c/(10^j*(10^r-1))^mu.        (3.1)
```

Every near-return incidence in (2.1) satisfies exactly one of (3.1) and its
negation. T26 then splits the residual complement at `r=n`. Thus the complete
partition is

```text
Q_pi(n,L_n) = L_n + E_n + S_n + R_n,                (3.2)
```

where

```text
E_n = 2 sum_(1<=r<L_n)
        |{j<L_n-r: near return and ArithmeticExcluded}|,

S_n = 2 sum_(0<r<n, r<L_n)
        |{j<L_n-r: near return and not ArithmeticExcluded}|,

R_n = 2 sum_(0<r<L_n, n<=r)
        |{j<L_n-r: near return and not ArithmeticExcluded}|.  (3.3)
```

For `n>=1`, `L_n>=1`. The two residual lag conditions are disjoint and their
union is all `0<r<L_n`. Together with the excluded/residual dichotomy, (3.2)
covers every off-diagonal incidence.

Lean checks (3.2), both endpoint equivalences, and the disjoint split in:

```text
sparse_Q_exact_sector_partition
mem_sparse_short_sector_iff
mem_sparse_long_sector_iff
```

T25's `EffectiveIrrationality(pi,mu,c,Q0)` is the explicit premise

```text
c>0, mu>1, and for every q>=Q0 with q>0 and every integer p,
c/q^mu < |pi-p/q|.                                  (3.4)
```

Under (3.4), T25 proves `E_n=0`, so (3.2) becomes exactly

```text
Q_pi(n,L_n) = L_n + S_n + R_n.                      (3.5)
```

The theorem `sparse_Q_eq_diagonal_add_short_add_long` checks (3.5), retaining
(3.4) as a hypothesis.

## 4. Source theorem and constant audit

The following are kernel-checked theorem types. A proposition in the
"premise" column is not asserted for pi.

| Source theorem | Exact relevant type or constant | T56 use |
|---|---|---|
| T27 `C7_quantifiers_iff_Q_linear_quantifiers` | C7 iff (1.2), with natural `n/2` | Identifies the target; asserts neither side |
| T27 `piSparseMicroscopicQBound_implies_C7_explicit` | `Q<=A*L` gives energy `<=17*A*H*L` | Final conditional bridge |
| T1 lag decomposition `Q_pi_orderedPair_lag_decomposition` | Exact `L+2*sum_r card`, strict cutoff | Imported into (2.1) |
| T25 `Q_pi_eq_diagonal_add_excluded_add_residual` | Exact diagonal/excluded/residual identity | First incidence split |
| T25 `excludedPairCount_eq_zero` | (3.4) implies `E_n=0` | Conditional only |
| T26 `Q_pi_eq_diagonal_add_excluded_add_short_add_long` | Exact four-sector identity | (3.2) |
| T26 `shortResidualPairCount_le_two_mul` | `S_n<=2*L_n*n` | Unconditional retained short bound |
| Long-lag T2 `PiUniformLongLagResidualPairDecay` | `(3.4)` and, for every `0<s<1`, one `C_s>=1` for all positive `m,N`, with `R<=C_s*(N+N^2*10^(-s*m))` | Conditional long-sector interface |
| Long-lag T8 `longResidualPairCount_le_majorant` | `R<=pi^2/(2*10^m)*|D| + pi^2/10^m*sum_(h=1)^(10^m)|S_h|` | Exact spectral reduction, no fixed-pi bound |
| Long-lag T8 `longResidualPairCount_le_of_spectralEnergy` | Premise `Energy<=K*10^m*N^2`; conclusion constant `(pi^2+1)*(K+1)` multiplying `N+N^2*10^(-m)` | Conditional long bound |
| Long-lag T12 `longResidualPairCount_le_of_scaleMatchedL1` | L1 premise with constant `B`; conclusion constant `pi^2*(1+B)` multiplying `N+N^2*10^(-s*m)` | Conditional long bound |
| Long-lag T12 `longResidualPairCount_le_of_scaleMatchedEnergy` | Energy premise with constant `A`; conclusion constant `pi^2*(1+sqrt(A))` | Conditional long bound |
| Long-lag T32 `inherited_longDifferenceWeightedGCD_le` | Unconditional `<=574913232*N^4` | Arithmetic/GCD type, not a fixed-pi incidence bound |
| Long-lag T32 `fixedPi_partialRange` | Constant one, but requires `((N-m)(N-m+1))^2<=N` | Inapplicable at `m=n,N=L_n` eventually |

The adjacent program's canonical `R_pi(m,N)` has a different type: it counts
exactly equal length-`m` decimal blocks only at lags `r>=m`. It is not
`Q_pi`. T1 checks

```text
piCylinderCollisionEnergy(m,N)
 <= R_pi(m,N) + N + 2*N*m,                           (4.1)
```

while the accepted cylinder comparison is

```text
piCylinderCollisionEnergy(m,N) <= Q_pi(m,N)
 <= 3*piCylinderCollisionEnergy(m,N).                (4.2)
```

Consequently even a conjectural bound
`R_pi<=C_s*(N+N^2*10^(-s*m))` leaves the same `N*m` loss. Exact-block decay
cannot silently be substituted for complete strict near-return decay.

### Pinned internal sources

```text
e4e7b2dd5d080616edee252e05c50c3cc9f56ddc7cd0420b71c3acaca2710c65  T27T27SparseMicroscopicEquivalence.lean
932faf3f1515b5073e07ba81f70aae3cdea9d168bb7ea280bd57e2300e643a68  T1LagDecomposition.lean
86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c  T25T25ResidualPairReduction.lean
744731fcaa2e252a8f63b0a0bbaf09ea86bdc72f379616437cc5b570f282e6b0  T26T26LongLagResidualReduction.lean
64ff2687e84edc22a843da65a54b3f801713455ff54df457f508cc5ef14a20b0  T1T1LongLagBlockCollisionDecay.lean
ffe231e2750445a8f2c0a342cb60e1259a2427e5bb0f8067bf1350ab62bdeba3  T2T2UniformLongLagResidual.lean
f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9  T8T8SpectralLongLagReduction.lean
a4108ff862c13ee0f9fa3fc877723856eb34497430cde36d85f7943ce0347bcf  T12T12ScaleMatchedSpectralFrontier.lean
3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc  T32T32AllBlockFixedPiRange.lean
```

## 5. What the long-sector interface yields at the sparse scale

Grant (only for this calculation) T2's uniform long-residual premise, which
includes (3.4). Choose `s=3/4` and let its constant be `C`. Put
`k=floor(n/2)`, so `L_n=10^k`. Since

```text
k <= n/2 <= 3*n/4,
```

monotonicity of real powers of ten gives

```text
L_n^2*10^(-3*n/4)
 = 10^(2*k-3*n/4)
 <= 10^k
 = L_n.                                              (5.1)
```

Thus the long interface gives the useful bound

```text
R_n <= 2*C*L_n.                                      (5.2)
```

The unconditional T26 estimate is only

```text
S_n <= 2*L_n*n.                                      (5.3)
```

Combining (3.5), (5.2), and (5.3) yields exactly

```text
Q_pi(n,L_n) <= (1 + 2*C + 2*n)*L_n.                 (5.4)
```

This is `O(n*L_n)`, not (1.2). The kernel-checked theorem
`sparse_Q_le_retained_sector_budget` keeps the corresponding finite bound
`L_n+2*L_n*n+B` explicit for an arbitrary supplied long budget `B`.

T8 and T12 change the constant in (5.2), not the `2*n` in (5.4). T32's
partial-range theorem does not repair this: its required
`((L_n-n)(L_n-n+1))^2<=L_n` fails once `L_n` is much larger than `n`.

## 6. Precise residual estimate

The verdict is therefore **INSUFFICIENT**. The exact missing estimate is the
following weighted short-repunit incidence statement, for fixed parameters
`mu,c,Q0` satisfying the separately stated arithmetic premise (3.4):

```text
exists A>0, exists N>=1, for every n>=N,

2 * sum_(0<r<n, r<L_n)
      |{j: 0<=j<L_n-r,
         rho(10^j*(10^r-1)*pi) < 10^(-n),
         not ArithmeticExcluded(mu,c,Q0,n,j,r)}|
  <= A*L_n.                                          (6.1)
```

The triangular capacities `L_n-r` are the weights implicit in this incidence
sum: if `a_(n,r)` denotes the fraction of available starts retained at lag
`r`, then its left side is

```text
2 * sum_(0<r<n) (L_n-r)*a_(n,r).                    (6.2)
```

Thus (6.1) requires cancellation/sparsity after summing all short lags; a
separate `O(L_n)` allowance at each lag would still lose a factor `n`.

Lean names (6.1) `SparseShortRepunitIncidenceBound`. The theorem
`sparse_sector_linear_bounds_imply_QBound` checks that (3.4), (6.1), and an
eventual `R_n<=B*L_n` estimate imply (1.2) with explicit constant `1+A+B`.
The theorem `sparse_sector_linear_bounds_imply_C7` then invokes T27 to obtain
C7 conditionally. None of those three premises is asserted here.

## 7. Replay-checkable abstract obstruction

The retained inequalities alone cannot prove (1.2). For arbitrary integers
`n>=2` and `L>=2n`, define a finite abstract family as follows:

```text
diagonal sector:       L incidences;
excluded sector:       0 incidences;
long residual sector:  0 incidences;
short lag r=1,...,n-1: starts j=0,...,L-n-1,
                       with both orientations.       (7.1)
```

Every listed start is endpoint-valid because `j<L-n<=L-r`. Its ordered short
count and total are

```text
S_abs(n,L) = 2*(n-1)*(L-n),
Q_abs(n,L) = L + 2*(n-1)*(L-n).                     (7.2)
```

It obeys the retained short estimate:

```text
S_abs(n,L) <= 2*n*L.                                (7.3)
```

At `L=2n`, (7.2) is exactly

```text
Q_abs(n,2n) = n*(2n).                               (7.4)
```

Therefore for every proposed natural constant `C`, taking `n=C+1` gives a
finite family satisfying all retained budgets but
`Q_abs(n,2n)>C*(2n)`. Lean checks (7.3), (7.4), and this quantified finite
obstruction in

```text
abstractShortIncidenceCount_le_retained_budget
abstractTotalIncidenceCount_two_mul
exists_abstract_obstruction_above_constant.
```

For a proposed real constant, choose a strictly larger natural `C` and use
`L>0`; the same family then exceeds the real constant as well. Lean checks
this Archimedean step in
`exists_abstract_obstruction_above_real_constant`.

The replay script also instantiates (7.1) at the actual target lengths
`L_n=10^(floor(n/2))` for `2<=n<=12`. It checks all triangular endpoints,
(7.2), (7.3), and `Q_abs>=n*L_n`. It separately gives explicit failures for
proposed constants `1,...,10`. This is an `experiment` on abstract finite
families, not evidence about pi.

Replay from a directory containing only the delivered artifacts:

```sh
python3 t56_obstruction.py --write replay.json
cmp replay.json obstruction_results.json
```

## 8. Verdict

**INSUFFICIENT.** The accepted identities give complete sector coverage. The
accepted long-lag interfaces, when their explicit premises are granted, can
make `R_n=O(L_n)` at the target scale. The retained unconditional short bound
is only `S_n<=2nL_n`, and the abstract family proves that this bound cannot be
summed to a uniform multiple of `L_n` by combinatorics alone. Estimate (6.1)
is the exact additional all-short-sector statement needed by this route.

This verdict does not say (6.1), C7, C2, or C1 is false. It says only that the
audited accepted interfaces do not establish them.

## 9. Verification commands

The Lean file contains no `sorry`, `admit`, `native_decide`, new axiom, or
unsafe declaration. From the project root:

```sh
lake env lean removed-workflow-record://todo-theory-pi-positive-decimal-factor-entropy-t56-1785649271-r0/theory_artifacts/T56LagSectorAudit.lean
```

The printed axiom sets are subsets of `propext`, `Classical.choice`, and
`Quot.sound`.

From the artifact directory:

```sh
sh ./verify.sh
```

## 10. Machine-checked theorem map

The public declarations intended for reuse are:

```text
DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_exact_lag_decomposition
DecimalFactorComplexity.T56LagSectorAudit.sparse_repunit_eq_structuredDenominator_cast
DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_exact_sector_partition
DecimalFactorComplexity.T56LagSectorAudit.mem_sparse_short_sector_iff
DecimalFactorComplexity.T56LagSectorAudit.mem_sparse_long_sector_iff
DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_eq_diagonal_add_short_add_long
DecimalFactorComplexity.T56LagSectorAudit.sparse_short_sector_le_two_mul_length_mul_n
DecimalFactorComplexity.T56LagSectorAudit.sparse_Q_le_retained_sector_budget
DecimalFactorComplexity.T56LagSectorAudit.sparseShortRepunitIncidenceBound_iff_quantifiers
DecimalFactorComplexity.T56LagSectorAudit.sparse_sector_linear_bounds_imply_QBound
DecimalFactorComplexity.T56LagSectorAudit.sparse_sector_linear_bounds_imply_C7
DecimalFactorComplexity.T56LagSectorAudit.abstractShortIncidenceCount_le_retained_budget
DecimalFactorComplexity.T56LagSectorAudit.abstractTotalIncidenceCount_two_mul
DecimalFactorComplexity.T56LagSectorAudit.exists_abstract_obstruction_above_constant
DecimalFactorComplexity.T56LagSectorAudit.exists_abstract_obstruction_above_real_constant
```
