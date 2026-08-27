# T83: literal T56/C7 statistic and conflicting short-sector audit

Claim label: **machine-checked** for the declarations listed in Section 8.
Review B's separator remains a precisely scoped **conjecture** for the reasons
in Section 7. No fixed-pi estimate is asserted.

## 1. Provenance and immutable canonical scope

The vendored `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

and is byte-identical to
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its canonical count is

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\]

Pairs are ordered, the diagonal is included, and the cutoff is strict. The
canonical open question has quantifiers

\[
 \forall A\in\mathbb N_{\ge1}\ \exists n_0\ge1\ \forall n\ge n_0\
 \exists N\ge1:\quad AnQ_\pi(n,N)\le N^2.                 \tag{1.1}
\]

Thus `N` may depend on `A,n`. Infinitely many `n`, one fixed `A`, every `N`,
unordered pairs, removed diagonals, exact block equality, and non-strict
cutoffs are not silently substituted here.

The vendored feedback has SHA-256

```text
78f63c13803e4860b513fae245d1ec5e77e8decd233ec287f2acd1da5516bd20
```

and labels all its contents `conjecture and audit input only`. In particular,
its Review A and Review B claims are not premises in the Lean file.

## 2. Program qualification: which T56 and which C7

The relevant T56 is not the pi-lacunary-near-return-sparsity program's T56
note. It is the module

```text
TheoryLib/PiPositiveDecimalFactorEntropy/T56T56LagSectorAudit.lean
namespace DecimalFactorComplexity.T56LagSectorAudit
SHA-256 41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc
```

Its C7 comes from

```text
TheoryLib/PiPositiveDecimalFactorEntropy/T26T26SparseLongBandFejer.lean
namespace DecimalFactorComplexity.SparseLongBandFejer
SHA-256 8f61cdce1f5cab84c58777274f019c124c872e42180c7a13123900883fe710f0
```

and its checked equivalence is in

```text
TheoryLib/PiPositiveDecimalFactorEntropy/T27T27SparseMicroscopicEquivalence.lean
namespace DecimalFactorComplexity.SparseMicroscopicEquivalence
SHA-256 e4e7b2dd5d080616edee252e05c50c3cc9f56ddc7cd0420b71c3acaca2710c65
```

Set, with natural-number division,

\[
 L_n=10^{\lfloor n/2\rfloor},\qquad H_n=\lfloor10^n/2\rfloor. \tag{2.1}
\]

For `n>=1`, the checked identity is `2*H_n=10^n`. Define the complete
triangular Fejer energy

\[
 \mathcal F_\pi(L,H)=
 \sum_{\substack{h\in\mathbb Z\\ |h|<H}}
 \left(1-\frac{|h|}{H}\right)
 \left|\sum_{j=0}^{L-1}e^{2\pi i h\{10^j\pi\}}\right|^2.   \tag{2.2}
\]

The range is strict, includes `h=0`, and contains every signed integer with
`|h|<H`. This is exactly `completePiFejerEnergy L H`; see
`completePiFejerEnergy_eq_complete_band` and
`mem_completePiFejerEnergy_frequencies_iff` in T26.

The literal C7 predicate is

\[
 \boxed{\exists C>0\ \exists N\ge1\ \forall n\ge N:\quad
 \mathcal F_\pi(L_n,H_n)\le C H_nL_n.}                    \tag{2.3}
\]

The constant precedes the cutoff and every later `n`. The theorem
`literal_C7_iff_quantifiers` replays (2.3) in the delivered Lean file.

## 3. C7's literal finite statistic

T27 machine-checks

\[
 \boxed{\mathrm{C7}\iff
 \exists A>0\ \exists N\ge1\ \forall n\ge N:\quad
 Q_\pi(n,L_n)\le A L_n.}                                  \tag{3.1}
\]

This is `literal_C7_iff_nearReturn_linear` in the delivered file and
`piSparseLongBandC7_iff_Q_linear_quantifiers` in T27. The two checked
directions retain explicit constants: C7 gives `pi^2*C/4`, and a `Q_pi`
constant `A` gives energy constant `17*A`.

Crucially, `Q_pi` is an ordered, diagonal-inclusive, strict circular
near-return count. Exact equality of length-`n` decimal blocks implies a
`Q_pi` incidence, but no converse is declared: the near-return predicate also
allows neighboring-cylinder and carry-boundary configurations in its generic
interface. Therefore the feedback's exact-equality claims cannot be
substituted into (3.1).

## 4. Exact T56 lag and sector ranges

For `n>=1`, T56's `sparse_Q_exact_lag_decomposition` is

\[
 Q_\pi(n,L_n)=L_n+2\sum_{r=1}^{L_n-1}
 \#\left\{0\le j<L_n-r:
 \|10^j(10^r-1)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\right\}. \tag{4.1}
\]

The factor two restores the reverse orientation. The `L_n` term is exactly
the diagonal. With parameters `mu,c,Q0`, T56 then partitions (4.1) as

\[
 Q_\pi(n,L_n)=L_n+X_n+S_n+T_n,                            \tag{4.2}
\]

where `X_n` is the arithmetic-excluded sector and `S_n,T_n` are residual
short and long counts. The exact short range is

\[
 0<r<n\quad\hbox{and}\quad r<L_n,                         \tag{4.3}
\]

and each lag still has the triangular start range `0<=j<L_n-r`. The exact
long range is

\[
 0<r,\qquad n\le r<L_n.                                   \tag{4.4}
\]

These are `literal_short_sector_range`,
`T56LagSectorAudit.mem_sparse_long_sector_iff`, and their source definitions
`shortResidualLags` and `longResidualLags`. Residual starts satisfy the strict
near-return in (4.1) and fail the explicit `ArithmeticExcluded` predicate.

Under the still-explicit premise

```text
EffectiveIrrationality Real.pi mu c Q0
```

T56 checks `X_n=0`, so (4.2) becomes `Q_pi=L_n+S_n+T_n`.
Unconditionally,

\[
 \boxed{S_n\le2L_nn.}                                      \tag{4.5}
\]

This is `literal_short_sector_coarse_bound`. It is `O(nL_n)`, not `O(L_n)`.
T56's machine-checked abstract obstruction shows that (4.5) alone cannot be
absorbed into a uniform linear C7 bound.

## 5. Machine-checked one-scale ENT implication

The delivered definition `SparseScaleSubexponential a` gives `L_n10^{o(n)}`
the explicit all-rates meaning

\[
 \forall\varepsilon>0\ \exists N\ge1\ \forall n\ge N:
 \quad a_n\le L_n10^{\varepsilon n}.                       \tag{5.1}
\]

The proof is the following numbered argument.

1. Specialize (5.1) to `epsilon=1/16`.
2. The theorem `eventually_one_add_two_mul_le_ten_rpow_sixteenth` checks
   `1+2n<=10^(n/16)` eventually.
3. If a collision or near-return statistic obeys
   \[
   E_n\le a_n+L_n+2L_nn,
   \]
   then eventually
   \[
   E_n\le2L_n10^{n/16}\le L_n10^{n/8}.                    \tag{5.2}
   \]
4. For `n>=2`, `n/4<=floor(n/2)`, hence
   \[
   L_n10^{n/8}\le L_n^2 10^{-n/8}.                        \tag{5.3}
   \]
5. Combining (5.2)-(5.3) gives the checked reusable theorem
   `sparse_subexponential_budget_implies_exponential_decay`.
6. T2's finite Cauchy-Schwarz theorem then gives
   \[
   10^{n/8}\le p_\pi(n)                                   \tag{5.4}
   \]
   at every sufficiently late `n`.

There are two separately checked applications.

### Exact equality

Let `R_pi(n,L_n)` be T1's ordered exact equal-block count at lags at least
`n`. Its exact source is

```text
TheoryLib/PiLongLagBlockCollisionDecay/T1T1LongLagBlockCollisionDecay.lean
SHA-256 64ff2687e84edc22a843da65a54b3f801713455ff54df457f508cc5ef14a20b0
```

T1 checks

\[
 E_\pi(n,L_n)\le R_\pi(n,L_n)+L_n+2L_nn.                  \tag{5.5}
\]

Thus `exactLongSectorSubexponential_implies_C1` proves the feedback's claimed
one-scale implication under the literal all-rates interpretation (5.1), with
the explicit entropy exponent `1/8`.

### Literal T56 near returns

For T56, let `a_n=T_n`, the residual long near-return sector in (4.4).
Then `residualLongSectorSubexponential_implies_C1` proves the analogous
implication from (5.1), but only with both explicit premises:

```text
EffectiveIrrationality Real.pi mu c Q0
ResidualLongSectorSubexponential mu c Q0
```

The proof passes through `PiExponentialNearReturnC2`, not through C7.
Subexponential `L_n10^{o(n)}` control and the retained `2nL_n` short budget do
not supply the uniform `O(L_n)` estimate required by C7.

## 6. Review A verdict

Feedback wording: arbitrary infinite words can realize order `nL_n` exact
short-sector equal-block collisions by inserting dominant constant runs, and
this does not obstruct positive entropy under the long-sector bound.

### Precise existential core: machine-checked

The delivered `exactShortPairCount x n L` counts both orientations of exact
equal length-`n` factors at lags `0<r<n`, omitting the diagonal. For the legal
infinite decimal stream

```text
constantDecimalStream k = 0
```

the exact count is

\[
 S^{\rm const}_{n,L}=2\sum_{\substack{1\le r\le L-1\\r<n}}(L-r). \tag{6.1}
\]

`exactShortPairCount_constantDecimalStream` checks (6.1). If `2n<=L`, the
selected core satisfies

\[
 S^{\rm const}_{n,L}\ge2(n-1)(L-n)\ge(n-1)L.               \tag{6.2}
\]

Theorems `abstractShortIncidenceCount_le_constantRunExactShortPairCount` and
`constantRun_short_pairs_ge_pred_mul_length` check (6.2). Finally,
`eventually_two_mul_le_sampleLength` checks `2n<=L_n` eventually, and
`constantDecimalStream_sparse_short_pairs_order_nL` gives

\[
 \exists N\ge1\ \forall n\ge N:\quad
 S^{\rm const}_{n,L_n}\ge(n-1)L_n.                         \tag{6.3}
\]

This proves Review A's existential constant-run mechanism. It does not prove
the stronger, undefined phrase "arbitrary infinite words can realize" if that
was intended universally or intended to preserve a preassigned word's
language or entropy after insertion.

### Compatibility with the long-sector implication: machine-checked

The `O(nL_n)` term is exponentially negligible in Section 5. Therefore large
short counts of the size (6.3) do not invalidate the conditional implication
from an independently supplied `R_pi(n,L_n)<=L_n10^{o(n)}` premise to positive
entropy. This is a logical compatibility statement, not an assertion that the
constant stream satisfies that long-sector premise; it does not.

### Transfer to T56: statistic mismatch, no implication audited

Exact equal blocks map into T56's carry-thickened strict near-return relation,
but no reverse comparison identifies their short counts. Consequently (6.1)
is not T56's `S_n`, and Review A's construction cannot be used as an identity
or bound for the literal T56 sector without a separate transfer. That transfer
is precisely scoped unresolved. The delivered near-return theorem instead
uses T56's own checked bound (4.5).

## 7. Review B verdict

Feedback wording:

\[
 S_{n,L}\le C_bL+\frac32R_{n,L},\qquad
 L=b^{\lfloor n/2\rfloor}.                                \tag{7.1}
\]

**Verdict: precisely scoped conjecture, unresolved.** The supplied text does
not define whether `S` includes the diagonal, whether it counts one or both
orientations, whether `R` uses `>=n` or `>n`, whether the finite word supplies
`L` starts or has total length `L`, or the quantifier order and permitted
dependence of `C_b`. The natural normalization compatible with T1 would set

\[
 S_{n,L}=2\,\texttt{shortLagCollisionSum}(n,L),\qquad
 R_{n,L}=\texttt{R_pi}(n,L),                               \tag{7.2}
\]

for pi, and would replace `B_pi` by generic block labels for an arbitrary
word. To avoid fractions, the proposed universal inequality would read

\[
 2S_{n,L}\le2C_bL+3R_{n,L}.                               \tag{7.3}
\]

No inspected declaration proves (7.3). In particular, T56 proves only (4.5),
T69 bounds a neighboring-cylinder five-case statistic by a global equality
load, and neither supplies Review B's periodic-word enumeration or coefficient
`3/2`. No exact counterexample to the fully quantified natural reading (7.3)
was found in this audit. The claim therefore remains unresolved rather than
being promoted from the feedback.

Review B also does not transfer to literal T56: replacing exact equality by
the strict near-return relation adds neighboring-cylinder/carry incidences
that (7.1) does not count.

The apparent conflict is therefore resolved only at the current logical
scope: Review A's existential `Theta(nL_n)` mechanism is machine-checked and
is compatible with a separate subexponential long-sector hypothesis; Review
B's proposed universal charging inequality is a stronger, underspecified
conjecture and is neither proved nor refuted here.

## 8. Declaration index and verification

All new declarations are in the fresh namespace
`DecimalFactorComplexity.T83LiteralStatisticAudit` in
`T83LiteralStatisticAudit.lean`.

| Declaration | Status | Content |
|---|---|---|
| `literal_C7_iff_quantifiers` | machine-checked | Exact C7 quantifiers and `C H_n L_n` normalization |
| `literal_C7_iff_nearReturn_linear` | machine-checked | C7 iff eventual `Q_pi(n,L_n)<=A L_n` |
| `literal_short_sector_range` | machine-checked | `0<r<n` and `r<L_n` |
| `literal_short_sector_coarse_bound` | machine-checked | Residual short count `<=2L_n n` |
| `sparse_subexponential_budget_implies_exponential_decay` | machine-checked | `L_n10^{o(n)}` plus diagonal/short budget gives exponent `1/8` |
| `exactLongSectorSubexponential_implies_C1` | machine-checked | Feedback's exact-equality one-scale ENT implication |
| `residualLongSectorSubexponential_implies_C1` | machine-checked | Literal T56 analogue with explicit arithmetic and long premises |
| `exactShortPairCount_constantDecimalStream` | machine-checked | Constant stream realizes the exact numerical short count |
| `constantDecimalStream_sparse_short_pairs_order_nL` | machine-checked | Eventual `(n-1)L_n` exact short-pair lower bound |

Compilation command from the repository root:

```sh
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t83-1786283389-r0/theory_artifacts/T83LiteralStatisticAudit.lean
```

The printed axiom dependencies are exactly `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorry`, `admit`, `native_decide`, new axiom,
unsafe declaration, or compiler-trusting shortcut.

## 9. Final scope

The audit proves conditional implications. It does not establish
`ExactLongSectorSubexponential`, `ResidualLongSectorSubexponential`, the
effective-irrationality premise used by literal T56, C7, C2, canonical (1.1),
positive entropy for pi, normality, equidistribution, or any fixed-pi
cancellation estimate.

**No fixed-pi conclusion follows merely from this audit.**
