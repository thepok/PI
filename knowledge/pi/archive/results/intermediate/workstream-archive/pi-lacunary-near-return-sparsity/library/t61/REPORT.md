# T61: kernel-checked direct-label adjacent phase variance

Claim label: **machine-checked** for the Lean theorems listed below. The
terminal research status remains open. This note does not claim a fixed-`pi`
estimate or a resolution of canonical A1.

## 1. Canonical statement and scope

The immutable statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with verified SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N >= 1`, it counts ordered pairs, including the diagonal,
whose base-ten `pi` orbit points are within `10^(-n)` on `R/Z`. Canonical A1
asks

```text
forall A >= 1, exists n0 >= 1, forall n >= n0, exists N >= 1,
  A*n*Q_pi(n,N) <= N^2.
```

`N` may depend on `A,n`. Infinitely many `n`, one fixed `A`, prescribed `N`,
unordered pairs, deleted diagonal pairs, and absolute rather than circle
distance are not substituted here. T61 proves none of A1, C1, C2, FSFS, T28,
or any unconditional statement about `pi`.

## 2. Checked inputs and unverified motivation

The Lean file imports exactly the following relevant checked interface:

| item | source SHA-256 | use |
|---|---|---|
| T26 | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | genuine adjacent chain coefficient |
| T55 | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | literal shells, coefficient recurrence, endpoint budget, signed Fejer identity |

The T58 note has SHA-256
`eae2a60b1112f6fa562e4e481cd0ce7d01d8ccb426b536f61a5fb7ee0391c913`.
It is an unverified proof sketch, not a premise. T57 is motivation only; no
claim from it is used.

## 3. Literal label domain

For T55 cutoff `R`, T61 retains

```text
source shell:   1 <= v <= (R-1)/10
terminal shell: (R-1)/10 < u <= R-1
block labels:   0 <= j < ell
signed cutoff:  -(R-1) <= frequency <= R-1
```

The Lean terminal range is literally
`Ioc ((R-1)/10) (R-1)`, and the block range is literally `range ell`.
Theorems `directAdjacentCorrelation_eq_labeled_sum` and
`directAdjacentVariance_eq_labeled_sum` expose both ranges. They are nested
sums, not sums over an image, so equal numerical frequencies retain their
label multiplicity. In particular, they preserve T55's checked collision
`10*(10^2-1) = 11*(10^2-10)` without identifying `(10,0)` and `(11,1)`.

## 4. Genuine adjacent T26 step

Set

```text
m(u,j) = u * (10^ell - 10^j),
beta0  = chain.nodeCoefficient k,
s      = incomingShift chain k.
```

T61 theorem `take_succ_eq_take_append_incomingShift` proves the required list
identity directly from T26's chain data. Then `nodeCoefficient_succ_exact`
derives

```text
chain.nodeCoefficient (k+1) = (10^s - 1) * beta0.
```

T61 theorem `phase_adjacent_pullback` proves, as an equality in `Complex`,

```text
e(((10^s-1)*beta0)*m)
  = e(beta0*(10^s*m)) * conj(e(beta0*m)).
```

`labeledPhase_adjacent_pullback` instantiates this at every literal `(u,j)`
label. Neither complex factor is replaced by its absolute value. Summing the
identity gives `directAdjacentCorrelation_eq_directTerminalCorrelation`.

## 5. Exact coefficient split

The direct terminal contribution uses T55's literal coefficient
`triangularWeight R u`. T61 defines

```text
predecessorRemainder
  = terminalCorrelation - directTerminalCorrelation.
```

This is not left as a tautological opaque remainder:
`predecessorRemainder_eq_labeled_sum` proves that it equals the complete
terminal-shell sum of T55's exported `predecessorCoefficient`, with every
`(u,j)` label retained. Thus the split genuinely removes the direct summand
from T55's checked recurrence

```text
orbitCoefficient = triangularWeight + predecessorCoefficient.
```

## 6. Explicit variance inequality

T61 defines, on the full literal terminal shell,

```text
V = sum_u sum_j w_R(u) *
      norm(e(beta0*(10^s*m(u,j))) - e(beta0*m(u,j)))^2,
A = sum_u sum_j w_R(u),
Bpred = norm(predecessorRemainder),
Bend = T55.endpointBudget,
Theta = ell / (4*R*delta^2).
```

The kernel-checked identity
`directAdjacentCorrelation_re_eq_mass_sub_half_variance` is exactly

```text
Re(directAdjacentCorrelation) = A - V/2.
```

The explicit formal predicate is named
`DirectLabelAdjacentPhaseVarianceWithExactRemainder` and states

```text
V < ell + 2*A - 2*Bpred - 2*Bend - Theta.
```

The endpoint remains T55's complete source-shell endpoint; `Bend` is not
dropped. The Fourier cutoff remains `R-1` in the conclusion.

## 7. Checked payoff

The theorem `directLabelAdjacentPhaseVariance_implies_fejer_threshold`
combines the exact direct variance identity, the exact predecessor split,
T55's endpoint bound, and T55's signed aggregation. It proves

```text
ell / (4*R*delta^2)
  < sum_{0 <= j < ell} fejerKernel (R-1)
      (beta*(10^ell-10^j)).
```

The chain-shaped theorem
`directLabelAdjacentPhaseVariance_implies_strict_t38_threshold` exposes
`q=k+1<d`, `1<=ell<commonDepth(chain,q)`,
`R=stratumOrder(chain,q,ell)`, and
`delta=stratumDelta(chain,q,ell)`. It proves only the strict analytic
threshold, not FSFS or a later conditional payoff.

## 8. Kernel-checked test

`directAdjacentVariance_eq_zero_of_nodeCoefficient_eq_zero` proves that the
full labeled variance is zero at a zero preceding coefficient.
`directTerminalMass_one_two` checks `A=1/2` at `ell=1,R=2`, while
`endpointBudget_one_two` checks that the source endpoint shell is empty.
Finally, `directLabelAdjacentPhaseVariance_one_two_test` checks the strict
constants at `ell=1`, `R=2`, `delta=1` from zero variance and zero exact
predecessor remainder. This is a formal interface test with explicit
premises, not a canonical-output or fixed-`pi` example.

## 9. Explicit weakening of T58

T58 equation (4.2) expands `orbitCoefficient` using the decimal valuation
`nu_10(u)` and then bounds all positive predecessor depths by a scalar `X`.
T61 does **not** claim that valuation-indexed formula as checked. Instead it
uses the norm of the exact, kernel-checked predecessor remainder. Consequently
the formal predicate is explicitly named `WithExactRemainder`; it is not
silently presented as T58's original DLAPV formula. Downstream formal work may
import the exact-remainder theorem, but it must not cite T58's valuation sum
as machine-checked from this artifact.

This replacement is not a renamed T55 `TopShellCorrelationHypothesis`: it
still controls the direct component by the positive square variance, while
the predecessor component is isolated separately. No synthetic phase is
introduced outside the genuine T26 adjacent interface.

## 10. Verification and remaining gap

The delivered Lean file recompiles directly with `lake env lean`. Every
printed theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, new axiom, `native_decide`, or unsafe
declaration.

The remaining named **Direct-Label Adjacent Phase-Covariance Gap** is to prove
an inequality of the displayed form for a legal adjacent node and stratum in
the positive-`r`, prescribed-`K` chains returned by T26's canonical-output
theorem. T26 controls only a nodewise exponential-sum magnitude and does not
currently control this multiharmonic labeled phase variance. T55 supplies the
exact finite decomposition but no such upper bound.

OPEN WITH ONE NAMED PHASE-COVARIANCE GAP
