# T5 applicability matrix for C1 and T2

Audit date: 2026-07-24 UTC

## Verdict scope

Each verdict asks one question only: does the quoted theorem, with its stated
hypotheses, imply T2's residual predicate at `a_n=10^n`, `alpha=pi`, radius
`10^(-m)`, with one constant selected before all positive `m,N`?

- `APPLIES`: yes, with every hypothesis discharged.
- `CONDITIONAL`: yes after one explicitly named extra premise, and the resulting
  constant dependence is displayed.
- `DOES NOT APPLY`: no; even granting an illegal fixed-point specialization or
  the theorem's probabilistic hypotheses leaves a quantifier, rate, scale,
  model, or alignment gap.

No retained literature row is `APPLIES` or `CONDITIONAL` under this definition.
That is a substantive negative applicability result, not evidence against C1.

## Exact comparator

The retained, machine-checked T2 source is
`T2UniformLongLagResidual.lean`, SHA-256
`ffe231e2750445a8f2c0a342cb60e1259a2427e5bb0f8067bf1350ab62bdeba3`.
Its exact locator is lines 27-37 for the predicate and lines 152-166 for the
implication theorem. The theorem is
`Theory.PiDigits.LongLagBlockCollisionDecay.T2.piUniformLongLagResidualPairDecay_implies_C1`.

For fixed effective-irrationality parameters `(mu,c,Q0)`, T2 requires

```text
EffectiveIrrationality(pi,mu,c,Q0)
and
for every real s with 0<s<1,
  there exists C_s>=1, chosen here,
  such that for every positive integer m and N,
    longResidualPairCount(mu,c,Q0,m,N)
      <= C_s [N + N^2 10^(-s m)].
```

The count is ordered and equals

```text
2 sum over integers r with m<=r<N of
  #{n : 0<=n<N-r,
        ||10^n(10^r-1)pi||_(R/Z) < 10^(-m),
        and ArithmeticExcluded(mu,c,Q0,m,n,r) is false}.
```

The factor `2` restores both orientations; no diagonal or lag below `m` is
present. T2 chooses the same `C_s` before `m,N` in C1. Thus the only positive
implication used in this report has the displayed order
`forall s, exists C_s, forall m,N`; it does not assert the premise.

This audit does not repeat or discharge T4's irrationality-measure source
premise. T4 isolates a separate conditional route to the
`EffectiveIrrationality` conjunct. Within T5's literature scope, the narrowest
unmet fixed-pi hypothesis is exactly the aggregate `longResidualPairCount`
inequality above.

## Matrix

| ID | Family and quoted result | Verdict | Point | Scale and averaging | Rate and constant | Pair convention | Boundary/alignment | Narrowest obstruction |
|---|---|---|---|---|---|---|---|---|
| M1 | Bailey--Crandall S1, Hypothesis A -> pi normal to base 2 | **DOES NOT APPLY** | Fixed `pi`, but only conditional on unproved Hypothesis A | Normality gives limiting frequencies for each fixed binary block length; it does not concern decimal `10^n` or radius `10^(-m)` | For fixed binary `m`, normality implies total ordered equal-block pairs `N^2/2^m+o_m(N^2)`; it gives no nonasymptotic rate uniform in `m`, and no `C_s` | It does yield a fixed-`m` two-point collision asymptotic after summing squared block frequencies; deleting lags below `m` changes only `O(mN)` pairs | Binary cylinders do not align with decimal cylinders; even hypothetical decimal normality would still lack the all-`m,N` rate | Decimal, all-scale, nonasymptotic two-point rate, not merely fixed-block normality |
| M2 | Philipp S2, Theorem 1, discrepancy LIL for lacunary integers | **DOES NOT APPLY** | Lebesgue-a.e. initial `x`; countable pullback gives all `x_r={(10^r-1)alpha}` for a.e. `alpha`, but not for `alpha=pi` | At `n_k=10^k`, controls interval discrepancy along each one-point orbit only as `N->infinity`; applying it lagwise requires all `x_r` | The displayed limsup bound is `C(q)<=166+664/(sqrt(q)-1)`, hence deterministic at `q=10`; an eventual bound has a point-dependent onset, and there is no common onset across all fixed-pi `x_r` | No aggregate pair count; applying the one-point estimate separately and summing over lags accumulates its discrepancy errors | The wrapped target is two intervals; source indices `k=1,...,L` instead of T2's `n=0,...,L-1`, changing at most one hit per lag, an aggregate `O(N)` boundary term | Fixed-pi control at every `x_r`, with cumulative discrepancy error `O(N)` |
| M3 | Fukuyama S3, exact discrepancy LIL for `{theta^k x}` | **DOES NOT APPLY** | Lebesgue-a.e. initial `x`; countable pullback gives every transformed point for a.e. `alpha`, not for fixed `pi` | `theta=10` is literal and interval discrepancy handles both components of radius `10^(-m)`, but only asymptotically for each orbit length | Exact limsup constant depends on `theta`; there is no common finite onset across the fixed-pi `x_r`, and the error remains order `sqrt(N log log N)` | One-point discrepancy applied lag by lag, not an ordered aggregate over all lags | The circle ball is two intervals; the `k=1,...,L` versus `n=0,...,L-1` shift costs at most one hit per lag; equal decimal block -> near-return is only one-way | Same fixed-pi, cumulative-discrepancy bound as M2 |
| M4 | Rudnick--Zaharescu S4, Corollary 3, Poisson pair correlation of `{alpha 10^n}` | **DOES NOT APPLY** | Lebesgue-a.e. `alpha`; cannot specialize to `alpha=pi` (or to `pi/10` for exact zero-based alignment) | Pair distance is literal, but the theorem has radius `sigma/N` for each fixed `sigma`; T2 needs `sigma=N10^(-m)` moving uniformly with `m,N` | Limit only, with no nonasymptotic rate or one global finite-sample constant | Source counts ordered `1<=j!=k<=N`; T2 uses exponents `0,...,N-1` and then restricts lag/residual classes | Shifting `1..N` to `0..N-1` replaces one point and can change the ordered count by at most `2(N-1)`, absorbable by T2's `N` term if a uniform bound existed; circle distance itself has no decimal-boundary loss | Fixed-pi, moving-scale, nonasymptotic pair-correlation bound |
| M5 | Chernov--Kleinbock S5, Theorem 1.7, shrinking intervals for `T(x)=10x mod 1` | **DOES NOT APPLY** | For a.e. initial `x`; T2 needs every `x_r={(10^r-1)pi}` | For fixed lag `r`, `T^n x_r` is literal; the strict circle ball is `[0,rho) union (1-rho,1)` for `rho=10^(-m)`, so Theorem 1.7 must be applied to both interval sequences | Each component has the asymptotic error `O(E_N^(1/2) log^(3/2+eps)E_N)`; the theorem states no uniformity across `r,m`, and summing such errors over `r` is too large | Two one-interval start-counts for one lag; no ordered aggregate over all `m<=r<N` | Splitting gives main term `2(N-r)10^(-m)`; source times `1,...,N-r` versus T2 times `0,...,N-r-1` cost at most one union-hit per lag; residual filtering only decreases counts | Uniform fixed-pi control simultaneously in `r,m,N`, with summable-over-lags error |
| M6 | Chernov--Kleinbock S5, Theorem 2.1, strongly Borel-Cantelli cylinders | **DOES NOT APPLY** | Random/Gibbs-a.e. symbolic orbit, not the decimal stream of `pi` | Prescribed D-nested cylinders and divergent total measure; a self-generated collision target is not prescribed independently of the orbit | Asymptotic hit count with square-root-type error; no all-scale collision rate | Counts visits to one target sequence, not all ordered pairs of equal blocks | Symbolic cylinders avoid circle-boundary loss, but the theorem does not treat the moving cylinder determined by the compared block | A fixed-stream, self-collision energy theorem with a uniform finite-sample rate |
| M7 | Rousseau S6, Theorem 1, longest common substring/Renyi entropy | **DOES NOT APPLY** | Almost every pair of independent random sequences; not one fixed pi stream | Controls only the maximal matching length as sample length tends to infinity | Logarithmic asymptotic, no bound on the number of matches and no `C_s` | Two independent strings and an existential maximum; T2 is one-string ordered pair count with long-lag exclusion | Exact symbolic equality has no decimal boundary loss, but independence and decimal source law are absent | A fixed-pi quantitative bound on total collision energy, not an extremal random-match law |

## Literal reductions and failures

### Pair-correlation specialization

Rudnick--Zaharescu's pair condition with `g=10` is

```text
||(10^i-10^j) alpha|| <= sigma/N.
```

Substituting `alpha=pi` and `sigma=N*10^(-m)` produces exactly radius
`10^(-m)` for the source's points with exponents `1,...,N`. T2 instead uses
exponents `0,...,N-1`. The two `N`-point sets share `N-1` points, and replacing
the remaining point changes an ordered off-diagonal count by at most
`2(N-1)`. Equivalently, using source parameter `alpha=pi/10` gives exact
zero-based alignment. Neither form is a valid specialization of the metric
corollary. Its decisive gaps are:

1. Neither `pi` nor `pi/10` is known to lie in the full-measure set.
2. Their limit is for each fixed `sigma`; here `sigma` varies with both `m,N`.

Even a fixed-pi Poisson limit at every fixed `sigma` would provide neither a
uniform rate nor one constant for all finite `m,N`.

### Shrinking-target specialization

For a positive lag `r`, put

```text
x_r = {(10^r-1)pi},  T(x)={10x}.
```

Then for every start `n`,

```text
T^n x_r = {10^n(10^r-1)pi},
```

so hitting the circle interval of radius `10^(-m)` about zero is exactly the
unfiltered T2 near-return condition. More literally, because
`rho=10^(-m)<1/2`, the strict circle ball is

```text
[0,rho) union (1-rho,1).
```

Thus Theorem 1.7 must be applied once to each component interval sequence and
the two hit counts added; the expected main term is `2(N-r)rho`, not
`(N-r)rho`. Chernov--Kleinbock applies only for almost every initial `x`, not
the prescribed countable family of fixed-pi points `x_r`, and states no
uniformity in `r,m`. Residual starts form a subset of full near-return starts,
so there is no loss in that direction; the missing input is fixed-pi
uniformity. Its sum uses times `1,...,N-r`, while T2 uses `0,...,N-r-1`;
replacing one time changes the union-hit count by at most one for each lag and
hence contributes only `O(N)` after summing lags.

### What discrepancy would have to prove

For either discrepancy theorem, multiplication by the nonzero integer
`10^r-1` preserves null sets modulo one. Pulling back the theorem's exceptional
set for each `r` and taking a countable intersection therefore gives the
one-orbit LIL at every `x_r={(10^r-1)alpha}` for almost every `alpha`. This
observation does not include the prescribed `alpha=pi`, gives no common finite
onset across `r`, and does not repair the accumulated error rate.

Suppose a fixed-pi theorem supplied, simultaneously for every transformed
initial point `x_r` with `m<=r<N`,

```text
#{0<=n<N-r : ||10^n(10^r-1)pi|| < 10^(-m)}
  <= 2(N-r)10^(-m) + E(N-r)
```

with one deterministic error function. Summing and restoring orientations
would give

```text
longResidualPairCount
  <= 2*10^(-m)*N^2 + 2*sum_(L=1)^N E(L).
```

To imply T2 for every `0<s<1`, it would suffice that, for each `s`, one
`K_s` chosen before `m,N` satisfy

```text
2*10^(-m)*N^2 + 2*sum_(L=1)^N E(L)
  <= K_s [N + N^2 10^(-s m)]
```

for all positive `m,N`. Philipp/Fukuyama give pointwise-a.e. discrepancy error
of order `sqrt(L log log L)` after an onset. Summing that error is of order
`N^(3/2) sqrt(log log N)`, which cannot be absorbed by the additive `K_s N`
when `m` is large. Thus even an illicit specialization to `pi` would not close
T2.

### Symbolic comparison

An equal decimal block is an exact symbolic collision and implies the circle
near-return used by T2. The converse has neighboring-cylinder/boundary loss,
which is why T2 deliberately asks for the stronger geometric residual count.
Rousseau addresses exact matching but only the longest match of two random
samples. Chernov--Kleinbock addresses counts but only visits to prescribed
cylinders. Neither controls the sum of squared block occupancies, hence neither
controls T2's total ordered self-collision count.

## Conclusion

The source-pinned matrix yields no imported positive route to T2. This audit
assigns the arithmetic premise to T4 without treating it as discharged; among
the geometric hypotheses audited here, the narrowest unmet hypothesis is not
decimal boundary control or pair orientation. It is:

> For each `0<s<1`, a fixed-pi, all-scale, nonasymptotic aggregate bound for
> the ordered long-lag residual near-return count, with one `C_s` chosen before
> every positive `m,N`.

Among standard theorem families, the closest reformulation is fixed-pi
moving-scale pair correlation with a finite uniform rate. Discrepancy and
shrinking-target results would additionally need error terms that remain
`O(N)` after summation over all lags. Symbolic matching results would need total
collision energy rather than only occurrence or maximum-match asymptotics.

This report makes no claim that C1 is proved, refuted, or heuristically
confirmed. It records only `literature-checked` non-applicability of the quoted
theorems and the exact remaining hypothesis.
