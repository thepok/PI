# Two-step signed horizon-overlap ladder

Date: 2026-08-27 UTC

Claim labels: the cited T176 and T189 theorems are `machine-checked`; the
capital identity and recursive ladder below are a `proof sketch`; both
actual-pi numerical steps are `experiment`.  No unbounded transport, V1, or
normality statement is proved.

## Exact one-step capital decomposition

Write

```text
B(q,A,L) = q * Re Z(q,A,L) - L * 7/(3q),
```

where `Z` is the complete primitive boundary sum.  Fix

```text
q >= 1000,  A < q,  N=10q,  Q=10q,  H=10N=100q.
```

For `d<10`, put

```text
P_d = B(Q,A+dq,N) - B(q,A,N),
M_d = Delta_0(q,A;N,H) + Xi_d(q,A;N,H) - 21/q.
```

T176 already gives some `d` with `P_d>0`.  T189 gives

```text
10 * Re[Z(Q,A+dq,H)-Z(Q,A+dq,N)] = Delta_0 + Xi_d.
```

Since `(H-N)*7/(3Q)=21`, direct substitution yields the exact capital law

```text
B(Q,A+dq,H) = B(q,A,N) + P_d + q*M_d.       (1)
```

No endpoint term is omitted: `Delta_0` already contains the parent increment
and T172 left-extension remainder, and every `Z` in (1) is the complete
primitive sum.

Three different conditions must not be conflated:

1. `P_d>0` and `M_d>0` is **strong fresh overlap**.  The same child improves
   at the old horizon and receives strictly positive new signed mass.
2. `P_d+q*M_d>0` is **monotone capital regeneration**.
3. `B(q,A,N)+P_d+q*M_d>0` is the logically minimal **positive-capital
   preservation** condition.

The strong condition implies the other two when the parent capital is
positive.  Conversely, positive final capital need not mean that the fresh
mass or combined gain was positive.

If strong fresh overlap holds at every reached node, choose such a digit and
replace `(q,A,N)` by `(10q,A+dq,10N)`.  The invariant `N=10q` is preserved,
and (1) gives strictly increasing positive capital at geometrically growing
horizons.  This is a conditional coherent predecessor ray, not control of all
targets.  A separate short T148 endpoint-budget consequence is still needed
before calling every `N=10q` rung a registered hit theorem; T156 itself is the
natural-horizon `N=q` consumer.

## Two actual-pi steps

At the root

```text
(q,A,N,H,d)=(1000,334,10000,100000,3),
```

the registered diagnostics give approximately

```text
P_3 ~= 11270.93,
M_3 ~= 14.7311.
```

Thus the strong overlap condition holds experimentally, producing the next
node `(q,A,N)=(10000,3334,100000)`.

At that node the literal closed-kernel replay through `H=1000000` gives

```text
{d : P_d>0}                 = {0,4,5,6,7,8},
{d : M_d>0}                 = {0,3,5,6},
{d : P_d>0 and M_d>0}       = {0,5,6}.
```

The strongest fresh-overlap witness in that set is

```text
d=6, target=63334,
P_6 ~= 78825.5198,
M_6 ~= 61.7007825,
B(100000,63334,1000000) ~= 740827.6277.
```

For quantifier discipline, the weaker sets differ: monotone combined gain
holds for `{0,5,6,7}`, while positive final capital holds for `{0,5,6,7,8}`.
In particular `d=8` spends some inherited capital and must not be advertised
as positive fresh mass.

The replay is
`workflows/experiments/t189_overlap_q10000.py`.  It verifies the certified
digit-file SHA-256, uses 22 suffix digits, a stable sine-product form for the
cosine difference, the exact T142 piecewise coefficients, the literal T139
endpoint, and assertions for all three digit sets.  It is a floating-point
falsification experiment, not a directed certificate.  An independent
implementation agreed on every sign; the smallest reported strong-overlap
margins are still many orders of magnitude above the observed numerical
variation.

## First open pi-specific rung

The constructive first open rung is now the recursive strong-overlap claim

```text
at every reached actual-pi node, there exists d<10 with P_d>0 and M_d>0.
```

Its target-signed information enters only through the same-digit coupling of
the old-horizon improvement with the fresh T189 predecessor/suffix sector.
T176 supplies an improving digit and T189 identifies the fresh mass, but
neither theorem makes their favorable digit sets intersect.

One failed level would destroy the strong ladder.  Two successful levels do
not prove persistence.  The next proof task is therefore a one-sided
cross-horizon overlap or covariance lemma forcing this intersection for the
actual pi state.  Counts, separate digit averages, unsigned energy, universal
kernel geometry, and fiber-uniform representation data cannot provide it.

## Failed scalar compression

The most natural one-number reductions were tested before promotion.  The
old-prefix-weighted scalar

```text
C_strong = sum_d max(P_d,0) * M_d
```

is sufficient when positive, but it is not necessary for strong overlap.  At
the root, where `d=3` is a valid joint-positive witness, the improving but
fresh-negative digits `2,4,9` dominate and give

```text
C_strong ~= -2.7849e6.
```

The analogous monotone-regeneration scalar is about `-6.8598e8` there.  Both
become strongly positive at the second node, so neither has a scale-stable
sign even across the two successful steps.

Sign counts plus raw covariance and the sharp mean/Parseval-variance lower
bound also fail at the root.  A directed clipped pairing such as
`sum_d P_d*max(M_d,0)` passes both pi nodes, but retains exactly the favorable
paired-sign sector and also passes matched de Bruijn periodic controls.  It is
therefore a diagnostic repackaging, not an independent pi-specific source or
a smaller proof target.

A multibranch portfolio does not bypass this alignment.  For
`X_d=B(q,A,N)+P_d+qM_d`, the weakest positive-capital portfolio condition is
`sum_d max(X_d,0)>0`, which is exactly `max_d X_d>0` in disguise.  Equal
weights erase every nonzero digit character because `sum_d Xi_d=0` and leave
the root-failing zero sector.  Unequal linear weights, log-sum-exp, top-k, or
positive-part potentials succeed only after retaining the jointly aligned
`P_d,M_d` coordinates, hence reintroduce the missing target signs.

This limitation is exact at the finite-vector level: permuting the same
`M_d` multiset against a fixed `P_d` preserves all separate means, norms,
energies, and order statistics but can change a vector with one positive
`B+P_d+qM_d` coordinate into a vector with none.  Thus target alignment, not
portfolio bookkeeping, is the atomic missing information.
