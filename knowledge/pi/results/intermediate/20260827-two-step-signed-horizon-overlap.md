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

There are three logically different research targets.  The weakest recursive
condition is positive-capital preservation

```text
exists d<10: B(q,A,N) + P_d + q*M_d > 0.
```

This is necessary and sufficient for one more positive rung, but merely
restates the desired child conclusion.  The weakest presently useful
same-digit bridge with genuine monotone gain is

```text
exists d<10: P_d > 0 and P_d + q*M_d > 0.               (MR)
```

It is strictly weaker than strong fresh overlap: the new block may lose some
of the old-horizon improvement.  By (1), MR gives
`B(Q,A+dq,H)>B(q,A,N)>0`.  In T189 notation its atomic pi-specific line is

```text
max_{d:P_d>0} (Xi_d + P_d/q) > 21/q - Delta_0.           (2)
```

Strong overlap remains a robust sufficient candidate, not the logically
minimal rung.  T176 makes `{d:P_d>0}` nonempty and T189 identifies `Xi_d`, but
neither aligns the fresh sector with that same digit.  The target-signed
information in (2) can enter only through the literal coupling of the actual
pi predecessor digit, suffix, and target character.

The recursive quantifier is an existential path: starting at the seed, choose
one witness digit at each reached node.  It is not a claim about every node in
the branching tree.  One failed level along every available branch would
destroy the ladder; two successful selected levels do not prove persistence.
Counts, separate digit averages, unsigned energy, universal kernel geometry,
and fiber-uniform representation data cannot provide (2).

The finite root input is itself still only an `experiment`.  The recorded
directed bound `Re Z(1000,334,10000)>47539/2500` would imply
`B(1000,334,10000)>284884/15>0`, but the full inequality is not yet checked in
Lean.  Certifying that bounded seed and proving the unbounded MR rung are
separate tasks.

## Prefix-preserving periodic-tail separator

The existing generic inputs cannot prove even positive-capital preservation.
Keep the first `N=10000` fractional decimal digits of pi and then replace the
tail by `333...`:

```text
theta = (floor(10^N * fract(pi)) + 1/3) / 10^N.
```

A literal floating-point replay at the root gives

```text
Re Z_theta(1000,334,10000) ~= 19.0165484,
B_theta(1000,334,10000)     ~= 18993.215 > 0,
{d:P_d>0}                    = {2,3,4,9},
{d:M_d>0}                    = empty.
```

The improving set is exactly the actual-pi root set.  Nevertheless every
final child capital is negative.  For its improving digit `d=3`,

```text
P_3 ~= 11274.7323,
M_3 ~= -3521.2309,
B_child(H) ~= -3.491e6.
```

For the other nine digits, `M_d` is about `-103.066`.  This simultaneously
destroys strong overlap, MR, and positive-capital preservation for the
replacement.  It does not refute an explicitly actual-pi theorem.  It proves
that the positive seed, T176/T189 identities, decimal recurrence, the old
improving set, and a long shared decimal prefix do not force any recursive
transport.  A continuation with a long fixed block and a sufficiently small
transcendental perturbation gives the same finite separator by continuity, so
generic transcendence does not repair it either.

Only the first `N` decimal digits are shared, not the first `N` real orbit
points: near the endpoint their infinite suffixes differ, and T139 also reads
terminal orbit values.  The replay therefore recomputes every primitive score
rather than identifying the old-horizon sums.  It can be reproduced without
editing the audited script by resetting its root parameters and inserting
`digits = digits[:N] + "3" * (len(digits)-N)` immediately after its digit-file
length assertion.  The numerical margins are large, but the result remains
an `experiment`, not a directed certificate.

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
