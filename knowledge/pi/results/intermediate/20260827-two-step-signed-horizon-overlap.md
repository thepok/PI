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

## Natural-diagonal ladder improvement

The `N=10q,H=100q` ladder is not the shortest recursion.  The root seed has
`(q,A,N)=(1000,334,10000)`.  One T176 fixed-horizon step with the observed
digit `d=3` reaches

```text
(q,A,N)=(10000,3334,10000),
```

so `N=q` and the recursion can continue on the natural diagonal.  For a
diagonal parent `B(q,A,q)>0`, put `Q=10q`, `H=10q` and

```text
U_d = B(Q,A+dq,q),
W_d = B(Q,A+dq,10q).
```

T189 and direct scalar arithmetic give

```text
W_d-U_d = q*(Delta_0(q,A;q,10q)+Xi_d(q,A;q,10q)) - 21/10.   (D1)
```

The debt is exactly `(10q-q)*7/(3*10q)=21/10`, one tenth of
the old `N=10q,H=100q` debt.  A positive `W_d` is already at the next natural
horizon and therefore composes directly with T156, avoiding the separate
arbitrary-horizon T148 scalar comparison.  This diagonal identity is a
`proof sketch` specialization of the machine-checked T189 identity, not a new
pi estimate.

For quantifier discipline, define the old-horizon gain and fresh sector by

```text
G_d = U_d-B(q,A,q),
F_d = Delta_0(q,A;q,10q)+Xi_d(q,A;q,10q).
```

T176 machine-checks that some `G_d>0`.  The first unproved pi-specific
capital-only diagonal rung is exactly

```text
exists d<10: G_d>0 and q*F_d > 21/10-G_d.              (MR-diag)
```

Indeed, (D1) gives
`W_d=B(q,A,q)+G_d+q*F_d-21/10`, so MR-diag strictly regenerates the parent
capital at the next natural horizon.  In literal signed-sector form, its only
new arithmetic line is

```text
Xi_d > 21/(10q)-Delta_0-G_d/q
```

for one old-horizon improving digit.  This is an alignment statement between
the past-derived improving set and the actual-pi predecessor-digit/suffix
correlation, not a separate average or unsigned bound.

MR-diag can regenerate capital while the fresh block is negative.  To retain
the signed-horizon objective itself, put

```text
D_d = W_d-U_d = q*F_d-21/10.
```

The live **fresh-monotone regeneration** rung is

```text
exists d<10: D_d>0 and G_d+D_d>0.                     (FMR)
```

Equivalently, its single pi-specific line is

```text
exists d<10:
  Xi_d > 21/(10q)-Delta_0+max(0,-G_d)/q.              (FMR-atom)
```

FMR gives both `W_d>U_d` and `W_d>B(q,A,q)>0`: the new block contributes
strictly positive target-signed capital and the next natural node strictly
improves the parent.  It is not equivalent to MR.  Writing strong overlap as
`G_d>0 and D_d>0`, strong overlap implies both MR and FMR, while MR and FMR
are otherwise incomparable.  FMR is therefore the diagonal weakening of
strong overlap that preserves positive fresh mass; MR is the weakening that
preserves the past-derived T176 digit.

Literal actual-pi replay gives the following FMR sets at the four available
first diagonal parents:

```text
A=2334: {2,6}      A=3334: {5,6,7,8}
A=4334: {3}        A=9334: {1,2,6}.
```

Every corresponding continuation that keeps the first `10000` pi digits and
then uses `333...` has an empty FMR set.  Thus FMR passes the predeclared
replacement control that MR and the past-only argmax selector fail.

More importantly, every FMR child of the initialized `A=3334` node has a
second FMR level:

```text
53334 -> {1,2,4,5,7}      63334 -> {0,2,3,4,7,8}
73334 -> {3,5,6,7}        83334 -> {0,1,2,4}.
```

An independent literal replay at suffix widths `16` and `22` preserved all
four positive parent capitals, all 19 second-level child signs, and every FMR
set.  The smallest first-level joint margin is about `42998`; the smallest
second-level joint margin exceeds `358497`.  These results are `experiment`,
not certificates.  They establish two finite branching FMR levels, not an
unbounded pi theorem, selector coverage, or V1.  The initialization through
the specific root digit `3` is itself still experimental.

A useful stronger atom fixes `d_*` as a past-only maximizer of `G_d` and asks
for the displayed inequality at `d_*`.  T176 makes `G_(d_*)>0`, but it does
not prove the signed-sector inequality.  If that atom is still too large, an
explicit margin `G_(d_*)>=gamma(q,A)>0` separates the remaining target as
`F_(d_*)>(21/10-gamma)/q`.  Splitting `Delta_0` and `Xi_(d_*)` further is not
licensed without an independent pi input; the observed negative zero sector
already warns that such a split can be strictly stronger.

This past-only selector survives the four available natural-diagonal replays,
but that finite success is not evidence for a pi-specific source.  For parent
targets `A in {2334,3334,4334,9334}`, the actual-pi argmax digits are
respectively `{5,4,2,5}` and every one is an MR-diag witness.  Replacing all
decimal digits after position `10000` by `3` leaves the same four argmax
digits and the same full MR witness sets:

```text
A=2334: {2,5}    A=3334: {0,4}
A=4334: {1,2,9}  A=9334: {2,5}.
```

An independent literal replay preserved every sign with suffix widths
`16,18,20,22`; the smallest argmax gap was about `2584.8` and the smallest
positive MR coordinate margin about `4352.9`.  These are `experiment` values,
not certificates.  Because the control deliberately retains the pi prefix, it
does not refute a future theorem about the actual-pi selector.  It does refute
treating four-node argmax success itself as fresh-tail pi arithmetic: the same
selection and regeneration occur for an eventually periodic continuation.

The next predeclared argmax step behaves the same way.  Following the
`A=3334` argmax digit `4` reaches `(q,A)=(100000,43334)`.  At the next natural
step the actual-pi argmax is `d_*=1`, the only MR-diag witness, with

```text
G_1 ~= 2137430,  W_1-B_parent ~= 1076108,
W_1-U_1 ~= -1061323.
```

The continuation that is `333...` after position `10000` again has the same
argmax and singleton MR set, with respective margins about `2167578`,
`1137135`, and `-1030443`.  Suffix widths `16,18,22` preserve every sign and
selection.  This is again an `experiment`.  It does not refute MR-diag as a
capital-transport mechanism, but it sharply separates it from positive fresh
regeneration: at the sole surviving digit, more than a million units of
inherited gain absorb a fresh-block loss of comparable size, even for the
eventually periodic control.  Finite MR persistence therefore cannot itself
be advertised as newly created target-signed pi mass.

The weakest recursive quantifier is only a reached path of positive diagonal
nodes satisfying MR-diag.  A reusable theorem for every positive
`A<10^k` would be sufficient but substantially stronger.  Neither quantifier
implies V1 without the separate symbolic coverage condition below.

At the first actual-pi diagonal node

```text
(q,A,N,H)=(10000,3334,10000,100000),
```

the literal replay gives

```text
{d:U_d>0}            = {0,4},
{d:W_d>0}            = {0,4,5,6,7,8},
{d:U_d>0 and W_d>0}  = {0,4}.
```

Both old-improving digits lose fresh capital, so strong fresh overlap is
empty.  Nevertheless their inherited gain is large enough that MR holds for
both `d=0` and `d=4`.  This `experiment` is a direct reason to keep MR rather
than the stronger `M_d>0` condition.

### Failed dominant-mode compression

A proposed smaller rung used one normalized digit-DFT anchor.  For a real
digit vector `X`, define

```text
Xhat(r) = (1/10) * sum_(d<10) X_d*zeta^(r*d).
```

For `rho in {1,3}`, bound every non-anchor mode absolutely by

```text
E_X(rho) = 2*sum_(1<=r<=4,r!=rho)|Xhat(r)| + |Xhat(5)|.
```

If the angle between `Uhat(rho)` and `What(rho)` is `delta<4*pi/5`, a
ten-grid midpoint selects one digit at which the anchor contribution to both
vectors is at least
`2*|Xhat(rho)|*cos(pi/10+delta/2)`.  Positive zero-plus-anchor-minus-tail
margins would force a common positive digit.  The generic geometry is sound,
but the sufficient margins fail decisively at the first diagonal pi node:

```text
rho=1: delta/pi ~= 0.72626,
       old margin ~= -174012.26, final margin ~= -171802.02;
rho=3: delta/pi ~= 0.06888,
       old margin ~=  -75021.12, final margin ~= -145700.62.
```

Thus the actual joint-positive coordinates `{0,4}` coexist with enormous
absolute non-anchor tails.  The fixed one-anchor plus `l1`-tail rung is
falsified on the registered `d=3` diagonal path and must not receive a proof
program.

The three alternative T176-positive root children were then replayed at the
same diagonal horizons.  None rescues the cone:

```text
parent A   MR witnesses   rho=1 margins (old,final)    rho=3 margins (old,final)
2334       {2,5}          (-79889,-272515)             (-63225,-208127)
3334       {0,4}          (-174012,-171802)            (-75021,-145701)
4334       {1,2,9}        (-52020,-48574)              (-112273,-181306)
9334       {2,5}          (-110177,-235182)            (-49086,-173682)
```

Every actual root initialization has MR witnesses, while every proposed
one-anchor absolute-tail margin is negative.  This closes the whole
`rho in {1,3}` initialization class, not just one selected path.

For `rho=1`, the midpoint digit is `d=4`; the signed residual after subtracting
the zero and anchor modes is positive for both vectors.  That weaker condition
survives numerically, but it retains the complete target-evaluated non-anchor
tail.  No independent pi theorem controls its sign, so it is only another
candidate interface, not a new arithmetic result.

Retaining more signed modes does not produce a credible smaller source.  The
fixed three-anchor set `{1,3,4}`, with only mode `2` and the Nyquist mode `5`
bounded absolutely, certifies MR at all four actual root children.  But it
retains seven of the ten signed real DFT degrees and also uses the magnitudes
of every omitted degree; only the phase of mode `2` and sign of mode `5` are
discarded.  The remaining pointwise absolute tail is sharp with that
information.  Moreover, the same condition passes three of the four
pi-prefix-plus-`333...` diagonal controls.  Decimal relabelling places modes
`2` and `4` in the same natural symmetry class, and neither T179, Machin, nor
BBP supplies a reason to control `4` while discarding `2`.  This is a
near-reconstruction diagnostic, not a pi-specific rung.

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

### Exact scope of an infinite ray

Even a proof of MR at every selected rung would not by itself prove V1.  If
the successive selected digits are `d_0,d_1,...`, the scale-`r` word is

```text
W_r = d_(r-1) ... d_1 d_0 334.
```

Positive capital at horizon `10q_r`, followed by the still-unpackaged T148
scalar comparison, gives a hit of `W_r`.  T156 alone cannot consume this rung
because it is stated at the natural horizon `N=q_r`.  Since every later
`W_r` contains each earlier `W_s` as a suffix, the ray would give arbitrarily
late recurrences of every finite factor of the single left-infinite word
`...d_2 d_1 d_0 334`.  There is no checked theorem amplifying that language to
all decimal words.

The weakest symbolic addition sufficient for V1 is that the selected
left-infinite word itself is disjunctive.  A branching alternative is

```text
for every finite decimal word w, some viable MR branch reaches w334.
```

A hit of `w334` contains `w`, so this also suffices.  Full ten-way
regeneration at every node is stronger than necessary.  Thus one-ray MR is a
meaningful first transport mechanism, but not the all-target summit; future
work must not report it as a V1 bridge without one of these additional
coverage statements.

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

A later sparse-Fourier supporting-weight proposal also fails to compress the
problem.  For any probability vector `lambda` supported on the improving set,
positivity of `sum_d lambda_d*(P_d+qM_d)` certainly implies MR.  The literal
weighted T179 identity, however, retains every fine frequency:

```text
sum_d lambda_d*Xi_d
 = 10*Re sum_(0<h<2Q,10 not| h)
     alpha_Q(h)*e(-h*c_parent/10)*lambdahat(h mod 10)
       * sum_(N<=n<H)e(h*10^n*pi).
```

It does not collapse to one coefficient times `e(10^n*pi)`.  At the root,
the preferred zero-plus-one-conjugate-pair Fourier support is impossible for
a nonnegative weight supported on `{2,3,4,9}`: its inverse transform is a
degree-one sinusoid and cannot vanish on all six excluded grid points.  The
finite choice `(delta_3+delta_4)/2` kills only character `5`, retains nine
characters, and has positive weighted gain only because it includes the
fresh-successful digit `3`.  It is not a past-derived reusable selector.

One-sided Machin truncation gives the side and size of `pi-r_J`, but the
derivative of the complete multi-`h` polynomial has either sign.  Correct
Taylor transfer therefore remains a directed rational replay of the same
unknown carrier, not a source of its sign.  No new pi-arithmetic lemma survives
this supporting-functional proposal.
