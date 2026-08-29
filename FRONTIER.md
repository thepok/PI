# π decimal disjunctivity frontier

Status: `conjecture`
Last audited: 2026-08-29 UTC

This is the only authoritative current research map. No theorem in this
repository proves V1, decimal density, or normality of π. The normalized
statement and quantifier audit are in
[`TARGET.md`](knowledge/pi/workstreams/TARGET.md).

## Exact target

[`Theory.PiDigits.V1`](TheoryLib/PiDigits/T7Statements.lean) states

```text
∀ s : List (Fin 10), ∃ n : ℕ,
  ∀ i < s.length, piDigit (n+i) = s[i].
```

Leading-zero words and overlaps are included; the empty word is vacuous.

## Verified consumer and current modules

- **T179 — Predecessor Lag-One Correlation — machine-checked identity.**
  [`T179T179PredecessorLagOneCorrelation.lean`](TheoryLib/PiQuantitativeBlockHitting/T179T179PredecessorLagOneCorrelation.lean)
  proves `predecessorDigitSector_eq_lagOneCorrelation`: the literal fresh
  sector retains predecessor digit, suffix phase, and target rotation.
- **T189 — Signed Horizon Sector Bridge — machine-checked consumer.**
  [`T189T189SignedHorizonSectorBridge.lean`](TheoryLib/PiQuantitativeBlockHitting/T189T189SignedHorizonSectorBridge.lean)
  proves the fresh-block identity and
  `signedPrefixSurplus_child_pos_of_horizon_sector_gt`, which turns the full
  one-sided sector inequality into a positive same-child surplus.
- **T190 — Complementary Rank Alignment — machine-checked deterministic
  alignment.** It applies only after independent π-specific rank information
  is supplied.
- **T191 — Central Boundary-Kernel Floor — machine-checked analytic rung.**
  [`T191T191CentralBoundaryKernelFloor.lean`](TheoryLib/PiQuantitativeBlockHitting/T191T191CentralBoundaryKernelFloor.lean)
  proves the uniform pointwise bound `boundaryMinorant>4859/10000` throughout
  the normalized chamber `|y|<=9/22` at every decimal scale `10^k`, `k>=3`.
  It contains no orbit or target-recurrence premise.
- **T192 — Primitive Valuation Shells — machine-checked structural rung.**
  [`T192T192PrimitiveValuationShells.lean`](TheoryLib/PiQuantitativeBlockHitting/T192T192PrimitiveValuationShells.lean)
  extracts the one-time primitive atom, partitions it into exact `v_10`
  shells, proves `H_s=L_s-L_(s+1)`, and retains more than
  `(9/20)*(4859/10000)` in the central zero shell. T193 aggregates the
  positive-valuation shells.
- **T193 — Positive Valuation-Shell Aggregate — machine-checked seed.**
  [`T193T193PositiveValuationShellAggregate.lean`](TheoryLib/PiQuantitativeBlockHitting/T193T193PositiveValuationShellAggregate.lean)
  proves the complete central atom bound `Re atom>7139/45000` and the native
  T176 unit-block surplus `>3q/20`. It contains no recurrence or
  irrationality input and does not control a natural prefix.
- **T194 — Conditional Central π Return Seed — machine-checked conditional
  π rung.**
  [`T194T194CentralPiReturnSeed.lean`](TheoryLib/PiQuantitativeBlockHitting/T194T194CentralPiReturnSeed.lean)
  proves from the explicit premise `IrrationalityMeasureBelow pi (36/5)` that
  every decimal scale `10^k`, `k>=3`, has some actual-π orbit point and
  containing cell with the T193 unit-block surplus `>3*10^k/20`. It now also
  proves that, after one premise-dependent onset, such a unit can always be
  chosen with start time `n<8*10^k`, hence inside the next natural horizon.
  The premise is not proved in the repository, the target is unprescribed,
  and no coherent ray or signed natural-horizon accumulation follows.

The exact declarations and downstream T148/T153/T156 path are indexed in
[`VERIFIED_CONSUMER_PATH.md`](knowledge/pi/results/machine-checked/VERIFIED_CONSUMER_PATH.md).

At a positive natural-diagonal node `(q,A)`, with `Q=10q`, define

```text
G_d = B(Q,A+dq,q) - B(q,A,q),
D_d = B(Q,A+dq,Q) - B(Q,A+dq,q)
    = q*(Delta_0 + Xi_d) - 21/10.
```

The finished T189 consumer requires one literal digit satisfying both signs:

```text
exists d<10: D_d > 0 and G_d + D_d > 0.            (FMR)
```

Separate witnesses are invalid. Quantifying over an already reached unbounded
path is circular. Full definitions are in
[`T189_FMR_R1_R2.md`](knowledge/pi/workstreams/T189_FMR_R1_R2.md).

## First open π lemma — same-child signed horizon transport

This is a `conjecture`, not a Lean declaration. Starting from a certified
positive π seed, construct an unbounded recursively reached path

```text
q_(k+1)=10*q_k,       A_(k+1)=A_k+d_k*q_k,
D_(k,d_k)>0,          G_(k,d_k)+D_(k,d_k)>0.
```

The new input must explain the target-signed Archimedean sign for the actual
constant π and preserve the same child. Symmetry, means, almost-everywhere
lacunary results, denominator or period structure, local congruences, unsigned
energy, rational shadows, and finite prefix replay do not supply it.

Uniform Pair/DC1 positivity is already falsified at the positive π node
`(q,A)=(1000,689)`: all five Pair margins and the DC1 premise are negative,
while literal FMR holds strongly and uniquely at `d=8` (`experiment`). The
stronger reproduced `experiment` at the legally reached positive node
`(10000,1334)` has unique FMR at `d=5` while every convex mask annihilating
predecessor sector `r=5` is negative. Thus a viable reduction must retain a
nontrivial, correctly oriented sector-5 component.

T179's sector 5 collapses, by anti-periodicity, to an ordinary odd-frequency
correlation on the decimal orbit of `5π` (`proof sketch`).  Its correctly
normalized real kernel has `z=pi*t` and opposite, nonvanishing sign chambers
on the same side of the target, so one-bit target orientation cannot sign it.
A deterministic private-prime depth makes the two inherited-deficit-corrected
parity margins unequal, but supplies essentially no transfer-scale magnitude.

The parity route is now closed from the certified `(1000,334)` seed.  An
independently reproduced outward-interval `experiment` finds root FMR digits
`{0,1,2,3,4,8,9}` and, at all seven legally reached `q=10000` nodes,
`max(M_even,M_odd)<-8424`.  By the one-Lipschitz clipping transfer lemma, no
p-free carrier inside the digitwise `E_D,E_G` buffers can satisfy the stronger
preferred-parity premise there.  This does **not** close literal FMR: at
`(10000,1334)`, `d=5` remains the unique witness.  The live rung must therefore
retain the complete literal multi-sector vector and explain its same-child
alignment, rather than proving `C+|q*R5-deltaH|>0` for a parity average.
Details and claim boundaries are in
[`20260828-sector5-odd-frequency-machin-direction.md`](knowledge/pi/results/intermediate/20260828-sector5-odd-frequency-machin-direction.md).

The remaining route must control this or the complete multi-sector
correlation while preserving relative phases and the same digit. Exact
quantifiers and admission tests are in
[`FIRST_OPEN_PI_LEMMA.md`](knowledge/pi/workstreams/FIRST_OPEN_PI_LEMMA.md).

A newly audited full-sector candidate packages the required alignment without
discarding character blocks.  For `F=G+D`, the corrected cross-energy

```text
E(D,F)=sum_d D_d*F_d-sum_d D_d^-*F_d^-
```

is strictly positive only if one literal digit has both `D_d>0` and `F_d>0`.
Its bilinear term has an exact five-block Parseval expansion, and strict
outward-interval `experiments` give `E>0` at the certified root and all seven
legal first-generation nodes, including `E>2.7430*10^9` at the hard reached
node `(10000,1334)`.  This is a viable deterministic rung, not new π
arithmetic: the open input is now a pathwise actual-π lower bound for `E` that
controls cross-block alignment and opposite-sign leakage.  Exact scope,
normalization, and finite bounds are recorded in
[`T189_FMR_R1_R2.md`](knowledge/pi/workstreams/T189_FMR_R1_R2.md).
This premise is genuinely stronger than FMR: a directed-interval periodic
decimal-orbit separator at `q=1000` has positive parent and unique FMR digit
but `E<-3.08*10^9`.  Hence any proof must use π-specific information, not
T189 bookkeeping alone.

A new actual-π chain gives a stronger but still insufficient signed side
result. T191 machine-checks its central kernel floor, T192 the exact
valuation-shell subtraction and positive zero-shell margin, T193 the
positive-shell aggregate, and conditional T194 the existence of an
unprescribed actual-π seed at every decimal scale under the explicit
`IrrationalityMeasureBelow pi (36/5)` premise. Thus every sufficiently central
literal orbit point has the machine-checked primitive atom bound
`p_(q,A)(n)>7139/45000` and T176 unit-block capital
`S_(q,A)(n,1)>3q/20`. T194 now localizes one such unit to `n<8q` after a
premise-dependent onset (without the previously sketched and unjustified
lower bound `q<=n`). The subsequent infinite-ladder selection remains open. Iterating
the machine-checked T176 step gives a coherent same-child block ray (`proof
sketch`) whose capital stays positive and strictly increases on that
unchanged unit block.  A fixed ray can be chosen with arbitrarily deep finite
ladders at depth-dependent return times (`proof sketch`). This does **not** control a natural
prefix: the periodic orbit `xi=1/9` has the same ladder, and the intervening
unit blocks are unsigned.  Separately, a Kempner--Mahler continuation sharing
10015 π digits eventually makes every child of every coherent `334`
descendant fail fresh positivity.  The live rung is therefore a genuinely
actual-π block-to-natural-horizon accumulation theorem for the recursively
reached same child, followed by prescribed-target leakage/old-score control.
Constants and claim boundaries are in
[`20260828-central-carrier-annular-flux.md`](knowledge/pi/results/intermediate/20260828-central-carrier-annular-flux.md)
and the [finite-cylinder separator](knowledge/pi/results/negative/20260827-finite-cylinder-horizon-bootstrap-separator.md).

## What remains after horizon transport

One coherent ray covers only factors of its selector word. V1 still requires
viable branching or a proof of selector-word coverage. The shortest route is

```text
actual-π same-child signed horizon transport
  -> T189 surplus
  -> T178/T176 transport
  -> T148/T153/T156 prescribed-cylinder hit
  -> branching or word coverage
  -> V1.
```

The active mathematical knowledge is deliberately small:

- [`machine-checked/`](knowledge/pi/results/machine-checked/) — theorem-role
  records and trust boundary;
- [`intermediate/`](knowledge/pi/results/intermediate/) — current finite seed
  and fixed-horizon evidence;
- [`SEPARATORS.md`](knowledge/pi/results/negative/SEPARATORS.md) — at most ten
  relevant no-go results;
- [`ATTEMPT_LEDGER.md`](knowledge/pi/workstreams/ATTEMPT_LEDGER.md) — compressed
  route memory: strongest lemma, first fatal line, and reopening condition.

Historical memos and raw model outputs are intentionally absent from the
visible tree; Git history is the archive. Cleanup and repository work are not
mathematical π progress.
