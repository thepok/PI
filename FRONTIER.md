# π decimal disjunctivity frontier

Status: `conjecture`
Last audited: 2026-08-30 UTC

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
- **T194 — Central π Return Seed — machine-checked π rung.**
  [`T194T194CentralPiReturnSeed.lean`](TheoryLib/PiQuantitativeBlockHitting/T194T194CentralPiReturnSeed.lean)
  proves unconditionally, using `irrational_pi`, that every decimal scale
  `10^k`, `k>=3`, has some actual-π orbit point and containing cell with the
  T193 unit-block surplus `>3*10^k/20`; this qualitative theorem has no timing
  bound. Under the additional explicit premise
  `IrrationalityMeasureBelow pi (36/5)`, it proves that after one onset such a
  unit can always be chosen with `10^k+1<=n<10^(k+1)`. Its literal predecessor
  digit then machine-checkably lifts the same centered coordinate to a child
  unit at scale `10^(k+1)` and time `n-1`, inside the exact T189 fresh block,
  with surplus `>3*10^k/2`. The quantitative premise is not proved in the
  repository, the target is unprescribed, and neither positivity of the
  entire same-child fresh block nor a coherent natural-horizon ray follows.
  The qualitative
  irrationality mechanism is generic to every irrational constant; it is
  actual-π information after specialization, not yet π-specific arithmetic.

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

T189 is frozen as the finished consumer. A new candidate enters the active
frontier only if all three tests hold:

1. it is false for a suitable word-avoiding replacement constant;
2. a named arithmetic property special to π makes it plausibly true for π;
3. it directly yields a prescribed target hit or the literal same-child signed
   horizon inequality.

A further kernel, determinant, cone, Padé, BBP, or equivalent reformulation
without such an order source does not qualify. The most concrete remaining BBP
object is the exact residue sequence

```text
r_n = (10^n-16) P_n mod D_n
```

for the inclusive rational BBP partial `B_n=P_n/D_n`. The final focused BBP
cycle is now paused. **Reason:** its strongest new ordered quantity,

```text
Theta_n = (10^(n+1)-16) B_(n+1) - 10(10^n-16) B_n,
```

satisfies `144*pi < Theta_(n+1) < Theta_n` for `n>=2` and converges to
`144*pi` (`proof sketch`, independently audited), but this orders only the
positive scalar tail. The exact identity
`Theta_n-144*pi=10E_n-E_(n+1)` makes it another removable scalar defect and
does not orient `r_n/D_n`. A targeted PaperSearch audit found only universal
perturbed-orbit coupling, fixed-modulus automatic congruences, and probabilistic
π heuristics; none controls the canonical residue in the moving modulus
([Lagarias](https://arxiv.org/abs/math/0101055),
[Rowland--Yassawi](https://arxiv.org/abs/1310.8635), and
[Barral--Loiseau](https://arxiv.org/abs/1004.3713); `literature-checked`,
2026-08-30). **Strongest retained lemma:** the exact
coboundary conjugation together with the strict scalar monotonicity above.
**First fatal line:** the unknown integer lift in
`(10^n-16)B_n=k_n+r_n/D_n` destroys the passage from order modulo `2*pi` to
order modulo `1`. **Reopening condition:** a new quantity from the exact
numerator structure that breaks `r_n <-> D_n-r_n`, supplies one-sided
Archimedean control on unboundedly many scales, and passes all three tests.

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
An independently audited scalar-cohomology criterion now shows that a finite
mean-zero trigonometric polynomial is an `L1` state-only decimal coboundary
exactly when every primitive frequency-ray coefficient sum vanishes. Each of
T189's nine nonzero child-character sectors has an explicit nonzero top-band
residue with its literal inverse child character. At `proof sketch` level,
scalar `L1` endpoint potentials and scalar summation by parts therefore cannot
eliminate any sector; the needed actual-π theorem must sign their surviving
joint remainder.

A newly audited full-sector candidate packages the required alignment without
discarding character blocks.  For `F=G+D`, the corrected cross-energy

```text
E(D,F)=sum_d D_d*F_d-sum_d D_d^-*F_d^-
```

is strictly positive only if one literal digit has both `D_d>0` and `F_d>0`.
Its bilinear term has an exact five-block Parseval expansion, and strict
outward-interval `experiments` for the actual π orbit give `E>0` at the
certified root and all seven legal first-generation nodes, including
`E>2.7430*10^9` at the hard reached node `(10000,1334)`. Historically this
made `E>0` a deterministic sufficient proxy, not new π arithmetic; the
all-child separator below has since paused it as a research target. Exact scope,
normalization, and finite bounds are recorded in
[`T189_FMR_R1_R2.md`](knowledge/pi/workstreams/T189_FMR_R1_R2.md).
This premise is genuinely stronger than FMR: a directed-interval periodic
decimal-orbit separator at `q=1000` has positive parent and unique FMR digit
but `E<-3.08*10^9`.  Hence any proof must use π-specific information, not
T189 bookkeeping alone.

The separator now reaches the active range and is Roth-optimal at `proof
sketch` level. An explicit orbit sharing the T173-certified first 10015 pi
digits has `E>5.889*10^9` at `(1000,334)` and follows the legal FMR edge `d=1`
to the positive node `(10000,1334)`, where literal FMR survives uniquely at
`d=5` but `E<-4.380*10^9`. In fact every one of the seven legal root FMR
choices reaches a positive node with negative `E` and retains exactly one next
FMR child. An explicit stability ball contains a transcendental orbit with
irrationality exponent `2`. Thus even an omniscient adaptive choice among the
current FMR children cannot make orbit-generic `E` hereditary, and the failure
cannot be blamed on FMR dying. This does not rule out an actual-pi theorem or
FMR transport by a different signed invariant.
See the [directed-interval separator](knowledge/pi/results/negative/20260829-pathwise-cross-energy-heredity-separator.md).

Cross-energy is therefore paused as the primary research focus. **Reason:**
successive results only sharpened a sufficient proxy without producing new
actual-pi target-signed information. **Strongest retained lemma:** the
all-seven-child active-scale separator above. **Reopening condition:** an
actual-pi joint-character leakage bound or selector theorem using information
false for the pi-prefix transcendental replacement.

A new actual-π chain gives a stronger but still insufficient signed side
result. T191 machine-checks its central kernel floor, T192 the exact
valuation-shell subtraction and positive zero-shell margin, T193 the
positive-shell aggregate, and T194 the unconditional existence of an
unprescribed actual-π seed at every decimal scale using only `irrational_pi`.
Thus every sufficiently central
literal orbit point has the machine-checked primitive atom bound
`p_(q,A)(n)>7139/45000` and T176 unit-block capital
`S_(q,A)(n,1)>3q/20`. Under the additional explicit
`IrrationalityMeasureBelow pi (36/5)` premise, T194 localizes one such unit to
`q+1<=n<10q` after a premise-dependent onset and lifts it through its literal
predecessor digit to a child-scale unit at time `n-1` with surplus `>3q/2`.
Both units lie in the exact fresh horizon block and preserve the centered
coordinate. This is same-child transport of one local positive atom, not
positivity of the whole same-child fresh sum. The target loss is exact: for a
generic radix orbit `x_n`, T194 chooses `A=floor(10^k*x_n)` and its centered
coordinate is `x_(n+k)-1/2`; imposing a preassigned `A*` is already the
`A*`-cylinder hit. Fishman's badly-approximable `{1,2}`-digit Cantor points
show that the generic central-unit and predecessor-lift premises may hold at
every time and scale while digit `3` never occurs (`literature-checked`
existence plus `proof sketch` analytic transfer). Thus neither the `36/5`
Diophantine premise nor arbitrarily abundant central units repair the target
quantifier. The subsequent
infinite-ladder selection remains open. Iterating
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
More sharply, an audited T128/T174 annular estimate shows that positive fresh
surplus requires `R<=125H+27`, where `H` counts selected target-cell hits and
`R` counts visits to `3/5<=|y|<=5/8`. A transcendental `mu=2` replacement can
preserve two exact predecessor atoms at every sufficiently large selected
scale while violating this condition and forcing `D_1<-Q/225` (`proof
sketch`). The adverse contribution has a universal positive pairing with an
adjacent cell, in fact `Phi_Q(y)+Phi_Q(y-1)>337/1000` on the right annulus
(`proof sketch`), but the adjacent parents retain distinct residues modulo the
root scale forever. They are parallel refinement rays, not a same-child
transport corridor. Hence bounded central renewal and neighboring-cell
compensation are not the missing transport law.
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
