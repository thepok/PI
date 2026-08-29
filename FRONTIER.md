# π decimal disjunctivity frontier

Status: `conjecture`
Last audited: 2026-08-28 UTC

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

A new actual-π `proof sketch` gives useful but insufficient side
information. The published finite irrationality exponent forces a central
decimal-orbit return in every sufficiently large multiplicative time block;
the exact carrier recurrence then yields some adaptively selected complete
literal relative gain `C>4859/10000` at a time `q<=n<8q`. It does not retain
the prescribed target, imply either T189 sign, or stack without a lag-one
loss. A matching Kempner--Mahler continuation sharing 10015 π digits has
`mu=2`, infinitely many limit points and a scalar recurrence, yet eventually
makes every child of every coherent `334` descendant fail fresh positivity.
The live rung is therefore still prescribed-target complementary leakage and
old-score control for the same child. Constants and claim boundaries are in
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
