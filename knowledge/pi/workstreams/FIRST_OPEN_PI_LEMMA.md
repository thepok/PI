# First open π-specific rung

Claim status: `conjecture`.

For a positive natural-diagonal node `(q,A)`, let `C_r(q,A)` be the complete
fresh-block predecessor sector and

```text
P_r(q,A)=C_r(q,A)+conj(C_(10-r)(q,A)),  1≤r≤5.
```

The formerly preferred uniform local statement was

```text
for every q=10^k and every positive node (q,A),
exists r in {1,...,5}:
  Delta_0(q,A) + |P_r(q,A)|/2 > 21/(10q).          (Pair-π, false)
```

This uniform statement is false.  An independently reproduced directed-
interval `experiment` at the actual-π node `(q,A)=(1000,689)` has
`B(q,A,q)>80.21738`, but all five Pair-π margins are below `-6.21`.
Nevertheless literal FMR holds strongly and uniquely at `d=8`.  The favorable
coordinate is assembled from several character sectors; no individual paired
amplitude detects it.

The same node has a negative DC1 right side (about `-7199.927`) while
`max_d(D_d-(-G_d)_+)>11062.693`.  Thus a universal actual-π positivity claim
for the aligned DC1 premise is also false.  The deterministic DC1 inequality
remains valid and may still be useful on a path selected by independent
arithmetic.

The first honest arithmetic rung is now a path-constructing, target-signed
theorem for the complete same-child correlation.  Starting from an explicitly
proved positive seed, it must jointly produce digits `d_k` and nodes

```text
q_(k+1)=10*q_k,       A_(k+1)=A_k+d_k*q_k,
D_(k,d_k)>0,          G_(k,d_k)+D_(k,d_k)>0
```

for unbounded `k`.  A genuinely smaller multi-sector statistic is admissible
only if new actual-π arithmetic proves its signed bound and the statistic
retains enough relative phase to select the same digit.  Reconstructing all
ten `Xi_d`, or merely restating FMR, is not a new lemma.

A pathwise theorem is legitimate only when its statement constructs this
recursive selector and proves its invariants inductively.  Quantifying over
"reached nodes" assumes the missing transport and is circular.  Formal
Laurent nonvanishing, generic transcendence, unsigned energy, rational
shadows, and finite replay still do not supply the unbounded actual-π sign.

Research may replace Pair-π with a genuinely shorter aligned theorem that
directly yields FMR. It may not replace it by an equivalent normalization of
`Xi_d`, or assume the unbounded reached path that the transport must construct.

## Machine-checked foothold and exact remaining correlation

T194 now supplies one literal same-child foothold, conditional on the explicit
external premise `IrrationalityMeasureBelow pi 8`. After a
premise-dependent onset, for each `q=10^k` it chooses

```text
q+1 <= n < 10q,
A = floor(q*piOrbit n),
d = floor(10*piOrbit(n-1)),
C = A+d*q,
```

and proves a parent unit surplus `>3q/20` at `n` and a child unit surplus
`U>3q/2` at `m=n-1`. Both times lie in the exact fresh window and the centered
coordinate is preserved. The target and digit are adaptive, and the theorem
does not sign the full child block.

Let `R` be the surplus of the other `9q-1` child units in `[q,10q)`. Exact
block additivity gives

```text
D_d = U+R,
D_d>0 iff R>-U.
```

After subtracting the singleton T189 identity, `R` is exactly the deleted
zero-sector increment plus the target-rotated T179 lag-one correlation over
the other times. All information contained in the lifted central coordinate
has cancelled. Thus the first positive arithmetic rung is now especially
concrete: control that deleted actual-π correlation for the same T194-selected
digit, and simultaneously retain enough inherited capital for `G_d+D_d>0`.

The natural floor-only sufficient bound `R>=-3q/2` is already false on the
certified actual-π path: at `(q,A,d)=(100000,51334,1)`, the directed-interval
`experiment` has `R<-629252` while `-3q/2=-150000`. The full fresh block is
positive only because the actual lifted atom is much larger than its uniform
floor together with independent favorable complement information. Therefore
neither another central-chamber estimate nor formalizing the deletion identity
will advance the frontier; new target-signed π information must enter in the
remaining multi-time correlation.

## Direct flexible-horizon alternative

There is also a shorter route that bypasses T189, same-child transport, and
the later branching/coverage stage by proving each target separately.  As an audited `proof sketch`,
T148 and T156 imply the following strict weakening of the original flexible
summit.  For `k>=3`, `q=10^k`, `A<q`, and any `N>=q`, put

```text
P(q,A,N)=Re(primitiveBoundaryFourierSum(q,A,N)).
```

Then

```text
P(q,A,N) >= -122091/200000
```

already forces a visit to the literal `(q,A)` cylinder before `N`.  Indeed,
T148 is equivalent to

```text
P(q,A,N)+N*boundaryZeroCoefficient(q)/2
  >= 2*primitiveBoundaryEndpointBudget(q,A)-7/500,
```

while T156's scalar closure, nonnegativity of the zero coefficient, and
`N>=q` give the sufficient uniform right-hand side

```text
-861/1000 + 52909/200000 - 7/500
  = -122091/200000.
```

Thus proving this existential bound for every `(k,A)` would yield V1
directly.  It is weaker than demanding `P(q,A,N)>=0`, though at the price of a
stricter constant than T156's fixed natural-horizon `-861/1000` theorem.

Do not replace the flexible quantifier `exists N>=q` by one common natural
horizon and demand the T156 threshold for every target there.  That stronger
proxy is already false for actual pi.  At `Q=10000`, the T173-certified prefix
contains the four-digit block `0582` at both zero-based orbit indices `49` and
`131` (`experiment` read directly from the machine-checked digit literal).
Hence the first `Q` orbit points do not occupy `Q` distinct `Q`-cells, so at
least one cell is missed and its T156 sufficient threshold cannot hold.  The
same pigeonhole obstruction applies to any proposed common horizon of exactly
one orbit point per target cell after a repeated block.

The timed T194 return also does not seed this flexible target-fixed bound
(`proof sketch`, independently audited).  For a target `A` fixed before its
adaptive containing cell `A*` is observed, either `A*=A`, in which case the
return already is the desired hit, or the T128 boundary minorant centered at
`A` is strictly negative at that return.  For `A*` itself, T194 controls only
one increment
`P_(A*)(n+1)-P_(A*)(n)>7139/45000`; it supplies no lower bound on the preceding
prefix `P_(A*)(n)`.  Thus its timing and positive singleton yield neither a
new prescribed-target stopping law nor the flexible PBFS threshold without
an independent bound on the complete prefix or remainder.

Exact ray compression gives a useful stopping identity

```text
P(q,A,N)+N*c_q/2
 = (1/2)*sum_(n<N) boundaryKernel_q(x_n-c_(q,A))
   + V_(q,A)(x_0)-V_(q,A)(x_N).
```

Before the target cylinder is hit, the kernel sum is nonpositive, so this is
an upper bound by the terminal-potential drop, whereas T148 needs a lower
bound.  The missing input is therefore an independently sourced actual-π,
target-sensitive lower recurrence coupling that negative accumulation to the
terminal potential.  Merely rewriting the sum as the exact predecessor-digit
versus future-suffix correlation is circular.

The narrow orbit-universal obstruction is exact.  For every target one of
the decimal-map fixed points `1/9` or `2/9` lies strictly outside its cylinder
and has strictly negative compensated increment.  Hence no scalar potential
on the circle and positive variable block length can give a universal
Bellman lower certificate on all target-avoiding blocks.  This does not rule
out a π-specific theorem or arbitrary extended-state schemes.  Reopen the
direct route only with an input that distinguishes the actual π tail from
these fixed cycles and from sparse continuations sharing any prescribed
finite π prefix.

## Preferred aligned alternative

The audited decagon certificate `DC1` in [`T189_FMR_R1_R2.md`](T189_FMR_R1_R2.md)
reduces direct FMR at any fixed node to the strict estimate

```text
q*Delta_0 - 21/10 - hbar
  + gamma_10(hhat_1-(q/2)*P_1) > 0.                (Aligned-π)
```

DC1 is still a valid pathwise consumer when an arithmetic mechanism naturally
couples the past deficit profile to the fresh paired sector.  It is not a
uniform actual-π conjecture after the `(1000,689)` separator. Pair-π is no
longer an active fallback.
