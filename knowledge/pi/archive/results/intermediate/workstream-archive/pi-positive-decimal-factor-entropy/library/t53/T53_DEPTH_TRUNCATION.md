# T53: depth truncation for endpoint-complete carry/KMP graphs

Status: `proof sketch` for the new cross-depth arguments; `machine-checked` for
the cited T44, T46, and T48 theorems; `experiment` for every finite T52/T53
calculation.

## 1. Provenance and exact scope

- Canonical statement: `pi-positive-decimal-factor-entropy.txt`.
- Original source URL: none. The canonical question was formulated locally.
- Required and replayed SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Canonical question: whether one fixed `eta > 0` satisfies
  `p_pi(n) >= 10^(eta*n)` for every sufficiently large integer `n`.
- T53 scope: the sibling T44/T48 finite-core route toward C6, for an arbitrary
  fixed nonempty forbidden decimal word. T53 does not resolve the canonical
  question.

The new statements below are not Lean declarations. The replayed files
`T44EndpointSafeInvariantCore.lean`, `T46T46LiveSCC.lean`, and
`T48EndpointCarryKMP.lean` are byte-exact copies of the prior kernel-checked
dependencies. Their hashes are checked before every T53 replay.

## 2. Normalized quantifiers and ambiguities

Fix, throughout Sections 3-8,

1. a list `w : List (Fin 10)`;
2. a proof `w != []`;
3. an integer depth `R >= 0`.

Write `G_R(w)` for T48's `carryKMPGraph w hw R`. A raw state is

```text
(k_0,...,k_R; c_0,...,c_(R-1)),
```

where each `k_i` is a proper-prefix KMP state of `w` and every carry belongs to
the endpoint-complete set

```text
C = {-1,0,...,15,16}.
```

The graph also has one synthetic root. A digit column is
`d=(d_0,...,d_R)` with each `d_i` in `{0,...,9}`. An ordinary transition is
valid exactly when every KMP coordinate accepts its digit and, for every
`0 <= j < R`,

```text
16*d_j + c'_j = d_(j+1) + 10*c_j.                 (2.1)
```

An initial edge applies the same transition to empty KMP states and an initial
carry tuple recorded in its label.

The following distinctions are mandatory.

- T46's `SameSCC` is computed in the full declared graph. Its terminality
  predicate considers only reachable-live edges.
- Edges are label-sensitive. Distinct digit columns remain distinct edges even
  when source and target states agree.
- `Cyclic` means that a nonempty closed walk exists; a self-loop qualifies.
- A projected SCC may be only a strongly connected subset of a larger SCC.
- A `nonterminal_delay_corridor` is T52 terminology, not a T46 definition. It
  means the finite data specified in Section 6.2.
- A lift of one selected finite witness is not a classification of the whole
  next-depth graph.
- Finitely many compatible lifts are not an infinite compatible tower.

## 3. The depth truncation map

### 3.1 States

Let `i_K : Fin (R+1) -> Fin (R+2)` and
`i_C : Fin R -> Fin (R+1)` be the order-preserving inclusions that leave the
underlying natural number unchanged. For a depth-`R+1` raw state `q`, define

```text
rho_R(q).kmp(i)   = q.kmp(i_K(i)),
rho_R(q).carry(j) = q.carry(i_C(j)).
```

Thus `rho_R` deletes `k_(R+1)` and `c_R`. Define the graph-state map

```text
tau_R(root)   = root,
tau_R(raw(q)) = raw(rho_R(q)).
```

### 3.2 Columns and labels

For a depth-`R+1` digit column `d`, define

```text
delta_R(d)_i = d_i,  0 <= i <= R.
```

For an initial carry tuple `c=(c_0,...,c_R)`, define

```text
gamma_R(c)_j = c_j,  0 <= j < R.
```

The label map is

```text
lambda_R(initial(c,d)) = initial(gamma_R(c),delta_R(d)),
lambda_R(next(d))      = next(delta_R(d)).
```

For a high edge `e=(s,a,t)`, put

```text
E_R(e) = (tau_R(s),lambda_R(a),tau_R(t)).
```

These formulas include the synthetic root and initial labels; truncation is
not merely a map on raw ordinary edges.

### 3.3 Valid-edge theorem

**Proposition 3.1.** For every nonempty `w`, every `R >= 0`, and every valid
edge `e` of `G_(R+1)(w)`, `E_R(e)` is a valid edge of `G_R(w)`.

**Proof.** First case-split a valid high graph edge. T48's
`transition_from_root` says a valid edge from the root has an initial label and
exposes its underlying `RawStep`; `transition_from_raw` says a valid edge from
a raw state has a `next` label and exposes its underlying `RawStep`. For either
raw transition, T48's definition requires one KMP transition
at every coordinate `0,...,R+1` and equation (2.1) at every carry coordinate
`0,...,R`. Restrict the first family to `0,...,R` and the second to
`0,...,R-1`. These are exactly the depth-`R` requirements. For an initial
edge, restriction commutes with `initialRaw` because both retained KMP tuples
are identically the empty KMP state and the retained carry tuples are
`gamma_R(c)`. Finally use T48's `transition_initial_eq_some_iff` in the root
case and `transition_next_eq_some_iff` in the raw-state case. The impossible
root/`next` and raw-state/`initial` combinations were excluded by the initial
case split. QED.

The maps on declared state and label types are surjective and noninjective.
No path-lifting property follows from this type-level surjectivity.

## 4. Properties that project

Every statement in this section is universally quantified over nonempty `w`,
`R >= 0`, and the displayed states, edges, or walks.

**Proposition 4.1 (finite walks).** If `u` is a finite high edge list and

```text
G_(R+1).IsWalk(s,u,t),
```

then

```text
G_R.IsWalk(tau_R(s), map(E_R,u), tau_R(t)).
```

**Proof.** Induct on `u`, using Proposition 3.1 in the nonempty case. QED.

**Corollary 4.2 (reachability).**

```text
G_(R+1).Reaches(s,t) -> G_R.Reaches(tau_R(s),tau_R(t)).
```

Since `tau_R` fixes the root,

```text
G_(R+1).Reachable(s) -> G_R.Reachable(tau_R(s)).
```

**Corollary 4.3 (cyclicity).**

```text
G_(R+1).Cyclic(s) -> G_R.Cyclic(tau_R(s)).
```

The projected closed walk remains nonempty because edges are mapped rather
than erased.

**Proposition 4.4 (infinite walks and liveness).** If
`z : Nat -> G_(R+1).Edge` is an infinite walk from `s`, then
`n |-> E_R(z(n))` is an infinite walk from `tau_R(s)`. Consequently,

```text
G_(R+1).Live(s) -> G_R.Live(tau_R(s)).
```

This follows pointwise from Proposition 3.1 and preservation of successive
edge endpoints.

**Corollary 4.5 (SCC membership).**

```text
G_(R+1).SameSCC(s,t) -> G_R.SameSCC(tau_R(s),tau_R(t)).
```

Thus the image of one high SCC is strongly connected and lies in one low SCC.
It need not equal the entire low SCC, and distinct high SCCs may merge.

**Corollary 4.6 (reachable-live edges).** A high `ReachableLiveEdge` maps to a
low `ReachableLiveEdge`, by Proposition 3.1 and Corollaries 4.2 and 4.4.

**Proposition 4.7 (label languages).** Define

```text
Pi_R(x)(n) = lambda_R(x(n)).
```

Then

```text
x in G_(R+1).InfiniteLabelLanguage
  -> Pi_R(x) in G_R.InfiniteLabelLanguage.
```

The coordinate-zero digits are retained, so T48's evaluation also satisfies

```text
graphEvaluation(Pi_R(x)) = graphEvaluation(x).
```

This graph statement agrees with the machine-checked T44 theorem
`core_antitone_radius`:

```text
Core(w,R+1) subset Core(w,R).                         (4.1)
```

## 5. Failures of reflection and SCC identity

No converse in Section 4 is asserted for an arbitrary state in a truncation
fiber.

### 5.1 Reachability does not reflect to every fiber

For `w=00`, the depth-one raw state

```text
((0,1); -1)
```

is absent from the exhaustively generated reachable graph, while its
depth-zero projection `((0); ())` is reachable. Replay checks both complete
finite graphs. Thus reachability of a low state does not make every high state
over it reachable.

### 5.2 Liveness and cyclicity do not reflect to every fiber

For `w=0`, both depth-one states

```text
((0,0); -1),   ((0,0); 16)
```

are reachable but dead. Section 7 shows that all subsequent digits from carry
`-1` would have to be `(0,9)`, rejected in coordinate zero, while all
subsequent digits from carry `16` would have to be `(9,0)`, rejected in
coordinate one. Their common depth-zero projection is live and cyclic.

A stronger path-lifting failure uses the valid depth-zero digit path

```text
1,3,1,3
```

for `w=0`. Starting from all 18 possible hidden carries, exact propagation of
the added avoiding digit and carry recurrence leaves respectively

```text
16, 13, 2, 0
```

possible hidden states. Hence this four-edge low path has no high lift from
any state in its initial fiber. The full surviving sets are recorded in
`t53_certificates.json`.

### 5.3 Distinct high SCCs can merge

For `w=01` at depth one, consider

```text
q_A = ((0,1);16),
q_B = ((0,0);5).
```

Both are reachable and cyclic. State `q_A` has the forced endpoint loop with
digit column `(9,0)`; `q_B` has a loop with digit column `(3,3)`. Carry `16`
can never leave `16`, so `q_A` cannot reach `q_B`; exhaustive SCC computation
places them in distinct high SCCs. Both project to the same depth-zero raw
state `((0);())`. Therefore SCC identity and maximality do not project.

## 6. Exact behavior of T46 obstruction witnesses

### 6.1 Branching cyclic SCC witnesses

A displayed branching witness consists of:

1. a root path to a state `s`;
2. two distinct internal first edges `e_1,e_2` from `s`;
3. a return path after each first edge, producing two nonempty closed walks
   from `s` to `s`.

By Section 4, all paths and closed walks project. The projected data is again a
branching witness at `tau_R(s)` **if and only if**

```text
E_R(e_1) != E_R(e_2).                               (6.1)
```

If (6.1) holds, both projected first edges are distinct reachable-live
internal edges in the low SCC, violating T46's edge-sensitive
`SimpleDirectedCycleSCC`. If (6.1) fails, this particular displayed branch
collapses. Another low obstruction may still exist.

An explicit collapse occurs for `w=0`, depth two to depth one, at

```text
s = ((0,0,0);5,5).
```

It is reached from initial carries `(2,2)` with digit column `(1,1,1)`. Two
closed walks from `s` have columns

```text
(331),(325),(224),(611)
(332),(321),(255),(895),(777).
```

Replay checks every KMP transition, carry equation, and return to `s`. The
first edges differ only in their deleted final digit, and both projected
targets retain carry `5`; therefore both first edges project to the same low
edge labelled `(3,3)`. The displayed high branch does not project as a branch.

### 6.2 Nonterminal delay corridors

T52's finite corridor data consists of:

1. a root path to a state `s` in a cyclic SCC `S`;
2. a reachable-live edge `e : s -> t` with `t` outside `S`;
3. a path from `t` to a displayed nonempty closed walk.

All displayed paths project. The projected data remains a nonterminal corridor
exactly when

```text
not G_R.SameSCC(tau_R(s),tau_R(t)).                 (6.2)
```

If (6.2) holds, the projected edge is a reachable-live exit from the projected
cyclic SCC. If (6.2) fails, it becomes internal and this particular
terminality violation disappears.

For `w=010`, depth two to depth one, let

```text
s = ((1,1,0);0,1).
```

The columns `(000),(062),(444),(001)` form a closed walk at `s`. The edge

```text
s --(006)--> t = ((1,1,0);0,16)
```

is live: columns `(090),(690),(290),(490)` reach
`u=((0,0,1);15,16)`, which has a `(990)` self-loop. Carry `16` prevents return
from `t` to `s`. After truncation, however, `s` and `t` are the same low state
and `(006)` becomes a low self-loop `(00)`. The displayed corridor collapses.

Therefore neither a particular branching SCC witness nor a particular delay
corridor forms an automatic inverse system under depth truncation.

## 7. Endpoint carry laws

Fix any valid raw edge, any carry coordinate, and abbreviate

```text
a=d_j, b=d_(j+1), c=c_j, c'=c'_j.
```

Here `0 <= a,b <= 9`, `-1 <= c,c' <= 16`, and

```text
16*a + c' = b + 10*c.                              (7.1)
```

**Proposition 7.1 (lower endpoint).**

```text
c=-1 -> (a,b,c')=(0,9,-1).
```

**Proof.** Equation (7.1) becomes `16*a+c'=b-10`. Since `c' >= -1`,
`16*a <= b-9 <= 0`, hence `a=0`. Now `c'=b-10 >= -1`, so `b=9` and
`c'=-1`. QED.

**Proposition 7.2 (upper endpoint).**

```text
c=16 -> (a,b,c')=(9,0,16).
```

**Proof.** Equation (7.1) becomes `16*a+c'=b+160`. Since `c' <= 16`,
`16*a >= b+144 >= 144`, hence `a=9`. Now `c'=b+16 <= 16`, so `b=0` and
`c'=16`. QED.

Thus both endpoint carries are forward absorbing, with forced adjacent digit
pairs. They are not backward absorbing:

```text
(c,a,b,c')=(7,5,9,-1),
(c,a,b,c')=(8,4,0,16)
```

both satisfy (7.1). Replay exhausts all `18*10*10*18` bounded quadruples and
finds exactly the asserted endpoint solutions.

The endpoint states are genuine states of the graph used by T48. For `w=01`,
the accepted loops

```text
((1,0);-1) --(0,9)--> ((1,0);-1),
((0,1);16) --(9,0)--> ((0,1);16)
```

encode the endpoint real identities `16*0 = 1+(-1)` and `16*1 = 0+16`, which
agree on the circle. T48's machine-checked `graphEvaluation_image_eq_core`
applies to this endpoint-complete graph. Removing the states defines a
different graph for which no corresponding image equality is established
here; one cannot cite T48's theorem after making that removal.

## 8. Strict finite one-step lift-or-death certificates

### 8.1 Definition

For one fixed T52 witness at depth `R`, a **strict finite-diagram lift** assigns
one hidden pair

```text
(k_(R+1),c_R) in {0,...,|w|-1} x {-1,...,16}
```

to every distinct raw state in the paths stored by T52. The same stored state
must receive the same pair in every occurrence and every stored path. Hence
stored path joins and stored closed-walk endpoints are preserved globally, not
occurrence by occurrence.

For an ordinary displayed edge whose last retained digit is `a`, a source
fiber `(k,c)` and target fiber `(l,c')` are compatible exactly when there is an
added digit `b` such that

```text
l = KMP_w(k,b) < |w|,
c' = b + 10*c - 16*a.                              (8.1)
```

The digit `b` is unique when the two carries and `a` are fixed. For an initial
edge, hidden source KMP state is zero and one also chooses an initial hidden
carry `u`:

```text
l = KMP_w(0,b) < |w|,
c' = b + 10*u - 16*a.                              (8.2)
```

For a corridor, the stored T52 paths display only the target-side cycle.
Therefore the checker independently constructs the product of the low source
SCC with the `18*|w|`-element fiber, computes every product SCC, and restricts
the assigned lifted exit source to product states lying on a nonempty closed
walk. A successful corridor certificate includes such a source-side high
closed walk based at that assigned source. Intermediate states on this added
walk are ordinary high states and may be different high fibers over the same
low state; they are not extra variables in the stored-path diagram.

### 8.2 Exhaustiveness of a death certificate

The checker begins with the complete `18*|w|`-element domain at every
displayed state. It intersects initial-edge and loop constraints and repeatedly
deletes a fiber value whenever no currently possible value at the adjacent
state satisfies (8.1). Every deletion is sound by induction: an actual global
assignment would supply the missing adjacent support. Thus an empty domain
proves that no strict lift of this finite diagram exists. All 13 reported
deaths reach an empty domain by this propagation alone. The checker also has a
deterministic exhaustive search fallback, but no reported death depends on an
unlogged heuristic cutoff.

A death certificate says only:

```text
this selected finite witness diagram has no strict one-step lift.
```

It does **not** say that the next-depth graph is good or lacks a different bad
SCC. For example, a selected `w=0`, depth-zero witness dies even though T52
separately displays a bad `w=0`, depth-one graph.

### 8.3 Replayed results

The input contains 16 completed negative T52 instances and one depth-three
resource-frontier row. Only the completed witnesses are checked.

| T52 order | word | depth | witness | strict one-step result |
|---:|---:|---:|---|---|
| 0-9 | `0` through `9` | 0 | branching | death (10 instances) |
| 10 | `0` | 1 | branching | death |
| 11 | `00` | 1 | branching | death |
| 12 | `01` | 1 | corridor | lift |
| 13 | `010` | 1 | corridor | lift |
| 14 | `0` | 2 | branching | death |
| 15 | `010` | 2 | corridor | lift |

Totals: 16 checked, 3 strict lifts, 13 strict deaths. For each lift,
`t53_certificates.json` records every hidden state, added digit, added initial
carry, lifted displayed path, and lifted source-side cycle. For each death it
records the finite fiber ordering, relation hashes and counts, every domain
reduction, and an empty final domain. Replay recomputes rather than trusts
these fields.

The T52 order-16 row `w=010, R=3` is a state-cap frontier with no mathematical
verdict. It is neither lifted nor called dead.

## 9. Cross-depth consequences

### 9.1 The unconditional monotonic implication available from T44/T48

T48 machine-checks, for every nonempty `w` and finite `R`,

```text
Core(w,R) finite <-> G_R(w).LiveSCCCriterion.       (9.1)
```

Combining (9.1) with T44's machine-checked inclusion (4.1) gives

```text
G_R(w).LiveSCCCriterion
  -> G_(R+1)(w).LiveSCCCriterion.                   (9.2)
```

Indeed, a subset of the finite set `Core(w,R)` is finite. Equivalently,

```text
not G_(R+1)(w).LiveSCCCriterion
  -> not G_R(w).LiveSCCCriterion.                   (9.3)
```

Statement (9.3) guarantees that the low T46 criterion fails when the high graph
is bad. It does not by itself select or decompose a finite branch/corridor
certificate. Sections 5-6 show why it cannot identify a low violation with the
direct projection of a chosen high branch or corridor.

### 9.2 Conditional compatible obstruction tower

Define a **compatible obstruction tower for `w`** to be finite T46 violation
certificates `W_R` for every `R >= R_0`, together with strict diagram maps
showing that `W_(R+1)` truncates to `W_R`. If such a tower exists, then,
conditionally:

1. every `G_R(w)` for `R >= R_0` fails the T46 criterion;
2. every corresponding `Core(w,R)` is infinite, hence nonempty, by the
   machine-checked T48 equivalence;
3. T44 makes these cores closed and antitone; every finite subfamily has
   intersection equal to its largest-depth nonempty member, so compactness of
   the circle and the finite-intersection property give a point in the total
   intersection;
4. no finite depth gives a finite core for this word.

Per-depth badness drives these consequences; compatibility is the additional
structure needed to call the witnesses a tower. Such a tower would refute
T44's universal finite-core hypothesis for that word, but it
would not imply that C6 fails: T44 supplies a sufficient implication toward
C6, not an equivalence. The three bounded T53 lifts are not such a tower.

### 9.3 Conditional linearly bounded lift rank

Suppose, as an additional unproved hypothesis, that there are real constants
`A >= 0` and `B` such that `A*|w|+B >= 0` for every nonempty `w`, and that both
properties below hold for every nonempty `w`:

1. **descent completeness:** if `G_R(w)` is bad, there are finite T46
   obstruction certificates `(W_0,...,W_R)`, with `W_r` at depth `r` and
   `W_(r+1)` truncating to `W_r` for every `r<R`;
2. **rank bound:** define the height of any compatible chain
   `(W_0,...,W_H)` to be its maximum depth `H`; every such chain has height
   `H <= floor(A*|w|+B)`.

Then `G_N(w)` is good for

```text
N = floor(A*|w|+B) + 1,
```

because a bad graph there would, by descent completeness, produce a chain of
height `N`, strictly larger than the rank bound. Moreover

```text
N <= A*|w| + (B+1).
```

By (9.1), `Core(w,N)` is finite. Thus these two extra hypotheses would imply
T44's uniform linear finite-core premise with adjusted additive constant and,
through T44's machine-checked conditional theorem, would imply C6. T53 does
not establish descent completeness or the rank bound.

## 10. Replay

From a directory containing only the delivered artifacts, run:

```sh
sh ./verify.sh
```

The command verifies all pinned inputs, regenerates
`t53_certificates.json` byte-for-byte in a temporary artifact-only directory,
rebuilds every completed T52 graph and witness, and replays all endpoint,
projection-counterexample, product-SCC, and lift-or-death checks.

## 11. Claim ledger

- `machine-checked`: the cited T44 antitonicity and conditional C6 theorem,
  T46 graph criterion, and T48 graph/core equivalences, subject to their exact
  statements in the pinned Lean files.
- `proof sketch`: Propositions 3.1, 4.1, 4.4, 4.7, the witness-projection
  criteria, endpoint algebra, and conditional tower/rank deductions in this
  note.
- `experiment`: all 16 T52 witness replays, all three finite lifts, all 13
  finite deaths, and every explicit bounded graph counterexample.
- No claim: universal extinction, C6 for pi, C1, positive decimal factor
  entropy for pi, or decimal disjunctivity.
