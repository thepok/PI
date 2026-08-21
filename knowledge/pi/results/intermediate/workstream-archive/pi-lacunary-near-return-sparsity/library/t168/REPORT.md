# T168: mixed-lag collision clusters of order at most three

Date: 2026-08-13 UTC.

This is a `proof sketch` with a self-contained finite `experiment`.  Every
general assertion below is proved in the note; the program is only a
completeness check on bounded instances.  No external mathematical theorem is
used.  The T161 note is unverified, so its same-lag quantity is rederived here
rather than imported as a premise.

```text
CANONICAL_SHA256: cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
PATTERN_TABLE_ROWS: 10
SCOPED_ENDPOINT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, normalized statement, and ambiguities

The byte-exact canonical statement is vendored as `canonical_statement.txt`.
It asks about ordered, diagonal-inclusive metric near returns in the fixed
decimal orbit of pi.  This note does not answer or alter that question.  It
studies the A10/A13/A14 sibling consisting of exact equal-word events in one
iid uniform decimal word.

The following conventions remove the ambiguous quantifiers.

1. Integers `N>=2` and `m>=1` are fixed.  There are exactly `N` legal starts
   and exactly `L=N+m-1` iid digits.  All intervals below are inclusive.
2. A primitive event is an unordered off-diagonal pair of starts.  A cluster
   is a set, not a tuple, of two or three distinct primitive events.
3. Two events are adjacent exactly when their digit supports intersect.  A
   cluster is connected when this event-dependency graph is connected.  This
   is stronger than merely sharing an event endpoint and includes translated
   overlapping events with four different starts.
4. A mixed-lag cluster has at least two distinct positive lags.  Thus every
   all-same-lag set is excluded, in particular every same-lag translation chain
   treated in the unverified T161 note.
5. Shapes are quotiented only by common translation, not by reflection or
   relabeling of the integer line.  Events themselves and clusters are
   unordered.  This convention makes the embedding multiplicity exact.
6. `Intensity` means expected number of active embeddings of an exact shape.
   It is not a Poisson parameter, cumulant, or maximal-cluster rate.
7. The required uniform regime is
   `1<=m<=floor((1/4)log_10 N)`.  It is nonempty only when `N>=10^4`.

## 2. Exact model and endpoints

Let `X_0,...,X_(L-1)` be independent and uniform on `{0,...,9}`.  For
`0<=i<N`, define

```text
B_i=[i,i+m-1],                  W_i=(X_i,...,X_(i+m-1)),
Alpha_N={{i,j}:0<=i<j<N},       I_{i,j}=1[W_i=W_j].       (2.1)
```

The last legal block ends at `(N-1)+(m-1)=L-1`.  For an event
`e={i,j}` with `i<j`, its positive lag and digit support are

```text
d(e)=j-i,                       S(e)=B_i union B_j.        (2.2)
```

The ordered, diagonal-inclusive collision count is reconstructed exactly by

```text
E=N+2*sum_(e in Alpha_N) I_e.                            (2.3)
```

Diagonals are deterministic and do not occur in a cluster.

## 3. Shapes, the two graphs, rank, and multiplicity

An exact normalized shape is a finite event set

```text
F subset {{a,b}:0<=a<b},       min union_(e in F)e=0,     (3.1)
```

with `|F|` equal to two or three.  Put

```text
A(F)=union_(e in F)e,           s(F)=max A(F).             (3.2)
```

There are two different finite graphs, both needed for an inspectable
classification.

* The block-incidence graph `H(F)` has vertex set `A(F)` and edge set `F`.
* The event-dependency graph `D_m(F)` has vertex set `F`; distinct `e,f` are
  adjacent when `S(e) intersect S(f)` is nonempty, with supports computed at
  the normalized starts.

The equality graph `G_m(F)` has digit vertices

```text
U_m(F)=union_({a,b} in F)([a,a+m-1] union [b,b+m-1])      (3.3)
```

and an undirected edge `{a+r,b+r}` for each `{a,b} in F` and `0<=r<m`.
Parallel equality edges are ignored.  If `c_m(F)` is the number of connected
components of `G_m(F)`, define

```text
R_m(F)=|U_m(F)|-c_m(F).                                  (3.4)
```

This is an exact finite formula, not an asymptotic rank surrogate.

### Rank and probability theorem

For every shape `F`,

```text
P(I_e=1 for every e in F)=10^(-R_m(F)).                  (3.5)
```

**Proof.** The active event equations are exactly the edges of `G_m(F)`.
Digits must be constant on each connected component, and this condition is
sufficient.  There are `10^c_m(F)` satisfying assignments on the
`|U_m(F)|` involved digits out of `10^|U_m(F)|` total assignments.  Digits
outside `U_m(F)` cancel.  This proves (3.5).  The proof applies without change
to every row of the table in Section 4.  QED.

### Embedding and intensity theorem

For a normalized shape `F`, all its embeddings in the `N` legal starts are
exactly

```text
F+t={{a+t,b+t}:{a,b} in F},       0<=t<N-s(F).            (3.6)
```

Consequently its exact embedding multiplicity and intensity are

```text
M_N(F)=(N-s(F))_+,
nu_(N,m)(F)=(N-s(F))_+ * 10^(-R_m(F)).                   (3.7)
```

**Proof.** Translation by `t` has least start `t` and greatest start
`t+s(F)`, so legality is equivalent to `0<=t<N-s(F)`.  Normalizing any legal
embedding by subtracting its least start recovers `F` and its unique `t`.
Translation preserves the equality graph and hence (3.5).  Linearity of
expectation proves (3.7), with no independence assertion between embeddings.
QED.

Two useful checks follow immediately.  If the intervals `B_a`, `a in A(F)`,
are pairwise disjoint and `H(F)` is connected on `k=|A(F)|` block starts, then
`R_m(F)=(k-1)m`: choose one free length-`m` word and equate each of the other
`k-1` words to it along a spanning tree.  Also, `R_m(F)` is independent of
which redundant edges of a connected `H(F)` are retained, because all block
words in one incidence component are equal transitively.

## 4. Complete parametric pattern table

For a graph name, `+` denotes disjoint union.  `2K2` is two disjoint edges,
`3K2` is a three-edge matching, `Pj` is the path on `j` vertices, `K1,3` is
the three-leaf star, and `K3` is the triangle.  Every row also carries the
explicit conditions

```text
D_m(F) connected, |{d(e):e in F}|>=2, min A(F)=0.        (4.1)
```

Each row is a parametric family, not one integer shape: it consists of all
normalized integer event sets satisfying the displayed pair of graph types and
(4.1).  Consequently every relative displacement, including displacements
larger than `m`, remains an explicit parameter of `F`; it enters the span
`s(F)`, equality graph, and rank.  The rank, multiplicity, and intensity
columns are exact formulas for every integer shape in that family.

| row | events | block-incidence `H(F)` | dependency `D_m(F)` | rank | multiplicity | intensity |
|---|---:|---|---|---|---|---|
| M2-D | 2 | `2K2` | `K2` | `R_m(F)` by (3.4) | `(N-s(F))_+` | `(N-s(F))_+10^-R_m(F)` |
| M2-W | 2 | `P3` | `K2` | same | same | same |
| M3-M-P | 3 | `3K2` | `P3` | same | same | same |
| M3-M-K | 3 | `3K2` | `K3` | same | same | same |
| M3-WD-P | 3 | `P3+K2` | `P3` | same | same | same |
| M3-WD-K | 3 | `P3+K2` | `K3` | same | same | same |
| M3-P-P | 3 | `P4` | `P3` | same | same | same |
| M3-P-K | 3 | `P4` | `K3` | same | same | same |
| M3-S | 3 | `K1,3` | `K3` | same | same | same |
| M3-T | 3 | `K3` | `K3` | same | same | same |

Rows M3-S and M3-T cannot have dependency graph `P3`: respectively all events
share the center block or every pair shares a block.  All other displayed
dependency alternatives occur.  Here are explicit witnesses `(m,F)`; direct
interval intersection checks give the displayed dependency graph, and their
lags visibly contain at least two values:

```text
M2-D    (2, {{0,3},{1,2}})          M2-W    (1, {{0,1},{0,2}})
M3-M-P  (2, {{0,1},{2,4},{3,5}})    M3-M-K  (2, {{0,2},{1,4},{3,5}})
M3-WD-P (2, {{0,1},{0,2},{3,4}})    M3-WD-K (2, {{0,1},{0,3},{2,4}})
M3-P-P  (1, {{0,1},{0,2},{1,3}})    M3-P-K  (2, {{0,1},{0,2},{1,3}})
M3-S    (1, {{0,1},{0,2},{0,3}})    M3-T    (1, {{0,1},{0,2},{1,2}}).
```

### Completeness proof

For two distinct simple edges, the incidence graph is either `2K2` or `P3`.
Connectivity forces the only two-vertex dependency graph `K2`, giving the
first two rows.

For three distinct simple edges, sort the incidence-component edge counts.
If they are `1+1+1`, the graph is `3K2`; if `2+1`, the two-edge component is
`P3`, giving `P3+K2`; and if all three edges lie in one component, a connected
simple graph with three edges is exactly `P4`, `K1,3`, or `K3`.  A connected
simple graph on three event vertices is exactly `P3` or `K3`.  Taking the
feasible cross-products, and deleting the impossible star-path and
triangle-path combinations, gives exactly the eight three-event rows shown.
Condition (4.1) deletes every all-same-lag case but creates no new graph type.
Thus the ten parametric families are exhaustive and disjoint: every exact
integer shape falls in exactly one family, while its normalized coordinates
remain in `F`.  Equations (3.4)--(3.7) then prove rank, probability, embedding
multiplicity, and intensity for every exact shape in every family.  QED.

The exact total mixed-lag intensity classified here is therefore the finite
sum

```text
Nu_mix(N,m)=sum_F (N-s(F))*10^(-R_m(F)),                 (4.2)
```

where `F` ranges once over normalized shapes satisfying (4.1), `|F|` is two
or three, and `s(F)<N`.  Formula (4.2), together with the table, is also a
nonredundant definition: normalization makes the translation orbits disjoint.

## 5. Infinite mixed-lag triangle counterfamily

Take starts `0<=x<y<z<N` with

```text
y-x>=m,                         z-y>=m,                  (5.1)
```

and the three events

```text
{{x,y},{x,z},{y,z}}.                                        (5.2)
```

This is row M3-T.  Its lags are `y-x`, `z-y`, and `z-x`; since the last is
strictly larger than each of the first two, it is mixed-lag.  Its dependency
graph is `K3` because each pair of events shares one whole block.  The three
block intervals are disjoint by (5.1).  All three events are active exactly
when three independent length-`m` words are equal.  Hence its equality graph
has `3m` vertices, `m` components, and

```text
R_m=2m,                          P(all active)=10^(-2m).  (5.3)
```

The substitution

```text
(x,y,z) -> (x, y-(m-1), z-2(m-1))                       (5.4)
```

is a bijection from triples satisfying (5.1) to ordinary three-subsets of
`{0,...,N-2m+1}`.  Therefore this subfamily alone has exact intensity

```text
J_triangle(N,m)=binom(N-2m+2,3)*10^(-2m),                (5.5)
```

with the binomial interpreted as zero when its top is below three.

This is an explicit infinite counterfamily of exact patterns, not a finite
experiment.  It also shows why a table indexed only by event-support topology
is insufficient: the equality rank supplies the decisive `10^-2m` weight.

## 6. Uniform comparison with the same-lag mechanism

For comparison in the same units, fix a lag `1<=d<N` and write
`Y_(d,i)=I_{i,i+d}` for `0<=i<N-d`.  A maximal nonempty same-lag translation
chain is a maximal consecutive run of ones in this row.  Equivalently its root
is an index `i` with `Y_(d,i)=1` and either `i=0` or `Y_(d,i-1)=0`.  Every
active event belongs to exactly one such run.  Let `Lambda_SL(N,m)` be the
expected total number of these roots over all lags.  This is the total
same-lag maximal-chain intensity considered in the unverified T161 note, but
we rederive it here.

The root at `i=0` has probability `q^m`, where `q=1/10`.  For `i>0`, the two
same-lag translated events form a rank-`m+1` chain, so
`P(Y_(d,i-1)=Y_(d,i)=1)=q^(m+1)` and the root probability is
`q^m(1-q)`.  There is one boundary root candidate and `N-d-1` interior root
candidates in lag row `d`.  Summing the arithmetic progression gives the exact
formula

```text
Lambda_SL(N,m)
 =10^-m*[(N-1)+(9/10)(N-1)(N-2)/2]
 <=binom(N,2)*10^-m.                                    (6.1)
```

The inequality also follows pointwise because the number of chains is at most
the number of active events.  Thus no claim from T161 is a premise here.

Now assume the full mandated range

```text
N>=10^4,                    1<=m<=floor((1/4)log_10 N).  (6.2)
```

Then `10^-m>=N^-1/4`.  Also `N-2m+2>=N/2`; for example
`m<=log_10(N)/4<=N/4+1` in this range.  Writing `M=N-2m+2`, we have
`M>=N/2`, `M-1>=N/4`, and `M-2>=N/4`, so

```text
binom(M,3)>=N^3/192.                                     (6.3)
```

Equations (5.5), (6.1), and `binom(N,2)<=N^2/2` give the uniform quantitative
comparison

```text
Nu_mix(N,m)/Lambda_SL(N,m)
 >=J_triangle(N,m)/Lambda_SL(N,m)
 >=(N^(3/4))/96.                                         (6.4)
```

The denominator is positive.  Thus the total mixed-lag intensity is not
negligible relative to the same-lag maximal-chain intensity; it exceeds it by
a factor tending to infinity as `N` tends to infinity, uniformly over every
allowed `m`.  This conclusion concerns the raw expected count of active connected
subsets defined in Section 1.  It is not, without a separate signed cluster
expansion, a claim about a factorial cumulant, total variation distance, or
maximal mixed-cluster process.  In particular, overlapping triangle subsets
inside a larger occupied block class are intentionally counted separately by
the agenda's pattern intensity.

For orientation, the T161 note argues (unverified) that its same-lag compound-
Poisson second factorial cumulant is asymptotic to `(2/9)binom(N,2)10^-m`.
Nothing in (6.4) assumes that claim, and the counterfamily remains larger even
if the full upper bound (6.1) is used.

## 7. Replayable completeness check

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t168.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

Except for selecting a bounded test grid, the script uses exact integer and
rational arithmetic.  It enumerates all
two- and three-event subsets for `2<=N<=7` and `1<=m<=3`, normalizes translation
orbits, independently checks support connectivity and mixed lags, verifies
that exactly one table row accepts each shape, verifies the rank and
multiplicity formulas computationally for every legal embedding, tests the
rank/probability identity by exhaustive binary words for ten representative
instances, produces a witness for all ten rows, checks (5.5) by direct
enumeration, and checks (6.4) over a
bounded grid in the required range.  These finite checks are an `experiment`,
not the completeness or asymptotic proof.

## 8. Separate unproved pi-specific transfer premise

**PI_MIXED_PATTERN_OCCUPANCY (`unproved pi-transfer requirement`; NOT
ASSERTED).**  A transfer of this iid classification toward T7 would require a
named increasing sequence of actual pi prefixes and a simultaneous empirical
occupancy theorem for every normalized shape in (4.2), with errors summable
after the exact multiplicities `(N-s(F))_+` and with an appropriate treatment
of larger clusters.  It would also require a proved conversion from exact
equal decimal blocks to T7's metric near-return event, including decimal
endpoints and carries.  The iid probabilities (3.5), the finite replay, and
the counterfamily do not establish this premise for pi.

No fixed-pi, A1, C1, or C2 claim is made.

## 9. Single conclusion

SCOPED_ENDPOINT (1/1): **COUNTERFAMILY**.

The ten-row parametric table assigns every stated iid mixed-lag cluster of
order at most three to exactly one family while retaining its exact integer
coordinates.  The disjoint-block triangle family has exact
intensity (5.5) and satisfies the uniform lower comparison (6.4), so mixed-lag
patterns are not negligible relative to T161's same-lag maximal-chain scale in
the mandated depth range.  This closes only the proposed iid low-order raw-
pattern negligibility test.  It does not close G28, justify a signed or maximal
mixed-cluster approximation, or assert anything about the digits of pi.
