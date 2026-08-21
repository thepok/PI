# T172: fourth cumulant and failure of occupancy-only clique absorption

Date: 2026-08-13 UTC.

Status: `proof sketch`. Every universal assertion used for the endpoint is
proved in prose below. `verify_t172.py` is a bounded `experiment`: it checks
the algebra and searches finite signature ranges, but finite checking is not a
proof. The deductions in T159 and T161 are `proof sketch` even though those
notes contain separately `literature-checked` source claims; T168 and T170 are
`proof sketch` with finite `experiment`. They are motivation only. T171 is
active but has no readable artifact in this snapshot, so no claim from it is
used or inferred.

```text
CANONICAL_SHA256: cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
REPETITION_STRATA: 5
FOURTH_CUMULANT_FORMULA: complete
EXACT_FALSIFYING_SIGNATURE: triangle-with-tail
SCOPED_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, normalized statement, and ambiguities

The byte-exact canonical statement is vendored as `canonical_statement.txt`.
It asks about ordered, diagonal-inclusive metric near returns in the fixed
decimal orbit of pi. T172 does not alter or answer it. T172 studies only the
A10/A13/A14 sibling of exact equal blocks in an iid uniform decimal word.

The following conventions are binding.

1. Integers `N>=2` and `m>=1` are fixed. There are exactly `N` legal starts and
   exactly `L=N+m-1` digits. Blocks are nonwrapping and unpadded.
2. Primitive collision events are indexed by unordered off-diagonal start
   pairs. Cumulant slots are ordered; conversion to event sets or multisets is
   made only with explicit multinomial coefficients.
3. A normalized event shape is quotiented only by common translation, not by
   reflection. Its least endpoint is zero.
4. "Connected" means connected in the event-dependency graph: two events are
   adjacent when their digit supports intersect. Endpoint-incidence,
   event-dependency, and digit-equality graphs are distinct.
5. "Occupancy-clique resummation" here has one precise meaning. Replace any
   event graph on block starts by the complete clique on each endpoint-incidence
   component, using transitivity of word equality, and then assign moments as
   if the involved length-`m` words were independent categorical variables.
   The first replacement is an exact logical identity. The second assignment
   is the occupancy-only hypothesis tested and falsified below.
6. The logarithmic-depth regime is
   `N>=10^4` and `1<=m<=floor((1/4)log_10 N)`. The lower bound on `N` follows
   because this depth range is otherwise empty.
7. "Signature classification" means an exact parameterized partition retaining
   the normalized integer event list. It is not a finite list of coarse graph
   isomorphism types, which would lose equality ranks.

## 2. Model, endpoints, and ordered reconstruction

Let `D={0,...,9}` and let

```text
X_0,...,X_(L-1) iid uniform on D,                 L=N+m-1,
B_i=[i,i+m-1],
W_i=(X_i,...,X_(i+m-1)),                          0<=i<N,
E_N={{i,j}:0<=i<j<N},                             M=binom(N,2),
I_{i,j}=1[W_i=W_j],
U_(N,m)=sum_(e in E_N) I_e.                              (2.1)
```

The last legal block ends at `(N-1)+(m-1)=L-1`. For `e={i,j}` its positive
lag is `j-i` and its exact digit support is `B_i union B_j`; a gap between two
disjoint blocks is not support.

The ordered off-diagonal count is `2U`. Restoring all `N` deterministic
diagonal pairs gives

```text
C_(N,m)=N+2U_(N,m).                                      (2.2)
```

Ordinary cumulants of order at least two are translation invariant and
homogeneous, so

```text
kappa_4(C_(N,m))=16*kappa_4(U_(N,m)).                    (2.3)
```

Equation (2.3) is deterministic conversion; the reversed ordered events are
not treated as independent.

## 3. Equality graph, rank, probability, and multiplicity

For a nonempty finite event set `F`, form `G_m(F)` with the digit positions
used by `F` as vertices and an undirected edge

```text
{a+r,b+r},                 {a,b} in F, 0<=r<m.            (3.1)
```

Parallel edges are discarded. Let `v_m(F)` and `c_m(F)` be its vertex and
component counts and put

```text
r_m(F)=v_m(F)-c_m(F).                                    (3.2)
```

### Lemma 3.1 (rank probability)

```text
P(I_e=1 for all e in F)=10^(-r_m(F)).                    (3.3)
```

**Proof.** The constraints say exactly that every digit is constant on each
component of `G_m(F)`. There are `10^c` satisfying assignments to its `v`
vertices out of `10^v`; unused digits cancel. QED.

A single event has rank `m`, including overlapping blocks: its edges join
forward positions in residue chains modulo the lag and form a forest of `m`
edges. Thus every `I_e` has mean

```text
p=10^(-m).                                                (3.4)
```

For an exact normalized shape `F`, define its span

```text
s(F)=max union_(e in F)e.                                 (3.5)
```

Its legal embeddings are exactly `F+t`, `0<=t<N-s(F)`. Hence its translation
multiplicity is

```text
M_N(F)=(N-s(F))_+.                                       (3.6)
```

**Proof.** The least translated endpoint is `t` and the greatest is `t+s(F)`;
legality is exactly `0<=t` and `t+s(F)<N`. Subtracting the least endpoint from
any embedding recovers the unique normalized shape and translation. QED.

## 4. Ordinary fourth joint cumulant

For four labeled random variables, the set-partition formula specializes to

```text
kappa(Y1,Y2,Y3,Y4)
 =E[Y1Y2Y3Y4]
  -sum_i E[Yi]E[product_(j!=i)Yj]
  -sum_(12|34,13|24,14|23) E[YiYj]E[YkYl]
  +2 sum_(six pairs {i,j}) E[YiYj]E[Yk]E[Yl]
  -6 product_i E[Yi].                                    (4.1)
```

Multilinearity gives the complete ordered expansion

```text
kappa_4(U)=sum_((e1,e2,e3,e4) in E_N^4)
              kappa(I_e1,I_e2,I_e3,I_e4).                (4.2)
```

The equality `I_e^a=I_e` is applied separately inside every moment block in
(4.1). The ordered tuples have exactly five equality partitions.

### 4.1 Stratum `4`

For one event,

```text
K_4(e)=p-7p^2+12p^3-6p^4
      =p(1-p)(1-6p+6p^2).                                (4.3)
```

There are `M` tuples of this type.

### 4.2 Strata `31` and `22`

For distinct `e,f`, put `q_ef=10^(-r_m({e,f}))` and
`c_ef=q_ef-p^2`. Direct substitution in (4.1) gives

```text
K_31(e;f)=kappa(I_e,I_e,I_e,I_f)
          =(1-6p+6p^2)c_ef,                              (4.4)

K_22(e,f)=kappa(I_e,I_e,I_f,I_f)
          =(1-2p)^2 c_ef-2c_ef^2.                        (4.5)
```

For each unordered pair there are two choices of tripled event and four slot
orders, giving coefficient `8` for (4.4), while `22` has `4!/(2!2!)=6`
orders.

### 4.3 Stratum `211`

For distinct `e,f,g`, with `e` repeated, abbreviate

```text
a=q_ef, b=q_eg, c=q_fg, t=q_efg,
K_3(e,f,g)=t-p(a+b+c)+2p^3.                              (4.6)
```

Then

```text
K_211(e;f,g)
 =kappa(I_e,I_e,I_f,I_g)
 =(1-2p)K_3(e,f,g)-2(a-p^2)(b-p^2).                      (4.7)
```

For a fixed repeated event there are `4!/2!=12` slot orders. There are three
choices of repeated event in every unordered triple, so this stratum has three
separate coefficient-12 terms, not one coefficient-36 term unless their
values happen to agree.

### 4.4 Stratum `1111`

For four distinct events `e,f,g,h`, write `q_A=10^(-r_m(A))`. Then

```text
K_1111(e,f,g,h)
 =q_efgh-p(q_efg+q_efh+q_egh+q_fgh)
  -(q_ef*q_gh+q_eg*q_fh+q_eh*q_fg)
  +2p^2(q_ef+q_eg+q_eh+q_fg+q_fh+q_gh)-6p^4.             (4.8)
```

Equivalently set

```text
d_A=|A|m-r_m(A).                                         (4.9)
```

After factoring `p^4`, the exact rank-signature weight is

```text
K_1111/p^4
 =10^d_efgh-sum_(|A|=3)10^d_A
  -(10^(d_ef+d_gh)+10^(d_eg+d_fh)+10^(d_eh+d_fg))
  +2sum_(|A|=2)10^d_A-6.                                (4.10)
```

Every unordered four-set has `4!=24` slot orders.

### Theorem 4.2 (complete fourth-cumulant expansion)

Combining the disjoint strata proves

```text
kappa_4(U_(N,m))
 =sum_e K_4(e)
  +8 sum_{ {e,f} } K_31(e;f)
  +6 sum_{ {e,f} } K_22(e,f)
  +12 sum_{ {e,f,g} }[K_211(e;f,g)+K_211(f;e,g)+K_211(g;e,f)]
  +24 sum_{ {e,f,g,h} } K_1111(e,f,g,h).                 (4.11)
```

The sums in braces are unordered sets of distinct primitive events. Equations
(3.3)--(4.10) give every coefficient and sign exactly. Unlike the third-order
case discussed in the T170 note, (4.5), (4.7), and (4.10) are not manifestly
nonnegative in an arbitrary rank geometry; no global positivity claim is made.

## 5. Complete parameterized signature classification

For each repetition stratum, take the distinct event set `F`, subtract its
least endpoint, sort each pair, and sort the event list lexicographically. Its
canonical signature `Sigma_m(F;lambda)` consists of:

```text
1. repetition partition lambda in {4,31,22,211,1111}, including which event
   is repeated for 31 and 211;
2. the complete normalized integer event list F and span s(F);
3. endpoint-incidence graph H(F), with vertices the block starts and edges F;
4. the complete endpoint overlap matrix
      omega(a,b)=max(0,m-|a-b|);
5. event-dependency graph D_m(F), joining events whose exact digit supports
   intersect, and its connected-component partition;
6. positive lag list in canonical event order and its equality partition;
7. r_m(A) for every nonempty A subset F;
8. the clique closure cl(A) for every A subset F, obtained by completing each
   incidence component, and the missing closure edges cl(A)\A.              (5.1)
```

This classifies every connected normalized four-event signature, including
repeated-index signatures: every ordered four-tuple has one equality partition;
its distinct events have one deterministic normalized list; and all remaining
fields are deterministic functions of that list, `m`, and the repeated role.
Conversely, translation by (3.6) produces every legal embedding exactly once.
Thus signatures are disjoint and exhaustive, their multiplicity is (3.6), and
their contribution is the applicable formula (4.3)--(4.10) times its explicit
ordered coefficient.

Keeping `F` is not vacuous bookkeeping. Four simple incidence edges can have
component edge partitions

```text
1+1+1+1, 2+1+1, 2+2, 3+1, or 4,                         (5.2)
```

The complete incidence-type list by number of distinct events is

```text
1: K2;
2: 2K2, P3;
3: 3K2, P3+K2, P4, K1,3, K3;
4: 4K2, P3+2K2, 2P3, P4+K2, K1,3+K2, K3+K2,
   P5, K1,4, fork5, C4, paw.                              (5.3)
```

Here `fork5` is the five-vertex tree with degree sequence `(1,1,1,2,3)`, and
`paw` is a triangle with one pendant edge. To prove completeness, partition
the four edges by incidence-component edge counts. Components with one, two,
or three edges are respectively `K2`, `P3`, and one of `P4,K1,3,K3`. A
connected four-edge simple graph is either a tree on five vertices, one of
`P5,K1,4,fork5`, or is unicyclic. Its unique cycle has length four, giving
`C4`, or length three with its remaining edge pendant, giving `paw`. Combining
component partitions gives exactly (5.3). The shorter lists follow identically.

Neither these types nor the dependency graph determine digit rank: integer
offsets and all subset ranks in (5.1) are essential. Thus (5.3) is the finite
graph skeleton, while normalized coordinates and the rank vector give exact
parametric subclasses. Formula (5.1) is directly enumerable for each `N,m`
without falsely collapsing offset-dependent families.

Disconnected signatures cancel. If `D_m(F)` is disconnected, its event
families use disjoint iid digit sets and are independent; any joint cumulant
meeting two independent groups is zero. The retained classification is exactly
the signatures with connected `D_m(F)`. The replay enumerates every normalized
four-distinct-event shape for `5<=N<=7`, `1<=m<=3`, verifies all 15 subset
ranks, and reports its exact sign. This is bounded completeness evidence only;
the preceding canonical-signature argument is the prose proof.

## 6. What complete occupancy cliques do absorb

First ignore overlap between block words and take `k` independent categorical
words, each uniform on an alphabet of size `10^m`. Let

```text
V_k=sum_(1<=i<j<=k) 1[W_i=W_j].                           (6.1)
```

For an equality-edge graph `A`, the joint moment is `p^(|V(A)|-c(A))`.
Transitive closure to complete occupancy cliques is exact. Distinct edges are
pairwise independent, so `31` and `22` vanish. At fourth order the only
connected contributions are:

1. the all-equal Bernoulli term on one edge;
2. a triangle with one repeated edge (`211`), with per repeated role
   `p^2(1-p)(1-2p)`;
3. a four-cycle (`1111`), with joint cumulant `p^3(1-p)`.

Forests vanish because their equality-edge indicators are mutually independent:
every forest subset has moment `p` to the number of edges. A triangle plus an
edge outside its incidence component is independent and vanishes. After
forests are removed, a connected four-edge simple graph is either a four-cycle
or the paw. In the paw, the pendant-edge indicator is independent of the sigma
field generated by the triangle indicators: condition on the first three
categorical words, and comparison of the fourth independent word with its
attachment vertex still has probability `p`, regardless of their equality
pattern. Therefore the paw cumulant vanishes. Hence

```text
kappa_4(V_k)
 =binom(k,2)p(1-p)(1-6p+6p^2)
  +36binom(k,3)p^2(1-p)(1-2p)
  +72binom(k,4)p^3(1-p).                                 (6.2)
```

The factors are inspectable: `36=3*12` for the repeated edge of each triangle,
and `72=3*24` for the three undirected four-cycles on each four-set. Every term
in (6.2) is positive for decimal `p<=1/10`. Thus complete cliques do absorb the
isolated mixed-lag triangle mechanism: they retain it, with its exact centered
`211` coefficient, instead of discarding it.

This does not imply that occupancy-only moments describe overlapping words.
The next exact signature falsifies that stronger absorption claim.

## 7. Exact falsifying signature: triangle with an overlapping tail

Assume `m>=2` and take the normalized four distinct events

```text
e={0,1},  f={1,2},  g={0,2},  h={2,3}.                   (7.1)
```

The first three form a complete equal-word triangle, with lags `1,1,2`; the
fourth is a lag-one tail. The endpoint-incidence graph is a triangle with a
tail and the event-dependency graph is connected. Its span is three, so (3.6)
gives exactly

```text
M_N(F)=(N-3)_+.                                          (7.2)
```

### Lemma 7.1 (all subset ranks)

For every `m>=2`, the pair ranks are

```text
r(ef)=r(eg)=r(fg)=r(fh)=m+1,
r(eh)=r(gh)=m+2.                                         (7.3)
```

The triple ranks are

```text
r(efg)=m+1,
r(efh)=r(egh)=r(fgh)=m+2,                                (7.4)
```

and

```text
r(efgh)=m+2.                                             (7.5)
```

**Proof.** Events `e` and `f` together force
`X_0=X_1=...=X_(m+1)`, a path on `m+2` consecutive digit vertices and rank
`m+1`; event `g` is then redundant. The same path argument applies to `eg`,
`fg`, and the unit translates `fh`. For `eh`, the equality edges are the unit
edges from `0` through `m-1` and from `2` through `m+1`; their union is the
path from `0` through `m+2`, of rank `m+2`; `gh` gives the same rank by direct
union of displacement-two and unit edges. These establish (7.3).

The triangle `efg` has the same closure as `ef`, proving its first rank in
(7.4). Adding `h` to `ef`, or adding the remaining indicated constraints,
extends or fills the same consecutive equality component through digit
position `m+2`, giving rank `m+2`. This proves the other triples and (7.5).
Every claim can also be checked by listing the edges (3.1); no probabilistic
independence approximation is used. QED.

### Theorem 7.2 (exact nonabsorption)

Substituting (7.3)--(7.5) into (4.8), with `p=10^-m`, gives

```text
K_tail(m)
 =p/100-(71/500)p^2+(21/25)p^3-6p^4
 =(p/500)(5-71p+420p^2-3000p^3).                         (7.6)
```

For `m>=2`, `p<=1/100`; hence

```text
K_tail(m)-p/125
 =p[1/500-(71/500)p+(21/25)p^2-6p^3]
 >=p[1/500-71/50000-6/10^6]
 =287p/500000>0.                                         (7.7)
```

Thus this exact connected signature has strictly positive cumulant and

```text
K_tail(m)~10^(-m-2).                                     (7.8)
```

In the occupancy-only model, (7.1) has incidence ranks: every pair rank two,
the triangle rank two, every other triple rank three, and full rank three.
Putting the corresponding moments into (4.8) cancels exactly:

```text
K_tail^occupancy(m)=0.                                   (7.9)
```

The discrepancy is structural. The actual full moment is `10^(-m-2)`, while
the occupancy-only full moment is `10^(-3m)`; their ratio is

```text
10^(2m-2).                                                (7.10)
```

Completing the triangle clique is logically valid, but assigning its closure
moments solely from the equal-word occupancy partition loses the offset-induced
long digit run. Therefore the pointwise occupancy-only rule fixed in Section 1
does **not** absorb this mixed-lag connected fourth-order effect. This does not
exclude a global resummation with offset-dependent corrected clique weights or
cancellation among several signatures. A richer signature retaining offsets
and digit equality ranks handles (7.1) only by restoring precisely the omitted
data.

The contribution of the translated orientation (7.1) to (4.11) is exactly

```text
24(N-3)K_tail(m).                                        (7.11)
```

Reflection is not quotiented out; its distinct normalized reflected shape has
the same contribution and is counted separately by (4.11).

## 8. Explicit logarithmic-depth comparison

Throughout the mandated range

```text
N>=10^4, 1<=m<=floor((1/4)log_10 N),                     (8.1)
```

the falsifier applies for `m>=2`. From (7.7) and `N-3>=N/2`,

```text
24(N-3)K_tail(m)
 > (12/125)N*10^(-m)
 >= (12/125)N^(3/4).                                     (8.2)
```

This is a uniform positive lower bound for this one orientation's exact
four-distinct contribution. Relative to the raw iid event mean
`lambda=binom(N,2)10^-m`, it satisfies

```text
24(N-3)K_tail(m)/lambda
 <=24(N-3)(p/100)/[N(N-1)p/2]
 <12/(25N),                                              (8.3)
```

where (7.6) is at most `p/100` because its remaining terms are negative plus
`p^3(21/25-6p)>0`; more directly, for `p<=.01` the bracket after `p/100` is
negative. Thus this single translated family is `Theta(1/N)` of the mean but
grows at least as `N^(3/4)` in absolute cumulant units. Its occupancy-only
cumulant is exactly zero, while its full joint moment exceeds the occupancy
prediction by the explicit factor (7.10), namely `10^(2m-2)`.

For the endpoint `m=1`, (7.1) uses individual iid digits and its actual and
occupancy-only cumulants both vanish. The fourth-cumulant expansion (4.11)
still applies. The nonabsorption theorem and (8.2) are explicitly restricted
to the nonempty subrange `2<=m<=floor((1/4)log_10 N)`, which begins at
`N>=10^8`. No claim is made that the one family dominates the entire signed
fourth cumulant; (8.2) is its exact positive contribution, not a lower bound
for a sum that may contain signed terms.

## 9. Comparisons and nonduplication boundary

No comparator conclusion is a premise.

1. T159 contains `literature-checked` source claims but its new deductions are
   `proof sketch`; it argues for a marked Palm--Stein iid collision audit and
   computes one- and two-event ranks. T172 instead gives the ordinary fourth
   cumulant and an occupancy-only falsifier, not a process approximation.
2. T161 likewise separates `literature-checked` source claims from
   `proof sketch` deductions; it argues for maximal same-lag chain declumping
   and a candidate compound-Poisson benchmark. T172 uses neither maximal chains
   nor a compound law; every event slot remains in (4.11).
3. T168 is a `proof sketch` with finite `experiment`; it argues that raw
   mixed-lag triangle intensity is large relative to same-lag roots. T172 uses
   it only as motivation and distinguishes intensity from centered cumulant.
4. T170 is a `proof sketch` with finite `experiment`; it argues for an ordinary
   third cumulant and a positive disjoint-block triangle term. T172 independently
   derives order four, where the triangle occurs in `211` and a new
   four-distinct triangle-with-tail signature detects overlap geometry.
5. T171 has an active generation-1 lease in `orchestrator-input.json`, but no
   report, source, theorem, hash, agenda text, or verification level is readable
   in this sandbox snapshot. Its identifier is reserved. T172 makes no semantic
   comparison or nonduplication claim beyond its explicit fourth-cumulant and
   occupancy-only endpoint.

## 10. Separate unproved fixed-pi transfer

**PI_FOURTH_CONNECTED_STATISTIC_BOUND_T172** (`conjecture`; `unproved
fixed-pi transfer`; NOT ASSERTED). A route toward T7 or T107 would require one
increasing sequence of actual pi prefixes and, uniformly on the relevant
triangular depth range, empirical versions of every subset moment entering
(4.1), grouped by the exact signatures (5.1), with a signed connected error
bound strong enough after multiplicities and ordered coefficients. One usable
form would require

```text
sum_(connected Sigma, order<=4)
  ordered_weight(Sigma) M_N(Sigma)
  |K_pi(Sigma)-K_iid(Sigma)|
   =o(N^2*10^(-m)),                                      (10.1)
```

simultaneously on one coherent prefix sequence, plus explicit control of
higher connected orders if a distributional conclusion is intended. The
definition of `K_pi` must use all subset occupancies on the same translation
window, not separately chosen samples.

For T7, (10.1) would still need conversion from exact block equality to its
ordered, diagonal-inclusive metric near-return count and a proof that the
actual count meets the threshold. For T107, it would still need that theorem's
separate coherent prefix, decimal-boundary, weak-convergence, and Fourier-row
budgets. Adjacent cylinders, wraparound, carries, and terminating versus
nonterminating decimal endpoints cannot be omitted.

Nothing in iid probability, (4.11), finite enumeration, or (7.6) proves
(10.1) for the prescribed digits of pi. No fixed-pi, A1, C1, or C2 claim is
made.

## 11. Replay, evidence labels, and verdict

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t172.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay uses exact integers and rational arithmetic. It verifies the
canonical hash; all 15 set partitions; formulas (4.3)--(4.8) and (4.10), with
all repeated roles; the five strata and their multinomial weights; graph types
(5.3); all signature fields in (5.1), subset clique closures, closure ranks, and
translation-orbit counts through `N=7`; direct binary-word fourth cumulants on
12 bounded `(N,m)` instances; categorical-clique formula (6.2) on eight
instances; all 15 tail subset ranks, reflection, the `m=1` endpoint,
(7.6)--(7.9), and six logarithmic comparisons; and every connected normalized
four-distinct-event shape for `5<=N<=7`, `1<=m<=3`. These are `experiment`
checks only.

The derivations in Sections 2--10 are `proof sketch`. The canonical fixed-pi
question remains open, and the transfer in Section 10 is an explicitly unproved
conjecture.

SCOPED_VERDICT (1/1): **NONABSORPTION**.

Complete equal-word occupancy cliques correctly retain the isolated triangle's
fourth-order `211` term, but the pointwise occupancy-only moment rule of
Section 1 does not absorb overlap geometry. The exact connected signature
(7.1) has occupancy-only cumulant zero and actual cumulant (7.6), uniformly
positive for `m>=2`, with exact multiplicity and logarithmic-depth comparison
(7.11)--(8.3). This closes only that proposed iid occupancy-only repair. It
does not close global or offset-aware resummations, G28, T7, T107, or any
statement about pi.
