# T170: ordinary third cumulant of iid overlapping-block collisions

Date: 2026-08-13 UTC.

Status: `proof sketch`.  All general statements are proved below without using
the conclusions of another note.  The supplied Python replay is an
`experiment`: it can falsify formulas on bounded instances, but it is not a
proof of a universal statement.  T159, T161, and T168 are unverified notes and
are compared only as motivation in Section 10.

```text
CANONICAL_SHA256: cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
CUMULANT_REPETITION_STRATA: 3
DISTINCT_INCIDENCE_TYPES: 5
SCOPED_ENDPOINT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, normalization, and ambiguities

The byte-exact canonical problem is vendored as `canonical_statement.txt`.
It asks about ordered, diagonal-inclusive metric near returns in the fixed
orbit of pi.  T170 neither changes nor answers it.  T170 independently studies
the A10/A13/A14 sibling consisting of exact equality of overlapping blocks in
one iid uniform decimal word.

The following conventions are binding.

1. Integers `N>=2` and `m>=1` are fixed.  There are exactly `N` legal starts
   and `L=N+m-1` independent digits.  Every interval is inclusive.
2. A primitive collision event is indexed by an unordered off-diagonal pair
   `{i,j}` with `0<=i<j<N`.  The statistic `U_(N,m)` is the number of active
   primitive events.
3. Sums over event tuples in the definition of a cumulant are ordered.  We
   convert them to unordered sets only after accounting for all permutations.
4. A digit equality graph is a simple graph: repeated equality edges impose no
   additional rank.  Its rank is vertices minus connected components.
5. Block-incidence connectivity, interval-support connectivity, and digit
   equality-graph connectivity are different notions and are never
   interchanged.
6. "Forest cancellation" means that the union of all labeled digit-equality
   constraints is a graphic-matroid forest.  It does not merely mean that each
   event separately is a forest or that its block intervals are disjoint.
7. The requested uniform range is
   `1<=m<=floor((1/4)log_10 N)`.  It is nonempty only for `N>=10^4`.
8. No assertion about pi is inferred from the iid model or finite replay.

## 2. Model, endpoints, and ordered reconstruction

Let `D={0,...,9}` and let

```text
X_0,...,X_(L-1) iid uniform on D,             L=N+m-1,
B_i=[i,i+m-1],
W_i=(X_i,...,X_(i+m-1)),                      0<=i<N,
E_N={{i,j}:0<=i<j<N},                         M=#E_N=binom(N,2),
I_{i,j}=1[W_i=W_j],
U_(N,m)=sum_(e in E_N) I_e.                                  (2.1)
```

The last legal block ends at `(N-1)+(m-1)=L-1`; no padding or wrapping is
used.  Put

```text
p=10^(-m).                                                   (2.2)
```

The ordered off-diagonal count is `O=2U_(N,m)`.  Restoring the `N`
deterministic diagonal pairs gives the ordered, diagonal-inclusive exact block
collision count

```text
E=N+2U_(N,m).                                                (2.3)
```

For ordinary cumulants of order at least two, deterministic translation has no
effect, and scaling by two scales the third cumulant by eight.  Therefore

```text
kappa_3(E)=kappa_3(O)=8*kappa_3(U_(N,m)).                    (2.4)
```

The equality in (2.4) does not turn the duplicated ordered indicators into
independent primitive events.  It is only the exact deterministic conversion.

## 3. Equality graphs and exact probabilities

For a finite event set `F subset E_N`, form the digit equality graph `G_m(F)`.
Its vertices are all digit positions in the block intervals used by `F`, and
for every `{i,j} in F` and `0<=r<m` it has the undirected edge

```text
{i+r,j+r}.                                                   (3.1)
```

Parallel copies are discarded.  Write `v_m(F)` and `c_m(F)` for its vertex and
component counts, and define

```text
r_m(F)=v_m(F)-c_m(F).                                       (3.2)
```

### Lemma 3.1 (rank probability)

For every finite `F`,

```text
P(I_e=1 for all e in F)=10^(-r_m(F)).                       (3.3)
```

**Proof.** The equalities (3.1) say exactly that digits are constant on each
component.  There are `10^c_m(F)` satisfying assignments to the `v_m(F)`
involved positions out of `10^v_m(F)` total assignments.  Unused digits cancel.
QED.

A single event has rank exactly `m`, even when its two blocks overlap.  One
way to see this is that the equations `X_(i+r)=X_(j+r)` identify positions in
each residue chain modulo `j-i`; their total rank is exactly the number `m` of
forward edges.  Hence every event has probability `p`.

For distinct events define pair and triple rank deficiencies

```text
d_(e,f)=2m-r_m({e,f}),
D_(e,f,g)=3m-r_m({e,f,g}).                                 (3.4)
```

Graphic-matroid rank is monotone and subadditive, so

```text
0<=d_(e,f)<=m,
max(d_(e,f),d_(e,g),d_(f,g))<=D_(e,f,g)<=2m.               (3.5)
```

The first inequality follows because adding the `m` edges of a second event
raises rank by at most `m`; the lower bound in the second follows from
`r(F union {g})<=r(F)+m`.

## 4. Complete ordinary third-cumulant expansion

For random variables `Y,Z,T`, use the ordinary joint cumulant

```text
kappa(Y,Z,T)=E[YZT]-E[YZ]E[T]-E[YT]E[Z]-E[ZT]E[Y]
             +2E[Y]E[Z]E[T].                              (4.1)
```

Multilinearity gives

```text
kappa_3(U)=sum_((e,f,g) in E_N^3) kappa(I_e,I_f,I_g).      (4.2)
```

There are exactly three repetition strata.

### 4.1 All three indices equal

For a Bernoulli variable of mean `p`,

```text
kappa(I_e,I_e,I_e)=p(1-p)(1-2p).                          (4.3)
```

There are `M` such ordered triples.

### 4.2 Exactly two indices equal

For distinct `e,f`, direct substitution in (4.1), using `I_e^2=I_e`, gives

```text
kappa(I_e,I_e,I_f)=(1-2p)(P(I_e I_f=1)-p^2).              (4.4)
```

For one unordered pair `{e,f}`, the repeated index can be `e` or `f`, and each
multiset has three orderings.  Thus its total coefficient is six, not three:

```text
6(1-2p)(10^(-r_m({e,f}))-p^2)
=6(1-2p)p^2(10^d_(e,f)-1).                                (4.5)
```

### 4.3 All three indices distinct

For an unordered event triple `{e,f,g}`, all six orderings have the same joint
cumulant.  Equations (3.3)--(3.4) give its total contribution

```text
6[10^(-r_m({e,f,g}))
  -p(10^(-r_m({e,f}))+10^(-r_m({e,g}))+10^(-r_m({f,g})))
  +2p^3]
=6p^3[10^D-10^d_(e,f)-10^d_(e,g)-10^d_(f,g)+2].           (4.6)
```

Combining the three disjoint strata proves the complete exact expansion

```text
kappa_3(U_(N,m))
 =M p(1-p)(1-2p)
 +6(1-2p)p^2 sum_({e,f} subset E_N)(10^d_(e,f)-1)
 +6p^3 sum_({e,f,g} subset E_N)
      [10^D_(e,f,g)-sum_({a,b} subset {e,f,g})10^d_(a,b)+2]. (4.7)
```

This is an ordinary cumulant.  No factorial-cumulant or compound-Poisson
identity is used.

## 5. Exact cancellations and sign

The next lemma controls every class in (4.7), including overlaps and
same-lag cases.

### Lemma 5.1 (rank-deficiency dichotomy)

For distinct `e,f,g`, write `D=D_(e,f,g)` and let `d1,d2,d3` be the three pair
deficiencies.  If some `di=D`, the other two deficiencies are zero.  Otherwise
all three satisfy `di<=D-1`.

**Proof.** Suppose `d_(e,f)=D`.  Rewriting definitions gives

```text
r_m({e,f,g})=r_m({e,f})+m.                                (5.1)
```

Thus all `m` constraints supplied by `g` are independent modulo the span of
the constraints supplied by `{e,f}`.  Independence from a set implies
independence from each subset, so
`r_m({e,g})=r_m({f,g})=2m`; hence the other deficiencies are zero.  If no
deficiency equals the integer `D`, (3.5) gives `di<=D-1`.  QED.

### Corollary 5.2 (exact cancellation criterion)

For distinct events, the bracket in (4.6) is nonnegative.  It is zero exactly
in one of the following two cases:

```text
(i)  D=0 and {d1,d2,d3}={0,0,0};
(ii) D>0 and {d1,d2,d3}={D,0,0}.                          (5.2)
```

**Proof.** If `D=0`, (3.5) forces all `di=0`, and the bracket is
`1-1-1-1+2=0`.  If one `di=D`, Lemma 5.1 makes the bracket
`10^D-10^D-1-1+2=0`.  Otherwise `D>=1`, every `di<=D-1`, and base ten gives

```text
10^D-sum_i 10^di+2 >= 10^D-3*10^(D-1)+2
                           =7*10^(D-1)+2>0.               (5.3)
```

These cases are exhaustive.  QED.

Case (i) is the requested equality-forest cancellation: all `3m` labeled
constraints are rank-independent, so their union is a graphic-matroid forest.
Case (ii) is disconnected cancellation in its exact algebraic form: one event
adds full rank to the other two jointly.  In particular it holds whenever one
event uses digit positions disjoint from the joint support of the other two.
It is stronger and safer than testing only pairwise support intersections.

The word "disjoint" cannot mean disconnected components of the digit graph.
For the triangle in Section 8, the digit graph is a disjoint union of `m`
three-cycles, and its cumulant is positive.  Nor is it enough that each event's
own equality edges form a forest: three forests can create a cycle jointly.

Since `p<=1/10`, (4.3) is positive.  Pair terms (4.5) are nonnegative because
`d>=0` and `1-2p>0`.  Corollary 5.2 makes every distinct term nonnegative.
Thus there is no hidden signed cancellation between classes:

```text
kappa_3(U_(N,m))>0 for every N>=2 and m>=1.                (5.4)
```

## 6. Exhaustive symbolic class partition

The expansion already ranges over every event multiset.  This section gives a
disjoint class key that exposes every convention demanded by the agenda.

Normalize an unordered event set `F` by subtracting its least block start from
all endpoints, then sort each event increasingly and sort the events
lexicographically.  This chooses one representative under common translation;
there is no quotient by reflection.  For `|F|=2` or `3`, define its canonical
signature `Sigma_m(F)` to contain all of the following fields:

```text
1. repetition stratum: 21 or 111;
2. normalized event list F itself and span s(F)=max union F;
3. endpoint-incidence graph H(F), with vertices the distinct block starts and
   edges F; endpoint coincidence is exactly vertex sharing in H(F);
4. complete interval-overlap matrix
   omega_(a,b)=max(0,m-|a-b|) for every pair of distinct endpoint starts;
5. positive lag tuple (b-a) in canonical event order and its equality
   partition (all same, exactly two same, or all distinct when |F|=3);
6. the canonically ordered pair ranks r_m({e,f}), equivalently deficiencies d;
7. for |F|=3, the triple rank r_m(F), equivalently D.         (6.1)
```

For stratum `3`, use the one-event analog: normalized event `{0,d}`, its lag
`d`, overlap `max(0,m-d)`, and rank `m`.

This is an exact parameterized partition, not a list of examples and not a
closed-form enumeration of every coarse topology.  Every event multiset has
exactly one repetition stratum.  Sorting and normalization are deterministic, so it
has exactly one signature.  Distinct signatures are disjoint by definition,
and retaining the normalized event list makes every relative displacement and
boundary span inspectable.  Conversely, translation by

```text
0<=t<N-s(F)                                                   (6.2)
```

gives every legal embedding of an exact normalized shape once.  Hence its
exact multiplicity is `(N-s(F))_+`.

For three distinct simple edges the endpoint-incidence graph has exactly one
of five types:

```text
3K2, P3+K2, P4, K1,3, K3.                                  (6.3)
```

Indeed, the component edge-size partition is `1+1+1`, `2+1`, or `3`; a
connected simple graph with three edges is exactly `P4`, `K1,3`, or `K3`.
For two distinct events it is exactly `2K2` or `P3`.  The complete overlap
matrix then determines the interval-support dependency graph, while field 5
records same-lag and mixed-lag subclasses.  Fields 6--7 determine the exact
signed weight in (4.5) or (4.6).  Retaining the integer event list is
essential: coarse graph names alone do not determine ranks.  This proves
symbolic completeness by
endpoint coincidence, interval overlap, lag pattern, and pair/triple rank.

To display the resulting finite sum, let `C_N,m(sigma)` be the number of
unordered event sets in the indicated stratum with signature `sigma`.  Then

```text
K_21(sigma)=6(1-2p)p^2(10^d-1),
K_111(sigma)=6p^3(10^D-10^d1-10^d2-10^d3+2),              (6.4)
```

and (4.7) is exactly the all-equal term plus
`sum_sigma C_N,m(sigma) K_21(sigma)` plus
`sum_sigma C_N,m(sigma) K_111(sigma)`.  Corollary 5.2 controls every fiber
uniformly: each weight is nonnegative, and its zero fibers are exactly (5.2).
The multiplicity of each exact shape is `(N-s(F))_+`; `C_N,m` merely groups
shapes with identical displayed fields.  There is no residual unclassified or
uncontrolled class, although no closed formula for every coarse topology's
aggregate multiplicity is claimed.

## 7. Same-lag and disconnected cases

Same-lag cases are included rather than delegated to a declumping model.  For
two translates

```text
e={i,i+d}, f={i+h,i+h+d}, h!=0,                            (7.1)
```

the union has `max(0,m-|h|)` duplicated equality edges and no new cycles, so

```text
r_m({e,f})=m+min(m,|h|),
d_(e,f)=max(0,m-|h|).                                      (7.2)
```

Its exactly-two-equal contribution is obtained by inserting (7.2) in (4.5).
For three distinct events of the same lag `d`, write them as
`e_u={u,u+d}` for three distinct starts `u in {a,b,c}`.  Their equality edges
all have displacement `d`, so the union is a subgraph of the disjoint union of
integer paths in residue classes modulo `d`; it is a forest.  Its rank is
therefore the number of distinct edges, namely

```text
r_m({e_a,e_b,e_c})
 =|[a,a+m-1] union [b,b+m-1] union [c,c+m-1]|,
D=sum_({u,v} subset {a,b,c}) max(0,m-|u-v|)
  -max(0,m-(max{a,b,c}-min{a,b,c})).                       (7.3)
```

The second formula is inclusion-exclusion; the last term is the common
three-interval overlap.  Together, (7.2)--(7.3) give every pair and triple rank
for the all-same-lag class and hence its exact contribution through (4.5)--(4.6).
Every mixed-lag triple is assigned its exact integer shape and the other fields
of signature (6.1); Corollary 5.2 controls its sign uniformly without a proposed
cluster law or omitted error term.

If the digit supports of two event groups are disjoint, the corresponding
indicator families are independent.  A joint cumulant meeting both independent
groups vanishes.  For three distinct events this is also visible in (5.2)(ii):
the isolated event adds rank `m` to the other pair and has additive pair rank
with each member.  For repeated indices, an independent distinct pair has
`d=0`, making (4.5) zero.  These statements account for every disconnected
cancellation.

## 8. Exact disjoint-block triangle contribution

Choose block starts `0<=x<y<z<N` satisfying

```text
y-x>=m and z-y>=m.                                         (8.1)
```

The three events are

```text
e={x,y}, f={x,z}, g={y,z}.                                 (8.2)
```

They are distinct and form the incidence graph `K3`.  Each pair of active
events implies the third.  Because the three blocks are disjoint independent
length-`m` words,

```text
P(I_e I_f=1)=P(I_e I_g=1)=P(I_f I_g=1)
=P(I_e I_f I_g=1)=10^(-2m)=p^2.                           (8.3)
```

Thus `d1=d2=d3=0`, `D=m`, and one unordered event triple contributes

```text
6[p^2-3p^3+2p^3]=6p^2(1-p).                               (8.4)
```

The spacing substitution

```text
(x,y,z) -> (x,y-(m-1),z-2(m-1))                            (8.5)
```

is a bijection onto ordinary three-subsets of
`{0,...,N-2m+1}`.  Therefore the exact total contribution of this family is

```text
T_triangle(N,m)
=6*binom(N-2m+2,3)*10^(-2m)*(1-10^(-m)),                  (8.6)
```

with the binomial interpreted as zero when its top is below three.  The factor
six is event-index ordering, not collision-pair reversal.  The factor `1-p`
is cumulant centering.  This distinguishes (8.6) from raw active-pattern
intensity.

## 9. Uniform full signed bound

All terms outside the triangle family are nonnegative by Section 5.  Hence for
all `N>=2,m>=1`,

```text
kappa_3(U_(N,m))
 >=6*binom(N-2m+2,3)*10^(-2m)*(1-10^(-m)).                 (9.1)
```

This is a lower bound for the full signed cumulant, not merely for a selected
raw intensity.  In the required range `N>=10^4` and
`1<=m<=floor((1/4)log_10 N)`, put `R=N-2m+2`.  The elementary estimates used in
the T168 note are rederived here: `R>=N/2`, `R-1>=N/4`, and `R-2>=N/4`, whence

```text
binom(R,3)>=N^3/192,   1-10^(-m)>=9/10.                    (9.2)
```

Substitution in (9.1) gives the explicit uniform positive bound

```text
kappa_3(U_(N,m)) >= (9/320) N^3 10^(-2m)
                  >= (9/320) N^(5/2)>0.                  (9.3)
```

The second inequality uses `10^m<=N^(1/4)`.  Equations (9.1)--(9.3), together
with the complete nonnegative partition in Section 6, are the selected agenda
endpoint.  There is no uniquely specified residual because no term remains
uncontrolled.

## 10. Comparison with T159, T161, and T168

These are all unverified notes.  No conclusion from them is a premise.

The comparison files were reopened in this verification pass.  Their local
SHA-256 values are T159 `67c89ec92afaa0d3ebe02617346bb0ae5aa2ffd2184e6ea0ecd4843a0cd85045`,
T161 `48ede4b571568c5e088c024687037a1d5b864cf3a27ff11f55136cf811ca7d79`,
and T168 `af39291a4302e06127f02338aad2557f36a27a735173476f2e4fb2e6b685a08c`.

1. The T159 note argues for a marked Palm--Stein audit of the same iid
   overlapping-block model and derives one- and two-event ranks plus a
   same-lag second factorial-cumulant scale.  T170 independently defines the
   model and instead computes the complete ordinary third cumulant, including
   repetitions and diagonals.
2. The T161 note argues for maximal same-lag declumping and reports second and
   third factorial cumulants of a candidate compound-Poisson benchmark.  Those
   are not cumulants of raw `U`.  T170 includes every same-lag event tuple
   directly through (7.2) and its recorded triple rank.
3. The T168 note argues for a ten-row topology partition of raw connected
   mixed-lag pattern intensities and reports the disjoint triangle raw
   intensity `binom(N-2m+2,3)10^(-2m)`.  It explicitly does not supply a signed
   expansion.  T170 adds repetition strata, exact rank-signature weights,
   cancellation, ordering, and centering, producing the factor
   `6(1-10^(-m))` in (8.6).

Thus T170 identifies the positive occupancy-clique contribution in the iid
model but does not validate any compound-Poisson approximation.

## 11. Separate unproved transfer premise toward T107

**PI_COHERENT_PREFIX_JOINT_COLLISIONS_T170** (`conjecture`; `unproved pi-transfer`;
NOT ASSERTED).  Use the nonterminating decimal expansion of pi and write
`W^pi_(i,ell)` for its length-`ell` word beginning at digit position `i`.
For a normalized event set `F` of size one, two, or three and a subset
`A subset F`, define the windowed occupancy

```text
A^pi_(P,ell)(F;A)
 =sum_(0<=t<P-s(F)) product_({a,b} in A)
      1[W^pi_(a+t,ell)=W^pi_(b+t,ell)],                    (11.1)
```

The use of `F` in the window endpoint makes every subset moment use the same
embeddings.
Put

```text
epsilon^pi_(P,ell)(F;A)
 =A^pi_(P,ell)(F;A)-(P-s(F))*10^(-r_ell(A)),                (11.2)
```

with `r_ell(empty)=0`.  Regard uniform choice of a legal translation `t` as a
finite probability space, so (11.1) divided by `P-s(F)` is its subset moment.
Define `K^pi_(P,ell)(F)` by (4.1), with the following repetition convention:
for `F={e}` use `kappa(I_e,I_e,I_e)`; for `F={e,f}` use the average of
`kappa(I_e,I_e,I_f)` and `kappa(I_e,I_f,I_f)`; and for `F={e,f,g}` use
`kappa(I_e,I_f,I_g)`.  Let `K^iid_ell(F)` use the same convention with subset
moments `10^(-r_ell(A))`.  This definition includes every pair moment inside a
distinct triple and avoids an underweighted marginal-error shorthand.

Let `S_q(P,ell)` be all normalized `q`-event sets with span below `P`.  The
premise asserts that there exist one strictly
increasing sequence of positive prefix lengths `N(k)` such that, simultaneously
for every triangular index

```text
k>=k0, m0<=m<=k, 1<=ell<m,                                (11.3)
```

the occupancies use that same prefix and, with `p=10^(-ell)`, satisfy the exact
cumulant-error bound

```text
sum_(F in S_1(N(k),ell)) (N(k)-s(F))*|K^pi(F)-K^iid(F)|
+sum_(F in S_2(N(k),ell)) 6(N(k)-s(F))*|K^pi(F)-K^iid(F)|
+sum_(F in S_3(N(k),ell)) 6(N(k)-s(F))*|K^pi(F)-K^iid(F)|
 =o(6*binom(N(k)-2ell+2,3)*p^2*(1-p)),                    (11.4)
```

uniformly on (11.3).  The coefficients `1,6,6` are exactly the ordered/unordered
conversion for the three repetition strata.  Repeated event indices are read
through `I_e^2=I_e`, as in Section 4.

For transfer to `piCylinderCode`, the same prefixes must also have a proved
agreement between the chosen words and cylinder codes at every legal endpoint.
For transfer onward to the canonical metric count, equality occupancy is
insufficient: the premise must additionally give the same weighted control for
every pair of equal or adjacent level-`ell` decimal cylinders, including the
wrap pair, and quantify terminating/nonterminating endpoint and carry
exceptions.  Adjacent cylinders can contain points less than `10^(-ell)` apart
even when their codes differ, so this clause cannot be omitted.

The iid range covers the full T107 triangle only if, at minimum,
`k-1<=floor((1/4)log_10 N(k))`; separately chosen prefixes at each depth are
not coherent enough.  Even (11.1)--(11.4) would only be input *toward* T107.
The machine-checked T107 module is
`knowledge_library/t107/T107AveragedTriangularFejer.lean`, SHA-256
`45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`.
Its exact budgets are lines 31--69 and its triangular quantifiers are lines
150--173.  That interface separately requires weak convergence of the
same empirical measures and an averaged analytic defect built from both the
literal active-boundary budget

```text
rowBoundaryLoad(ell,N(k))<=N(k)/(40*10^ell)                (11.5)
```

and the Fourier budget

```text
||rowFourierRemainder(ell,N(k))||<=N(k)^2/(10*10^ell).     (11.6)
```

No collision cumulant here proves (11.1)--(11.6), weak convergence, T107's
averaged defect, or any fixed-pi statement.  No fixed-pi, A1, C1, or C2 claim
is made.

## 12. Replay and endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t170.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay uses exact integer and rational arithmetic.  It verifies the
canonical hash; repetition coefficients; rank probabilities by exhaustive
base-10 words on small instances; exact cumulants by exhaustive distributions;
the five incidence types and uniqueness of the signature partition on a
bounded grid; forest and disconnected cancellations; nonnegativity of every
enumerated rank signature; same-lag pair ranks; and exact triangle counts,
ranks, factors, and uniform inequalities.  These are finite `experiment`
checks only.

SCOPED_ENDPOINT (1/1): **UNIFORM POSITIVE LOWER BOUND**.

The complete ordinary third cumulant is (4.7).  Every summand is nonnegative,
the exact zero classes are (5.2), the disjoint-block triangles contribute
(8.6), and the full cumulant satisfies (9.1)--(9.3).  This resolves only the
iid exact-block sibling.  It makes no fixed-pi, A1, C1, C2, or T107 claim.
