# T74: fixed-word core stabilization

Status: `proof sketch` (rigorous prose using the kernel-checked T44, T46, T48,
and T72 interfaces and T21's pinned, literature-checked Furstenberg source).

This note proves a word-by-word qualitative statement. It does **not** prove a
uniform depth bound, C6, C1, or any unconditional positive-entropy statement
about pi. The order of quantifiers in the conclusion is

```text
for every nonempty decimal word w, there exists a depth R(w).
```

The depth may depend arbitrarily on the literal digits of `w`, not merely on
its length.

## 1. Source and imported checked interfaces

The immutable canonical statement is packaged as
`pi-positive-decimal-factor-entropy.txt`; its SHA-256 is
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
It asks whether pi has positive decimal factor entropy. T74 concerns a sibling
finite-core certificate and does not answer that question.

Write `T_m(x)=m x mod 1` on the circle `T=R/Z`. The following declarations are
imported facts, not reproved here.

1. T44, `T44EndpointSafeInvariantCore.lean`, defines
   `KWord w`, `finiteAvoidanceIntersection w R`, and `Core w R`. Its
   `KWord` uses an existential decimal expansion, so a terminating endpoint is
   admitted if either its terminating-zero or nonterminating-nine expansion
   avoids `w`.
2. T44's `KWord_isCompact`, `core_isClosed`,
   `core_forward_timesTen_invariant`,
   `core_eq_finiteAvoidanceIntersection`, and `core_antitone_radius` are
   kernel-checked.
3. T48's `graphEvaluation_image_eq_core` and
   `graphLanguage_finite_iff_core_finite` identify the endpoint-complete
   carry/KMP graph language at the inclusive depth `R` with `Core(w,R)`, with
   finite evaluation fibers in both directions needed for finiteness.
4. T46's `infiniteLabelLanguage_finite_iff_liveSCCCriterion` is the exact
   reachable-live finite-language characterization.
5. T72's
   `globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic`
   and its T48 specialization
   `endpointComplete_global_primitivePhase_iff_coordinateZeroEventuallyPeriodic`
   identify the successful projected-phase certificate at one fixed word and
   depth.

Exact module hashes and names are in `SOURCE_MANIFEST.md`. No result from T73
is used.

## 2. Normalized definitions and quantifiers

Fix once and for all a list `w` of decimal digits with `|w|>=1`. T44's
definitions expand to

```text
K_w = {x in T : at least one decimal expansion of x avoids w},

A_R(w) = intersection over 0 <= j <= R of T_16^(-j)(K_w),

Core(w,R) = {x : T_10^n(x) belongs to A_R(w) for every n>=0}.
```

The endpoint `j=R` is included. T44 proves `Core(w,R)=A_R(w)`, because `K_w`
and hence `A_R(w)` are forward `T_10`-invariant. Define

```text
C_infinity(w) = intersection over all R>=0 of Core(w,R).
```

All invariance below is forward invariance. No inverse image, surjectivity, or
backward-invariance hypothesis is used.

## 3. Core inclusions and the limiting core

### Proposition 3.1 (one-depth times-16 inclusion)

For every `R>=0`,

```text
T_16(Core(w,R+1)) subset Core(w,R).
```

**Proof.** Let `x` belong to `Core(w,R+1)` and set `y=T_16(x)`. To prove
`y in Core(w,R)`, use the expanded definition. For arbitrary `n>=0` and
`0<=j<=R`, commutativity of integer multiplication on `T` gives

```text
T_16^j T_10^n(y)
  = T_16^j T_10^n T_16(x)
  = T_16^(j+1) T_10^n(x).
```

Since `j+1<=R+1`, the last point belongs to `K_w` by the hypothesis on `x`.
This checks every `n` and every inclusive index `j<=R`. QED.

### Proposition 3.2 (compactness and invariance)

`C_infinity(w)` is compact and is forward invariant under both `T_10` and
`T_16`.

**Proof.** Each core is closed by T44, and the circle is compact. Their
intersection is therefore closed and compact. If `x` is in every core, T44's
forward-times-10 invariance puts `T_10(x)` in every core. For `T_16`, fix an
arbitrary `R`. Membership of `x` in `Core(w,R+1)` and Proposition 3.1 imply
`T_16(x) in Core(w,R)`. Since `R` was arbitrary, `T_16(x)` lies in the full
intersection. QED.

### Proposition 3.3 (endpoint-safe proper containment)

```text
C_infinity(w) subset K_w proper subset T.
```

Here the displayed word `proper` asserts that `K_w` itself is a proper subset
of the circle; `C_infinity(w)` is not asserted to be a strict subset of `K_w`.

**Proof of containment.** A point in `C_infinity(w)` lies in `Core(w,0)`. In
the expanded core definition take `n=0` and `j=0`; both multipliers are one,
so the point lies in `K_w`. This uses the inclusive zero endpoint.

**Proof that `K_w` is proper, including decimal endpoints.** Form a decimal
stream `a` by writing `w` in positions `0,...,|w|-1` and then appending the
tail `1,2,1,2,...`. Its real value lies strictly between zero and one, and the
stream is neither eventually zero nor eventually nine. The elementary decimal
uniqueness argument says that two distinct base-ten expansions of the same
real in `[0,1]` can differ only in the endpoint pattern

```text
prefix, d, 9,9,9,...    versus    prefix, d+1, 0,0,0,... .
```

Indeed, number places after the radix point starting at one, and let `k` be
the first differing place. The leading difference has magnitude at least
`10^(-k)`, while the entire later tail has magnitude at most
`9 sum_(n>k) 10^(-n)=10^(-k)`; equality forces adjacent leading digits and the
two constant extremal tails.
Thus `a` is the unique expansion of its circle point: its value is in `(0,1)`,
so equality on the circle cannot instead identify it with the real endpoints
zero or one. The unique expansion contains `w` at position zero. Consequently
there is no avoiding expansion of this point, including no alternative
endpoint expansion, and the point is outside `K_w`. QED.

## 4. Exact Furstenberg applicability and finiteness

Let

```text
Sigma = {10^s 16^t : s,t>=0}.
```

It is nonlacunary in Furstenberg's Definition IV.1: 10 and 16 cannot both be
powers of one integer. Equivalently, `10^a=16^b` forces `a=b=0`, since a
positive `a` leaves a factor `5^a` absent from the right side. Propositions
3.2 and commutativity imply `Sigma C_infinity(w) subset C_infinity(w)`.

The pinned source is H. Furstenberg, *Mathematical Systems Theory* 1 (1967),
1-49, DOI <https://doi.org/10.1007/BF01692494>, retrieved from
<https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf>, SHA-256
`cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358`.
The two needed statements are:

1. **Lemma IV.2, printed page 47 with proof on page 48:** if `Sigma` is a
   nonlacunary integer semigroup and `A` is a closed forward
   `Sigma`-invariant subset of the circle in which zero is non-isolated, then
   `A` is the whole circle.
2. **Theorem IV.1, printed/PDF page 48:** if `Sigma` is a nonlacunary integer
   semigroup and `alpha` is irrational, then `Sigma alpha` is dense in the
   circle.

Both are qualitative and require only forward semigroup invariance. Neither
supplies a rate.

### Theorem 4.1 (the limiting core is finite)

For every fixed nonempty `w`, `C_infinity(w)` is finite; the empty set is
allowed.

**Proof.** Put `C=C_infinity(w)`. By Proposition 3.3, `C` is a proper closed
subset of the circle.

First, every point of `C` is rational modulo one. If an irrational `alpha`
belonged to `C`, forward `Sigma`-invariance would put `Sigma alpha` inside
`C`. Theorem IV.1 says that orbit is dense, and closedness would force
`C=T`, contradicting properness.

Suppose now that `C` were infinite. Its difference set

```text
D = C-C = {x-y : x,y in C}
```

is compact, hence closed, as the continuous image of `C x C`. It is forward
`Sigma`-invariant because each semigroup element is an additive circle
endomorphism and maps both `x` and `y` back into `C`. Since an infinite compact
metric space has an accumulation point, choose distinct `x_k in C` converging
to `x in C`. Then the nonzero points `x_k-x` converge to zero, so zero is
non-isolated in `D`. Lemma IV.2 gives `D=T`.

On the other hand, the first paragraph put every point of `C` in `Q/Z`, so
every difference in `D` is rational modulo one. Hence `D subset Q/Z`, which
cannot equal `T` (for example, the class of `sqrt(2)` is irrational). This is
a contradiction. Therefore `C` is finite. QED.

The difference-set step is essential. Theorem IV.1 alone only excludes
irrational points from a proper invariant set; it does not, by itself, say
that a closed all-rational set is finite.

## 5. Positive-expansive stabilization

We use the following convention. A continuous map `f:X->X` on a compact
metric space is **positively expansive with constant `c>0`** if

```text
[d(f^k(x),f^k(y)) < c for every k>=0] implies x=y.
```

### Lemma 5.1 (neighborhood convergence of nested compacta)

Let `K_0 superset K_1 superset ...` be compact subsets of compact `X`, and put
`F=intersection_n K_n`. For every open neighborhood `U` of `F`, some `K_N` is
contained in `U`.

**Proof.** Otherwise choose `x_n in K_n\U`. A convergent subsequence has limit
`x`. For each fixed `m`, all sufficiently late terms lie in the closed set
`K_m`, so `x in K_m`; hence `x in F subset U`. But all terms lie in the closed
set `X\U`, so `x notin U`, a contradiction. QED.

### Theorem 5.2 (finite-intersection stabilization)

Let `f` be continuous and positively expansive on compact metric `X`. Let
`K_0 superset K_1 superset ...` be compact sets satisfying
`f(K_n) subset K_n` for every `n`. If `F=intersection_n K_n` is finite, then
there is `N` such that

```text
K_N=K_(N+1)=...=F.
```

This includes empty `F` and finite sets on which `f` is merely preperiodic,
not invertible or periodic.

**Proof, empty case.** If every `K_n` were nonempty, the finite-intersection
property for nested compact sets would make their intersection nonempty.
Thus some `K_N` is empty. Every later set is then empty, so stabilization
holds.

**Proof, singleton case.** Suppose `F={p}`. Forward invariance gives `f(p)=p`.
Choose `0<r<c` and apply Lemma 5.1 to `U=B(p,r)`, obtaining
`K_N subset U`. If `x in K_N`, all `f^k(x)` remain in `K_N subset B(p,r)`,
while `f^k(p)=p`. Positive expansivity gives `x=p`, so `K_N=F`.

**Proof, finite case with at least two points.** Let

```text
s = min {d(p,q) : p,q in F and p!=q} > 0.
```

Because `f(F) subset F` and `F` is finite, continuity at the points of `F`
allows one radius `r>0` such that

```text
r<c,   r<s/3,
and d(x,p)<r implies d(f(x),f(p))<s/3 for every p in F.
```

Apply Lemma 5.1 to `U=union_(p in F) B(p,r)` and choose `N` with
`K_N subset U`. Fix `x in K_N` and choose `p in F` with `d(x,p)<r`.
Inductively we claim

```text
d(f^k(x),f^k(p))<r for every k>=0.
```

Assume it at `k`. Continuity gives
`d(f^(k+1)(x),f^(k+1)(p))<s/3`. Forward invariance puts
`f^(k+1)(x)` in `K_N subset U`, so it lies within `r` of some `q in F`.
Therefore

```text
d(q,f^(k+1)(p)) < r+s/3 < 2s/3 < s.
```

Both points on the left belong to `F`; by the definition of `s` they must be
equal. Thus the next iterate is within `r` of `f^(k+1)(p)`, proving the
induction. Since `r<c`, positive expansivity gives `x=p`. Hence `K_N subset F`;
the reverse inclusion follows from the definition of `F`. Decreasingness then
gives equality at every later depth. Notice that this argument only follows
the deterministic finite itinerary `p,f(p),f^2(p),...`; it never assumes that
`f|F` is injective. QED.

### Proposition 5.3 (explicit expansivity for times ten)

`T_10` on `T` is positively expansive with constant `c=1/100`.

**Proof.** For distinct `x,y`, let `delta=d(x,y) in (0,1/2]`. If
`delta>=1/100`, time zero separates them. Otherwise let `k` be the least
integer with `10^k delta>=1/100`. Minimality gives

```text
1/100 <= 10^k delta < 1/10.
```

Choose the representative of `x-y` of absolute value `delta`. At time `k`
its multiplied absolute value lies below `1/2`, so no nearer integer changes
the circle distance. Therefore

```text
d(T_10^k(x),T_10^k(y))=10^k delta>=1/100.
```

The contrapositive is precisely positive expansivity with the stated strict
constant. QED.

### Corollary 5.4 (word-dependent finite depth)

For every fixed nonempty `w`, there is `R_0=R_0(w)` such that

```text
Core(w,R)=C_infinity(w) and Core(w,R) is finite for every R>=R_0.
```

**Proof.** T44 gives compactness, decreasingness, and forward `T_10`
invariance of the cores. Theorem 4.1 makes their intersection finite.
Apply Theorem 5.2 and Proposition 5.3. QED.

## 6. Exact T48/T46-to-T72 bridge

Fix the nonempty `w`, its proof `hw`, and a stabilized depth `R_0` from
Corollary 5.4. Let

```text
G = carryKMPGraph w hw R_0,
rho = coordinateZeroProjection.
```

The following chain retains the synthetic endpoint start, all endpoint carries
in `[-1,16]`, inclusive coordinates `0,...,R_0`, start reachability, liveness,
cyclicity, complete SCCs, internal hidden walks, and coordinate-zero
projection.

### Step 6.1: finite core to finite endpoint-complete language

T48's kernel-checked `graphLanguage_finite_iff_core_finite` states exactly

```text
G.InfiniteLabelLanguage.Finite iff Core(w,R_0).Finite.
```

Its proof uses `graphEvaluation_image_eq_core` and finite fibers, so decimal
endpoint multiplicity is not discarded. Corollary 5.4 therefore makes the
complete accepted infinite-label language finite.

### Step 6.2: finite language to T46's reachable-live criterion

T46's kernel-checked
`infiniteLabelLanguage_finite_iff_liveSCCCriterion` gives
`G.LiveSCCCriterion`. Thus for every state `q` that is reachable from the
synthetic start, live, and cyclic, its complete SCC is terminal in the
reachable-live graph and every SCC vertex has exactly one internal
reachable-live edge. Edge uniqueness includes the label; parallel differently
labeled choices are not collapsed.

### Step 6.3: T46 criterion to universal internal projected periodicity

We verify the semantic predicate used by T72. Fix such a `q`, a vertex `v` in
its SCC, and an internal right-infinite walk `z` from `v`. Every edge `z_n` is
valid and has source and target in the SCC. Its source and target are reachable
because `q` is reachable and the SCC is strongly connected. They are live
because the corresponding tails of `z` are infinite walks. Hence every `z_n`
is one of the internal reachable-live edges to which T46's uniqueness applies.

The graph has finitely many states, so two source states repeat: for some
`i<j`, `(z_i).src=(z_j).src`. Uniqueness at that source gives `z_i=z_j`,
including equality of labels and destinations. Applying uniqueness repeatedly
at the equal successor sources gives

```text
z_(i+k)=z_(j+k) for every k>=0.
```

Thus the edge stream, and hence `rho(z_n)`, is eventually periodic with
preperiod `i` and positive period `j-i`. This proves T72's
`G.EveryInternalProjectionEventuallyPeriodic q rho` for every reachable,
live, cyclic `q`, with exactly the quantifiers in
`GlobalEveryInternalProjectionEventuallyPeriodic`.

### Step 6.4: semantic periodicity to the exact T72 certificate

T72's kernel-checked
`globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic`
now yields

```text
G.GlobalPrimitivePhaseCriterion rho.
```

Equivalently, by T72's endpoint-complete T48 specialization
`endpointComplete_global_primitivePhase_iff_coordinateZeroEventuallyPeriodic`,
the exact coordinate-zero projected-phase certificate succeeds at depth
`R_0(w)`. T72 constructs bounded primitive roots and compatible vertex phases;
the argument above does not substitute a weaker eventual-periodicity checker.

Combining the sections gives the final qualitative statement

```text
for every w : List (Fin 10), w != [],
  there exists R : Nat such that
    GlobalPrimitivePhaseCriterion
      (carryKMPGraph w hw R) coordinateZeroProjection.
```

This is word-dependent eventual success only. No estimate for `R(w)`, no
function of `|w|`, no common depth across words, no uniform linear rate, no C6,
and no C1 follows.

## 7. Dependency and claim audit

1. New claims in this note are `proof sketch`, not machine-checked.
2. Imported T44/T46/T48/T72 declarations are kernel-checked under their
   recorded axiom audits; the note uses their exact statements named above.
3. Furstenberg Lemma IV.2 and Theorem IV.1 are `literature-checked` against the
   pinned PDF and exact printed/PDF pages 47-48.
4. T73 is not a premise.
5. The canonical pi entropy question remains open.
6. C6 and C1 remain open, and no claim about either is made here.
