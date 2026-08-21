# T140: hypergraph-container census applicability audit

Audit date: 2026-08-12 UTC.

The two retained source theorems are `literature-checked` against the pinned
PDFs and exact locators in `SOURCE_PINS.md`. The encodings, substitutions,
entropy tests, and novelty comparisons are `proof sketch` deductions. The
finite replay is an `experiment`: it checks hashes, source anchors, and finite
identities, not an asymptotic theorem or a statement about pi.

```text
PRIMARY_SOURCE_COUNT: 2
PRIMARY_SOURCE_CAP: 6
RETAINED_THEOREM_COUNT: 2
RETAINED_THEOREM_CAP: 2
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement and normalized scope

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether, for every integer `A>=1`, every sufficiently large depth `n`
has some `N>=1` for which `A*n*Q_pi(n,N)<=N^2`. In `Q_pi`, pairs are ordered,
all diagonal pairs are retained, circle distance is used, and the cutoff is
strict. This report does not alter or answer that question. It audits a
related symbolic census only (canonical ambiguities A10, A13, and A14).

The source URL is local provenance, not an external Erdos Problems URL: the
statement says it was formulated by this system on 2026-07-22. That provenance
is preserved in the vendored file.

### 1.1 Fixed fingerprint parameters

Let `D={0,...,9}`. For every integer `N>=10^8`, fix

```text
kappa = 1/4,                 rho = 1/4,
k = floor((1/4)*log_10 N),   M_k = {ceil(k/2),...,k},
L = N+k-1.
```

A candidate word is `z=(z_0,...,z_(L-1)) in D^L`. The cutoff restricts starts,
not symbols read: all starts are `0<=i<N`, and a depth-`m<=k` block may use
the endpoint `i+m-1<=N+k-2=L-1`. There is no wrapping or padding.

For `w in D^m`, put

```text
c_z(w;m,N) = #{0<=i<N:(z_i,...,z_(i+m-1))=w},
E_z(m,N)   = sum_(w in D^m) c_z(w;m,N)^2.
```

Thus

```text
E_z(m,N)=#{(i,j) in {0,...,N-1}^2:W_i^m=W_j^m}.            (1.1)
```

Equation (1.1) counts ordered pairs and includes exactly `N` diagonal pairs.
The audited high-collision event is the explicit set

```text
B_N = {z in D^L:
       #{m in M_k:E_z(m,N)>=N^2/(4m)} >= ceil(k/4)}.        (1.2)
```

The threshold and positive-density convention are frozen before theorem
substitution. The lower endpoint ensures `k>=2`, so all `m in M_k` are
positive and (1.2) is defined. All conclusions concern sufficiently large `N`
in this domain.

### 1.2 Required entropy certificate

A word container is a subset `C subset D^L`. A census is a finite family
`C_(N,k) subset P(D^L)` covering `B_N`. All logarithms in the certificate are
natural. The required output is one explicit fixed `delta>0` and, for every
sufficiently large `N`,

```text
log |C_(N,k)| + max_(C in C_(N,k)) log |C|
  <= (1-delta)*N*log 10.                                  (ENT)
```

The baseline is exactly `N log 10`, as required by the agenda, not `L log 10`.
The extra `k-1=O(log N)` symbols are endpoint data and cannot absorb a fixed
linear saving. A theorem that only counts arbitrary vertex subsets, labels at
each start independently, or one constructed word does not establish (ENT).

## 2. Bounded source search

The search stopped after two primary papers and retained exactly two theorems.

| ID | primary source | retained theorem | role |
|---|---|---|---|
| S1 | Saxton--Thomason, *Hypergraph containers* | Theorem 3.4 | explicit co-degree function, independent/edge-sparse container theorem |
| S2 | Balogh--Morris--Samotij, *Independent sets in hypergraphs* | Theorem 2.2 | density/supersaturation premise plus bounded codegrees for independent sets |

These are independent foundational formulations. No application theorem is
silently counted as a third retained theorem. Exact versions, URLs, DOI data,
hashes, theorem statements, and physical/printed pages are in
`SOURCE_PINS.md`. Retrieval succeeded for both sources.

## 3. Retained source theorems

### 3.1 S1: Saxton--Thomason Theorem 3.4

For an `r`-uniform hypergraph `G` of order `v` and average degree `d`, S1
Definitions 3.1--3.3 (printed pp. 11--12; physical PDF pp. 11--12) define

```text
d(sigma)=#{e in E(G):sigma subset e},
d^(j)(x)=max{d(sigma):x in sigma, |sigma|=j},
delta_j*tau^(j-1)*v*d=sum_x d^(j)(x),
delta(G,tau)=2^(binom(r,2)-1)
             *sum_(j=2)^r 2^(-binom(j-1,2))*delta_j,       (3.1)
mu(S)=(v*d)^(-1)*sum_(x in S)d(x).
```

Theorem 3.4 (printed pp. 13--14; physical PDF pp. 13--14) assumes
`delta(G,tau)<=zeta`. For every independent `I` it gives a fingerprint tuple
`T=(T_(r-1),...,T_0)` and a container `C(T)` with

```text
I subset C(T),
|T_i|<=2*tau*v/zeta^2,
mu(C(T))<=1-1/r!+4*zeta+2*r*tau/zeta.                     (3.2)
```

The same conclusion also covers sets satisfying either a displayed
degeneracy condition or

```text
e(G[I]) <= 2*r*tau^r*e(G)/zeta.                           (3.3)
```

The direction in (3.3) is an upper edge bound. S1 does not state that sets
with many induced edges have a compressed census.

### 3.2 S2: Balogh--Morris--Samotij Theorem 2.2

S2 Definition 2.1 (printed p. 11; physical PDF p. 11) calls `H`
`(F,epsilon)`-dense when `F` is increasing and

```text
e(H[A])>=epsilon*e(H) for every A in F.                   (3.4)
```

S2 defines `deg_H(T)` and `Delta_l(H)` on printed pp. 11--12. Theorem 2.2
(printed p. 12; physical PDF p. 12) fixes the uniformity `r` and constants
`c,epsilon`, then supplies a constant `C=C(r,c,epsilon)`. It assumes

```text
0<p<1,
|A|>=epsilon*v(H) for every A in F,
Delta_l(H) <= c*p^(l-1)*e(H)/v(H),  1<=l<=r,              (3.5)
```

and concludes that every **independent** set `I` has a fingerprint `g(I)` of
size at most `C*p*v(H)` and

```text
I\g(I) subset f(g(I)),   f(g(I)) notin F.                 (3.6)
```

The theorem does not cover edge-rich sets. Taking
`F={A:e(H[A])>=epsilon e(H)}` makes (3.4) tautological, but (3.6) still only
describes independent sets and does not count members of `F`.

## 4. Encoding A: exact block-label collision graph

Fix `m`. Let `G^lab_(N,m)` be the ordinary graph

```text
V=[N]_0 x D^m,
{(i,u),(j,u)} in E iff i<j.                                (4.1)
```

Here `[N]_0={0,...,N-1}`. It is the disjoint union of `10^m` copies of `K_N`,
so, with S1 notation,

```text
r=2, v=N*10^m, e=10^m*binom(N,2), d=N-1,
d^(2)(x)=1,
delta_2=delta(G^lab,tau)=1/(tau*(N-1)).                   (4.2)
```

The label set of a word is

```text
I_z^m={(i,W_i^m):0<=i<N}.
```

Overlap consistency is imposed by `z`, not by the graph. Directly from
(4.1),

```text
e(G^lab[I_z^m])=(E_z(m,N)-N)/2.                           (4.3)
```

Thus this graph preserves the exact ordered, diagonal-inclusive convention.

### 4.1 S1 substitution

Take `zeta=1/48`. The co-degree hypothesis requires

```text
tau >= 48/(N-1).                                          (4.4)
```

The independent-set clause means `E_z=N`, the minimum possible energy, so it
has the opposite direction from (1.2). The edge-sparse extension (3.3) becomes

```text
(E_z-N)/2 <= 4*tau^2*10^m*binom(N,2)/zeta.                (4.5)
```

Equation (4.5) is still an upper bound. Choosing `tau` large enough can make
it cover all word-label sets, but then the theorem does not distinguish high
collision from low collision.

### 4.2 Entropy substitution

Even the favorable independent-container size from (3.2) lives in the
`N*10^m`-vertex label space. A container with at most `alpha*N*10^m` labels
can allow, by AM--GM, as many as

```text
product_(i<N) #{u:(i,u) in C} <= (alpha*10^m)^N           (4.6)
```

independent start labels. Its logarithm is
`m*N*log 10+N*log alpha`, not `(1-delta)N log 10`.
Most label choices in (4.6) are not overlapping blocks of any word. S1 gives
no theorem preserving that consistency. Importing consistency by a separate
specification or global-incidence argument would duplicate the T128/T131
lane. Therefore Encoding A supplies neither a high-collision supersaturation
bridge nor (ENT).

**CARD A RESULT: theorem inapplicable as a sufficient certificate.** This does
not falsify a possible compressed census or another container encoding.

## 5. Encoding B: digit-assignment collision hypergraph

This encoding retains the correct `O(N)` digit ambient space. Fix `m in M_k`
and put `L=N+k-1`. Define the simple `2m`-uniform hypergraph `H^dig_(N,k,m)` by

```text
V=[L]_0 x D.
```

For starts `0<=i<j<N` with `j-i>=m` and a block `u in D^m`, include the edge

```text
e(i,j,u)={(i+t,u_t):0<=t<m} union
         {(j+t,u_t):0<=t<m}.                              (5.1)
```

The lag condition makes the two coordinate intervals disjoint, so every edge
has exactly `2m` distinct vertices. Different `(i,j,u)` give different edges.
For a word let

```text
X_z={(q,z_q):0<=q<L}.
```

Then `e(H^dig[X_z])` is exactly the number of unordered equal-block pairs at
nonoverlapping starts. Put

```text
P_(N,m)=#{(i,j):0<=i<j<N,j-i>=m}
       =(N-m)(N-m+1)/2.
```

The complete hypergraph parameters are

```text
r=2m, v=10L, e=P_(N,m)*10^m,
d_avg=r*e/v=2m*P_(N,m)*10^(m-1)/L.                        (5.2)
```

For every vertex subset `sigma`, its codegree is

```text
d(sigma)=#{(i,j,u):j-i>=m and sigma subset e(i,j,u)},      (5.3)
Delta_l=max_(|sigma|=l)d(sigma),
d^(l)(x)=max_(x in sigma,|sigma|=l)d(sigma).               (5.4)
```

Equations (5.3)--(5.4), not a linear-hypergraph surrogate, are the codegrees
used below.

### 5.1 Elementary high-collision supersaturation bridge

There are at most `N*(m-1)` unordered equal-block pairs whose positive lag is
less than `m`. Hence

```text
e(H^dig[X_z]) >= (E_z(m,N)-N)/2-N*(m-1).                  (5.5)
```

If `E_z(m,N)>=N^2/(4m)` and `N>=16m^2`, then

```text
e(H^dig[X_z]) >= N^2/(16m).                               (5.6)
```

This is a genuine high-collision supersaturation bridge for each good depth.
It is elementary and is not counted as a third source theorem. It is also not
enough: the retained theorems must cover the edge-rich sets and have usable
codegrees.

### 5.2 Explicit second-codegree obstruction

For `m>=2`, choose a coordinate `q` with
`m-1<=q<=floor(N/2)-1` and digits `a,b`. The pair
`{(q,a),(q+1,b)}` lies in at least

```text
(m-1)*(N/2-m)*10^(m-2)                                   (5.7)
```

edges: choose one of the `m-1` starts placing the adjacent coordinates in
one block, choose a disjoint second start to the right, and choose the other
`m-2` block digits. Floors only improve the bound when `N` is even; the replay
checks the exact finite version.

Consequently, for `N>=8m` and `m>=2`, summing (5.7) over at least
`10*(N/2-m)` vertices and using `v*d=r*e<=m*N^2*10^m` gives

```text
delta_2 >= 9/(1280*tau).                                  (5.8)
```

In S1's co-degree function the `delta_2` coefficient is
`2^(binom(2m,2)-1)`. Therefore

```text
delta(H^dig,tau)
 >= 2^(binom(2m,2)-1)*9/(1280*tau).                       (5.9)
```

For (3.2) to give any nontrivial degree-measure saving, its right side must be
strictly below one. This requires

```text
4*zeta+2*(2m)*tau/zeta < 1/(2m)!,                         (5.9a)
```

and hence `tau<zeta/(4m*(2m)!)<1`. Combining this necessary condition with
(5.9) makes `delta(H^dig,tau)<=zeta` impossible for growing `m`. The
overlapping coordinates, not a missing logarithmic factor, destroy the useful
S1 codegree certificate.

### 5.3 S2 density and codegree substitutions

Every digit transversal `X_z` contains exactly one digit at each coordinate.
For each start pair `(i,j)`, at most one block `u` can produce an edge inside
`X_z`. Therefore

```text
e(H^dig[X_z]) <= P_(N,m),
e(H^dig[X_z])/e(H^dig) <= 10^(-m).                        (5.10)
```

S2 fixes `epsilon>0` before Theorem 2.2 is applied. Thus no fixed positive
`epsilon` can put these growing-depth transversals in its fixed-density regime.
The absolute lower bound (5.6) is genuine, but is only a `10^(-m)`-scale
fraction of the ambient hypergraph and is not premise (3.4).

For S2, (5.7) and (5.2) yield the exact lower substitution

```text
Delta_2/(e/v)
 >= (m-1)*(N/2-m)*L / (10*P_(N,m)).                       (5.11)
```

This is bounded below by a positive multiple of `m` in the displayed range.
Thus (3.5) at `l=2` forces `p` at least a positive multiple of `m/c`, contrary
to `p<1` for fixed `c` once `m` grows. Allowing `c` to grow makes the
unspecified `C(r,c,epsilon)` grow and supplies no uniform entropy constant.
Also S2 fixes `r=2m`, while here `m` tends to infinity. Even if these premises
held, Theorem 2.2 still covers only independent sets, whereas (5.6) makes
every audited set edge-rich.

### 5.4 Multidepth and entropy endpoint

For a word in `B_N`, at least `ceil(k/4)` distinct hypergraphs satisfy (5.6)
for all sufficiently large `N`, because `m<=k=O(log N)` implies `N>=16m^2`.
Neither theorem covers those edge-rich transversals at even one depth, so no
intersection or product of theorem-generated families covers `B_N`.
Accordingly the required objects `C_(N,k)` are not produced and there is no
source-derived `delta>0` to insert into (ENT).

This is a failed sufficient certificate, not a lower bound on `|B_N|`.

**CARD B RESULT: theorem inapplicable as a sufficient certificate.** The
failure occurs at theorem direction and logarithmic-depth codegrees, before a
fixed entropy saving can be certified.

## 6. Theorem-level T89--T139 novelty comparison

Verification level is part of every row. `LC/PS` means source statements are
literature-checked but local deductions are proof sketches; `PS` means an
unverified note; `MC` applies only to named Lean declarations and never to an
open premise. Comparator reports and readable Lean modules are archived in
`prior_evidence.tar.gz`; exact members, SHA-256 values, titles/declarations,
and verification levels are indexed in `PRIOR_INDEX.md`.
No comparator deduction is used to prove Sections 4--5.

| item | available theorem-level fingerprint and level | T140 boundary |
|---|---|---|
| T89 | adjacent exact-arithmetic obstruction models, LC/PS | low factor complexity explains large energy; excluded, not a census |
| T90 | fixed-point expanding-map models, LC/PS | pointwise discrepancy/model dynamics, not bad-word enumeration |
| T91 | synchronization-model note, PS | overlap endpoint warning only |
| T92 | constant-run discriminator note, PS with named MC helper | one-family charging, not census |
| T93 | fixed Stoneham sibling note, LC/PS | rational skeleton, not census |
| T94 | paperfolding tensor-square recurrence note, PS/experiment | exact model recurrence, not entropy containers |
| T95 | universal exact-word charging note, PS | short-to-remote charging, not census |
| T96 | Stoneham family note, LC/PS | rational skeleton, not census |
| T97 | paperfolding diagonal-collision note, PS | exact model profile, not census |
| T98 | exact-word/near-return transport note, PS with MC inputs | transport audit only |
| T99 | exceptional-prime Stoneham note, LC/PS | model obstruction, not census |
| T100 | exact-word charging, named MC artifact in notes | overlap-period charging, not census |
| T101 | paperfolding splitting-failure note, PS | warns high energy need not imply T14 splitting |
| T102 | generalized Stoneham order profiles note, LC/PS | arithmetic classification, not census |
| T103 | positive-entropy Toeplitz tower audit, LC/PS | structured collision-rich model, not ambient census |
| T104 | bounded cross-domain mechanism scout, LC/PS | Mahler/fractal/metric mechanisms; no containers |
| T105 | additive-energy and sum-product scout, LC/PS | additive-set energy is not word-collision enumeration |
| T106 | `FiniteBranchingResonanceTree.lean`, named MC conditional declarations in `PRIOR_INDEX.md` | Fourier resonance branching, not census |
| T107 | `T107AveragedTriangularFejer.lean`, named MC conditional declarations in `PRIOR_INDEX.md` | same multidepth geometry, opposite low-defect mechanism; not imported |
| T108 | `T108LiteralTransport.lean`, named MC conditional declarations in `PRIOR_INDEX.md` | metric transport, not census |
| T109 | recovered rejected robustness report, PS | warning: failed sufficient certificates are not necessary obstructions |
| T110 | higher-order uniformity scout, LC/PS | fixed-order uniformity, not growing-depth census |
| T111 | remote decimal-label separation, LC/PS | exponential factor complexity/specification lane excluded |
| T112 | carry-cocycle spectral/local-limit scout, LC/PS | finite-state Fourier mechanism, not census |
| T113 | effective-avoidance note, LC/PS | existential sibling avoidance, not census |
| T114 | interpolation-determinant occupancy scout, LC/PS | rank/determinant lane, not containers |
| T115 | substitution Riesz recursion scout, LC/PS | model Fourier recursion, not census |
| T116 | finite-scale avoidance selector, LC/PS | constructive selector, not inverse census |
| T117 | Legendre pattern-cancellation audit, LC/PS | low-collision character model, not bad-word census |
| T118 | cyclotomic short-orbit audit, LC/PS | rational orbit arithmetic, not census |
| T119 | recovered collision-versus-rank report, LC/PS but package incomplete | predictive/Hankel/Prony rank compression explicitly excluded |
| T120 | countable-state renewal scout, LC/PS | measure/path mismatch, not census |
| T121 | aggregate word-collision L2 scout, LC/PS | global Parseval/L2 route explicitly excluded |
| T122 | recovered rejected discrepancy report, PS | offline discrepancy, not containers |
| T123 | recovered parked named-orbit report, LC/PS | effective specification; accepted recovery is T128 |
| T124 | arithmetic monodromy note, LC/PS | expander sibling, not census |
| T125 | multiplicative block-collision scout, LC/PS | global subset-correlation L2, excluded |
| T126 | reduced H1 coefficient-orbit note, LC/PS | valuation/orbit arithmetic, not census |
| T127 | clean-restart cross-domain scout, LC/PS | negative delta, no containers |
| T128 | effective named-orbit block control, LC/PS | definitive specification/de Bruijn exclusion |
| T129 | no direct report or declaration in refreshed snapshot; only T136 correction | comparison unavailable; no theorem-level novelty or duplication claim inferred |
| T130 | decimal collision to S-unit audit, LC/PS | growing-rank equation counting, not census |
| T131 | balanced integral cycle-flow scout, LC/PS | offline incidence/specification, excluded |
| T132 | weighted multi-modulus collision audit, LC/PS | projection majorization, not census |
| T133 | centered valuation-transducer audit, LC/PS | rational orbit range, not census |
| T134 | zero-cylinder occupancy audit, LC/PS | one fiber only, not whole-energy census |
| T135 | coordinate-projection Renyi-2 audit, LC/PS | marginal tensorization fails; not reused for entropy |
| T136 | post-T133 delta scout, LC/PS | negative cross-domain inventory, no containers |
| T137 | tensor Lorenz-meet note, PS/experiment | profile model only; all dependent conclusions remain conditional |
| T138 | rejected result only; listed artifacts absent | reviewer records exact T104 duplication; supplies no novelty premise |
| T139 | absent from knowledge snapshot and recent results | comparison unavailable; T139 nonduplication is not asserted |

No readable T89--T138 artifact contains the complete supersaturation-plus-
container census fingerprint. That is not promoted to a full T89--T139 novelty
claim: T129 lacks a direct report and T139 is unavailable. Those rows are
theorem-level availability failures, not claims of distinction. The candidate
is rejected independently by Sections 4--5, so neither unavailable item is a
mathematical premise and no surviving novelty claim depends on adjudicating it.

The named exclusions are therefore explicit:

1. Counting words via bounded factor complexity would duplicate T89/T111.
2. Predictive, Hankel, Prony, or automaton rank would duplicate T119.
3. Parseval or aggregate collision L2 would duplicate T121/T125.
4. De Bruijn, specification, or integral-flow incidence would duplicate
   T123/T128/T131.
5. Multiplying projected collision bounds would duplicate T135's rejected
   overlapping-coordinate tensorization.
6. Assuming the target total collision decay would restate T7.
7. Turning positive-density depths into T107 boundary/Fourier good rows would
   require T107's independent analytic premise and reverse the audited event.

## 7. Independent arithmetic transfer premise

Suppose an independently proved combinatorial census gives families
`C_(N,k)` satisfying (ENT), and define

```text
U_N = union_(C in C_(N,k)) C subset D^(N+k-1).             (7.1)
```

**PI-CONTAINER-EXCLUSION-T140 (`conjecture`; independent unproved arithmetic
transfer premise; not asserted).** For an unbounded sequence of `N>=10^8`,
the exact length-`N+k-1` decimal segment `z_pi^(N)` of pi, with
`k=floor((1/4)log_10 N)`, satisfies

```text
z_pi^(N) notin U_N.                                       (7.2)
```

The combinatorial census and arithmetic exclusion are logically independent;
S1 and S2 supply neither. If the containers cover `B_N`, (7.2) would imply
only that this pi segment is outside the related symbolic set `B_N` at those
cutoffs. This report draws no fixed-pi, C1, or C2 conclusion from that
conditional observation.

Failure of this transfer format would show only its inapplicability. It would
not falsify a fixed-pi estimate, C1, C2, or another transfer mechanism.

## 8. Replay and endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t140.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes; converts only the pinned
PDF pages and checks theorem anchors; verifies source/theorem caps; replays
ordered diagonal collision identities; counts both hypergraphs at finite
parameters and the corrected average degree; checks the exact block-label
co-degree, nonoverlap supersaturation inequality, BMS density ratio, and S1
useful-saving implication; and validates all structured endpoint, novelty,
transfer, and claim-firewall markers. These are transcription and finite
checks, not a proof of an asymptotic census.

SCOPED_VERDICT (1/1): **close**.

This closes only the audited sufficient certificate: the two foundational
container theorems, under the two explicit natural encodings, do not produce a
compressed census for high ordered, diagonal-inclusive overlapping collision
energy at logarithmically many depths. Encoding A has the wrong event direction
and an `N*10^m` label entropy; Encoding B has a real supersaturation bridge but
edge-rich sets are outside both conclusions and overlap forces fatal growing-
uniformity codegrees. No fixed `delta>0` satisfying (ENT) is certified. This is
inapplicability, not falsification. No successor is proposed, and no fixed-pi,
C1, or C2 result is asserted.
