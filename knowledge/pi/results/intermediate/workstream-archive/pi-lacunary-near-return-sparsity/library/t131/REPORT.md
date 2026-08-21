# T131: balanced integral cycle-flow scout

Search date: 2026-08-10 UTC.

```text
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 8
SEARCHED_LANE_COUNT: 4
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

The source statements and locators in `SOURCE_PINS.md` are
`literature-checked`. The graph substitutions, loss ledger, and collision
calculations below are `proof sketch` deductions. The bounded identities checked
by `verify_t131.py` are an `experiment`; finite replay is not a proof of an
asymptotic statement.

This report concerns artificial decimal words and finite decimal de Bruijn
graphs. Those are A13 siblings of the canonical question. Nothing below proves a
property of the decimal expansion of pi. No fixed-pi, C1, or C2 conclusion is
made.

## 1. Immutable statement, normalized scope, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question fixes `x=pi`, radius `10^(-n)`, ordered pairs, and the
diagonal. Its quantifiers are

```text
for every integer A>=1 there exists n0>=1 such that for every n>=n0
there exists N>=1 with A*n*Q_pi(n,N)<=N^2.
```

T131 neither changes nor answers these quantifiers. It tests the related-model
fingerprint

```text
balanced fractional flow on a decimal de Bruijn graph
  -> balanced integral circulation
  -> one ordered Euler tour
  -> one coherent family across depths
  -> logarithmic-depth ordered block-collision control.
```

The following ambiguities are fixed before using sources.

1. A depth-`m` edge is a decimal word of length `m`, not an unordered block.
2. Flow balance means equality of incoming and outgoing multiplicity at every
   length-`m-1` vertex.
3. An integral circulation need not have connected positive support. Euler-tour
   existence is used only after strong connectivity is checked.
4. A cyclic tour has one start per edge copy. A linear representative either
   appends its first `m-1` symbols, preserving all cyclic starts, or charges every
   omitted wrap start.
5. Ordering one circulation is not cross-depth nesting. Literal nesting means
   that the order-`k` finite word is an initial segment of the order-`k+1` word.
   Concatenating unrelated tours is recorded separately as splicing.
6. The logarithm in `m<=floor(kappa*log_10 N)` is base ten, and `kappa` is fixed
   before `N`.
7. Counts are ordered and diagonal-inclusive after squaring occupancies.
8. A theorem that directly assumes collision decay, T7, or T107's triangular
   boundary/Fourier premise is circular for this scout.
9. A theorem constructing a new word does not constrain pi.

## 2. Bounded clean-context search

The search stopped after seven primary sources in four lanes.

| lane | opened primary sources | retained card |
|---|---|---|
| integral discrepancy | S1 Doerr | C-TU |
| graph circulations and Euler tours | S2 Holroyd et al.; S3 Holroyd-Propp | C-EULER |
| constructive pseudorandomness | S4 Angel et al. | C-EULER |
| symbolic collision theory and nested de Bruijn constructions | S5 Fishman-Merrill-Simmons; S6 Nellore-Ward; S7 Becher-Carton | C-NEST |

Exact versions, URLs, DOI links, SHA-256 values, hypotheses, theorem numbers,
and PDF page locators are in `SOURCE_PINS.md`. The three retained theorem cards
are exactly `C-TU`, `C-EULER`, and `C-NEST`.

## 3. Common graph, endpoint, and collision definitions

Let `A={0,...,9}`. For `m>=1`, the decimal de Bruijn digraph `G_m` has

```text
V_m=A^(m-1),             |V_m|=10^(m-1),
E_m=A^m,                 q_m=|E_m|=10^m.
```

The edge `w=w_1...w_m` goes from `w_1...w_(m-1)` to
`w_2...w_m`. Let `B_m` be the signed vertex-edge incidence matrix. A
nonnegative vector `y in R^(E_m)` is a circulation when `B_m y=0`.

For a finite or infinite word `z`, depth `m`, and `N` starts, define

```text
c_w(N,m)=#{0<=i<N:(z_i,...,z_(i+m-1))=w},
V_z(N,m)=sum_(w in A^m)(c_w(N,m)-N/q_m)^2,
E_z(N,m)=sum_(w in A^m)c_w(N,m)^2.                (3.1)
```

There are exactly `N` starts, including starts whose blocks read through the
fixed tail beyond position `N-1`. Thus

```text
E_z(N,m)=N^2/q_m+V_z(N,m).                         (3.2)
```

This is the ordered, diagonal-inclusive Renyi-2 block collision count.

### 3.1 The complete loss ledger

Let a fractional target `x` have total `X=sum_e x_e`, let an integral
circulation `y` have total `M=sum_e y_e`, and write

```text
F=||x-(X/q_m)1||_2^2,       R=||y-x||_2^2.
```

Orthogonal projection to the zero-sum hyperplane gives

```text
V_cyc(y):=||y-(M/q_m)1||_2^2 <= (sqrt(F)+sqrt(R))^2.       (3.3)
```

Order the `M` edge copies and let `a(N)` count the first `N<=M` copies. Put

```text
O(N)=||a(N)-(N/M)y||_2^2.
```

Then the Euler-ordering loss is

```text
||a(N)-(N/q_m)1||_2^2
  <= (sqrt(O(N))+(N/M)*sqrt(V_cyc(y)))^2.                  (3.4)
```

If `D` starts are deleted or inserted and `C` start labels are changed while
passing from a cyclic ordering to a linear word, the centered count vector
changes in norm by at most `D+sqrt(2)C`: a deletion or insertion has projected
norm at most one, while a changed label contributes `e_v-e_u`. Hence the
endpoint loss is

```text
V_linear <= (sqrt(V_cyclic)+D+sqrt(2)C)^2.                 (3.5)
```

Appending the first `m-1` symbols of a tour gives `D=C=0`. Taking only the raw
tour symbols deletes at most `D=m-1` wrap starts.

Finally, suppose `J` separately controlled pieces are concatenated. At a fixed
depth, if piece `j` has centered cyclic variance `V_j`, pieces too short to
invoke their theorem have total length `P`, and all boundaries change at most
`C` start labels, then the cross-depth/splicing loss is

```text
V_splice <= (sum_(j controlled)sqrt(V_j)+P+sqrt(2)C)^2.    (3.6)
```

For `J` boundaries of finite words, `C<=J*(m-1)`. Equations (3.3)--(3.6) separately
expose rounding, Euler ordering, cyclic-to-linear endpoints, and nesting.

Every card is tested at

```text
m_N=floor(kappa*log_10 N),
m_N*E_z(N,m_N)/N^2 = m_N/10^m_N + m_N*V_z(N,m_N)/N^2.     (3.7)
```

## 4. C-TU: totally-unimodular circulation rounding

### 4.1 Exact source theorem and substitution

S1 defines linear discrepancy for an `r x n` matrix `A` and `p in [0,1]^n`
by minimizing `||A(p-z)||_infinity` over `z in {0,1}^n`. S1 Theorem 1 states
for every totally unimodular `r x n` matrix

```text
lindisc(A) <= 1-1/(n+1),
and, when r>=2, lindisc(A)<=1-1/r.                         (4.1)
```

S1 also records that a directed vertex-arc incidence matrix is totally
unimodular. Let `x>=0` be a fractional circulation and write
`x=floor(x)+p`. Apply (4.1) to the columns on which `p` is nonzero. It gives
`chi in {0,1}^E` with

```text
||B_m(p-chi)||_infinity<1.
```

Both `B_m p=-B_m floor(x)` and `B_m chi` are integral, so the displayed
integer vector must be zero. Therefore

```text
y=floor(x)+chi,       B_m y=0,
y_e in {floor(x_e),ceil(x_e)},       R<q_m.                (4.2)
```

S1 does not state (4.2) in de Bruijn language; (4.2) is the proof-sketch
substitution of its theorem.

For the uniform target `x=(X/q_m)1`, `F=0`, and (3.3) gives

```text
V_cyc(y)<q_m.                                               (4.3)
```

If `X/q_m>=1`, every `y_e>=1`; hence positive support is the whole strongly
connected `G_m`. S2's Euler criterion and Lemma 4.9 then order all `M=sum y_e`
edge copies in one tour. At the complete-tour endpoint `O(M)=0`. Appending the
first `m-1` symbols gives `D=C=0`, so (4.3) is the full finite-word loss.

### 4.2 Logarithmic-depth calculation

Project an order-`k` edge-count vector to order `m<=k` by summing the
`10^(k-m)` extensions of every `m`-word. Cauchy-Schwarz gives

```text
V_m <= 10^(k-m)*V_k < 10^(2k-m).                          (4.4)
```

When the tour length `N` is comparable to `10^k`, (3.2) and (4.4) yield

```text
m*E(N,m)/N^2
 <= m/10^m + O(m/10^m) -> 0                               (4.5)
```

for every moving `m<=floor(kappa*log_10 N)` with fixed `0<kappa<=1`.
The endpoint charge without appending would replace the second term by
`O(m*(10^(k-m/2)+m)^2/10^(2k))`, which also tends to zero.

### 4.3 Quantitative rejection test

`QR-TU`: set `X=q_m`. Then the uniform target is already the integral unit
circulation `x_e=1`, so (4.2) has `R=0`, `M=q_m`, and

```text
V_cyc=0,       m*E/M^2=m/10^m.                            (4.6)
```

Thus every numerical gain used in (4.5) is present before applying S1. For
nonmultiples of `q_m`, S1 gives independent rounded tours but no relation
between their edge orderings at different `k`. C-TU passes the one-tour energy
test but fails the mechanism test: in the only selected low-collision target,
integral rounding is superfluous, and the remaining exact de Bruijn tour is the
finite global-L2 mechanism already represented by T121's F-NECK calculation.
It supplies no coherent nesting theorem. `C-TU` is closed as a T121 collapse.

## 5. C-EULER: rotor ordering of one integral circulation

### 5.1 Exact source theorems and ranges

S2 defines an Eulerian digraph to be finite, strongly connected, and balanced
at every vertex. S2 Lemma 4.9 states that from a unicycle on an Eulerian
directed multigraph with `M` edge copies, exactly `M` rotor steps traverse every
edge copy once, make every rotor complete one full turn, and return to the
initial state. This is
zero ordering loss at the complete endpoint.

S4 Theorem 2 says that for arbitrary discrete probability distributions
`pi_i` on a countable set there is a deterministic sequence whose count of
each symbol through every prefix differs from its cumulative expected count by
strictly less than one. S4 pp. 5--6 further note that for a rational fixed
distribution a deterministic tie rule gives a periodic sequence and exact
counts after a denominator period. Applied separately to outgoing copies at
each vertex, a cyclic interval has local edge error less than two.

S3 assumes a finite irreducible Markov chain with rational rotor mechanism.
For each target vertex `b`, hitting-time function `k_b(v)=E_v T_b`, stationary
distribution `pi`, and

```text
K4(b)=max_v k_b(v)+d(b)/(2*pi(b))
     +(1/2)sum_(u,v)d(u)p(u,v)|k_b(u)-k_b(v)-1|,          (5.1)
```

S3 Theorem 4 proves for every time `N`

```text
|n_N(b)-N*pi(b)| <= K4(b)*pi(b).                           (5.2)
```

For an integral circulation `y`, put `d_u=sum_(e:u->*)y_e`,
`p_e=y_e/d_u`, and `pi(u)=d_u/M`. Set
`K4_star=max_(u in V_m)K4(u)`. Combining the local S4 stack bound with (5.2)
at `b=u=tail(e)` gives the proof-sketch edge estimate

```text
|a_e(N)-(N/M)y_e| < 2+y_e*K4(tail(e))/M
                         <=2+y_e*K4_star/M.                (5.3)
```

Consequently

```text
O(N) <= sum_e (2+y_e*K4_star/M)^2.                         (5.4)
```

### 5.2 Endpoint and logarithmic-depth calculation

At `N=M`, S2 gives the exact stronger statement `O(M)=0`; (3.3), (3.5), and
the C-TU rounding bound then recover (4.3)--(4.5). For a partial prefix of the
uniform unit circulation, (5.4) reads

```text
O(N) <= q_m*(2+K4_star/q_m)^2.                            (5.5)
```

If the prefix scale is `N asymp q_m`, its ordering contribution to (3.7) is

```text
O((m/q_m)*(2+K4_star/q_m)^2).                             (5.6)
```

This tends to zero if, for example,
`K4_star=o(q_m^(3/2)/sqrt(m))`. Neither S3 nor S4 gives a bound on the growth of
`K4_star` for a family of increasing de Bruijn graphs. Finiteness for each fixed
graph does not imply (5.6).

The cyclic-to-linear charge is again zero after appending `m-1` symbols and at
most `(m-1)` otherwise. None of S2--S4 relates the rotor states or edge order at
depth `m` to those at depth `m+1`, so the cross-depth term in (3.6) remains
uncontrolled unless independently balanced pieces are assumed.

### 5.3 Quantitative rejection test

`QR-EULER`: require the source-certified partial-prefix bound (5.6) to tend to
zero at `N=q_m`. This requires the displayed growth condition on `K4_star`, but the
retained theorems provide no such growing-graph estimate. At the sole escape
endpoint `N=M`, S2 makes ordering loss exactly zero, leaving only C-TU's
already-closed complete-tour calculation. C-EULER therefore either has an
unproved logarithmic-depth constant or merely orders the same T121-shaped
global incidence vector. It also supplies no nesting. `C-EULER` is closed.

## 6. C-NEST: exact and almost-exact nested de Bruijn words

### 6.1 Literal nested prefixes: Fishman-Merrill-Simmons

S5 defines a noncyclic order-`n` de Bruijn word to have length
`10^n+n-1` and contain every length-`n` word exactly once. Its equation (2.1)
defines a totally de Bruijn infinite word as one whose prefix of that length is
de Bruijn for every `n`. Corollary 4.3, for alphabet size at least four, proves
that the set of totally de Bruijn expansions has positive Hausdorff dimension.
Its proof on pp. 7--8 explicitly extends an order-`n` word to order `n+1` by
completing an Euler path after closing the prior Hamiltonian path. Decimal
alphabet size ten satisfies the range.

For one such decimal word, take `N=10^k`. The prefix contains the tail through
position `N+k-2`. For every `m<=k`, each length-`m` word is the prefix of
exactly `10^(k-m)` of the order-`k` words, so

```text
c_w(N,m)=10^(k-m),       V(N,m)=0.                         (6.1)
```

Here integrality, Euler ordering, endpoint, and literal nesting losses are all
zero. For fixed `0<kappa<=1` and `m=floor(kappa*log_10 N)`, (3.7) is

```text
m*E(N,m)/N^2=m/10^m -> 0.                                 (6.2)
```

### 6.2 Arbitrary lengths: Nellore-Ward

S6 Definition 1.1 and Proposition 1.1 define a cyclic length-`L`
`P_L^(10)` word for which every length-`m` word occurs either
`floor(L/10^m)` or `ceil(L/10^m)` times. Theorem 2.4 proves that its
`LIFTANDJOIN` operation transforms a `P_L^(10)` word into a
`P_(10L)^(10)` word by joining necklaces from a Lempel lift. Theorems 2.5 and
2.6 construct one for every `L>=1` in linear time and `O(L log 10)` space.

Let `q=10^m`, `a=floor(L/q)`, and `r=L-qa`. Proposition 1.1 gives `r`
counts equal to `a+1` and `q-r` counts equal to `a`. Therefore the exact cyclic
variance is

```text
V_cyc=r*(1-r/q)^2+(q-r)*(r/q)^2
     =r-r^2/q <= q/4.                                     (6.3)
```

Appending the first `m-1` symbols makes the endpoint loss zero.

To display rather than hide the cross-depth cost, choose one rotation for each
`P_(10^j)^(10)` word and concatenate them. At the endpoint after `J` pieces,
`N_J=sum_(j<=J)10^j asymp 10^J`. For a current depth
`m<=floor(kappa*log_10 N_J)`, pieces of length at least `m` each contribute at
most `sqrt(q)/2` in (3.6), earlier pieces have total length `P=O(m)`, and the
`J` boundaries (including the final read into the next piece) change at most
`C=O(J*m)` start labels. Hence

```text
V(N_J,m)=O(J^2*q+J^2*m^2),                                (6.4)
m*E(N_J,m)/N_J^2
 =O(m/q+m*J^2*q/N_J^2+m^3*J^2/N_J^2) -> 0                (6.5)
```

for every fixed `0<kappa<2`. Equation (6.4) is a splicing calculation, not a
claim that S6's tours are literal nested prefixes.

### 6.3 Nested perfect necklaces: Becher-Carton

S7 defines `(k,s)`-perfect and nested-perfect necklaces on preprint p. 2.
Theorem 1 states that concatenating `(s,s)`-nested perfect necklaces at
`s=2^d` gives one base-`b` point with all-prefix discrepancy

```text
D_N(({b^n x})_(n>=1))=O((log N)^2/N).                      (6.6)
```

For decimal cylinders, (6.6) gives pointwise block-count error
`O((log N)^2)`, and therefore the standard incidence-to-collision estimate

```text
E(N,m)<=N^2/10^m+O(N*(log N)^2).                           (6.7)
```

This is quoted here only as a duplication boundary: it is exactly T122's
C-NPN route, not a new T131 deduction.

### 6.4 Quantitative rejection test

`QR-NEST`: equations (6.1), (6.3), and (6.5) all pass the numerical threshold.
That success rejects novelty rather than correctness:

```text
FMS:              V=0 at nested de Bruijn endpoints;
Nellore-Ward:     V<=10^m/4 before ordering, with splicing (6.4);
Becher-Carton:    max cylinder error O(log^2 N), hence (6.7).
```

The first is exact global incidence balance, the second theorem defines its
object by direct multidepth incidence balance, and the third is literally the
T122 survivor. None is a theorem that arbitrary preselected short-cycle flows
can be coherently nested while retaining a new collision invariant. C-NEST
therefore collapses to T121's global-L2 statistic or T122's offline
incidence-balancing construction. `C-NEST` is closed by the agenda's mandatory
duplication rule.

## 7. Exact T121 and T122 comparison

Verification levels are part of this comparison. The T121 and T122 deductions
are not treated as machine-checked premises.

| item | delivered pin and level | normalized mechanism | T131 comparison |
|---|---|---|---|
| T121 | `prior-t121-REPORT.md`, SHA `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2`; source statements literature-checked, deductions proof sketch, replay experiment | Section 3 uses `E=N^2/10^m+V`; F-NECK has exact cyclic counts and an explicit `(m-1)^2` linear endpoint but no prefix transfer; its selected F-LEG route controls global L2 without max-word summation | C-TU's complete tour is exactly another `V`-first finite calculation; C-EULER changes only ordering and vanishes at the complete endpoint; C-NEST's exact or `q/4` incidence bounds feed the same identity |
| rejected T122 | `prior-t122-REJECTED-REPORT.md`, SHA `6ea3b7798ff4b211c0f6c3b514d062fbce8e518208c570231a1f2c32417845b7`; sources literature-checked, deductions proof sketch, final record rejected | online vector candidates fail because digit choices are adaptive and non-antipodal; C-NPN instead uses nested-perfect-necklace all-prefix cylinder discrepancy | C-TU avoids online digit selection but has no nesting; C-EULER orders an already chosen flow but does not choose or nest it; C-NEST/S7 is C-NPN itself, while S6 balances the same incidence vectors offline through lift-and-join |

The changed cycle-space premise therefore separates the obstructions cleanly:

```text
integrality:       cheap, and zero for the uniform flow;
Euler ordering:    exact at a full tour, but partial-prefix constants are unscaled;
multiscale nesting: available only in exact/direct incidence constructions
                    already represented by T121/T122.
```

It does not repair T122's online applicability failure; it moves the selection
offline and then assumes or constructs the incidence balance directly.

## 8. T7 and T107 noncircularity checks

The machine-checked T7 statistic is the same shape as (3.2) for pi and is
comparable to canonical near returns up to a factor three. T131 uses that only
as a target shape. No candidate is identified with the pi orbit.

T107's machine-checked conditional interface requires one increasing pi-prefix
family, weak convergence, and a positive-density triangular bound involving
both active boundary load and a Fourier remainder. S1--S7 state no such
pi-specific boundary or Fourier estimate. Assuming T7 decay or T107's
triangular premise would be circular and is not used in (3.3)--(6.7).

## 9. Separately labeled pi-transfer hypothesis

`PI-CYCLE-SHADOW` (`conjecture`; unproved and not asserted): there exist a
fixed `0<kappa<1`, one independently constructed cycle word `z`, increasing
endpoints `N_j`, and numbers `H_j` such that, with
`m_j=floor(kappa*log_10 N_j)`, for every `1<=m<=m_j`, at most `H_j` starts
`i<N_j` have different length-`m` blocks in the decimal expansion of pi and
in `z`, and

```text
m_j*H_j^2/N_j^2 -> 0.                                     (9.1)
```

Changing one start label changes the count vector by one positive and one
negative unit. Thus its centered norm changes by at most `sqrt(2)*H_j`, and a
model satisfying (6.5) would conditionally give

```text
V_pi(N_j,m)^(1/2)
 <= V_z(N_j,m)^(1/2)+sqrt(2)*H_j.                          (9.2)
```

This is a symbolic shadowing certificate tied to an independently named word,
not the assertion that pi already has low collision energy and not T107's
boundary/Fourier premise. No source supplies (9.1), and it is not tested here.
Equations (9.1)--(9.2) make no fixed-pi, C1, or C2 claim.

## 10. Replay, scope, and disposition

From a directory containing only the delivered artifacts, run

```text
python3 verify_t131.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes, source anchors, the seven
source and three candidate caps, the exact collision and arbitrary-length
variance identities on bounded examples, the complete loss markers, T121/T122
pins, unique disposition marker, absent successor, separate pi-transfer label,
and scope firewall. These are finite transcription checks only.

SCOPED_VERDICT: close (the cycle-space premise solves integrality and complete-tour ordering, but every sourced coherent low-collision realization reduces quantitatively to T121 global-L2 or T122 offline incidence balancing; no fixed-pi, C1, or C2 conclusion)
