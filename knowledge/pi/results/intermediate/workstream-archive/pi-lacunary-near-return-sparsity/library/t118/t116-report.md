# T116: effective finite-scale orbit-avoidance selector

Audit date: 2026-08-10 UTC.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 12
SEARCHED_LANE_COUNT: 4
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 1
```

Claim labels are load-bearing. The statements attributed to S1-S4 in
`SOURCE_PINS.md` are `literature-checked` against the delivered primary PDFs.
The specializations, interval recurrences, shell estimates, and `Q_x`
calculations below are `proof sketch` deductions, not machine-checked
theorems. The bounded replay is an `experiment`; it checks hashes,
transcription, and finite instances only.

This report concerns computable related-model points. It proves no statement
about `pi`, canonical C1, C2, normality of `pi`, or decimal complexity of `pi`.
A constructed sibling point is not progress on any of those fixed-point
claims.

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For real `x` and integers `n,N>=1`, write

```text
Q_x(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)x||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, and the circle
inequality is strict. The canonical question fixes `x=pi` and asks

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N) <= N^2.
```

T116 changes the point and is therefore an A13 sibling audit. The following
ambiguities are fixed throughout.

1. A source is counted once even when its PDF and text derivative are both
   delivered.
2. A candidate is retained only if a source theorem is quantitatively close
   enough to test the effective-selector fingerprint. Retention is not
   endorsement.
3. "Effective" means an algorithm which, on finite input, computes a rational
   child interval, with a proved convergence modulus and a proved invariant
   through all future stages. Nonemptiness and positive Hausdorff dimension do
   not imply this.
4. A safe macro-interval for a finite constraint is an interval all of whose
   points avoid the specified finite bad neighborhoods. An immediate game
   child may only be certified extendible; Section 3.3 distinguishes these two
   notions and computes safe intervals at the scheduled forbidden depths.
5. Positive branching slack must be a displayed computable inequality. An
   unquantified compactness or choice step fails the cheap test.
6. A finite replay can falsify a proposed constant. It cannot prove the
   universal selector or any fixed-`pi` assertion.

## 2. Bounded clean-context protocol

The search used exactly four lanes and stopped after one primary source in
each lane:

| ID | lane | source | retained candidate |
|---|---|---|---|
| S1 | algorithmic/computable avoidance | Rosenfeld-Shen weighted tree game | C-RS |
| S2 | symbolic entropy/collision coding | Fishman-Merrill-Simmons totally de Bruijn extensions | C-FMS |
| S3 | restricted-denominator approximation | Moshchevitin variable-`H` avoidance | C-MOS |
| S4 | fixed-point/lacunary game dynamics | Broderick-Fishman-Kleinbock Schmidt game | C-BFK |

Thus four primary sources are below the cap twelve, and four retained
candidates meet the cap four. No source or candidate was added merely to fill
a cap. Exact URLs, versions, hashes, printed-page locators, and derivative-line
locators are in `SOURCE_PINS.md`; `SEARCH_LOG.md` records the stopping rule.

Two candidates survive their literal effective-selector tests: C-RS and
C-FMS. C-FMS is the already-inspected T111 symbolic mechanism, retained to
make the duplication boundary explicit. C-RS is nonduplicative among the
inspected prior artifacts, including the now-readable T114 determinant/rank
audit and T115 substitution-Riesz audit. This is only a bounded fingerprint
comparison, not a novelty claim beyond the inspected corpus.

## 3. C-RS: computable variable-depth dyadic avoidance tree

### 3.1 Exact source theorem and source defect boundary

S1 Theorem 1, printed pp. 2-3, considers a `q`-ary rooted tree. A forbidden
vertex at relative depth `ell` has weight `beta^(-ell)`. Alice may add newly
forbidden vertices of total relative weight at most `omega` on each move. If

```text
1 < beta < q,  omega > 0,  beta*(1+omega) <= q,             (3.1)
```

then Bob has a strategy maintaining total forbidden weight strictly below one
in his current subtree. Theorem 2, printed pp. 3-4, states the computable
version: `beta,omega` are computable, and Alice supplies both a membership
program and a convergence modulus for the new forbidden weight. A finite
explicit list is the source's stated special case. Bob computes child weights
until a child with weight strictly below one is found.

The later S1 Theorem 8 is not used. Its displayed hypothesis is

```text
beta + 3*C/beta^(k-1) <= 2,
```

whereas its proof forbids `3*C` descendants at relative depth `k-2` and hence
invokes Theorem 1 with

```text
beta*(1 + 3*C/beta^(k-2))
  = beta + 3*C/beta^(k-3) <= 2.                            (3.2)
```

The two conditions differ by a factor `beta^2` in the second term. T116 does
not repair or quote Theorem 8. It derives the specialization below directly
from the checked general Theorems 1-2 and verifies (3.1) at every move.

### 3.2 Effective input and output

Define the positive decimal-difference set and dyadic shells

```text
D+  = {10^i-10^h : integers i>h>=0},
P_j = D+ intersect (2^j,2^(j+1)]        (j>=3).             (3.3)
```

Each `P_j` is finite and computable by integer comparison. For fixed `i`, the
block

```text
D_i={10^i-10^h:0<=h<i}
```

has `i` elements and lies in

```text
[9*10^(i-1), 10^i-1].                                     (3.4)
```

The minimum of `D_(i+1)` is `9*10^i`, more than twice the maximum of `D_i`.
A ratio-two dyadic shell therefore meets at most one decimal block. If `P_j`
meets `D_i`, (3.4) and `t<=2^(j+1)` imply the deliberately coarse bound
`i<=j+1`. Hence

```text
C_j := |P_j| <= j+1.                                      (3.5)
```

Use the binary tree and fix the rational constants

```text
q=2,  beta=3/2,  omega=1/3,
beta*(1+omega)=2.                                          (3.6)
```

For each `j>=3`, let `r_j` be the least integer `r>=3` satisfying

```text
(3/2)^(r-2) >= 9*(j+1).                                   (3.7)
```

This is an exact terminating integer loop, equivalently
`3^(r-2) >= 9*(j+1)*2^(r-2)`. Put

```text
epsilon_j = 2^(-r_j).                                     (3.8)
```

At Bob level `m=j+2`, and for each `t in P_j`, Alice lists every level

```text
L_j = m+r_j-2 = j+r_j                                     (3.9)
```

dyadic descendant of Bob's current interval which intersects

```text
B(t,j)={y in [0,1]: ||t*y||_(R/Z) <= epsilon_j}.           (3.10)
```

The list is finite and exactly computable from rational endpoints `a/t` and
`2^(-L_j)`. The bad stripes have width `2*epsilon_j/t`. Since
`t in (2^(m-2),2^(m-1)]` and `r_j>=3`, two stripes cannot meet Bob's current
level-`m` interval, and one stripe meets at most three level-`L_j`
descendants. These are the inequalities in S1 Lemma 1, printed pp. 10-11:

```text
(1-2*epsilon_j)/t > 2^(-m),
2*epsilon_j/t < 2*2^(-L_j).                               (3.11)
```

By (3.5) and (3.7), the newly forbidden weight is at most

```text
3*C_j*(3/2)^(-(r_j-2))
 <= 3*(j+1)/(9*(j+1))
 = 1/3 = omega.                                           (3.12)
```

Thus every source hypothesis is effective and (3.1) holds exactly.

### 3.3 Explicit finite-stage interval recurrence

Let `E_m` be the finite set of vertices newly announced on Alice move `m`, and
put

```text
F^m = union_(0<=u<=m) E_u.                                 (3.13)
```

Here the superscript indexes game moves, not vertex depths: `E_m` can contain
vertices deeper than `m`. Duplicates are inserted once. Vertices outside Bob's
current subtree are discarded when weights are computed. Start with

```text
p_0=0,  I_0=[0,1].                                        (3.14)
```

Suppose

```text
I_m=[p_m/2^m,(p_m+1)/2^m].                                (3.15)
```

After adding the shell `P_(m-2)` when `m>=5` (and adding nothing for empty
shells), compute for each child bit `b in {0,1}` the exact rational weight

```text
W_m(b) = sum_{v in F^m, v below child b}
           (3/2)^(-(depth(v)-(m+1))).                     (3.16)
```

Duplicate forbidden vertices are counted once. Choose

```text
b_m = 0 if W_m(0)<1, and b_m=1 otherwise,
p_(m+1)=2*p_m+b_m,
I_(m+1)=[p_(m+1)/2^(m+1),(p_(m+1)+1)/2^(m+1)],
sigma_m=1-W_m(b_m)>0.                                     (3.17)
```

The source invariant proves that at least one child has weight strictly below
one; if the left child does not, the right child does. Every comparison in
(3.16)-(3.17) is between exact rationals. Thus `sigma_m` is an exactly
computable positive rational branching margin certifying future extendibility.
There is no compactness, oracle, or tie choice in the recurrence.

The intervals are nested and have diameter `2^(-m)`. Their unique common
point is named

```text
x_RS = the point in intersection_(m>=0) I_m.              (3.18)
```

On precision input `s`, compute (3.13)-(3.17) through move `s-1` and output
`p_s/2^s`; its error is at most `2^(-s)`. Since the branch never enters any
scheduled forbidden vertex, its unique point satisfies

```text
||t*x_RS||_(R/Z) > epsilon_j for every j>=3 and t in P_j. (3.19)
```

The immediate interval `I_(m+1)` is extendible but need not yet avoid the bad
stripe scheduled at move `m`; that stripe is represented by forbidden vertices
at the deeper level `L_j`. Define the finite-constraint macro-interval

```text
K_j=I_(L_j),  where L_j=j+r_j.                             (3.20)
```

The thresholds in (3.7) increase with `j`, so `r_j` is nondecreasing and
`L_j` is strictly increasing. Hence the rational intervals `K_j` are nested.
At depth `L_j`, Bob cannot occupy any vertex forbidden for shell `P_j`, so
`K_j` is disjoint from every set `B(t,j)`, `t in P_j`. It remains inside all
earlier `K_k`; therefore every point of `K_j` avoids all shells `P_k` for
`3<=k<=j`. This is the requested safe rational subinterval at finite shell
stage `j`. The pair `(I_m,sigma_m)` certifies effective continuation between
macro-stages, while `K_j` certifies finite-stage avoidance.

### 3.4 Complete finite-scale constant and `Q_x` calculation

Minimality in (3.7) gives

```text
(3/2)^(r_j-3) < 9*(j+1).                                  (3.21)
```

Let `a=log(2)/log(3/2)<2`. Since `j+1>=1`,

```text
2^(r_j-3)
 = ((3/2)^(r_j-3))^a
 < (9*(j+1))^a
 <= (9*(j+1))^2.
```

Consequently

```text
epsilon_j=2^(-r_j) > 1/(648*(j+1)^2).                    (3.22)
```

Fix `N>=2` and `0<=i!=h<N`. The magnitude
`t=|10^i-10^h|` lies in some `P_j`. Since

```text
t < 10^N < 2^(4*N),
```

we have `j+1<=4*N`. Equations (3.19), (3.21)-(3.22) give

```text
||(10^i-10^h)*x_RS||_(R/Z) > 1/(10368*N^2).              (3.23)
```

Now fix integers `A>=1`, `n>=16*A`, and prescribe

```text
N=A*n.                                                     (3.24)
```

Because `A<=n/16`,

```text
10368*A^2*n^2 <= (10368/256)*n^4 = 40.5*n^4 < 10^n.       (3.25)
```

The last inequality holds at `n=16`, and its left-to-right ratio after
incrementing `n` is multiplied by at most `(17/16)^4/10<1`. Combining
(3.23)-(3.25), every off-diagonal ordered pair has distance strictly greater
than `10^(-n)`. Exactly the `N` diagonal pairs remain, so

```text
Q_(x_RS)(n,A*n)=A*n                     for A>=1,n>=16*A, (3.26)
A*n*Q_(x_RS)(n,A*n)=(A*n)^2=N^2.                         (3.27)
```

This is a quantified A13 sibling implication toward the T7 finite-energy
interface. It uses the canonical order, diagonal, strict radius, base 10, and
linear witness, but changes `pi` to the computable sibling `x_RS`.

## 4. C-FMS: existing effective symbolic selector

### 4.1 Exact source and selector

S2 Section 2 immediately preceding and including definition (2.1), printed
pp. 3-4, defines a non-cyclic order-`n` de Bruijn word on a `k`-letter
alphabet to have length `k^n+n-1` and to contain every length-`n` word exactly
once, then defines infinite variants. Remark 3.3, printed p. 5, gives the
Hamiltonian-cycle correction. Corollary 4.3 and its proof, printed pp. 10-11,
show for `k>=4` that every order-`n` de Bruijn prefix has order-`n+1`
extensions. Its selected family has cardinality

```text
(k-1)*((k-2)!)^(k^n).                                    (4.1)
```

Use the ordered decimal alphabet `{1,3,5,7}`. Put

```text
L_n=4^n+n-1,  w_1=1357.                                  (4.2)
```

Given `w_n`, enumerate the finite set of words of length `L_(n+1)` and choose
the lexicographically least word `w_(n+1)` which extends `w_n` and is a de
Bruijn word of order `n+1`. The source theorem proves termination. With
`k=4`, (4.1) gives

```text
3*2^(4^n)                                                  (4.3)
```

source-certified selected extensions, so the branching slack after choosing
one is at least `3*2^(4^n)-1>0`.

Let `p_n` be the decimal integer represented by `w_n`. If
`w_(n+1)=w_n u_n`, then

```text
|u_n|=3*4^n+1,
p_(n+1)=10^(3*4^n+1)*p_n+U_n,                             (4.4)
```

where `U_n` is the padded integer represented by `u_n`. The closed safe
intervals

```text
J_n=[p_n/10^L_n + 1/10^(L_n+1),
     p_n/10^L_n + 8/10^(L_n+1)]                           (4.5)
```

are rational, nested, and have diameter `7*10^(-(L_n+1))`. They retain the
entire prefix `w_n`; (4.4) and the next digit in `{1,3,5,7}` show
`J_(n+1) subset J_n`. Their unique common point is the lexicographically
selected FMS odd-digit decimal `x_FMS`. On precision input `s`, take the least
`n` with `L_n>=s` and return the lower endpoint of `J_n`. Its error is at most
`diam(J_n)<10^(-s)`. Thus (4.5) is an explicit convergence modulus and safe
child.

The deterministic specialization and interval recurrence are T116
`proof sketch` deductions. They are not terminology or a named point in S2.
They reproduce, rather than upgrade, the T111 symbolic mechanism.

### 4.2 Exact diagonal-only calculation

For fixed `n>=1`, the first `4^n` length-`n` decimal blocks of `x_FMS` are
pairwise distinct. Their integer codes are all odd. If a metric return at
radius `10^(-n)` occurred between starts `i,j<4^n`, write

```text
10^n*{10^i*x_FMS}=B_i+u,
10^n*{10^j*x_FMS}=B_j+v,             0<=u,v<1.
```

For some integer `q`, strict circle distance would give

```text
|(B_i-B_j-q*10^n)+(u-v)|<1.                               (4.6)
```

The integer in parentheses lies in `{-1,0,1}`. It is even because `B_i,B_j`
are odd and `10^n` is even, so it is zero. Thus
`B_i-B_j=q*10^n`. Both codes lie strictly between `0` and `10^n`, so
`|B_i-B_j|<10^n`; hence `q=0` and `B_i=B_j`. De Bruijn uniqueness gives
`i=j`. Therefore

```text
Q_(x_FMS)(n,N)=N              for n>=1, 1<=N<=4^n.        (4.7)
```

Taking `N=A*n`, the exact certified range is

```text
A>=1, n>=1, A*n<=4^n.                                     (4.8)
```

In particular `n>=max(1,ceil(log_2 A))` is sufficient because then
`A<=2^n` and `n<=2^n`. On (4.8),

```text
Q_(x_FMS)(n,A*n)=A*n,
A*n*Q_(x_FMS)(n,A*n)=(A*n)^2.                             (4.9)
```

This is a related computable point only. The T113 note observes the same
stronger consequence of the T111 ingredients, but T113 is an unverified note;
(4.6)-(4.9) are displayed here independently rather than treating that note
as a discharged premise.

## 5. C-MOS: variable-`H` avoidance killed by effectivity

S3 Theorem 2, printed pp. 2-3, starts with increasing `t_k`, natural `h(k)`,
decreasing positive `delta(k)`, and `0<eta<1`. It assumes that `k-h(k)` is
nondecreasing where `k>h(k)`,

```text
h(k) >= H(k-h(k),1/delta(k-h(k))),                         (5.1)
sum_(v=k-h(k)+1)^(k-1) delta(v) <= (1-eta)*eta/4,          (5.2)
sum_(v=1)^k delta(v) <= (1-eta)/16 when k<=h(k),           (5.3)
```

and concludes only that

```text
{x in [0,1]: ||t_k*x||>delta(k) for all k>=1}
```

is nonempty. The T113 note argues, as an unverified `proof sketch`, that the
ordered decimal differences satisfy these hypotheses with

```text
eta=1/2, delta(k)=1/(64*k^2),
h(k)=ceil(8*sqrt(k)*log(64*k)),                            (5.4)
```

and then give `Q_x(n,A*n)=A*n` for `n>=16*A`. T116 does not import that note
as proof.

Cheap-kill failure: S3 supplies no computable member, no convergence modulus,
and no rule choosing one finite component with certified continuation through
all future sets. Its finite sets have positive lower bounds, but those bounds
decay with the stage. A nonempty computable finitely branching tree can lack a
computable path. Thus (5.1)-(5.3), even when all data are computable, do not
certify one safe rational child at each stage. C-MOS is rejected at the first
effectivity requirement, not at its avoidance scale.

## 6. C-BFK: Schmidt-game lacunarity killed by decimal differences

S4 Theorem 1.3, printed p. 3, and Theorem 4.1, printed pp. 8-9, require a
lacunary matrix sequence with

```text
Q=inf_k ||M_(k+1)||/||M_k|| > 1,                           (6.1)
```

a uniformly discrete target sequence, and a support carrying a
`(C,gamma)`-absolutely decaying measure. For

```text
alpha < 1/(2*C^(1/gamma)+1),
epsilon=1-C*(2*alpha/(1-alpha))^gamma>0,                   (6.2)
```

the proof fixes arbitrary `0<beta<1`, chooses

```text
r=floor(log_(1/(1-epsilon)) N)+1,
(alpha*beta)^(-r)<=Q^N,                                   (6.3)
rho<min(alpha*beta*delta/4,rho_(C,gamma)),
c=min(rho*(alpha*beta)^(2*r-1),delta/4),                  (6.4)
```

and obtains a winning avoidance set.

For the increasing decimal differences, the last two values in block `D_i`
are `10^i-10` and `10^i-1`, whose ratio tends to one. Hence the increasing
sequence has infimum adjacent ratio exactly one and fails (6.1). Moreover,
S4 Lemma 3.2, printed pp. 7-8, selects a center from a positive-measure set by
integration; no computable presentation or rational-center algorithm is among
its hypotheses. C-BFK therefore fails both the decimal-difference lacunarity
test and the safe-rational-child test. No `Q_x` calculation can start.

## 7. Cheap kill ledger

| candidate | unquantified compactness/choice | computable positive branching slack | one safe rational child per stage | result |
|---|---|---|---|---|
| C-RS | none: exact rational finite-list recurrence (3.13)-(3.17) | passes: `sigma_m=1-W_m(b_m)>0` is an exact rational continuation margin | passes: macro-child `K_j=I_(L_j)` is disjoint from all bad sets through shell `j` | survivor |
| C-FMS | none: finite lexicographic enumeration with source-proved termination | passes: `3*2^(4^n)-1>0` unused children | passes: rational interval (4.5) | survivor, already T111 |
| C-MOS | fails: source concludes nonemptiness without an effective branch | not a computable local branching margin | fails: no future-extendibility decision | reject |
| C-BFK | fails as stated in Lemma 3.2's measure selection | irrelevant after `Q=1` failure | fails: no rational-center selector in hypotheses | reject |

These are certificate-applicability tests. Failure says that the cited theorem
does not supply the T116 mechanism; it is not an impossibility theorem for all
other constructions.

## 8. Comparison with every mandatory prior and active fingerprint

Verification level is part of every comparison. Notes and rejected artifacts
are navigation, not discharged premises.

Prior pins used in this table:

```text
T90  730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0
T104 2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5
T105 ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f
T111 89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8
T112 72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa
T113 30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445
T109 6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf
T114 db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca
T115 29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36
SEM  aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f
```

T90's source corpus is `literature-checked` and its transfers are `proof
sketch`. T104, T105, T111, and T112 have source-pinned literature components
and explicitly labeled proof-sketch deductions. T113 is an unverified note.
T109 is a terminal rejected record; in particular its sufficient certificate
tests are not treated as necessary conditions. T114 and T115 have
literature-checked source statements and explicitly labeled proof-sketch
deductions; none of those deductions is used as a premise here. The semantic
obstruction memory is an unverified audit ledger with mixed-level references.

| candidate | T90 | T104 | T105 | T111 | T112 | T113 note | terminal T109 | active T114 | active T115 | semantic memory |
|---|---|---|---|---|---|---|---|---|---|---|
| C-RS | Unlike computable discrepancy points, gives individual all-difference lower bounds | No ambient measure/fixed-fiber transfer; selects one point directly | Uses T105's difference shape only as elementary shell data, not energy/BSG or modular cancellation | Nonduplicate: weighted dyadic game rather than odd de Bruijn coding | No carry law, random input, or growing-state spectral premise | Directly repairs the note's named-point gap by a different theorem and weaker `N^-2` threshold; does not import its variable-`H` claim | No model-to-pi transport and no necessity inference from failed certificates | T114's proof-sketch obstruction concerns homogeneous interpolation determinants, rational rank, and aggregate occupancy; C-RS instead constructs one branch by local forbidden-weight budgets and uses no determinant or lower bound | T115's proof-sketch model is a finite Riesz-coefficient recursion with persistent mass on `10^r`; C-RS gives pointwise avoidance for every decimal difference of a selected point and uses no substitution or spectral coefficient identification | Supplies one coherent infinite branch, not isolated finite certificates; still only a sibling |
| C-FMS | Strong individual separation rather than aggregate discrepancy | No fractal Fourier/fiber transfer | No energy or modular sum | Exact duplication boundary: this is T111's odd-digit de Bruijn selector, with the stronger count written out | No carry local limit or spectral mechanism | T113 note already observes the stronger T111 count; T116 re-derives it | No perturbative transport | The T114 report's proof-sketch determinant/rank cards do not occur: C-FMS obtains diagonal-only collisions from de Bruijn uniqueness and odd-code parity, not from arithmetic nonvanishing or an occupancy contradiction | Both are base-ten symbolic models, but the T115 report's proof-sketch model studies Riesz densities and a nondecaying coefficient ray, whereas C-FMS selects a single nested decimal word and proves finite block separation; no coefficient array is transferred | One nested absolute-root prefix sequence exists, but for an artificial sibling |
| C-MOS | Avoidance rather than discrepancy | Not a fixed-fiber or ambient Fourier route | Uses ordered differences, not energy | Unlike T111, has no named computable point | No carry/spectral operator | Exact mechanism audited by the unverified T113 note; T116 does not upgrade it | No transport; rejection is only lack of an effective certificate | The T114 report's proof-sketch comparison separates variable-threshold avoidance from determinant nonvanishing; C-MOS is rejected earlier because nonemptiness supplies no computable branch, so it neither uses nor repairs the reported rank/height failures | The T115 report's proof-sketch scalar Fourier recursion supplies neither Moshchevitin's nested avoidance hypotheses nor a safe-child selector; its displayed persistent decimal ray is a different model obstruction | Violates the warning that nested nonempty finite sets alone do not name a coherent computable branch |
| C-BFK | Winning-set existence rather than explicit discrepancy | Measure-supported model has the same named-fiber warning | No direct prescribed-character estimate | No symbolic code or computable decimal recurrence | Its measure choice is not the finite carry model but shares an averaging-to-point gap | Uniform lacunarity cannot cover the sublacunary ordered differences used in the note | No robustness transport and no fixed-`pi` inference | The T114 report's proof-sketch witnesses are determinants and fixed-lag recurrences; C-BFK is a Schmidt-game theorem killed instead by adjacent ratio `Q=1` and a noneffective measure-based center choice | The T115 report's proof-sketch model uses a constant-length substitution and finite Riesz products, not Schmidt-game lacunarity or rational-center selection; neither its ray identity nor its cheap kill supplies the missing BFK selector | Fails both the prescribed sequence hypothesis and the explicit branch requirement |

The comparison uses the complete staged T114 and T115 reports with the hashes
listed above. The T114 report's scoped `CLOSE` verdict concerns only its
proof-sketch interpolation-determinant and rank fingerprint at the collision
scale. The T115 report's scoped `close` verdict concerns only its proof-sketch
base-ten substitution Riesz fingerprint and displayed persistent coefficient
ray. The eight candidate-specific cells identify the exact separation; neither
report is used to discharge a source theorem, selector invariant, or sibling
collision bound in T116.

## 9. Explicit additional pi-specific certificate

The mechanism-specific sufficient premise is

```text
PI-RS:
  for every integer j>=3 and every t in P_j,
  ||t*pi||_(R/Z) > 2^(-r_j),                               (9.1)
```

with `P_j,r_j` exactly as in (3.3) and (3.7). A stronger cell-level sufficient
certificate would say that, for every `j>=3` and `t in P_j`, the level-`L_j`
dyadic cell containing `{pi}` is disjoint from `B(t,j)`. This implies (9.1),
but is not equivalent to it. To transfer the literal selected point rather than
only its inequalities, one would need the still stronger certificate

```text
{pi} belongs to I_m for every m.                           (9.2)
```

which identifies `{pi}=x_RS`.

Neither (9.1) nor (9.2) is proved or suggested by the source audit. Under
(9.1), equations (3.23)-(3.27) would apply with `x=pi`; this is a stronger
sufficient surrogate, not a necessary characterization of canonical C1.
Failure of (9.1) would reject this certificate only and would not refute the
canonical question. A constructed `x_RS` or `x_FMS` gives no evidence that
either premise holds.

## 10. Replay, scope, and terminal classification

From a directory containing only the delivered artifacts, run

```text
python3 verify_t116.py
sha256sum -c SHA256SUMS
```

The script checks the canonical and primary-source hashes, source anchors,
actual artifact/source/candidate counts, all forty mandatory comparison cells,
uniqueness of the terminal and successor markers, finite shell occupancy and
game budgets through shell 500, explicit C-RS game moves and safe
macro-intervals through shell 20, the polynomial lower bound (3.22), threshold
instances, and corrected FMS chains through order four. These are `experiment`
checks only.

TERMINAL_VERDICT: hold as model

The sole bounded successor is to formalize the C-RS shell occupancy bound,
weighted-game budget and branch recurrence, and the sibling identity (3.26),
without introducing any fixed-`pi` premise or claim.
