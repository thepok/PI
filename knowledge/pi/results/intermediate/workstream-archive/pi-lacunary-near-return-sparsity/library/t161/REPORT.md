# T161: maximal same-lag chain declumping audit

Audit date: 2026-08-12 UTC.

This is a `proof sketch` note with a self-contained finite `experiment`. Source
statements explicitly attributed to S1 are `literature-checked` at the locators
in `SOURCE_PINS.md`; S2 is only `bibliographic context` because its DVI could
not be text-inspected. All equality-graph, chain-intensity, cumulant, and
asymptotic calculations below are newly derived `proof sketch` claims. T159 is
an unverified note and is changed evidence only, never a discharged premise.

Revision note: this retry corrects the feasible-chain endpoint to
`a+ell<=N-d`, restores the factor `(1-q)^(1-r)` in the geometric cumulant
identity, adds replay assertions for both corrections, and refreshes T158's
now-readable comparison level.

```text
PRIMARY_SOURCE_COUNT: 2
PRIMARY_SOURCE_CAP: 4
CUMULANT_CALCULATION_COUNT: 3
SEPARATOR_TEST_COUNT: 5
SCOPED_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, normalized statement, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question asks, for the fixed orbit of pi, whether
`for every A there exists n0 such that for every n>=n0 there exists N` with an
ordered, diagonal-inclusive strict metric near-return bound. T161 neither
changes nor answers it. T161 studies the A10/A13/A14 sibling of exact equal
blocks in one iid uniform decimal word.

Quantifiers and ambiguities fixed before calculation:

1. `N>=2` is the number of starts and `m>=1` the common block length; the iid
   word has exactly `L=N+m-1` digits.
2. Blocks are nonwrapping and unpadded. The required regime is
   `m<=floor((1/4)log_10 N)`; hence it is nonempty only for `N>=10^4`.
3. Primitive random events use unordered off-diagonal pairs. The requested
   ordered statistic is reconstructed exactly, including deterministic
   diagonals.
4. "Connected same-lag" means adjacency under unit translation
   `(i,i+d)->(i+1,i+1+d)`, not support intersection and not equality-graph
   connectivity across different lags.
5. "Intensity" means the expected number of maximal chains of one exact
   `(lag,length,boundary-type)` under the iid law, not an asserted Poisson rate.
6. A compound-Poisson law constructed from these intensities is a candidate
   moment model. Without a valid approximation theorem, matching cumulants is
   not a total-variation or point-process approximation.
7. Finite separator words are applicability tests only. They cannot prove or
   disprove an iid distributional theorem or any assertion about pi.

## 2. Exact process, endpoints, ordered reconstruction, and lag marks

Let `D={0,...,9}` and let `X_0,...,X_(L-1)` be independent uniform digits. Put

```text
L=N+m-1,
W_i=(X_i,...,X_(i+m-1)),                         0<=i<N,
Alpha={(i,j):0<=i<j<N},
I_(i,j)=1[W_i=W_j],
Z=sum_(i,j in Alpha) I_(i,j).                    (2.1)
```

The first and last coordinates of `W_i` are `i` and `i+m-1`; the largest last
coordinate is `(N-1)+(m-1)=L-1`. For `alpha=(i,j)`, define the positive lag,
support, overlap, and deterministic location mark by

```text
d(alpha)=j-i,
S_alpha=[i,i+m-1] union [j,j+m-1],
o(alpha)=max(0,m-d(alpha)),
u_alpha=(i,j,d(alpha),o(alpha)).                  (2.2)
```

The ordered, diagonal-inclusive process and count are exactly

```text
Xi_ord=sum_(i=0)^(N-1) delta_(i,i,0,DIAG)
       +sum_(i<j) I_(i,j)(delta_(i,j,d,o)+delta_(j,i,-d,o)),
E=|Xi_ord|=N+2Z.                                  (2.3)
```

No Poisson approximation is used in (2.1)--(2.3).

## 3. Equality graph and rank

For any finite event set `F subset Alpha`, its equality graph `G(F)` has digit
vertices appearing in the events and one edge

```text
{i+r,j+r},  0<=r<m,                               (3.1)
```

for each `(i,j) in F`. Let `v(F)` and `c(F)` be its vertex and connected-
component counts and define

```text
rank(F)=v(F)-c(F).                                 (3.2)
```

Every component chooses one of ten digits independently, so directly counting
assignments gives the exact probability

```text
P(I_alpha=1 for every alpha in F)=10^(-rank(F)).   (3.3)
```

A single event has rank `m`, including overlapping blocks. For the unit-
translated same-lag chain

```text
F_(d,a,ell)={(a+r,a+r+d):0<=r<ell},                (3.4)
```

the first event contributes `m` equality edges and each translation contributes
one new edge; cycles do not arise. Therefore

```text
rank(F_(d,a,ell))=m+ell-1,
P(F_(d,a,ell) active)=10^(-m-ell+1).               (3.5)
```

The replay checks (3.5) over bounded `m,d,ell` and also by exhaustive binary
enumeration, where rank is alphabet-independent and probability is `2^-rank`.

## 4. Maximal cluster types and exact intensities

For each lag `1<=d<N`, write `Y_(d,i)=I_(i,i+d)`, `0<=i<N-d`. A maximal
same-lag chain is a triple

```text
C=(d,a,ell),  0<=a, 1<=ell, a+ell<=N-d,            (4.1)
```

such that

```text
Y_(d,a),...,Y_(d,a+ell-1)=1,
a=0 or Y_(d,a-1)=0,
a+ell=N-d or Y_(d,a+ell)=0.                        (4.2)
```

This definition is unique: at each lag, every active event belongs to exactly
one maximal consecutive run. The cluster mark is

```text
t(C)=(d,a,ell,b_L,b_R),                             (4.3)
```

where `b_L=1[a=0]` and `b_R=1[a+ell=N-d]` record missing boundary tests. The
cluster contributes jump size `ell` to `Z`; hence, deterministically,

```text
Z=sum_(maximal C) ell(C).                            (4.4)
```

Let `q=1/10`, `p=q^m`, and let `s=2-b_L-b_R` be the number of tested external
neighbors. From (3.5), extending the chain one step costs one independent
equality constraint. Inclusion-exclusion on the two external equalities gives
the exact probability and point intensity

```text
P(C=(d,a,ell) is maximal)=p*q^(ell-1)*(1-q)^s,
nu_(d,a,ell,b_L,b_R)=that same number.              (4.5)
```

Summing starts of a fixed `(d,ell)`, let `K=N-d-ell+1`. If `K<=0`,
`nu_(d,ell)=0`. If `K=1`, the unique chain fills the lag row and has no
external test. If `K>=2`, there are `K-2` two-sided starts and two one-sided
boundary starts, so

```text
nu_(d,ell)=p*q^(ell-1)                              if K=1,
nu_(d,ell)=p*q^(ell-1)*[(K-2)(1-q)^2+2(1-q)]       if K>=2. (4.6)
```

Equation (4.6) defines the candidate compound-Poisson law

```text
Z_CP=sum_(d,ell) ell*Pois(nu_(d,ell)),               (4.7)
```

with all Poisson variables independent. This is a defined benchmark, not yet
an informative approximation theorem. Section 6 gives a valid but vacuous
point-process error from S1.

## 5. Three factorial-cumulant calculations

For a compound-Poisson sum with jump intensity `nu_(d,ell)`, its `r`th
factorial cumulant is

```text
kappa_r^CP=sum_(d,ell) (ell)_r nu_(d,ell),           (5.1)
```

where `(ell)_r=ell(ell-1)...(ell-r+1)`. Boundary terms are `O(m/N)` relative
when first `N/m->infinity`; then letting `m->infinity`, division by the raw
event mean `lambda=binom(N,2)p` and the geometric identity
`sum_(ell>=1)(ell)_r(1-q)^2 q^(ell-1)
 =r!q^(r-1)(1-q)^(1-r)` give:

```text
kappa_1^CP/lambda -> 1,                              (5.2)
kappa_2^CP/lambda -> 2q/(1-q)=2/9,                   (5.3)
kappa_3^CP/lambda -> 6q^2/(1-q)^2=2/27.              (5.4)
```

Calculation 1 is exact even at finite `N,m`: summing `ell` over maximal chains
reconstructs every active event, hence `kappa_1^CP=lambda`. Calculations 2--3
are positive constant-order corrections. Thus maximal same-lag declumping
**absorbs** T159's reported `2/9` contribution as the candidate law's second
factorial cumulant; it does not make the obstruction disappear or become
`o(lambda)`. The third cumulant shows that the cluster law is genuinely
non-Poisson beyond variance.

This is useful moment matching but insufficient for total variation: mixed-lag
connected equality graphs are not represented in (4.7), and matching three
cumulants does not bound their aggregate intensity.

## 6. Complete source-theorem substitution and first sharpness failure

S1 Theorem 4.1 (`literature-checked`) starts with a process

```text
M=sum_a J_a delta_(U_a),                             (6.1)
```

where the source explicitly assumes the marks `U_a` are independent random
elements. It then chooses neighborhoods `A_a`, defines outside counts `V_a`,
and bounds `d_2(Law(M),Po(sum_a p_a Law(U_a)))` by its equation (4.1), including
the local joint terms and `min(epsilon_1,epsilon_2)`.

Do **not** use one root with a random cluster-length mark; that mark would fail
the source independence hypothesis. Instead let the finite index set `C` be
all feasible exact candidates `(d,a,ell,b_L,b_R)` from (4.1)--(4.3), put

```text
J_C=1[C is maximal as in (4.2)],
U_C=C deterministically,
M_cl=sum_(C in C) J_C delta_C,
K=|M_cl|,   Lambda_cl=E[K]=sum_C nu_C.               (6.2)
```

Deterministic marks are mutually independent and independent of every `J_C`.
By uniqueness of maximal decomposition, `Z=sum_C ell(C)J_C`, so a Poisson
process with mean `sum_C nu_C delta_C` maps under weighted total mass exactly
to `Z_CP` in (4.7).

For a complete conservative substitution choose `A_C=C`, the entire candidate
set. Then `V_C=0`. The outside sigma-field is trivial, hence the source's
`epsilon_1=0`; no Palm coupling or `epsilon_2` is needed because the theorem
uses `min(epsilon_1,epsilon_2)`. The first double sum in S1 equation (4.1) is

```text
(5/Lambda_cl+3) E[K(K-1)],                            (6.3)
```

and the second is `(5/Lambda_cl+3)Lambda_cl^2`. Every
maximal chain contains a distinct active event, so `K<=Z<=P=binom(N,2)`.
Therefore S1 gives the explicit point-process error

```text
d_2(Law(M_cl),Po(sum_C nu_C delta_C))
 <= B_CP(N,m)
 :=min(1,(5/Lambda_cl+3)
          [P(P-1)+Lambda_cl^2]),                       (PP-161)
Lambda_cl=sum_(d=1)^(N-1)sum_(ell=1)^(N-d)nu_(d,ell),
nu_(d,ell) given exactly by (4.6).                    (6.4)
```

The outer minimum uses the source metric's range `d_2<=1`. Equations
(6.2)--(6.4) discharge every S1 hypothesis and constant. They are valid for
all `N>=2,m>=1`, hence in particular for the full required range
`m<=floor((1/4)log_10 N)`.

The first failed **sharpness** point is now numerical, not a hidden theorem
hypothesis: in the required range `N>=10^4`, hence `P>=2`, and
`Lambda_cl>0`, so the untruncated right side in (PP-161) already exceeds one
and `B_CP(N,m)=1`. Thus this complete S1 substitution does
not prove a sharper approximation than T159's unclustered attempt. The required
scale makes the unresolved local refinement substantial: `p>=N^-1/4`, with
`Theta(N^2)` events and `Theta(mN)` support-neighbors per event. A useful bound
would have to retain local candidate neighborhoods and control mixed-lag
connected equality graphs; no such aggregate bound is derived here.

## 7. Five exact separator tests

The tests use the deterministic definitions (2.1)--(4.4). Their bounded values
are `experiment`; general family formulas are `proof sketch`.

1. **Constant.** Every off-diagonal event is active, `E=N^2`. At each lag `d`
   there is one maximal chain of length `N-d`, so the model has `N-1` macroscopic
   chains, not rare geometric clumps.
2. **Primitive-periodic.** For primitive period `r`, `m>=r`, and `r|N`,
   `E=N^2/r`. Active lags are exactly multiples of `r`; each such lag is one
   maximal chain of length `N-d`. The replay uses period 3, `N=12,m=4` and gets
   lags `{3,6,9}`.
3. **Repeated de Bruijn.** Repeating a cyclic decimal de Bruijn word of order
   `m`, with `10^m|N`, gives `E=N^2/10^m`. For two repeats at `m=2,N=200`, the
   only active lag is 100 and it forms one length-100 chain. The energy matches
   the iid mean scale while the cluster geometry is deterministic and giant.
4. **Shared prefix.** If the first `R+m-1` digits agree, then for every
   `1<=d<R` there is a chain of length at least `R-d`, so `E>=R^2`. This is a
   triangular family of long chains, not the geometric type law (4.5).
5. **Regular paperfolding.** Define independently
   `p_(2^a(2j+1))=j mod 2`. For starts `1,...,48` and `m=7`, replay gives
   `E=98`, hence 25 unordered events, and reconstructs all 25 as maximal-chain
   lengths. Its finite automatic structure is neither iid nor evidence for
   Poisson roots; the test rejects importing (4.5) merely from low complexity.

These tests separate exact applicability. They do not contradict an iid-law
theorem because each is one deterministic family outside that theorem's
hypotheses.

## 8. Comparisons with T120, T150, and T158--T160

Exact levels and hashes are in `COMPARATORS.md`. No comparator deduction is a
premise.

| item | comparison boundary |
|---|---|
| T120 | Its source-audited countable-state renewal models use return tails and expose named-path failure. T161 has finite iid digits, equality graphs, and no renewal theorem. |
| T150 | Its source-audited Gibbs concentration note gives a bad-word census with coordinate-reuse loss. T161 studies the collision count distribution and gives no census. |
| T158 | The readable accepted note labels its source statements `literature-checked`, deductions `proof sketch`, and replay `experiment`; its scoped verdict is to close empirical transition-gap expansion as a deterministic occupancy mechanism. T161 instead studies iid collision-cluster laws and imports no T158 deduction. |
| T159 | The unverified note argues for an unclustered marked-Poisson model and reports `2/9`. T161 independently derives maximal-chain intensities and finds `2/9` retained as the CP second cumulant. |
| T160 | No readable artifact exists in the refreshed snapshot; identifier reserved, no result or nonduplication claim inferred. |

## 9. Separate unproved pi-specific transfer

**UNPROVED_PI_CONNECTED_INTENSITY_BOUND (`conjecture`; `unproved pi-transfer`;
NOT ASSERTED).** A transfer to T7 or T107 would require one increasing sequence
of actual pi prefixes and explicit nonnegative bounds `Gamma_(N,m,r)` for every
connected equality-graph type `r` not contained in a single same-lag maximal
chain, such that uniformly for
`m<=floor((1/4)log_10 N)`:

```text
sum_r Gamma_(N,m,r)*(1+|r|+|r|^3)=o(N^2*10^(-m)),          (9.1)
```

and the same-lag maximal-chain empirical intensities differ from (4.6) by a
weighted `o(N^2*10^-m)` total. For T7 one must additionally prove the resulting
ordered count lies below its exact threshold on the named prefixes. For T107
one must additionally derive its separate decimal-boundary and Fourier-row
budgets. Exact block equality is weaker than metric near return, so an endpoint
and carry conversion is also required.

Neither iid probability, (4.5), finite cumulants, nor any inspected source
proves (9.1) for the prescribed digits of pi. No fixed-pi, A1, C1, or C2 claim
is made.

## 10. Endpoint

From a directory containing only delivered artifacts, run

```bash
python3 verify_t161.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay checks all source and canonical hashes, process endpoints, equality
ranks, exact maximal-chain probabilities, the three cumulants, the complete
`(PP-161)` substitution at bounded instances, all five separators, comparator
markers, verdict count, and claim firewall. Finite checks are experiments, not
proofs of the asymptotic deductions.

SCOPED_VERDICT (1/1): **close**.

Close only this proposed refinement as a claimed sharper approximation on the
mandated scale. Same-lag declumping explains rather than removes the `2/9`
term and produces a nonzero `2/27` third cumulant. The complete S1 substitution
is valid after indexing exact chain candidates, but `(PP-161)` equals the
metric ceiling one. The compound-Poisson law (4.7) remains a defined moment
benchmark. This closes neither a sharper local-neighborhood analysis nor
compound-Poisson methods under stronger hypotheses, nor G28, nor any statement
about pi.
