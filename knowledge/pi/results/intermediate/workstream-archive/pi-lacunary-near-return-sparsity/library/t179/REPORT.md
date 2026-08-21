# T179: additive structure of the full heavy-lag set

Audit date: 2026-08-13 UTC. This is one bounded clean-context G28 scout.
Statements explicitly attributed to S1--S6 are `literature-checked` against the
six pinned primary PDFs and exact ranges in `SOURCE_LEDGER.csv`. Definitions,
finite-set deductions, substitutions, and model separators are `proof sketch`.
The replay is an `experiment`: it checks exact finite identities and artifact
structure, not the universal prose arguments. T147 and T169 are unverified notes;
no conclusion from either is imported as a discharged premise.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
SOURCE_THEOREM_TUPLE_COUNT: 6
SEARCHED_DOMAIN_COUNT: 3
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
EXCLUSION_LEDGER_RANGE: T89-T178
EXCLUSION_LEDGER_COUNT: 90
RESERVED_ACTIVE_ITEMS: T178
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable question and normalized scope

The local canonical statement was formulated by this program and has no external
source URL. The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether, for the fixed decimal orbit of pi and its ordered,
diagonal-inclusive strict circle-distance count,

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with A*n*Q_pi(n,N)<=N^2.
```

T179 studies only exact equality in arbitrary finite decimal words and named
related models (ambiguities A10, A13, A14). It neither changes nor answers the
canonical question.

Quantifiers and potential ambiguities are fixed before source use:

1. `N>=2` is the number of legal block starts, not the word length.
2. `m>=1`; the supplied finite word has exactly `N+m-1` symbols. Starts are
   `0,...,N-1`, with no wrap or padding. The last inclusive endpoint is
   `(N-1)+(m-1)=N+m-2`.
3. Lags are positive integers `1<=r<=N-1`. At lag `r`, legal left starts are
   exactly `0<=i<=N-r-1`; there are `N-r` of them. Both endpoints `i+m-1`
   and `i+r+m-1` are at most `N+m-2`.
4. Ordered collision energy includes all `N` diagonal pairs. `L_m(r;N)` counts
   one orientation; the reverse orientation is paid separately.
5. The threshold satisfies `0<tau<=1`. Since `L_m` is integral,
   `L_m(r;N)>=tau*N` means `L_m(r;N)>=ceil(tau*N)`.
6. Additive structure is measured on the complete threshold set, not a chosen
   lag and not the multiset of block differences.
7. A theorem assuming small doubling is a classifier only after that hypothesis
   is independently proved. A classification of Fourier characters, a
   topological return set, or an unspecified subset is not a classification of
   the finite set below.
8. The logarithmic schedule is always the literal
   `m_N=floor((1/4)*log_10 N)` and is used only when `m_N>=1`.

## 2. Lag and additive-structure definitions

Let `x=x_0...x_(N+m-2)` and

```text
B_m(i)=(x_i,...,x_(i+m-1)),                    0<=i<N,
L_m(r;N)=#{i in Z:0<=i<=N-r-1 and B_m(i)=B_m(i+r)},
                                                    1<=r<N,
R_(m,tau)(N)={r in Z:1<=r<N and L_m(r;N)>=tau*N}.   (2.1)
```

Thus every endpoint and range in (2.1) is explicit. Define the ordered,
diagonal-inclusive block collision energy

```text
C_m(N)=#{(i,j):0<=i,j<N and B_m(i)=B_m(j)}
      =N+2*sum_(r=1)^(N-1)L_m(r;N).                       (2.2)
```

The equality partitions off-diagonal ordered pairs by `r=|i-j|`.

For a nonempty finite integer set `R`, define

```text
R+R={a+b:a,b in R},              doubling K_+(R)=|R+R|/|R|,
E_+(R)=#{(a,b,c,d) in R^4:a+b=c+d}.                       (2.3)
```

A rank-`d` generalized arithmetic progression (GAP) is

```text
P={a0+n1*a1+...+nd*ad:0<=nj<Lj};                           (2.4)
```

it is proper if all parameter tuples give distinct integers. "Bounded rank"
means `d` is bounded independently of `N` and `m`; a container is efficient at
this scale only if `|P|<=K0*|R|` for a constant `K0` independent of `N,m`.
These conventions prevent the ambient interval `[1,N-1]`, a rank-one GAP
containing every possible lag, from being misreported as useful structure.

## 3. What collision concentration actually forces

Let `R=R_(m,tau)(N)` and `s=|R|`. From (2.2), and from `L_m(r;N)<=N-r<N`
on `R` while `L_m(r;N)<tau*N` off `R`, the weaker non-strict bound gives

```text
(C_m(N)-N)/(2N)=sum_r L_m(r;N)/N
 <=s+tau*(N-1-s)=tau*(N-1)+(1-tau)*s.                    (3.1)
```

Therefore

```text
s >= ((C_m(N)-N)/(2N)-tau*(N-1))/(1-tau),                 (3.2)
```

when the numerator is positive. This is the exact threshold extraction; no
inverse theorem is used.

The T7-shaped high-energy model scale is `C_m(N)>=N^2/m`. Choose the cheapest
fixed fraction threshold

```text
tau=1/(4m).                                                (3.3)
```

Substitution into (3.2), with every floor retained, gives

```text
m=m_N=floor((1/4)*log_10 N),
|R_(m,1/(4m))(N)| >= (N+1-2m)/(4m-1).                    (3.4)
```

The right side is interpreted as a real lower bound on the integer cardinality.
Hence it can be replaced by its ceiling. At logarithmic depth this guarantees
only `Omega(N/m)`; periodic examples below show this order can occur, while
constant words can have much larger `R`. It is not a positive density bound
uniform in `m`.

Because `R subset {1,...,N-1}`,

```text
|R+R|<=2N-3,
K_+(R)<=((2N-3)*(4m-1))/(N+1-2m),                         (3.5)
E_+(R)>=|R|^4/|R+R|>=|R|^4/(2N-3).                       (3.6)
```

Equation (3.6) is Cauchy--Schwarz applied to representation counts of sums.
Thus `E_+(R)/|R|^3>=|R|/(2N-3)=Omega(1/m)` under the same
high-collision premise. Large ordered block-collision energy guarantees additive
energy only with a worst-case loss proportional to the block depth; the ratio can
be larger. It forces `K_+(R)=O(m)`, not constant small doubling.

There is also a cheaper classification than any inverse theorem:

```text
R subset [1,N-1], rank=1, |[1,N-1]|/|R|
 <=(N-1)*(4m-1)/(N+1-2m)=O(m).                            (3.7)
```

This ambient interval statement follows from density alone. Consequently an
inverse theorem provides related-model classification beyond collision
concentration only if it improves the guaranteed `O(m)` container ratio or the
rank/structure in a way tied to block equality. None of S1--S6 does so.

## 4. Bounded source search

The search stopped after six previously unaudited primary source/theorem tuples
across exactly the three agenda domains. Stable URLs, PDF hashes, and exact
locators/ranges are in `SOURCE_LEDGER.csv`.

| card | source tuple(s) | retained? | literal result of substitution |
|---|---|---|---|
| C-FREIMAN | S1 Theorem 1.1 | yes | classifies `R` only after (3.5); at `K=Theta(m)` its rank and size bounds grow with `m` and are weaker than (3.7) |
| C-POPULAR | S2 Theorem 4 | yes | applies to popular differences of one set in an abelian group, but the exact embedding below gives only an independent-dimension bound, not small doubling of `R` |
| C-RECURRENCE | S3 Khintchine statement and Theorems 2.1--2.2 | no | shows system-dependent correlation behavior; supplies no finite-lag inverse classification |
| C-PRONIL | S4 Theorem A | yes | classifies topological polynomial return sets modulo a non-piecewise-syndetic error under minimality, not weighted finite block-return lags |
| C-SPECTRUM | S5 Theorems 3.2--3.3 | no | covers large Fourier characters of a density; without a sourced primal-dual transfer it does not classify `R` |
| C-TRIPLE-SUM | S6 Theorem 2.1 and Lemma 3.2 | no | bounds a modular triple exponential sum using energy of a geometric progression; it has no block-lag observable and gives no inverse implication for `R` |

Exactly three candidate cards are retained: C-FREIMAN, C-POPULAR, and C-PRONIL.
The other two tuples are screened comparators, not hidden candidates.

### 4.1 C-FREIMAN: a conditional classifier that loses depth

S1 Theorem 1.1 states: if a finite subset `A` of an abelian group obeys
`|A+A|<=K|A|`, it lies in a coset progression of dimension at most
`C*K^4*log(K+2)` and size at most
`exp(C*K^4*log^2(K+2))*|A|`, for an absolute `C`.

For `A=R`, (3.5) supplies only `K=O(m)`, with no constant bound. At
`m=floor((1/4)log_10 N)`, the sourced dimension is therefore
`O(m^4 log m)`, not bounded rank, and its size factor is
`exp(O(m^4 log^2 m))`, whereas the elementary ambient interval (3.7) already
has rank one and factor `O(m)`. S1 is valid but adds no useful
block-sensitive classification. Assuming constant doubling before invoking S1
would be precisely the missing conclusion, not an inverse derivation.

### 4.2 C-POPULAR: exact embedding, wrong structural output

S2 defines `P_gamma(A)={g:r_A(g)>=gamma|A|}` and Theorem 4 bounds the maximum
independent subset of `P_gamma(A)` by an explicit multiple of
`gamma^(-1)log_2|A|` (with the stated least-element-order condition).

Embed our block process in the abelian group
`G=Z/(2N+1)Z x V`, where `V` is the free vector space over `F_2` on the finite
set of observed block values, and put

```text
A={(i,e_(B_m(i))):0<=i<N}.                                (4.1)
```

There is no wrap in first-coordinate differences because `|i-j|<N<2N+1`.
For `1<=r<N`, representations of `(r,0)` as a difference of two elements of
`A` are exactly starts `i` with `B_m(i+r)=B_m(i)`. Hence

```text
r_A((r,0))=L_m(r;N),
r in R_(m,tau)(N) iff (r,0) in P_tau(A).                  (4.2)
```

This is a literal popular-difference embedding, not an analogy. But S2 bounds
only independent dimension in the ambient torsion group. It neither bounds
`|R+R|`, gives a GAP containing all of `R`, nor improves (3.7). At
`tau=1/(4m)`, even its scale is `O(m log N)=O(m^2)`. Thus it detects one
notion of additive dependence but does not produce the requested small-doubling
or bounded-efficient-progression conclusion.

### 4.3 C-PRONIL: a related model with unmatched hypotheses

S4 defines a topological return-time set by nonempty intersections of open-set
pullbacks in a minimal invertible system. Theorem A says that polynomial
return-time sets differ from their maximal infinite-step pronilfactor versions
by a set that is not piecewise syndetic, under its stated minimality,
essential-distinctness, and nonempty-interior hypotheses.

The finite word in (2.1) supplies neither one minimal infinite system nor an
open-set return event independent of the starting point: `L_m(r;N)` is a
weighted count over all starts, and thresholding it is essential. Even a
topological identification of the unweighted set `{r:L_m(r;N)>0}` would lose
the `tau*N` multiplicity. S4's pronil classification therefore has no legal
substitution for `R_(m,tau)(N)`. It is a genuine related-model structure theorem,
but not an inverse theorem for heavy finite lags.

### 4.4 Screened recurrence and Fourier tuples

S3's printed p. 1 Khintchine statement guarantees infinitely many correlations
at least `mu(A)^2-epsilon`; Theorems 2.1--2.2 on p. 3 show that strict under- or
over-recurrence depends on the system. These statements do not bound additive
energy of a finite threshold set, and their examples warn against inferring a
universal finite classification from recurrence alone.

S5 Theorem 3.3 covers the large Fourier spectrum of a probability density by
at most `4 Ent(f)/delta^2` generators; Theorem 3.2 covers a large subset with
a sharper entropy-dependent count. This structure is in the dual group. To use
it here one must first show that many primal lags in `R` create the required
large Fourier coefficients and then return from a covered dual spectrum to a
small-doubling primal set. No such implication is in S5. Assuming it would
rename the missing inverse step.

S6 Theorem 2.1 bounds a triple modular exponential sum under its exact prime,
interval, multiplicative-order, and coefficient hypotheses. Its Lemma 3.2 bounds
the additive energy of `{g,...,g^K}` modulo `p` by `O(K^(5/2))`. Substituting the
integer lag set `R` is illegal: `R` is neither a geometric progression modulo a
specified prime nor the source sum's exponent index set with the required
coefficients. More fundamentally, S6 uses an energy upper bound to prove
cancellation; it provides no inverse direction from block-collision energy to
structure of `R`. It is a screened structured-exponential-sum tuple, not a fourth
retained candidate.

## 5. Exact logarithmic-depth separators

In S1--S6, no source theorem distinguishes the following finite words. The
calculations use the exact threshold from (3.3):

```text
m=m_N=floor((1/4)*log_10 N),
q_N=ceil(N/(4m)),
R=R_(m,1/(4m))(N).                                       (5.1)
```

### SEP-CONSTANT

For `x=0^(N+m-1)`, `L_m(r;N)=N-r`. Therefore exactly

```text
R={1,...,N-q_N},  |R|=N-q_N.                              (5.2)
```

It is an interval with doubling `2-1/|R|` when nonempty. This additive
structure comes directly from every lag being heavy.

### SEP-PERIODIC

Let an infinite primitive period-`p` word be truncated after the required
look-ahead, and assume `m>=p`. Its phase blocks are distinct, so

```text
L_m(r;N)=N-r if p divides r, and 0 otherwise,
R={p,2p,...,floor((N-q_N)/p)*p}.                           (5.3)
```

This is a rank-one progression. The period, not ordered collision energy or an
inverse theorem, supplies its generator.

### SEP-REPEATED-DE-BRUIJN

Take a cyclic decimal de Bruijn word of order `m`, repeat it indefinitely, and
use `N` starts. Its period is exactly

```text
p_m=10^m=10^floor((1/4)*log_10 N),
N^(1/4)/10 < p_m <= N^(1/4).                              (5.4)
```

Distinct phases have distinct length-`m` blocks, so (5.3) holds with `p=p_m`:

```text
R={p_m,2p_m,...,floor((N-q_N)/p_m)*p_m}.                   (5.5)
```

Thus `|R|=Theta(N^(3/4))`, far above zero but density tends to zero; its exact
rank-one structure comes from repeated Euler-cycle order. This separates lag
additivity from a uniform one-period block census.

### SEP-T147-SHARED-PREFIX

The T147 note is unverified. We use only its explicit family specification and
recheck the needed count. Put `N=10^(4k)`, so (5.1) gives `m=k` exactly, let
`a=ceil(k/2)`, and fix the first `R0+k-1` symbols to zero, where
`R0=ceil(N/sqrt(a))`. For `1<=r<R0`, the pairs
`i=0,...,R0-r-1` are legal equal blocks, hence

```text
L_k(r;N)>=R0-r,
{1,...,R0-q_N} subset R_(k,1/(4k))(N),                    (5.6)
q_N=ceil(N/(4k)).
```

For `k>=2`, `R0>q_N`, so the displayed interval is nonempty. The suffix can add
other heavy lags; equality with the interval is not claimed. The separator is
that one shared prefix alone creates an additively structured heavy-lag subset,
without any global inverse theorem or pi conclusion.

### SEP-T169-CHAMPERNOWNE

The T169 note is an unverified proof sketch about the finite word
`W_K=dec(1)...dec(10^K-1)`. It uses

```text
L_K=[1+(9K-1)10^K]/9,  N_(K,m)=L_K-m+1,                  (5.7)
```

and argues for a sharp energy asymptotic only in the range `m<=floor(K/4)`.
Apply the agenda's schedule literally to its natural start count by requiring

```text
m*=floor((1/4)*log_10(N_(K,m*))).                         (5.8)
```

For `K>=11`, any legal solution of (5.8) has `m*<=K`: indeed
`N_(K,m*)<=L_K<K*10^K`, so
`m*<(K+log_10 K)/4<=K`. Also
`N_(K,m*)>=L_K-K+1>10^(K+1)`. Consequently, if `K=4j+3>=11`,
then (5.8) gives `m*>=j+1>floor(K/4)=j`.
Therefore T169's stated uniform range does not cover any legal exact-schedule
solution on the infinite subsequence `K congruent 3 mod 4`, `K>=11`. This is an exact scale separator,
not an inference from the note's asymptotic.

Conditionally, only to explain direction: if one had an independently verified
uniform estimate `C_m(N)<=2N^2/10^m` at (5.8), then

```text
|R|*q_N <= sum_r L_m(r;N)=(C_m(N)-N)/2 < N^2/10^m,
|R| < 4m*N/10^m <=40m*N^(3/4),                            (5.9)
```

using `10^m>N^(1/4)/10`. This would be much smaller than the lower bound
`Omega(N/m)` forced by `C_m(N)>=N^2/m`; hence the Champernowne model would lie
on the low-collision side. The premise of (5.9) at the exact schedule is not
established here and is not imported from T169.

## 6. Explicit nonduplication comparisons

`EXCLUSION_LEDGER.csv` contains exactly one row for every T89--T178. This retry
reconciles the refreshed snapshot: T166 is machine-checked; T173 and T177 are
accepted but unverified sketch notes; T174 is rejected; only T178 remains a
reserved active identifier with unavailable mathematical content. No deduction
from T173 or T177 and no claim from T174 is imported. No nonduplication claim
against T178's unavailable content is made.

| comparator | verification boundary | exact T179 boundary |
|---|---|---|
| T105 arithmetic difference-set energy | pinned source statements; local deductions `proof sketch` | T105 studies additive energy of `{10^i-10^j}` and prescribed character cancellation. T179 studies `E_+(R_(m,tau)(N))`, where elements are positive index lags selected by block-return multiplicity. C-FREIMAN is not claimed new as a theorem; its application to the heavy-lag set is tested and found weaker than the ambient interval. |
| T157 block-difference concentration | pinned source statements; local deductions `proof sketch` | T157 maps each block pair to a digit-coordinate difference vector and exact collisions to the zero vector. T179 never uses those vectors; it retains all lag fibers and asks for additive quadruples among distinct heavy lags. |
| T160 recurrence certificates | pinned source statements; deductions `proof sketch` | T160 emphasizes all ordered pair multiplicity versus one next recurrence. T179 begins with the exact all-pair identity (2.2), then thresholds the complete lag profile; it does not linearize to first recurrence or claim an upper collision certificate. |
| T162 return separation | pinned source statements; deductions `proof sketch` | T162's sufficient statistic is the minimum gap between any equal blocks. T179 can have many short or long heavy lags and studies sums among all of them; no minimum-separation premise is used. |
| T166 finite-word separation and collision packing | machine-checked Lean theorems `equal_factors_start_separation`, `factorMultiplicity_le_packing`, and `collisionEnergy_le_packing` | Under the additional `P`-power-free hypothesis, T166 separates starts carrying one equal block, bounds each block's occurrence multiplicity, and sums those fiber bounds into a collision-energy upper bound. It does not form the complete threshold set `R_(m,tau)(N)`, compare sums of distinct heavy lags, or bound `E_+(R)`, `|R+R|`, or an efficient GAP container. Conversely, T179's collision lower regime and threshold extraction assume no power-freeness and do not imply T166's separation premise. Thus T166 neither duplicates nor subsumes the full-heavy-lag additive-structure analysis. |
| T176 repeated-offset analysis | pinned source statements; deductions `proof sketch` | T176 asks whether there are many distinct offsets and a collision floor, retaining a Cantor heavy-fiber obstruction. T179 assumes/derives a thresholded full lag set and tests its additive energy, doubling, and GAP classification; individual offset count alone does not supply those relations. |

The shared-prefix and Champernowne calculations are rederived or explicitly
conditional. The unverified T147/T169 notes are comparators, never premises.

## 7. Separate unproved pi-transfer premise

**PI-HEAVY-LAG-EXCLUSION-T179 (`conjecture`; UNPROVED PI-SPECIFIC PREMISE; NOT
ASSERTED).** To use this cell toward the machine-checked T7 symbolic frontier,
one would need an independent theorem for the actual decimal blocks of pi with
T7's quantifiers: for every required `A` and all sufficiently large block depths
`m`, there is a legal prefix size `N` such that the full heavy-lag profile cannot
simultaneously satisfy the collision lower regime and one of its structured
realizations. Concretely, at `tau=1/(4m)` it must prove, directly from
pi-specific arithmetic and without assuming collision decay, at least one of:

```text
(P1) |R_(m,tau)(N)| < (N+1-2m)/(4m-1); or
(P2) every rank-one/O(m)-efficient container or comparable additive model for
     R_(m,tau)(N) carries total lag multiplicity sum_r L_m(r;N)<(N^2/m-N)/2.
                                                                    (7.1)
```

Either conclusion would exclude the structured heavy-lag mechanism responsible
for (3.4), but no audited source proves it for pi. Even such a symbolic theorem
would still require the separately checked symbolic-to-metric interface before
the canonical circle-distance question. This premise is unproved and makes no
fixed-pi, A1, C1, or C2 claim.

## 8. Endpoint

`SCOPED_VERDICT (1/1): CLOSE.`

Close only the audited claim that existing additive inverse, popular-difference,
return-set, or large-spectrum theorems turn high ordered block-collision energy
into useful new additive organization of the full heavy-lag set at
`m=floor((1/4)log_10 N)`. Threshold extraction guarantees density only
`Omega(1/m)`, a normalized additive-energy lower bound `Omega(1/m)`, and
doubling `O(m)`; these are worst-case guarantees, not two-sided estimates for
every word. The rank-one ambient interval already classifies the set with `O(m)` loss;
S1 is weaker at this substitution, S2 controls only independent dimension, and
S4 has unmatched infinite-system and unweighted-return hypotheses. The exact
separators show that intervals and progressions arise directly from constant,
periodic, de Bruijn, and shared-prefix constructions, while the T169 range does
not cover the exact schedule on an infinite subsequence. This closes one
literature cell, not G28 or any assertion about pi.

`SUCCESSOR (0/1): NONE.`

From a directory containing only delivered artifacts, run:

```text
python3 verify_t179.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay checks all local hashes, exact caps, consecutive ledger coverage,
source anchors and page counts, definitions/endpoints, the threshold algebra,
bounded exact collision identities and separators, mandatory comparisons, one
verdict, zero successors, and the claim firewall. It is an `experiment`, not a
proof of the source statements, prose deductions, or unproved transfer.
