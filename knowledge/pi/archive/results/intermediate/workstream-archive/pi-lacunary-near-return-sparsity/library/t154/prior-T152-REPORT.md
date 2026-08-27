# T152: a depth-localized fractional-cover census

Date: 2026-08-12 UTC.

Claim label: `proof sketch`.  Sections 2--7 give an elementary universal
argument, but it has not been formalized in a proof assistant.  The replay is
an `experiment`: it checks finite identities, endpoints, constants, and test
families, not the universal argument.  No theorem from the unverified T144 or
T147 notes is used as a premise, and no literature theorem is needed.

```text
BASE: 10
KAPPA: 1/4
RHO: 1/2
ENTROPY_CONSTANT: 1/100
CENSUS_CONSTANT_WITH_TYPES: 1/100
PURE_CENSUS_CONSTANT_FOR_N_GE_10^16: 1/200
CHARGING_RULE: DLFC-152
TERMINAL_ENDPOINT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Provenance, normalized scope, and ambiguities

The canonical question has no external Erdos Problems URL.  Its immutable
statement says that this program formulated it on 2026-07-22.  The byte-exact
delivered `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question asks whether, for every integer `A>=1`, every
sufficiently large depth `n` admits an `N` such that
`A*n*Q_pi(n,N)<=N^2`.  Here `Q_pi` counts ordered, diagonal-inclusive metric
circle near returns of the fixed orbit of pi.  T152 neither changes nor answers
that question.

T152 treats the finite-word equal-block sibling allowed by recorded
ambiguities A10 and A14.  The distinctions are load-bearing:

1. equality of decimal blocks is weaker than metric near return;
2. the census ranges over all finite words, not the prescribed digits of pi;
3. a small exceptional set does not exclude a fixed deterministic word;
4. finite replay checks are experiments and are not proofs of asymptotic or
   fixed-pi assertions.

All logarithms below are natural except `log_10`.  Coordinates and starts are
zero-indexed.  Square roots are positive real square roots.

## 2. Exact overlapping process and positive-density event

Fix an integer `N>=10^16` and put

```text
k=floor((1/4)*log_10 N),       a=ceil(k/2),
L=N+k-1,                       D={0,...,9}.
```

Thus `k>=4`.  For a word `x=(x_0,...,x_(L-1)) in D^L`, a depth
`1<=m<=k`, and a start `0<=i<N`, define

```text
W_i^m(x)=(x_i,...,x_(i+m-1)),
c_x(w;m)=#{0<=i<N:W_i^m(x)=w},                 w in D^m,
E_x(m)=sum_(w in D^m)c_x(w;m)^2.                         (2.1)
```

There are exactly `N` starts at every depth.  The last depth-`m` endpoint is

```text
(N-1)+(m-1)<=N+k-2=L-1,                                  (2.2)
```

so there is no wrapping, truncation, or padding.  Expanding the squares gives

```text
E_x(m)=#{(i,j) in {0,...,N-1}^2:W_i^m(x)=W_j^m(x)}.       (2.3)
```

The pairs in (2.3) are ordered and include exactly the `N` diagonal pairs.
Define

```text
Bad_x={m in {1,...,k}:E_x(m)>=N^2/m},
P_(N,k)={x in D^L:#Bad_x>=ceil(k/2)}.                     (2.4)
```

This is a positive-density bad-depth event with fixed density `rho=1/2`.
If `x in P_(N,k)` and `m_*(x)=max Bad_x`, then

```text
a=ceil(k/2)<=m_*(x)<=k.                                  (2.5)
```

Indeed, a subset of `{1,...,k}` with at least `a` elements has maximum at
least `a`.  This elementary observation is the only use of positive density:
the charging rule deliberately selects one localized witness depth rather than
adding savings over all bad depths.

## 3. The charging rule fixed before family tests

**DLFC-152 (depth-localized fractional cover).**  For each bad word:

1. choose the witness depth `m=m_*(x)`, with no discretionary tie-breaking;
2. localize further to its exact empirical block type
   `p(w)=c_x(w;m)/N` on the `K=10^m` blocks;
3. give each of the `N` coordinate intervals
   `I_i={i,...,i+m-1}` weight exactly `1/m`;
4. for each coordinate `q in {0,...,L-1}`, let
   `d_q=#{i:q in I_i}` and give the singleton `{q}` the residual weight
   `lambda_q=1-d_q/m`;
5. charge no other depth, interval, pair, or coordinate.

This rule is fixed independently of all examples in Section 8.  It is
witness-localized because only the deterministic maximal bad depth and its
exact type are used.  It is reuse-adjusted because a coordinate lying in
`d_q` selected windows receives total interval weight `d_q/m`, and its
singleton receives exactly the missing weight.  Since `0<=d_q<=m`,

```text
lambda_q>=0,
sum_(i=0)^(N-1)(1/m)*1_(q in I_i)+lambda_q=1.             (3.1)
```

The endpoint correction has an exact total, not an `O(k)` placeholder:

```text
sum_q lambda_q
 =L-(1/m)*sum_q d_q
 =L-(1/m)*sum_i #I_i
 =L-N
 =k-1.                                                    (3.2)
```

Thus every coordinate is covered with total weight exactly one and all
overlap reuse is charged once.  The `k-1` residual mass includes both the
triangular boundary deficiency of the selected depth and the `k-m` look-ahead
coordinates unused at that depth.

## 4. Fractional Shearer inequality, proved in the needed form

**Lemma 4.1 (fractional coordinate cover).**  Let `X=(X_0,...,X_(L-1))` be a
finite random vector.  If subsets `A` have nonnegative weights `gamma_A` and
each coordinate belongs to sets of total weight at least one, then

```text
H(X)<=sum_A gamma_A H(X_A).                               (4.1)
```

**Proof.**  Order the coordinates increasingly.  The entropy chain rule gives

```text
H(X_A)=sum_(q in A) H(X_q | X_(A intersect {0,...,q-1})). (4.2)
```

Conditioning reduces entropy, so each summand in (4.2) is at least
`H(X_q|X_0,...,X_(q-1))`.  After multiplying by `gamma_A` and summing, the
coefficient of the latter conditional entropy is at least one.  A final use of
the chain rule gives (4.1). QED.

Apply Lemma 4.1 to the intervals and singletons of DLFC-152.  Fix a depth `m`
and an exact type `p`, and let `A_(m,p)` be the set of all words in `D^L` with
that type at depth `m`.  If it is nonempty, take `X` uniformly on `A_(m,p)`.
For each start `i`, let `P_i` be the law of `W_i^m(X)`.  Every member of the
stratum has type `p`, hence exactly

```text
(1/N)*sum_i P_i(w)=p(w)                                   (4.3)
```

for every block `w`.  Concavity of Shannon entropy and (4.3) give

```text
(1/N)*sum_i H(P_i)<=H(p).                                 (4.4)
```

Every decimal singleton has entropy at most `log 10`.  Equations
(3.1), (3.2), (4.1), and (4.4) therefore give the fixed charging inequality

```text
log #A_(m,p)=H(X)
 <=(1/m)*sum_i H(P_i)+(sum_q lambda_q)*log 10
 <=(N/m)*H(p)+(k-1)*log 10.                 (DLFC-INEQ-152)
```

This is the load-bearing inequality.  It does not assume independence of
overlapping blocks, does not select disjoint residues, and does not sum costs
over depths.

## 5. Independent collision-to-Shannon estimate

For a probability vector `p=(p_1,...,p_K)`, put

```text
C_2(p)=sum_j p_j^2,
H(p)=-sum_j p_j log p_j,
D(p)=log K-H(p).                                          (5.1)
```

**Lemma 5.1.**  If `m>=2`, `K=10^m`, and `C_2(p)>=1/m`, then

```text
D(p)>sqrt(m)/100.                                         (5.2)
```

**Proof.**  Let

```text
S={j:p_j>1/(2m)},        alpha=sum_(j in S)p_j.            (5.3)
```

Outside `S`, `p_j^2<=(1/(2m))p_j`; inside `S`, the sum of
squares is at most `alpha^2`.  Therefore

```text
1/m<=C_2(p)<=alpha^2+1/(2m),
alpha>=1/sqrt(2m).                                        (5.4)
```

Also `#S<2m`.  The log-sum inequality on `S` and its complement gives

```text
D(p)>=alpha log(alpha*K/#S)
       +(1-alpha)log((1-alpha)*K/(K-#S)).                 (5.5)
```

The second term is at least `(1-alpha)log(1-alpha)>=-alpha`.
The function `u -> u(log(u*K/(2m))-1)` has derivative
`log(u*K/(2m))`, which is positive for
`u>=1/sqrt(2m)` and `m>=2`.  Hence (5.4)--(5.5) imply

```text
D(p)>
 [m*log 10-log(2*sqrt(2)*m^(3/2))-1]/sqrt(2m).            (5.6)
```

At `m=2`, the numerator in (5.6) exceeds
`4.60-2.08-1=1.52`, while `sqrt(2)*m/100<0.03`.
For real `m>=2`, the derivative of

```text
m*log 10-log(2*sqrt(2)*m^(3/2))-1-sqrt(2)*m/100
```

is `log 10-3/(2m)-sqrt(2)/100>2.30-0.75-0.02>0`.
Thus the numerator in (5.6) exceeds `sqrt(2)*m/100`, proving
(5.2). QED.

This proof is included in full.  It does not import the entropy certificate
argued in the unverified T144 note.

## 6. Exact type census

At depth `m`, an exact type is a vector of `K=10^m` nonnegative integer counts
summing to `N`.  Each coordinate lies in `{0,...,N}`, so the number of types is
at most

```text
(N+1)^K.                                                   (6.1)
```

(The exact count is `binom(N+K-1,K-1)`; only (6.1) is used.)  If a type is bad,
then `C_2(p)=E_x(m)/N^2>=1/m`.  By Lemma 5.1 and DLFC-INEQ-152,

```text
log #A_(m,p)
 <=(N/m)*(m*log 10-sqrt(m)/100)+(k-1)*log 10
 =L*log 10-N/(100*sqrt(m)).                               (6.2)
```

Summing (6.2) over (6.1) yields

```text
#{x in D^L:E_x(m)>=N^2/m}
 <=10^L exp(-N/(100*sqrt(m))+10^m*log(N+1)).              (6.3)
```

Every endpoint and reuse correction is already included in the `10^L`
baseline; there is no suppressed boundary factor.

## 7. Constant-explicit positive-density census

**Theorem 7.1 (T152 finite-word census; `proof sketch`).**  For every integer
`N>=10^16`, with `k,L` as in Section 2,

```text
#P_(N,k)
 <=10^L exp(-N/(100*sqrt(k))+10^k*log(N+1)+log k).        (7.1)
```

In particular,

```text
#P_(N,k)<=10^L exp(-N/(200*sqrt(k))).                     (7.2)
```

**Proof.**  By (2.5), every word in `P_(N,k)` is bad at some
`m in {a,...,k}`.  Union-bound (6.3) over at most `k` depths.  Since `m<=k`,
`1/sqrt(m)>=1/sqrt(k)` and `10^m<=10^k`, giving (7.1).

For the explicit simplification, the definition of `k` gives
`10^k<=N^(1/4)` and `k<=10^k<=N^(1/4)`.  For `N>=10^16`,
`log(N+1)<=N^(1/4)` and `log k<=k`, so

```text
10^k*log(N+1)+log k<=N^(1/2)+N^(1/4)<=2*N^(1/2).         (7.3)
```

Also `sqrt(k)<=N^(1/8)` and `400<=N^(3/8)` at this endpoint, whence

```text
2*N^(1/2)<=N/(200*sqrt(k)).                               (7.4)
```

Substituting (7.3)--(7.4) into (7.1) proves (7.2). QED.

The saving has the requested explicit scale `N/sqrt(k)`.  Positive density is
used to force one witness depth comparable with `k`; there is no false
additive gain of order `N*sqrt(k)`.

## 8. Required family tests

These tests follow the already-fixed DLFC-152 rule.  They do not select or
modify the rule.

### 8.1 Constant words

For each of the ten constant words, every one of the `N` depth-`m` blocks is
the same.  Therefore

```text
E_x(m)=N^2>=N^2/m
```

at every `1<=m<=k`, so all ten words lie in `P_(N,k)`.  Their logarithmic
cost relative to all `10^L` words is `(L-1)log 10`, much larger than the
upper-bound saving `N/(200sqrt(k))`; there is no contradiction.

### 8.2 Periodic words

Take the length-`L` prefix of an infinite decimal word with period dividing
`p`.  At each depth there are at most `p` distinct blocks.  Cauchy--Schwarz
gives

```text
E_x(m)=sum_w c_x(w;m)^2>=N^2/p.                           (8.1)
```

Thus every depth `m>=p` is bad.  If `p<=floor(k/2)+1`, then
`k-p+1>=ceil(k/2)`, so the word lies in `P_(N,k)`.  At most `10^p` words are
generated by period-`p` seeds.  This is far below the census upper bound and
tests that DLFC-152 permits very cheap globally reused witnesses.

### 8.3 Repeated de Bruijn words

Let a cyclic decimal de Bruijn word of order `k` be repeated, assume `N` is a
multiple of `10^k`, and append its first `k-1` symbols to obtain length `L`.
For every `1<=m<=k`, each length-`m` word occurs exactly `N/10^m` times among
the `N` starts.  Hence

```text
E_x(m)=10^m*(N/10^m)^2=N^2/10^m<N^2/m,                   (8.2)
```

because `10^m>m`.  There are no bad depths, so this family is outside
`P_(N,k)`.

### 8.4 T147 shared-prefix specification

This calculation is independent; it does not import the T147 note's claim.
Put

```text
a=ceil(k/2),             R=ceil(N/sqrt(a)),
F_(N,k)={x in D^L:x_q=0 for 0<=q<R+k-1}.                 (8.3)
```

Since `a>=2`, `R<=N`, and exactly `R+k-1` coordinates are fixed.  Therefore

```text
#F_(N,k)=10^(L-(R+k-1))=10^(N-R).                         (8.4)
```

For `m in {a,...,k}` and `0<=i<R`,
`i+m-1<=R+k-2`, so the first `R` blocks are `0^m`.  Thus

```text
E_x(m)>=R^2>=N^2/a>=N^2/m.                               (8.5)
```

There are `k-a+1=floor(k/2)+1>=ceil(k/2)` such depths, so

```text
F_(N,k) subset P_(N,k).                                   (8.6)
```

The logarithmic cost of this family relative to `10^L` is exactly
`(R+k-1)log 10`, of order `N/sqrt(k)`.  It is compatible with (7.2): already
`R log 10>=N*log(10)/sqrt(a)>N/(200sqrt(k))`.  Unlike a false additive
multidepth estimate, T152 charges the shared witness depth once and obtains
exactly the obstruction scale exhibited by this family.

## 9. Fingerprint and duplication boundaries

The exact readable comparator reports and their hashes are listed in
`PRIOR_INDEX.md`.  Their prose claims are comparison memory, not premises.

| item | available level and fingerprint | T152 boundary |
|---|---|---|
| T144 | unverified `proof sketch` note | The T144 note argues a one-depth residue-class extraction into disjoint blocks and then only a union bound for multiple depths.  T152 independently counts an exact overlapping type using a fractional cover of every window; it neither selects a residue class nor imports T144's entropy lemma. |
| T147 | unverified `proof sketch` note | The T147 note gives a shared-prefix counterfamily to adding one-depth savings over many depths.  T152 does not revive that additive inequality: maximal-depth localization charges once, and Section 8.4 independently recovers the same `N/sqrt(k)` lower-family scale. |
| T149 | active three-point semidefinite lane; no readable artifact in the supplied snapshot | The only available agenda-level fingerprint is three-point PSD/semidefinite consistency.  T152 forms no three-point matrix, moment matrix, PSD constraint, determinant, or semidefinite relaxation.  Its certificate is Shannon entropy plus a fractional coordinate cover.  No unpublished T149 result or finer distinction is inferred. |
| T150 | source statements `literature-checked`; substitutions and deductions `proof sketch` | T150's Candidate C applies separately-Lipschitz Gibbs concentration to one minimum statistic and loses `k^4`, giving an `N/k^4` saving.  T152 uses no concentration theorem or Gibbs measure.  It stratifies by one exact witness type and uses deterministic entropy charging, giving `N/sqrt(k)` while remaining compatible with the shared-prefix family. |

The T152 terminal proof is therefore not T144's disjoint-residue argument,
T147's counterfamily endpoint, T149's semidefinite fingerprint, or T150's
bounded-difference concentration estimate.  This is a scoped mechanism
distinction, not a literature novelty claim.

## 10. Additional unproved pi-specific premise toward T107

**PI-MEMBERSHIP-EXCLUSION-AND-T107-TRANSFER-T152 (`conjecture`; ADDITIONAL
UNPROVED PI-SPECIFIC PREMISE; NOT ASSERTED).**  There exist a strictly
increasing sequence of positive integers `N_j`, associated
`k_j=floor((1/4)log_10 N_j)`, and sets
`G_j subset {1,...,k_j}` with `#G_j>=ceil(k_j/2)` such that, for every
sufficiently large `j`:

1. the length-`N_j+k_j-1` decimal look-ahead word generating the first `N_j`
   starts of pi is outside `P_(N_j,k_j)`; and
2. for every `ell in G_j`, with `P=N_j`, the following two literal T107
   inequalities hold:

```text
rowBoundaryLoad(ell,P)<=P/(40*10^ell),
|rowFourierRemainder(ell,P)|<=P^2/(10*10^ell).
```

The supplied knowledge snapshot describes the T107 module copied as
`prior-T107-module.txt` as machine-checked; T152 does not independently compile
or audit that text copy and does not use it as a theorem premise.  The module
itself explicitly leaves its averaged fixed-pi analytic estimate as a premise.
The census (7.1), which only counts all finite words, proves neither numbered
condition above and supplies no implication from condition 1 to condition 2.
Their conjunction is the additional unproved pi-specific transfer package.

No fixed-pi result, canonical A1 result, C1 result, C2 result, or local
pi-digits result is claimed.

## 11. Replay and terminal endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t152.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier uses Python integers and exact `Fraction` arithmetic for block
counts, coverage weights, type identities, and family endpoints.  Floating
point is used only to test the displayed logarithmic analytic inequalities at
finite sample points.  Each required family receives one finite representative;
the universal family arguments are the displayed calculations in Section 8,
not the replay.  These computations can expose transcription errors but do not prove
Theorem 7.1; its universal `proof sketch` is Sections 3--7.

TERMINAL ENDPOINT (1/1): **PROOF SKETCH OF A RELATED-MODEL CENSUS.**

DLFC-152 gives the constant-explicit bound (7.1), and for `N>=10^16` the pure
bound (7.2).  It reaches the T147 shared-prefix obstruction scale by charging
one maximal bad-depth type with an exact fractional cover, not by adding costs
across depths.  This closes only the stated finite-word charging question and
makes no fixed-pi claim.
