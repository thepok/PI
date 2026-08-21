# T154: the finite reuse-capacity entropy LP

Date: 2026-08-12 UTC.

Claim label: `proof sketch`. The finite linear-programming and asymptotic
arguments below are given in full, but this note has no kernel-checked
formalization. The replay is an `experiment`: it checks exact rational finite
instances, endpoints, certificates, comparator hashes, and report markers. It
is not a proof of the universal arguments. T152 is motivation only; every
claim used below is re-derived.

```text
BASE: 10
KAPPA: 1/4
RHO: 1/2
RATIONAL_ENTROPY_CONSTANT: 1/100
LP_KIND: depth-uniform interval packing
TERMINAL_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, normalized sibling, and ambiguities

The canonical question has no external Erdos Problems URL. Its immutable
provenance says that this program formulated it on 2026-07-22. The byte-exact
`canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether every integer `A>=1` and every sufficiently large depth `n`
admit an `N` for which `A*n*Q_pi(n,N)<=N^2`; `Q_pi` counts ordered,
diagonal-inclusive metric circle near returns of the fixed decimal orbit of
pi. T154 neither changes nor answers that question. It studies a finite-word
equal-block sibling under recorded ambiguities A10 and A14.

Fix an integer `N>=10^16` and define

```text
k=floor((1/4)*log_10 N),   a=ceil(k/2),   L=N+k-1,
Q={0,...,L-1},             U={a,...,k}.
```

Then `k>=4`. For `m in U` and `0<=i<N`, define the coordinate interval

```text
I_(m,i)={i,i+1,...,i+m-1} subset Q.                       (1.1)
```

Its first and last endpoints are `i` and `i+m-1`. The largest possible last
endpoint is

```text
(N-1)+(k-1)=N+k-2=L-1,                                   (1.2)
```

so all intervals exist without wrapping, truncation, or padding. For `q in Q`
put

```text
d_(m,q)=#{i in {0,...,N-1}:q in I_(m,i)}
       =max(0,min(N-1,q)-max(0,q-m+1)+1).                 (1.3)
```

Consequently

```text
0<=d_(m,q)<=m,                 sum_(q in Q)d_(m,q)=N*m.   (1.4)
```

Let `S` be any nonempty subset of `U`. It is the set of depths whose exact
empirical types have independently been certified to satisfy the collision
condition `sum_w p_m(w)^2>=1/m`. The LP is conditional on this finite
certificate. The stipulated density `rho=1/2` among depths `1,...,k` guarantees
at least one eligible upper-half depth, not that every depth in `U` is eligible.
Write `m_0=min S`.

The load-bearing ambiguities are fixed as follows.

1. Every interval at one certified depth receives the same LP weight. An
   independent variable per interval is rejected in Section 3.
2. Coordinate capacity is exactly one; no coordinate may be charged twice.
3. The LP data are rational. Square-root profits are replaced by explicit
   rational lower surrogates.
4. The LP optimizes a Shannon description deficit on one exact multidepth-type
   stratum. Type-count and union overheads are not part of its objective.
5. All logarithms in entropy and census costs are natural except `log_10`.

## 2. Rational profit and the primal LP

For an integer `m>=1`, define

```text
h_m=min{h in positive integers:h^2>=m}=ceil(sqrt(m)),
g_m=m/(100*h_m).                                          (2.1)
```

Both are exact rational data. Since

```text
sqrt(m)<=h_m<=sqrt(m)+1<=2sqrt(m),
sqrt(m)/200<=g_m<=sqrt(m)/100,                            (2.2)
```

`g_m` is a conservative rational replacement for a Shannon deficit
`sqrt(m)/100`.

The finite rational **primal interval-packing LP** is

```text
(P_(N,S))  maximize       sum_(m in S) N*g_m*t_m
           subject to     sum_(m in S)d_(m,q)*t_m<=1  (q in Q),
                          t_m>=0                       (m in S). (2.3)
```

The interpretation is literal: every interval `I_(m,i)` gets weight `t_m`, so
coordinate `q` receives total interval weight
`sum_m d_(m,q)t_m`. Its capacity is one. The objective credits all `N`
depth-`m` intervals with total certified entropy profit `N*g_m*t_m`.

The LP is feasible (`t=0`). It is bounded because each `m` has some coordinate
with `d_(m,q)>=1`, whence `t_m<=1`. Therefore its optimum is finite and
attained on a nonempty compact rational polytope.

## 3. Why depth-uniform weights are necessary

This section re-derives the entropy meaning rather than importing T152. Fix,
for every `m in S`, an exact empirical block law `p_m` with

```text
sum_w p_m(w)^2>=1/m.                                      (3.1)
```

Let `A` be a nonempty set of decimal words in `D^L`, `D={0,...,9}`, having all
these exact types, and let `X` be uniform on `A`. Denote by `P_(m,i)` the law of
`X` restricted to `I_(m,i)`. Exact-type averaging gives

```text
(1/N)*sum_(i=0)^(N-1)P_(m,i)=p_m.                         (3.2)
```

By concavity of Shannon entropy,

```text
sum_i H(P_(m,i))<=N*H(p_m).                               (3.3)
```

For completeness, the collision-to-Shannon estimate needed here follows by
the same elementary heavy-set argument recorded next. Put `K=10^m`,
`D(p)=log K-H(p)`, and `T={w:p(w)>1/(2m)}`. From (3.1),

```text
alpha=sum_(w in T)p(w)>=1/sqrt(2m),        #T<2m.          (3.4)
```

The log-sum inequality on `T` and its complement yields

```text
D(p)>=alpha*log(alpha*K/#T)
       +(1-alpha)*log((1-alpha)*K/(K-#T))
    > [m*log 10-log(2sqrt(2)m^(3/2))-1]/sqrt(2m)
    > sqrt(m)/100                                         (3.5)
```

for every `m>=2`. For the final inequality, after multiplication by
`sqrt(2m)`, the difference at `m=2` is positive and its derivative for real
`m>=2` is at least `log 10-3/4-sqrt(2)/100>0`. Since `m in S subset U` and
`a>=2`, this covers every LP depth. Equations (2.1), (3.3), and (3.5) imply

```text
sum_i [m*log 10-H(P_(m,i))]
 >=N*[m*log 10-H(p_m)]
 >N*g_m.                                                  (3.6)
```

For primal-feasible `t`, define residual singleton weights

```text
r_q=1-sum_(m in S)d_(m,q)t_m>=0.                          (3.7)
```

The weighted coordinate-cover inequality says

```text
H(X)<=sum_(m in S)sum_i t_m H(X_(I_(m,i)))
      +sum_(q in Q)r_q H(X_q).                            (3.8)
```

Here is its proof. Order coordinates increasingly, expand every entropy by the
chain rule, and use that conditioning on fewer earlier coordinates increases
conditional entropy. The coefficient of each full-past conditional entropy is
`sum_m d_(m,q)t_m+r_q=1`; summing recovers `H(X)`.

Since `H(X_q)<=log 10`, subtracting (3.8) from `L log 10`, using (3.7), and
then (3.6), gives

```text
L*log 10-log #A
 >=sum_(m in S)t_m sum_i[m*log 10-H(P_(m,i))]
 >=sum_(m in S)N*g_m*t_m.                                 (3.9)
```

Thus every primal objective is a proved lower bound on the description deficit
of this exact multidepth-type stratum.

An apparently richer LP with independent weights `t_(m,i)` is not justified:
(3.3) controls only an unweighted average. Unequal weights could concentrate on
the high-entropy windows while still claiming the average deficit. No such
weighted inequality follows from the exact type. T154 therefore does not use
that false relaxation.

## 4. Coordinate-capacity dual

The rational **dual coordinate-price LP** is

```text
(D_(N,S))  minimize       sum_(q in Q)y_q
           subject to     sum_(q in Q)d_(m,q)y_q>=N*g_m (m in S),
                          y_q>=0                         (q in Q). (4.1)
```

Equivalently, its depth-`m` condition is

```text
sum_(i=0)^(N-1)sum_(q in I_(m,i))y_q>=N*g_m.              (4.2)
```

Thus a coordinate may pay for every interval containing it, but its price is
counted only once in the objective. This is the exact reuse-aware obstruction.

For primal-feasible `t` and dual-feasible `y`, direct rearrangement proves weak
duality:

```text
sum_m N*g_m*t_m
 <=sum_m t_m sum_q d_(m,q)y_q
  =sum_q y_q sum_m d_(m,q)t_m
 <=sum_q y_q.                                             (4.3)
```

## 5. Direct finite strong duality

We prove equality without citing an LP duality theorem. Write `A_(q,m)=d_(m,q)`,
`b=1`, and `c_m=N*g_m`. The primal is `max c^Tt` subject to `At<=b`, `t>=0`.
Let its attained value be `v>0`.

### 5.1 A finite-cone separation lemma

A cone generated by finitely many vectors is closed. Indeed, every conic
representation can be reduced, by eliminating a linear dependence while
preserving nonnegative coefficients, to one using linearly independent
generators. There are finitely many independent subsets. Along any convergent
sequence, pass to one fixed subset; injectivity of its generator matrix forces
the coefficients to converge to nonnegative limits.

If `z` lies outside a closed convex cone `C`, let `p in C` minimize Euclidean
distance to `z`. Minimality along the segment from `p` to any `q in C` gives

```text
(z-p) dot (q-p)<=0.                                       (5.1)
```

Taking `q=0` and `q=2p` gives `(z-p) dot p=0`. Hence `h=p-z` satisfies

```text
h dot q>=0 for q in C,              h dot z=-||h||^2<0.   (5.2)
```

This proves the only separation fact used below.

### 5.2 Application to the primal and dual

In `R^(L+1)`, let `C` be generated by

```text
(A_col(m),c_m) for m in S,       and       (e_q,0) for q in Q. (5.3)
```

Membership `(b,u) in C` means that some `t,s>=0` satisfy
`At+s=b` and `c^Tt=u`. Therefore `(b,v+epsilon)` is outside `C` for every
`epsilon>0`.

Apply (5.2), writing the separator as `(u,alpha)`. Nonnegativity on the
generators gives

```text
u>=0,                         A^T u+alpha*c>=0,            (5.4)
```

while strict separation gives

```text
u^T b+alpha*(v+epsilon)<0.                                (5.5)
```

Because `u>=0`, `b=1`, and `v+epsilon>0`, (5.5) forces `alpha<0`. Put
`y=u/(-alpha)`. Then

```text
y>=0,          A^T y>=c,          v<=b^T y<v+epsilon,     (5.6)
```

where the first inequality on the objective is weak duality.

Choose `epsilon=1/n`. The corresponding dual points eventually have
`sum_q y_q<v+1`, so nonnegativity bounds every coordinate. A convergent
subsequence has a dual-feasible limit `y*` with `sum_q y*_q=v`. Thus both
optima are attained and

```text
max(P_(N,S))=min(D_(N,S))=v.                              (5.7)
```

Finally, the common value and optimizers may be taken rational. A maximizer can
be replaced by a vertex of the rational primal polytope; its active rational
linear system has a rational solution. Equation (5.7) makes the dual optimal
face nonempty, and intersecting it with `sum_q y_q=v` makes it compact; a
vertex is again the solution of a rational active system. Hence (5.7) is strong
duality for the stated rational LPs, not merely for their real relaxations.

## 6. Exact optimum and asymptotic quantifiers

The one-depth primal certificate

```text
t_(m_0)=1/m_0,                   t_m=0 for m!=m_0          (6.1)
```

is feasible by `d_(m_0,q)<=m_0`. Its value is

```text
N*g_(m_0)/m_0=N/(100*h_(m_0)).                            (6.2)
```

There is an exact one-coordinate dual certificate. Put `q_*=k-1`. For every
`m<=k`, one has `m-1<=q_*<=N-1`, and (1.3) therefore gives

```text
d_(m,q_*)=m.                                               (6.3)
```

Set

```text
y_(q_*)=N/(100*h_(m_0)),              y_q=0 for q!=q_*.   (6.4)
```

This is dual feasible because `h_m>=h_(m_0)` and (6.3) gives

```text
sum_q d_(m,q)y_q=m*N/(100*h_(m_0))
                   >=N*m/(100*h_m)=N*g_m.                 (6.5)
```

Its objective equals the primal value (6.2). Weak duality, even without the
general strong-duality proof, now gives the exact formula

```text
v_(N,S)=N/(100*h_(m_0)).                                  (6.6)
```

The endpoint `q_*=k-1` is valid because `k<=N` for `N>=10^16`; it is an
interior coordinate for every admitted interval length. No boundary term is
hidden in (6.6).

Since `a<=m_0<=k`, `h_(m_0)<=sqrt(k)+1<=2sqrt(k)`, and
`h_(m_0)>=sqrt(a)>=sqrt(k/2)`, (6.6) gives for every
`N>=10^16` and every nonempty `S subset U`

```text
N/(200*sqrt(k)) <= v_(N,S)
 <=sqrt(2)*N/(100*sqrt(k)).                               (6.7)
```

This proves, uniformly in the certified nonempty set `S`,

```text
v_(N,S)=Theta(N/sqrt(k))                                  (6.8)
```

with explicit absolute constants.

There is also an exact first-order statement. For every sequence of integers
`N_j->infinity`, put `k_j=floor((1/4)log_10 N_j)` and choose nonempty
`S_j subset {ceil(k_j/2),...,k_j}`. If

```text
m_(0,j)/k_j -> theta in [1/2,1],                          (6.9)
```

then `h_(m_(0,j))/sqrt(k_j)->sqrt(theta)`; (6.6) therefore
proves

```text
v_(N_j,S_j)/(N_j/sqrt(k_j)) -> 1/(100*sqrt(theta)).       (6.10)
```

In particular, if `a_j in S_j` eventually, the limit is `sqrt(2)/100`. The
stipulated `rho=1/2` condition without knowledge of the shallowest certified
depth gives only the uniform constants (6.7), not that special constant.

## 7. The T147 shared-prefix dual test

This section independently reconstructs the family; no claim from the
unverified T147 note is a premise. Let

```text
R=min{r in positive integers:a*r^2>=N^2}=ceil(N/sqrt(a)),
B=R+k-1.                                                  (7.1)
```

Fix the first `B` coordinates, indexed `0,...,B-1`, to zero and leave the other
`L-B=N-R` coordinates arbitrary. The family therefore has exactly

```text
#F_(N,k)=10^(N-R).                                         (7.2)
```

For every `m in U` and `0<=i<R`,

```text
i+m-1<=(R-1)+(k-1)=B-1,                                  (7.3)
```

so the first `R` depth-`m` blocks equal `0^m`. Their ordered,
diagonal-inclusive collision contribution is at least

```text
R^2>=N^2/a>=N^2/m.                                       (7.4)
```

Thus every upper-half depth is certified for this family.

More strongly, the fixed prefix supports a genuine dual certificate. Set

```text
y_q^pref=N/(100*R*h_a) for 0<=q<B,       y_q^pref=0 otherwise. (7.5)
```

For any `m in U`, the first `R` intervals lie inside the prefix, so their
contribution alone gives

```text
sum_q d_(m,q)y_q^pref
 >=R*m*N/(100*R*h_a)
  =N*m/(100*h_a)>=N*m/(100*h_m)=N*g_m.                    (7.6)
```

Therefore (7.5) is dual feasible for every `S subset U`. Its exact cost is

```text
C_pref^LP=B*N/(100*R*h_a).                                (7.7)
```

For `S=U`, divide (7.7) by the exact optimum `N/(100*h_a)`:

```text
C_pref^LP/[N/(100*h_a)]=B/R=1+(k-1)/R.                   (7.8)
```

Because `R>=N/sqrt(a)`, `(k-1)/R<=k^(3/2)/N->0`. Hence the
prefix-supported dual is asymptotically optimal. It is not the unique optimizer:
the one-coordinate certificate (6.4) is already exact. Nevertheless the prefix
test proves that the coordinates reused by the T147 family themselves support
a dual whose relative excess tends to zero. Moreover,

```text
C_pref^LP=(sqrt(2)/100+o(1))*N/sqrt(k).                   (7.9)
```

The family census cost relative to all `10^L` words is separately

```text
B*log 10=(sqrt(2)*log 10+o(1))*N/sqrt(k).                 (7.10)
```

Equations (7.9) and (7.10) match in rate, not in normalization: the LP uses the
deliberately weak entropy constant `1/100`, whereas fixing a decimal coordinate
costs `log 10`. The family is an exact infinite obstruction along, for example,
`N=10^(4k)` for every integer `k>=4`; finite computation is unnecessary for
that assertion. For this simultaneous upper-half event, it excludes every
universal upper census of the form
`10^L*exp(-c*N*sqrt(k)+o(N*sqrt(k)))` with fixed `c>0`. It does not prove that
shared prefixes are the unique extremizers.

## 8. Cheap family tests and scope

1. **Constant words.** Every depth is certified, so the LP yields only an
   `N/sqrt(k)` deficit. The actual set has ten members and much larger deficit;
   the LP is valid but intentionally nonexact for this family.
2. **Period-`p` words.** At most `p` depth-`m` blocks occur, so collision is at
   least `1/p`. If `p<=a`, every `m in U` is certified. Again the LP is a weak
   universal certificate, not an exact census.
3. **Repeated decimal de Bruijn words.** With a repeated order-`k` cycle and
   `N` divisible by `10^k`, collision at depth `m<=k` is `10^(-m)<1/m`.
   Hence `S` is empty and no positive LP profit is justified. T154 never runs
   the nonempty-depth LP on this family.
4. **Shared prefix.** Sections 7.2--7.10 give both its exact cardinality and an
   asymptotically optimal prefix-supported coordinate dual.

The LP value is a description deficit for one exact multidepth-type stratum.
Turning it into a complete exceptional-set census still requires counting
types and possible certified depth sets. The rate result does not assert that
the rational constant `1/100` is the best collision-to-Shannon constant or that
this relaxation captures every possible reuse-aware entropy proof.

## 9. Fingerprint comparison and duplication boundary

The delivered comparator copies are byte-exact, and their hashes are checked by
the replay. Verification levels are load-bearing. No unverified note is used as
a premise above.

| item | available level and fingerprint | T154 boundary |
|---|---|---|
| T135, report SHA `4439850a49ee2fa7351d85daf366eba4b2b4a55e756a15bf7c431d92fb195e21` | source claims `literature-checked`; deductions `proof sketch`; rejects unconditional coordinate-projection Renyi-2 tensorization | T154 uses Shannon entropy on actual coordinate intervals and proves a fractional cover directly. It infers nothing from projection Renyi-2 marginals and introduces a finite packing/cover dual pair instead. |
| T144, report SHA `96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a` | unverified `proof sketch`; one-depth disjoint-residue extraction and method of types | T154 selects no residue class and proves no one-depth census. It optimizes simultaneous depth-uniform interval charges under shared coordinate capacities. |
| T147, report SHA `d1af43d8b2c21c6b3106a4c75e8e38467146e7c09f219adf240ee83a9250a909` | unverified `proof sketch`; shared-prefix counterfamily to additive multidepth charging | T154 independently rebuilds the prefix and converts its reused coordinates into the feasible dual (7.5), showing rate-level optimality rather than merely using it as a negative test. |
| T150, report SHA `937a6a9c23ba6c319de2f7f2457d33b163f67005e0651f6c199d0453902d5907` | source claims `literature-checked`; substitutions `proof sketch`; separately-Lipschitz Gibbs concentration gives an `N/k^4` related-model saving | T154 uses no Gibbs measure or concentration theorem. Its deterministic exact-type entropy LP has `N/sqrt(k)` value but does not itself sum over types. |
| T152, report SHA `01ae77f2f125d70d31e5ae774fb2c7adb8f741b04bb9fbec6e19cdc1fc497171` | unverified `proof sketch`; one maximal-depth exact type with interval weight `1/m` and residual singletons | T152 is motivation only. T154 re-proves the cover and entropy estimate, allows any certified nonempty depth set, optimizes simultaneous weights, derives the coordinate dual, proves strong duality, and finds the T147-supported dual certificate. The one-depth feasible point recovers T152's rate, so this is an optimization/refinement rather than an independent census. |
| active T153, inspectable `active-items-snapshot.json` | only an active generation-1 lease is present at lines 197--205 of the snapshot; no agenda text, report, result, hash, verification level, or mathematical fingerprint is supplied | No semantic overlap or novelty distinction can honestly be asserted. T154 records only this availability boundary. A refreshed readable T153 artifact must be compared before any novelty claim. |

These are mechanism comparisons, not literature-novelty claims.

## 10. Additional unproved fixed-pi transfer toward T107

**PI-LP-MEMBERSHIP-AND-T107-TRANSFER-T154 (`conjecture`; ADDITIONAL UNPROVED
FIXED-PI PREMISE; NOT ASSERTED).** There is an increasing sequence `N_j`, with
`k_j=floor((1/4)log_10 N_j)`, for which exact look-ahead decimal words generated
by the first `N_j` starts of the pi orbit admit independently certified
nonempty upper-half bad-depth sets and exact-type strata to which (3.9) applies,
the resulting exceptional-set information excludes those fixed words in the
direction required by the program, and a separate checked conversion supplies
T107's literal boundary and Fourier budgets.

Nothing in the finite LP, strong duality, all-word family tests, or exact
prefix counterfamily proves membership or exclusion for the prescribed digits
of pi. Equal blocks are also not the canonical metric near-return event. The
T107 conversion remains an additional premise rather than a consequence of
the LP. No fixed-pi result, A1 result, C1 result, or C2 result is claimed.

## 11. Replay and terminal verdict

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t154.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier uses Python integers and `Fraction` arithmetic. It checks the
canonical and comparator hashes; interval endpoints and incidence identities;
primal, uniform-dual, and prefix-dual feasibility; exact finite LP optima by
vertex enumeration for bounded instances; the strong-duality equality on those
instances; family endpoints and cardinalities; and structured scope markers.
These finite checks can falsify formulas but do not prove Sections 3, 5--7 for
all parameters. Those universal arguments are the displayed proof sketch.

TERMINAL VERDICT (1/1): **PROVED MATCHING RATE.**

For every `N>=10^16` and every nonempty certified upper-half depth set, the
finite rational entropy-safe interval packing and coordinate-capacity dual have
the exact common attained rational optimum (6.6), satisfying the explicit
`Theta(N/sqrt(k))` bounds (6.7). When the shallow upper-half depth is certified,
the first-order constant is `sqrt(2)/100`; the independently reconstructed
T147 prefix supports an asymptotically optimal dual certificate and has an
exact infinite census cost of the same rate. This is a related finite-word LP
result only, not a fixed-pi or program-conjecture result.
