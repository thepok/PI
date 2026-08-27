# T156: inverse stability at the reuse scale

Search date: 2026-08-12 UTC.

The eight source statements in Sections 4--6 are `literature-checked` against
the byte-pinned PDFs and exact locators in `SOURCE_PINS.md`. Every translation
to the word problem, including all asymptotic substitutions, is a `proof
sketch`. Section 8 contains elementary `proof sketch` family calculations.
The replay is an `experiment`: it checks finite instances, formulas, source
anchors, and hashes, not an asymptotic inverse theorem. The fixed-pi premise in
Section 11 is an explicitly unproved `conjecture`.

```text
PRIMARY_SOURCE_COUNT: 8
PRIMARY_SOURCE_CAP: 8
DOMAIN_COUNT: 3
DOMAIN_CAP: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable question and scope

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether every integer `A>=1` and every sufficiently large depth `n`
admit an `N` with `A*n*Q_pi(n,N)<=N^2`, where `Q_pi` counts ordered,
diagonal-inclusive metric circle near returns of the fixed orbit
`{10^j*pi}`. T156 neither changes nor answers this question. It studies a
finite-word equal-block sibling under recorded ambiguities A10 and A14.
Equal blocks are weaker than metric near returns, a census over all words does
not exclude one fixed word, and none of the sources proves anything about pi.

The source URL is the local canonical provenance, not an external Erdős
Problems URL. That provenance is preserved in `canonical_statement.txt`.

## 2. Literal event and target template certificate

All logarithms are natural except `log_10`; coordinates and starts are
zero-indexed. Fix an integer `N>=10^16` and put

```text
k=floor((1/4)*log_10 N),   a=ceil(k/2),
U={a,...,k},               L=N+k-1,
D={0,...,9},               R=N/sqrt(k).
```

Thus `k>=4`. For `x in D^L`, `m in U`, and `0<=i<N`, define

```text
W_i^m(x)=(x_i,...,x_(i+m-1)),
c_x(w;m)=#{0<=i<N:W_i^m(x)=w},
E_x(m)=sum_(w in D^m)c_x(w;m)^2.                         (2.1)
```

The last possible endpoint is `(N-1)+(k-1)=L-1`; there is no wrapping,
padding, or truncation. Expanding the squares gives

```text
E_x(m)=#{(i,j) in {0,...,N-1}^2:W_i^m(x)=W_j^m(x)}.      (2.2)
```

Hence pairs are ordered and (2.2) contains exactly `N` diagonal pairs. The
literal upper-half event audited here is

```text
B_(N,k)={x in D^L:E_x(m)>=N^2/m for every m in U}.       (2.3)
```

This is exactly the all-upper-half convention of the T147 note. It is a subset
of the T152 note's event requiring at least `ceil(k/2)` bad depths among
`{1,...,k}`. It supplies `S=U` to the T154 note's LP convention. These are
comparisons to unverified notes, not imported premises.

### 2.1 Literal templates

An **interval-periodic coordinate-core template** is a finite list

```text
T=((ell_j,q_j,p_j,u_j):1<=j<=h),                          (2.4)
```

where `0<=ell_j`, `1<=q_j`, `ell_j+q_j<=L`, `1<=p_j<=q_j`,
and `u_j in D^(p_j)`. Its cylinder consists of all `x in D^L` satisfying

```text
x_(ell_j+t)=(u_j)_(t mod p_j) for 0<=t<q_j and all j.    (2.5)
```

Overlapping records must agree; otherwise the cylinder is empty. Let `Q(T)`
be the union of constrained coordinates. Use the explicit description charge

```text
code(T)=h*log(2*(L+1)^3)+log(10)*sum_j p_j.              (2.6)
```

This pays `log 2+3log(L+1)` for each record's start, interval length, period,
and delimiter, followed by exactly `p_j` decimal seed symbols. Thus it is a
self-delimiting upper charge and does not rely on an unspecified compression
language.

The tested inverse fingerprint `ITC-156(c)` is the existence, for some fixed
`c>0`, of families `T_(N,k)` such that

```text
B_(N,k) subset union_(T in T_(N,k)) cylinder(T),
log #T_(N,k)=o(R),
max_T code(T)=o(R),
min_T #Q(T)>=c*R.                                         (2.7)
```

No source uses this definition. Equation (2.7) is the precise target against
which theorem outputs are tested. It is deliberately stronger than closeness
in probability or symmetric difference: it asks for exact coverage. A fixed
periodic seed is a template; an arbitrary coordinate set is not free, because
its locations and values must be paid for in (2.6).

### 2.2 Near-saturation scale

The unverified T152 note argues for a whole-event saving `R/200`; the
unverified T154 note argues that its exact-type reuse LP has value comparable
to `R`. T156 uses only the scale `R`, not either claim as a premise. A source
translation survives only if both its structural error and the logarithm of
its template/fingerprint choices are `o(R)`, while each output fixes at least
`cR` coordinates. This is the meaning of “near-saturation” in this audit.

## 3. Bounded source ledger

The clean-context search stopped at exactly eight new primary papers in exactly
three domains. None is one of T140's two or T150's six pinned sources.

| ID | domain | exact retained results | tested role |
|---|---|---|---|
| S1 | entropy/fractional-cover stability | Ellis--Friedgut--Kindler--Yehudayoff, Theorems 1 and 4 | inverse uniform-cover stability |
| S2 | entropy/fractional-cover stability | Madiman--Tetali, Theorem I', Proposition II, Theorem IV | fractional entropy gaps |
| S3 | supersaturation/container stability | Campos--Samotij, Theorems A, B, D, E | optimal-uniformity fingerprints |
| S4 | supersaturation/container stability | Balogh--Samotij, Theorems 1.1 and 1.6 | efficient growing-uniformity containers |
| S5 | supersaturation/container stability | Samotij, Definitions 3.2--3.3 and Theorem 3.4 | robust stability transfer |
| S6 | symbolic LD/Gibbs conditioning | Dembo--Zeitouni, Theorem 2.1, Corollaries 2.7/2.11, Propositions 2.12/2.15 | growing conditioned blocks |
| S7 | symbolic LD/Gibbs conditioning | Csiszár--Cover--Choi, Theorems 4/5 and Lemma 3 | overlapping Markov types |
| S8 | symbolic LD/Gibbs conditioning | Chaintron--Conforti--Reygner, Theorem 2.7, Proposition 2.10, Remark 2.11, Proposition 2.19, Corollary 2.20 | conditional LDP and constraint stability |

Exact titles, versions, URLs, DOI data, hashes, and physical/printed pages are
in `SOURCE_PINS.md`. Retrieval succeeded for all eight; `pdftotext -layout`
worked and no OCR was used.

## 4. Domain I: entropy and fractional-cover stability

### 4.1 S1: genuine stability, wrong premise and error scale

`literature-checked`: S1 Theorem 4 takes a weighted coordinate cover with
separation weight

```text
sigma=min_(i!=j) sum_(g intersect {i,j}={i}) w(g)>0,
rho=1/sigma.
```

If a finite `S subset Z^d` nearly saturates the weighted uniform-cover
projection inequality with multiplicative defect `epsilon`, it gives a box
`B` with

```text
#(S symmetric_difference B)/#S
 <=(4*d^2+64*d)*rho*epsilon.                              (4.1)
```

`proof sketch` substitution: the word support has dimension `d=L`. For one
depth `m`, interval weights `1/m` separate two adjacent interior coordinates
with weight `1/m`, so `rho>=m`. Therefore even the optimistic benchmark formed
by replacing the actual coefficient `rho` by its lower bound `m` is

```text
benchmark error =(4*L^2+64*L)*m*epsilon.                  (4.2)
```

At upper-half depths `m=Theta(k)` and `L=Theta(N)`, making the theorem's
displayed guarantee `o(1)` necessarily requires the already optimistic
condition `epsilon=o(1/(N^2*k))`; the actual `rho` can only worsen it. The
collision condition (2.3) is not a near-equality statement for support
projection cardinalities and supplies no such `epsilon`. More decisively,
(4.1) leaves exceptions. Exact coverage in (2.7) cannot turn an uncontrolled
positive exceptional set into `exp(o(R))` templates; forcing fewer than one
exception would require `(4L^2+64L)rho*epsilon*#S<1`, exponentially beyond the
theorem's premise.
The output box also need not constrain `cR` coordinates without a separate
volume-deficit premise.

**S1 rejection:** explicit dimension/separation stability error plus exact
coverage gap.

### 4.2 S2: exact gap identities are not inverse structure

`literature-checked`: S2 Theorem I' and Proposition II give strong and weak
fractional entropy inequalities for arbitrary discrete random vectors.
Theorem IV exactly identifies normalized upper and complementary lower gaps;
equation (16) identifies one special gap with total correlation/KL divergence.

`proof sketch` substitution: S2 cleanly expresses the interval weights and
residual singleton cover used by the T152/T154 notes. It introduces no extra
loss into a forward entropy charge. It gives only a scalar gap, however, and
no coordinates, intervals, box, or family of cores. At a gap of order `R`,
Pinsker is vacuous as a small-distance statement; at a small normalized gap it
still controls a distributional distance, not exact support coverage. No
constant in S2 bounds `log #T` or `code(T)` in (2.7).

**S2 rejection:** no inverse conclusion to substitute.

## 5. Domain II: supersaturation and container stability

### 5.1 Exact collision encoding reused only as a test

For comparison with source hypotheses, use T140's digit-assignment encoding,
re-derived here. At depth `m`, vertices are `[L]_0 x D`; for nonoverlapping
starts `i<j`, an equal word `u in D^m` gives a `2m`-edge consisting of its two
digit assignments. Then

```text
s=2m, v=10L, e=P_(N,m)*10^m,
P_(N,m)=(N-m)(N-m+1)/2.                                  (5.1)
```

An adjacent fixed digit pair belongs to at least

```text
(m-1)*(N/2-m)*10^(m-2)                                   (5.2)
```

edges in the stated interior range. Consequently

```text
Delta_2/(e/v)
 >=(m-1)*(N/2-m)*L/(10*P_(N,m))=Omega(m).                (5.3)
```

Equations (5.1)--(5.3) are `proof sketch` elementary translations, also
recorded in T140; they are not source theorems. The event is edge-rich, while
all three retained container sources classify independent or low-edge sets.

### 5.2 S3: small fingerprints without coordinate shrinkage

`literature-checked`: S3 Theorem A gives every independent set in an
`r`-uniform hypergraph a fingerprint of size at most
`8*r^2*p*v` for `p<=1/(8r^2)` and a container carrying a low-`p`-weight
hypergraph cover. Theorems B/E give uniformity-free fingerprints of size
`p*v/delta`; Theorem D stops when balanced supersaturation fails.

`proof sketch` substitution: with `r=2m` and `v=10L`, crude fingerprint
enumeration costs

```text
log sum_(j<=8r^2*p*v) binom(v,j)
 <=8r^2*p*v*log(e/(8r^2*p))                               (5.4)
```

when `8r^2p<=1`. Making (5.4) `o(R)` requires roughly
`p*log(1/p)=o(k^(-5/2))`. S3 permits small `p`, but its conclusion supplies
neither a reduction of `cR` digit coordinates nor a periodic interval core.
Theorem D merely records failure of balanced supersaturation. More basically,
the T156 transversals have many collision edges and are not independent.

**S3 rejection:** theorem direction and missing coordinate rigidity; the
fingerprint bound alone is not (2.7).

### 5.3 S4: polynomial uniformity loss still consumes reuse scale

`literature-checked`: S4 Theorem 1.1 assumes

```text
Delta_t <=K*(q/(10^6*s^5))^(t-1)*(e/v)
```

and returns container shrinkage `delta=(10^3*s^4*K)^(-1)`. Theorem 1.6 has
container-count exponent
`10^4*s^5*beta^(-1)*log(e/alpha)*q*log(e/q)*v`.

`proof sketch` substitution: (5.3) at `t=2` forces

```text
q >= Omega(m^6/K).                                        (5.5)
```

Since `q<1`, one needs `K=Omega(m^6)`. With `s=2m`, the theorem's set `f`
omits `delta*v` vertices, but the actual container is `g union f` and the
fingerprint may restore `q*v` of them. Hence guaranteed net shrinkage is only
`max(0,(delta-q)*v)`. In fact (5.5) and
`delta=(10^3*s^4*K)^(-1)` give `q/delta=Omega(m^10)`, so there is no positive
guaranteed net shrinkage. Even the more favorable, but insufficient, scale of
the `f`-set omission alone is

```text
delta=O(m^(-10)),       delta*v=O(N/k^10)=o(R).           (5.6)
```

Thus even the `f`-set omission is below the required `cR`, while the actual
container has no guaranteed omitted coordinate at all. Even
ignoring (5.3), `K>=1` gives only `O(N/k^4)=o(R)`. The packaged exponent has
an additional `s^5` factor and no parameter range simultaneously yields
`o(R)` fingerprints, `Omega(R)` shrinkage, and (5.5). The theorem still points
toward independent sets, not edge-rich words.

**S4 rejection:** overlap reuse enters `Delta_2` and consumes the `R` gain.

### 5.4 S5: the desired family is an assumption

`literature-checked`: S5 Definition 3.2 assumes deterministic
`(alpha,B)`-stability relative to a supplied family `B_n`. Theorem 3.4 also
assumes fixed uniformity, `(K,p)`-boundedness,
`p_n^s*|H_n| -> infinity`, and

```text
#B_n=exp(o(p_n*v(H_n))).                                  (5.7)
```

It transfers that stability to a random induced setting.

`proof sketch` substitution: choosing `p_n~1/sqrt(k)` makes the exponent in
(5.7) the desired `R`, but the theorem already assumes the low-entropy template
family. Moreover `s=2m=Theta(k)` grows, violating fixed uniformity. With
`|H|` at most exponential in `O(k)` times `N^2`,
`p_n^s|H|` has a `-Theta(k log k)` logarithmic term and tends to zero along
`N=10^(4k)`, rather than infinity.

**S5 rejection:** circular template assumption, fixed-uniformity mismatch, and
failed density scale.

## 6. Domain III: symbolic large deviations and conditioning

### 6.1 S6: growing iid blocks do not fit the event

`literature-checked`: S6 controls iid samples conditioned on empirical-measure
constraints. Corollary 2.7 treats a fixed finite-dimensional statistic and
convex constraint and allows block size `r=o(N/log N)`; Proposition 2.15
allows `r=o(N)` under stronger local-limit hypotheses. Corollary 2.11 treats a
fixed bounded positive quadratic kernel and a convex sublevel event.

`proof sketch` substitution: T156 has overlapping windows, `Theta(k)` growing
constraints, cylinder dimension `10^m`, and the superlevel condition

```text
Q_m(mu)=sum_(w in D^m)mu(w)^2 >=1/m.                      (6.1)
```

Since `Q_m` is convex, its superlevel set is generally nonconvex. None of S6's
hypotheses is uniform in this triangular regime. Even optimistically inserting
only a conditioning lower bound `exp(-C*R)` into the one-particle entropy
bound gives entropy `C/sqrt(k)` and Pinsker scale `O(k^(-1/4))`; this is diffuse
marginal information and identifies no hard coordinate.

**S6 rejection:** iid/convex/fixed-dimension mismatch and marginal-to-core gap.

### 6.2 S7: type overhead survives, but the structural gap remains

`literature-checked`: S7 Lemma 3 bounds the probability of a fixed attainable
second-order Markov type between an exponential divergence term and the same
term times `(N+1)^(-|X|^2-|X|)`. Theorems 4 and 5 give conditional limits for
fixed-order, fixed-state, irreducible constraints with a unique Markov
I-projection; the higher-order theorem uses fixed order.

`proof sketch` favorable substitution: encoding order-`k` blocks as states
gives `A=10^(k-1)`. The crude logarithmic type overhead is

```text
(A^2+A)*log(N+1)=O(10^(2k)*log N)
                    =O(N^(1/2)*log N)=o(R).               (6.2)
```

Thus template/type count is not automatically fatal at `k=(1/4)log_10 N`.
But S7 supplies no uniform divergence gap `Omega(1/sqrt(k))`, uniqueness, or
finite-`N` rate for growing state space and growing constraints. A Markov type
also permits many spatial arrangements and is not an interval-periodic core.

**S7 rejection:** the only favorable overhead (6.2) stops at empirical type;
the uniform gap and type-to-spatial-core inverse theorem are absent.

### 6.3 S8: convex stability excludes collision superlevels

`literature-checked`: S8 Theorem 2.7 proves a conditional LDP under continuous
possibly infinite constraint families. Proposition 2.10 specializes to iid
linear constraints. Remark 2.11 gives a one-particle entropy bound.
Proposition 2.19 and Corollary 2.20 give

```text
H(mu_0|mu_epsilon)<=C_stab*epsilon                         (6.3)
```

under convexity and qualification hypotheses; `C_stab` is not explicit
uniformly in a growing dimension.

`proof sketch` substitution: writing (6.1) as
`Psi_m(mu)=1/m-Q_m(mu)<=0` makes `Psi_m` concave, violating S8's convexity
assumption for (6.3). The word process is also not an iid particle empirical
measure. The general conditional LDP has no finite-`N` error or spatial-core
output. Even a hypothetical uniform version of (6.3) controls empirical laws,
not exact coordinate cylinders.

**S8 rejection:** wrong convexity, iid mismatch, and no hard spatial output.

## 7. Quantitative negative map

All entries below are `proof sketch` source translations, not claims that the
desired inverse theorem is false.

| bottleneck | exact substitution | source endpoint |
|---|---|---|
| stability error | `(4L^2+64L)*m*epsilon`; even `o(1)` needs `epsilon=o(1/(N^2 k))` | S1 gives approximate boxes only |
| no inverse | exact fractional gaps have no coordinate output | S2 |
| fingerprint without shrinkage | (5.4) can be `o(R)`, but no `cR` core follows | S3 |
| overlap reuse | `Delta_2/(e/v)=Omega(m)` forces `K=Omega(m^6)` and `q/delta=Omega(m^10)`, hence no positive net shrinkage; even `delta*v=O(N/k^10)=o(R)` | S4 |
| circular stability | `#B_n=exp(o(p_n v))` is assumed | S5 |
| conditioning error | at best marginal TV `O(k^(-1/4))` from an `exp(-CR)` denominator | S6/S8 |
| type count | `O(N^(1/2)log N)=o(R)` survives, but no uniform divergence gap or spatial core | S7 |

There is also an elementary generic-template entropy warning. Choosing `r`
arbitrary locations among `L` and their values costs

```text
log binom(L,r)+r*log 10.
```

At `r=R`, `L/r~sqrt(k)`, so this is
`Theta(R*log k)`, larger than the available `Theta(R)` saving. Therefore a
survivor must force compressible locations such as a bounded number of
intervals and compressible values such as low-period seeds. Generic coordinate
selection cannot establish (2.7).

## 8. Five exact cheap family tests

These are elementary `proof sketch` calculations. The replay performs finite
instances and labels them `experiment`.

### 8.1 Shared prefix

Put `r=ceil(N/sqrt(a))` and fix coordinates `0,...,r+k-2` to zero. For every
`m in U`, the first `r` blocks equal `0^m`, so

```text
E_x(m)>=r^2>=N^2/a>=N^2/m.                                (8.1)
```

This family lies in `B_(N,k)` and has exactly `10^(N-r)` members. One
period-one interval template has `#Q=r+k-1=Theta(R)` and `code=O(log N)=o(R)`.
It passes (rather than refutes) the target and fixes the sharp reuse scale.

### 8.2 Translated-prefix union

For every `0<=t<=N-r`, fix `[t,t+r+k-2]` to one digit `d`. The `r` starts
`t,...,t+r-1` prove (8.1). The union has at most

```text
10*(N-r+1)                                                 (8.2)
```

templates, whose logarithm is `O(log N)=o(R)`. Any theorem returning one
distinguished location rather than a low-entropy location family fails this
test; exact ITC-156 permits it.

### 8.3 Repeated de Bruijn words

Let `d=floor(log_10 a)` and `p=10^d<=a`. If `d=0`, use the one-symbol constant
cycle. If `d>=1`, repeat any decimal de Bruijn cycle of order `d` periodically
through all `L` coordinates. There are at most `p`
length-`m` block values among `N` starts, hence Cauchy--Schwarz gives

```text
E_x(m)>=N^2/p>=N^2/m.                                     (8.3)
```

The number of cycles modulo rotation is
`(10!)^(10^(d-1))/10^d` for `d>=1`. A coordinate-indexed seed also chooses one
of `p=10^d` origins, so the exact marked-seed count is
`(10!)^(10^(d-1))`. In any case it is at most
`10^p=exp(O(k))=exp(o(R))`. A period-`p` full-interval template has code
`O(log N+k)=o(R)`. The family is far more constrained than the near-saturation
scale but rejects claims that high energy implies only constant cores.

### 8.4 Periodic words

More generally, every word of period `p<=a` satisfies (8.3). The union over
all seeds and `p<=a` uses at most

```text
sum_(p=1)^a 10^p <(10/9)*10^a=exp(O(k))=exp(o(R))         (8.4)
```

full-interval templates. It rejects a unique-optimizer conclusion but not a
low-entropy mixture conclusion.

### 8.5 Multi-core mixtures

Fix `2<=h<=10`, assume `a>=4h`, and take `N` sufficiently large for the fixed
`h` that the intervals below fit. Put

```text
q=ceil(N/sqrt(a*h)).                                      (8.5)
```

Choose `h` disjoint intervals of length `q+k-1` and make interval `j`
constant with a chosen digit. If the digits are distinct, at every `m in U`
there are `q` starts for each of `h` distinct constant blocks, so

```text
E_x(m)>=h*q^2>=N^2/a>=N^2/m.                              (8.6)
```

Repeated digits only increase the relevant square. The number of location and
digit templates is at most

```text
(L+1)^(2h)*10^h=exp(O_h(log N))=exp(o(R)),                (8.7)
```

and their constrained union has
`h*(q+k-1)=Theta_h(R)` coordinates. This rejects single-core uniqueness while
remaining compatible with (2.7). If `h` were allowed to grow freely, location
entropy would have to be charged; (8.7) is intentionally the exact bounded-`h`
cheap test.

## 9. Comparator and duplication boundaries

Every row records the supplied verification level. No sketch is treated as a
discharged premise. Exact reports and the active snapshot are vendored in
`PRIOR_EVIDENCE.tar`.

| item | supplied theorem/source tuple and level | T156 boundary |
|---|---|---|
| T140, report SHA `ff05177ccaaebfd56d41467f2f74dce085aae3b855be95f6d1c458526541f35c` | Saxton--Thomason Theorem 3.4 and Balogh--Morris--Samotij Theorem 2.2 are `literature-checked`; encodings are `proof sketch` | T156 does not repeat its forward container audit. S3--S5 are new theorem tuples and are tested specifically for inverse stability and `o(R)` templates. |
| T144, report SHA `96c685692710b05035208ca459e4536f992bef2a69c030cc318625c5de00da7a` | unverified `proof sketch`; one-depth residue extraction and types | T156 derives no one-depth census and imports no T144 bound. |
| T147, report SHA `d1af43d8b2c21c6b3106a4c75e8e38467146e7c09f219adf240ee83a9250a909` | unverified `proof sketch`; all-upper-half event and shared-prefix additive obstruction | T156 uses its literal event convention but independently gives (8.1); it asks for inverse templates, not additive charging. |
| T150, report SHA `937a6a9c23ba6c319de2f7f2457d33b163f67005e0651f6c199d0453902d5907` | six source statements `literature-checked`; Gibbs substitutions `proof sketch` | T156 excludes those six sources. S6--S8 test conditional inverse stability, not T150's forward concentration census. |
| T152, report SHA `01ae77f2f125d70d31e5ae774fb2c7adb8f741b04bb9fbec6e19cdc1fc497171` | unverified `proof sketch`; maximal-depth fractional-cover census | T156 does not repeat its entropy proof or census. Its claimed `R` saving is scale motivation only. |
| T154, report SHA `46a19449de1687226eb168998b73270e0e8112be437841b37623211bf7ef289f` | unverified `proof sketch`; reuse-capacity primal/dual LP and matching prefix | T156 neither imports nor repeats the LP; it tests whether source stability can turn that scale into coordinate cores. |
| T153, report SHA `4551c4f6770c0acc7efc186d6b8133c09d2a3ece6a6b355e1f5a2f966602740d`; source-pin SHA `757543aff26ad84c12e8518f9afd25a5ac4c7a4adb116196fe86047d0768f6f3` | six source statements are `literature-checked`; locality substitutions are `proof sketch`; the refreshed artifact studies `k`-Abelian/de Bruijn-flow locality, substring reconstruction, regular sequences, fractal Fourier decay, and matrix-power sums | T156 uses none of T153's six PDF hashes or theorem tuples. It asks whether near-saturation has exact interval-core coverage, not whether logarithmic local statistics imply a maximum length-`m` atom. Repeated de Bruijn words are a shared rejection family, not a shared theorem mechanism. |
| T155, report SHA `ba916762e40e2abbf0783f3ca5d6dac89069fe8fe355279cc9df4f4c165341e2`; source-pin SHA `42458421f87fe67464cd4e9abf6fb89f07425cf73ae819dfb0b91dbb8e789930` | three source statements are `literature-checked`; comparisons/transfers are `proof sketch`; the refreshed artifact screens maximal runs and nested DRC and retains Palm--Stein only as a random-model diagnostic | T156 uses none of T155's three PDF hashes or theorem tuples. Interval-periodic templates permit runs and periodic cores but are not inferred from the Runs Theorem; T156 has no DRC, Palm coupling, or Poisson approximation step. |

The refreshed T153/T155 reports and source pins are byte-vendored in
`PRIOR_EVIDENCE.tar`. The replay checks their four artifact hashes, identifying
theorem tuples, all nine source PDF hashes, and disjointness from T156's eight
PDF hashes. Their prose deductions remain comparison evidence only: no
`proof sketch` claim is imported as a premise. The earlier active/availability
rows have been replaced rather than preserved from stale metadata.

## 10. Scoped conclusion

SCOPED_VERDICT (1/1): **close the generic inverse-stability fingerprint.**

This is a source-pinned negative map, not a disproof of ITC-156. None of the
eight inspected theorem tuples yields exact coverage (2.7): S1 loses through
dimension-dependent approximate stability; S2 has no inverse output; S3--S5
classify independent/low-edge sets or assume the templates; S4 additionally
loses the `R` scale to overlap codegrees; S6/S8 give diffuse conditional laws
under incompatible convex/iid hypotheses; and S7's favorable type overhead
does not give a uniform gap or spatial core. The five exact families show that
any future word-specific theorem must allow translations, low-period cycles,
and bounded multi-core mixtures while charging their choices.

There is no successor. Reopening this fingerprint requires a new primary
theorem whose conclusion itself supplies spatial interval cores with explicit
growing-depth errors; another generic container or conditioning scout would
repeat the closed search.

## 11. Separate fixed-pi premise

**PI-TEMPLATE-EXCLUSION-156 (`conjecture`; UNPROVED FIXED-PI PREMISE).** If a
future theorem produces explicit families `T_(N,k)` satisfying (2.7), one would
still need to prove that the length-`L` decimal prefix associated with the
fixed orbit of pi lies outside `union T_(N,k)` at the required quantifiers.
No source here supplies that arithmetic exclusion. A further proved transfer
from equal decimal blocks to the named metric near-return frontier would also
be required where appropriate.

T156 does not assert this premise, does not assert that pi avoids any surviving
template, and makes no fixed-pi, A1, C1, or C2 claim.
