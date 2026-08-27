# T135: coordinate-projection Renyi-2 tensorization audit

Audit date: 2026-08-10 UTC.

Statements attributed to S1--S5 are `literature-checked` against the delivered
primary PDFs and the locators in `SOURCE_PINS.md`. The finite identities,
separators, translations, T7 substitutions, and comparisons below are `proof
sketch` deductions unless an accepted Lean interface is explicitly cited. The
replay in `verify_t135.py` is an `experiment`: it verifies hashes, anchors, and
finite rational arithmetic, not any universal theorem.

This is a bounded related-model audit. It proves no fact about the prescribed
constant, no canonical near-return estimate, and no program conjecture.

```text
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 10
SEARCHED_DOMAIN_COUNT: 3
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, normalized scope, and ambiguities

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt` and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, the canonical count is

```text
Q_pi(n,N)=#{(i,j) in {0,...,N-1}^2:
             ||(10^i-10^j)pi||_(R/Z)<10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are retained, and the circle-distance
inequality is strict. The quantifier order is

```text
for every integer A>=1, there exists n0>=1 such that
for every integer n>=n0, there exists N>=1 with
                         A*n*Q_pi(n,N)<=N^2.
```

The cutoff `N` may depend on `A,n`. This audit does not change those
quantifiers. It studies the weaker equal-decimal-block energy interface and
related models only.

The following agenda ambiguities are fixed before any source is used.

1. Canonical depth is `n`; generic block depth is `m`.
2. An orbit-prefix block law has exactly `N` starts. A block at start `i<N`
   may read symbols through `i+m-1`, hence through `N+m-2`. The infinite tail
   is read; no start is deleted, padded, or wrapped by an artificial cutoff.
3. Decimal cylinders are `[w/10^m,(w+1)/10^m)`. Leading zeroes remain in the
   fixed-width word. For irrational points no orbit value is a cylinder
   endpoint. Rational-model cards separately exclude denominators divisible by
   2 or 5, so their nonzero orbit values are also off decimal boundaries.
4. A coordinate projection selects named positions of a word. It is not a
   residue map of the encoded block integer, a Fourier coefficient, a prefix
   truncation unless the selected set is a prefix, or a conditional law.
5. Every collision energy is ordered and diagonal-inclusive. Renyi-2 entropy
   means `-log_2` of normalized collision probability.
6. A fractional cover and a fractional partition are different: cover
   constraints are inequalities; partition constraints are equalities.
7. Shannon, Renyi, and Tsallis-Havrda-Charvat entropies are not interchanged.
8. A theorem about independent convolution factors is not silently promoted to
   a theorem about overlapping coordinates of one deterministic block.
9. `m=O(log N)` means a fixed logarithmic constant before the asymptotic
   limit. It is not a post-hoc choice depending on an observed collision row.
10. A hypothesis that already gives full collision decay, positive-density
    nested successor decrement, or a target-sized full-law approximation is
    rejected as T7, T14, or transfer burden in different notation.

## 2. Exact finite distribution and projection definitions

Let `D={0,...,9}` and let `z=z_0 z_1 ...` be an infinite word over `D`. Fix
integers `m,N>=1`, and put

```text
[m]_0={0,...,m-1},
W_i=(z_i,z_(i+1),...,z_(i+m-1)) in D^m,       0<=i<N.
```

For `w in D^m`, define the all-start occupancy and empirical block law

```text
c_[m](w)=#{0<=i<N:W_i=w},
p_[m](w)=c_[m](w)/N.
```

Now let `S={s_1<...<s_k}` be any subset of `[m]_0`, including noncontiguous
sets. Define the coordinate map and projected law by

```text
pi_S(w)=(w_(s_1),...,w_(s_k)) in D^k,
c_S(u)=sum_(w:pi_S(w)=u)c_[m](w),
p_S(u)=c_S(u)/N.
```

For `S=empty`, `D^0` is a singleton, `c_empty=N`, and `p_empty=1`. All cover
families below use nonempty `S`.

The normalized collision, Renyi-2 entropy, and integer collision energy are

```text
C_S=sum_(u in D^|S|)p_S(u)^2,
H_2(S)=-log_2 C_S,
E_S=sum_u c_S(u)^2=N^2*C_S
   =#{(i,j) in {0,...,N-1}^2:pi_S(W_i)=pi_S(W_j)}.       (2.1)
```

Thus (2.1) is ordered and includes all `N` diagonal pairs. If `X,X'` are
independent draws from `p_[m]`, then `C_S=Pr[pi_S(X)=pi_S(X')]`. Since
`{X=X'}` is contained in `{pi_S(X)=pi_S(X')}`,

```text
C_[m] <= C_S                                                  (2.2)
```

for every nonempty `S`. This elementary monotonicity is sharp: if a law is
supported on `(a,...,a)`, every nonempty projection has exactly the same
collision as the full law.

A fractional cover is a finite family `G` of nonempty subsets of `[m]_0` with
weights `a_S>=0` satisfying

```text
sum_(S in G:r in S)a_S >= 1       for every r in [m]_0.       (2.3)
```

It is a fractional partition if equality holds for every `r`. In the partition
case, double counting gives

```text
sum_(S in G)a_S*|S|=m.                                     (2.4)
```

For any nonnegative weights `lambda_S` summing to one, (2.2) gives only

```text
C_[m] <= product_S C_S^(lambda_S).                          (2.5)
```

If `a` is a fractional cover of total weight `W=sum_S a_S`, the universally
valid normalized consequence is (2.5) with `lambda_S=a_S/W`. Its exponent
normalization removes the desired tensor gain.

## 3. Literal T7 screen

The accepted machine-checked T7 module `FiniteCylinderEnergy.lean`, SHA-256
`cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c`,
defines the fixed-pi energy and proves at lines 292--318

```text
E_pi(m,N) <= Q_pi(m,N) <= 3*E_pi(m,N).                     (3.1)
```

Lines 346--386 give the exact finite-energy frontier; they do not prove decay
for pi. This audit applies the stronger requested quantitative screen

```text
E_[m] <= N^2/(6*A*m),
equivalently C_[m] <= 1/(6*A*m).                           (3.2)
```

If (3.2) held for the fixed-pi T7 energy, then (3.1) would give
`A*m*Q_pi(m,N)<=N^2/2`, leaving a factor-two safety margin. Every use below is
for an explicit finite or related model unless the separately labeled unproved
transfer premise is being discussed.

## 4. Bounded source search

The search stopped after five primary sources in exactly three domains.

| domain | opened primary sources | retained card |
|---|---|---|
| symbolic entropy and collision theory | S1 Madiman--Tetali; S2 Renyi; S3 Rastegin | C-SHEARER |
| arithmetic or fractal Fourier analysis | S4 Shmerkin | C-SHMERKIN |
| short structured exponential sums | S5 Bourgain | C-BOURGAIN |

Exact versions, URLs, DOIs, SHA-256 values, theorem/equation numbers, and PDF
page locators are in `SOURCE_PINS.md`. No source outside S1--S5 is used as a
primary theorem in a candidate card. Exactly three cards were retained.

## 5. C-SHEARER: unconditional Renyi-2 fractional covers

### 5.1 Complete sourced hypotheses

S1 Definition II (PDF p. 2) defines fractional covers, packings, and
partitions exactly as in (2.3). S1 Theorem I' (PDF p. 5) assumes arbitrary
jointly distributed random variables with finite Shannon entropies, a set
family, a fractional packing `beta`, a fractional cover `alpha`, and a
fractional partition `gamma`. Its bounds use ordering-dependent conditional
Shannon entropies. S1 Proposition II, equation (8) (PDF p. 6), gives the weak
form

```text
sum_S beta_S H(X_S|X_(S^c)) <= H(X_[m])
                            <= sum_S alpha_S H(X_S).        (5.1)
```

The constants in (5.1) are exactly the cover/packing weights. There is no
independence assumption, but the entropy is Shannon entropy and the source
derives the result from submodularity.

S2 printed p. 549, equations (1.20)--(1.21), defines order-`alpha` entropy

```text
H_alpha(P)=(1/(1-alpha))*log_2(sum_x p_x^alpha),
alpha>0, alpha!=1,                                         (5.2)
```

and records additivity for a direct product, explicitly interpreted as
independent experiments. Printed p. 553, Theorem 2 and equation (2.14), extends
the characterization. At `alpha=2`, (5.2) is `H_2=-log_2 C`. S2 states no
submodularity or fractional-cover theorem for dependent coordinates.

S3 PDF p. 2, equation (2.1), instead defines Tsallis-Havrda-Charvat entropy

```text
T_alpha(P)=(sum_x p_x^alpha-1)/(1-alpha).                  (5.3)
```

S3 Proposition 7, equation (3.19) (PDF pp. 8--9), assumes a random vector on a
finite product, a family `G` in which each coordinate occurs at least `k`
times, and `alpha>=1`, and proves

```text
k*T_alpha(X_[m]) <= sum_(S in G) T_alpha(X_S).             (5.4)
```

At `alpha=2`, `T_2=1-C`; hence (5.4) is a lower bound on `C_[m]`, often
vacuous. It is not a Renyi-2 upper-collision tensorization.

### 5.2 Exact finite separators

The hoped-for forward tensorization for a fractional partition is

```text
C_[m] <= product_S C_S^(a_S),                              (F)
```

equivalently `H_2([m])>=sum_S a_S H_2(S)`. It is false even for an exact
overlapping block law. Let `z=(0000011111)` repeated periodically, use all ten
starts, and take length-two blocks. The ordered edge multiplicities are

```text
c(00)=4, c(01)=1, c(10)=1, c(11)=4.
```

Both one-coordinate marginals are uniform, but

```text
C_{0,1}=2*(4/10)^2+2*(1/10)^2=17/50,
C_{0}=C_{1}=1/2,
17/50 > 1/4=C_0*C_1.                                     (5.5)
```

The directed edge counts are balanced and strongly connected. Thus ordinary
overlap consistency, stationarity of this periodic all-start law, and flow
balance do not repair (F).

The overlapping-pair fractional partition also fails maximally. Put mass
`1/2` on each of `000` and `111`, and assign weight `1/2` to each of
`{0,1},{0,2},{1,2}`. Every nonempty collision is `1/2`, while

```text
C_{0,1,2}=1/2 > (1/2)^(3/2)=1/(2*sqrt(2)).                (5.6)
```

The opposite direct substitution of `H_2` into Shannon's upper bound would
assert

```text
C_[m] >= product_S C_S^(a_S).                              (R)
```

It also fails. On three binary coordinates use integer counts out of four

```text
001:1, 100:1, 101:2.
```

Then

```text
C_{0,1,2}=3/8, C_{0,1}=C_{1,2}=5/8, C_{0,2}=3/8.
```

For the three-pair partition of weight `1/2`, (R) would require

```text
3/8 >= sqrt((5/8)*(5/8)*(3/8)).
```

Squaring gives `72/512>=75/512`, which is false. Hence neither product
direction is an unconditional Renyi-2 Shearer law.

### 5.3 Exact dependence defect and rejection test

For a fractional partition define

```text
K_2(P;G,a)=C_[m]/product_S C_S^(a_S).                      (5.7)
```

An independently proved bound `K_2<=K` would imply

```text
C_[m] <= K*product_S u_S^(a_S)                            (5.8)
```

from local bounds `C_S<=u_S`. If `u_S<=10^(-sigma*|S|)`, (2.4) turns the
right side into `K*10^(-sigma*m)`. The literal test is

```text
K*product_S u_S^(a_S) <= 1/(6*A*m).                       (5.9)
```

But for the uniform diagonal law on `q` symbols and the singleton partition,
`K_2=q^(m-1)`. There is no dimension-free universal defect bound. Assuming
(5.9), or assuming exactly the needed upper bound on `K_2`, merely inserts the
T7 target into the dependence premise. C-SHEARER is therefore rejected as an
unconditional mechanism. A future conditional theorem would have to derive
`K` from an independently checkable mixing or convolution hypothesis.

## 6. C-SHMERKIN: separated convolution factors

### 6.1 Complete sourced hypotheses and conclusion

S4 equations (1.3)--(1.5), journal pp. 329--330, fix `0<lambda<1`, finitely supported
probability measures `Delta(x)` with supports in one common compact interval,
and the dynamically driven independent convolution model

```text
mu_x = convolution_(i>=0) S_(lambda^i) Delta(T^i x),
mu_(x,n)=convolution_(0<=i<n) S_(lambda^i) Delta(T^i x),
mu_x=mu_(x,n) * S_(lambda^n) mu_(T^n x).                  (6.1)
```

S4 Definition 1.9, printed p. 330, calls the model pleasant when `X` is compact
metric, `T` is uniquely ergodic with invariant probability `P`, every `mu_x` is
non-atomic and lies in one bounded interval, and `x -> mu_x` is weakly
continuous outside a `P`-null set.

S4 Definition 1.10, printed pp. 330--331, requires exponential separation: for
`P`-almost every `x`, some `R>0` works for infinitely many `n`, at which all
atoms of `mu_(x,n)` are distinct and pairwise at least `lambda^(R*n)` apart.
Distinctness means that the support cardinality equals the product of local
support cardinalities.

S4 Theorem 1.11 and equation (1.6), printed p. 331, additionally assume that
`x -> Delta(x)` is `P`-almost-everywhere continuous and the number of atoms of
`Delta(x)` is uniformly bounded. For every `q in (1,infinity)`, uniformly in
`x`, it concludes

```text
lim_(s->infinity) -log_2(sum_(I in D_s)mu_x(I)^q)/((q-1)*s)
 = min{ integral log_2(||Delta(x)||_q^q)dP(x)
          /((q-1)*log_2(lambda)), 1 }.                    (6.2)
```

Here `D_s` is the half-open dyadic partition of mesh `2^(-s)` and
`||Delta||_q^q=sum_y Delta(y)^q`. The theorem gives no numerical convergence
rate or explicit first `s`.

For completeness, S4 Theorem 5.1, journal p. 359 and arXiv PDF pp. 38--39,
assumes `sigma>0`, `q>1`, differentiability of its spectrum `T` at `q`, and
`T(q)<q-1`. Put `q'=q/(q-1)`. It gives some `epsilon(sigma,q)>0` and a
sufficiently large, non-explicit `m` such that, for every `x in X` and every
`2^(-m)`-measure `nu` satisfying

```text
||nu||_(q')^(q') <= 2^(-sigma*m),
```

one has

```text
||nu*mu_x^(m)||_q^q <= 2^(-(T(q)+epsilon)*m).
```

The dependency chain and equation (5.1) are on journal p. 360 / arXiv PDF
p. 39. This is the finite-scale flattening engine, but the card uses the
cleaner global Theorem 1.11.

### 6.2 Quantitative T7 substitution

For the finite decimal-grid specialization in this card, impose the additional
hypothesis `supp(mu_x) subset [0,1)` for every `x`. This is a specialization of
the source's common-bounded-interval hypothesis, not a conclusion of S4. At
`q=2`, set

```text
d_2=min{ integral log_2(sum_y Delta(x)(y)^2)dP(x)
             /log_2(lambda), 1 }.
```

Assume the sourced model hypotheses and `d_2>0`. For each fixed
`0<eta<d_2`, uniform convergence in (6.2) gives a model-dependent
`s_0(eta)` such that

```text
sum_(I in D_s)mu_x(I)^2 <= 2^(-eta*s)
for s>=s_0(eta), uniformly in x.                           (6.3)
```

For `w in {0,...,10^m-1}`, let
`J_(m,w)=[w/10^m,(w+1)/10^m)` and set
`s=ceil(m*log_2 10)`. Each decimal interval meets at most three intervals of
`D_s`, and each interval of `D_s` meets at most two decimal intervals.
Cauchy--Schwarz therefore gives the explicit base-conversion bound

```text
C_10(m;mu_x)=sum_w mu_x(J_(m,w))^2
 <= 6*sum_(I in D_s)mu_x(I)^2
 <= 6*10^(-eta*m).                                       (6.4)
```

Take `N` independent samples from `mu_x` and let `E_m^(iid)(N)` be their
ordered, diagonal-inclusive decimal-cylinder collision count. Exact pair
enumeration gives

```text
E[E_m^(iid)(N)/N^2]
 =1/N+(1-1/N)*C_10(m;mu_x)
 <=1/N+6*10^(-eta*m).                                    (6.5)
```

Choose any fixed `kappa>0` and `N=ceil(10^(m/kappa))`. For all sufficiently
large `m`, `m<=kappa*log_10 N`, `N>=12*A*m`, `s>=s_0(eta)`, and

```text
72*A*m <= 10^(eta*m).                                     (6.6)
```

Equations (6.4)--(6.6) make the expectation at most `1/(6*A*m)`, so at least
one deterministic sample obeys

```text
E_m^(iid)(N) <= N^2/(6*A*m).                              (6.7)
```

This is an exact logarithmic-depth T7 substitution for the related iid sample
model. It retains diagonal pairs; the `1/N` term in (6.5) is not discarded.

### 6.3 Applicability boundary

S4 has genuine local-to-global Renyi-2 flattening because the local random
variables in (6.1) are independent convolution factors and exponential
separation excludes coincidences and gives `lambda^(R*n)` spacing along the
infinitely many scales in Definition 1.10, for `P`-almost every state. Coordinate projections
of one overlapping deterministic word are neither independent factors nor
convolutions. No inspected source constructs (6.1), proves exponential
separation, or supplies an empirical-prefix coupling for the decimal orbit of
pi.

Thus C-SHMERKIN survives only as a sharply scoped related-model mechanism. Its
separation premise is structurally independent of T7, but the absent coding and
transfer are load-bearing. It is not a fixed-pi candidate theorem.

## 7. C-BOURGAIN: incomplete geometric-progression sums

### 7.1 Complete sourced theorem

S5 printed p. 828, Section 2.2, Theorem 2.1 and equation (20), fixes a prime
`p`, an element `theta in F_p^*` of multiplicative order `t`, and a prefix
length `N` satisfying

```text
t>=N>p^delta,       delta>0 fixed.                         (7.1)
```

It asserts the existence of `eta_delta=delta'(delta)>0` such that, uniformly
for `a in F_p^*`,

```text
|sum_(j=1)^N exp(2*pi*i*a*theta^j/p)|
 < N*p^(-eta_delta).                                      (7.2)
```

The source supplies neither a numerical formula for `eta_delta` nor a
computable first modulus. The multiplicative constant in (7.2) is exactly one.
Nonvacuously `delta<1` along an
unbounded prime family because `t<=p-1`.

### 7.2 Rational decimal model and T7 substitution

Specialize to `theta=10 mod p`, with `p` prime and `p` not 2 or 5, and let
`alpha=a/p`, `a!=0 mod p`. Assume (7.1) with
`N<=ord_p(10)`. For `0<=j<N`, put

```text
x_j={10^j*alpha},
W_j=(the m decimal digits of alpha beginning at j+1).
```

The block is read from the infinite periodic expansion. There are exactly `N`
starts and no endpoint deletion. Since `p` is coprime to 10 and the orbit is
nonzero, no `x_j` lies on a decimal-cylinder boundary.

Let `D_N^*` be normalized star discrepancy. The elementary one-dimensional
Erdos--Turan inequality has an absolute constant `K_ET` such that, for
`1<=H<=p-1`, (7.2) gives

```text
D_N^* <= K_ET*(1/(H+1)
                 +p^(-eta_delta)*(1+log H)).               (7.3)
```

This report uses (7.3) only as an explicitly displayed proof-sketch deduction;
it is not attributed to S5. Set

```text
beta=min(eta_delta/2,1/2), H=floor(p^beta).
```

For all sufficiently large `p`,

```text
D_N^* <= K_ET*(p^(-beta)
                 +p^(-eta_delta)*(1+beta*log p)).          (7.4)
```

For depth-`m` decimal occupancies, write
`Delta_w=c_w-N/10^m`. Interval discrepancy gives
`max_w|Delta_w|<=2*N*D_N^*`; because the two count vectors have total mass
`N`, `sum_w|Delta_w|<=2*N`. Hence

```text
E_m/N^2
 =10^(-m)+sum_w Delta_w^2/N^2
 <=10^(-m)+4*D_N^*
 <=10^(-m)+4*K_ET*(p^(-beta)
       +p^(-eta_delta)*(1+beta*log p)).                    (7.5)
```

The literal T7 screen is therefore the explicit inequality

```text
6*A*m*[10^(-m)+4*K_ET*(p^(-beta)
 +p^(-eta_delta)*(1+beta*log p))] <= 1.                    (7.6)
```

Conditional on any separately supplied unbounded sequence of primes for which
`ord_p(10)>p^delta`, choose `p` along that sequence and an admissible `N`.
For fixed `kappa>0` and `m=floor(kappa*log_10 p)`, every term in (7.6) tends
to zero. Moreover `N>p^delta` implies

```text
m < (kappa/(delta*log 10))*log N,                          (7.7)
```

so this is logarithmic depth. It is asymptotically exact in all named source
constants, but no numerical first `p` can be extracted from S5.

### 7.3 Projection and duplication failure

A full length-`m` word is one interval, which is why (7.5) is cheap. A
projection to `k` named coordinates is generally a union of up to
`10^(m-k)` depth-`m` intervals. Applying discrepancy separately pays that
component count. C-BOURGAIN therefore estimates the full law directly; it
does not infer it from coordinate-projection collisions.

S5 does not prove that such an unbounded prime sequence exists for `theta=10`;
without it the asymptotic specialization may be vacuous. Conditional on that
extra arithmetic supply, the candidate passes (3.2) for admissible rational modular orbits but fails the
normalized T135 fingerprint. Its collision conversion is T121's global
discrepancy/variance route with new arithmetic input. It also concerns `a/p`,
not pi. C-BOURGAIN is rejected as a new local-to-global mechanism.

## 8. Named prior and active fingerprint comparison

Verification levels are load-bearing. The byte-exact comparator files and the
binding orchestrator input are delivered inside `prior_evidence.tar.gz`, whose
member hashes and locators are listed in `PRIOR_INDEX.md`. Accepted literature artifacts below have
source statements labeled `literature-checked`, but their prose deductions
remain `proof sketch` unless a Lean theorem is explicitly named. No comparison
claim is used as a premise in Sections 5--7.

| item and inspectable pin | normalized fingerprint | T135 boundary |
|---|---|---|
| T14, accepted Lean module `CoherentSuccessorSplitting.lean`, SHA `bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833` | Lines 503--572 machine-check that positive-density, collision-mass-weighted one-step successor splitting gives polynomial energy decay; lines 574--590 identify coherent splitting exactly with the open C2 condition, without asserting either for pi. | If T135 uses nested prefixes and assumes a fixed contraction on positive-density levels, it has renamed T14. Arbitrary coordinate marginals do not provide T14's parent-conditioned splitting; separator (5.5) has uniform marginals but strong successor dependence. |
| rejected T119 recovered report, SHA `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a`; source package absent here, so unverified comparison memory | It asks whether collision concentration forces predictive, ordinary Hankel, or Prony rank and records separators at lines 682--701. | T135 asks the opposite-direction question, projected collision to full collision. The shared warning is that one L2 statistic does not determine hidden dependence. Any rank premise must be independently proved; it cannot be inferred from projection collisions. |
| T121 accepted literature report, SHA `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2`; deductions proof sketch | Lines 142--158 expand full binary collision as the global average of squares of all Walsh subset correlations. Lines 187--276 apply complete character bounds to a related Legendre model. | A projection collision contains Walsh coefficients supported inside that projection. Controlling projections by expanding until all subset correlations are covered repackages T121, not tensorization. C-BOURGAIN also duplicates T121's direct global-discrepancy-to-variance conversion. |
| active T132 | The binding snapshot names modular or CRT projections and has an active generation-2 lease. Its earlier result was marked for citation repair, but no T132 report or source package is present in this knowledge snapshot. | Coordinate deletion is not a residue/CRT map of an encoded word. No theorem-level duplication claim is made without a readable revised artifact. C-BOURGAIN is modular, so it is conservatively excluded from novelty even though its map is global discrepancy rather than a CRT projection theorem. |
| active T134 | The binding snapshot supplies only the phrase zero-cylinder occupancy and an active generation-1 lease; no report, hypotheses, or result are readable. | One exceptional atom can dominate `C_[m]`, so a future tensorization theorem may need a zero-cylinder clause. No stronger comparison is inferred. T135 does not assume or prove zero-cylinder sparsity. |
| T130 accepted literature report, SHA `c130b2c8790dce80080367201e56efb3847f8262189af57f2ce756aacb6a893c`; deductions proof sketch | Exact equal blocks are converted to S-unit equations; available common multiplicative rank grows as `N+O(m)`, and support bounds do not control squared occupancy. Its separately unproved transfer is at lines 618--682. | T135 uses finite-law coordinate dependence, not multiplicative-group rank. It would duplicate T130 only by encoding projections into the same common S-unit group. Neither C-SHEARER nor C-SHMERKIN repairs T130's rank or zero-block obstruction. |
| T131 accepted literature report, SHA `ed2229ceedcff357f80121fbdc31ffbb8e3582717f487a3a85368eabe64790db`; deductions proof sketch | Balanced circulation, Euler ordering, and nested de Bruijn constructions produce or assume global incidence balance; lines 430--469 explain the collapse to T121/global L2 or offline incidence balancing. | Projection is an easy global-to-local coarsening. T135 seeks the false converse. Separator (5.5) is itself a balanced strongly connected circulation, so local flow balance does not repair the converse. Assuming balanced full incidence would duplicate T131. |
| T133 accepted literature report, SHA `53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40`; deductions proof sketch | A finite valuation transducer and exact reduced rational orbit still yield only `N asymp_A log q`; see lines 370--416. Its unproved fixed-pi continuation is rejected at lines 445--467. | Finite-state coordinate computation does not imply Renyi-2 independence. T135 uses neither the H1 coefficients nor the valuation transducer, and makes no continuation claim. |

These comparisons isolate the only nonduplicate shape found here: local
independent convolution factors plus an independently proved separation
theorem can yield global Renyi-2 decay. Unconditional coordinate projections,
balanced overlap flow, complete all-subset Fourier control, S-unit rank, modular
projection, and finite valuation state are distinct fingerprints or recorded
failures.

## 9. Circularity screens

The following premises are expressly rejected.

1. `C_[m]<=1/(6*A*m)` or an equivalent upper bound on `K_2` in (5.7) is T7
   decay in different notation.
2. A fixed one-step contraction on nested prefixes at a positive density of
   levels is T14 successor splitting/decrement in different notation.
3. Exact or target-sized full-word incidence balance is T121/T131 global L2,
   not a consequence of local projections.
4. A shrinking-scale `L2` approximation of the pi empirical block law with
   error `o(m^(-1/2))` already carries the decisive transfer burden.
5. Calling coordinate maps independent, convolutional, Markov, mixing, or
   separated without proving the corresponding finite constants does not
   discharge dependence.

## 10. Separately labeled unproved pi-transfer premise

**PI-PROJECTION-TRANSFER-T135 (`conjecture`; UNPROVED PI-TRANSFER PREMISE;
not asserted).** There exist a fixed `kappa>0`, one fixed Section 6.2
specialized pleasant exponentially separated S4 model with `d_2>0` and
`supp(mu_y) subset [0,1)` for every state `y`, one state `x`, and positive
integers `N_m` for every sufficiently large `m`, with

```text
m=floor(kappa*log_10 N_m),
sqrt(m)*||p_(pi,m,N_m)-q_(x,m)||_2 -> 0.                  (10.1)
```

Here `p_(pi,m,N_m)` is the exact all-start length-`m` decimal block law of pi
with the endpoint convention in Section 2, and

```text
q_(x,m)(w)=mu_x([w/10^m,(w+1)/10^m)).                    (10.2)
```

Equations (6.3)--(6.4) would make `sqrt(m)||q_(x,m)||_2` tend to zero, and the
triangle inequality together with (10.1) would do the same for the empirical
law. This conditional observation is a `proof sketch`, not a conclusion.

No inspected source constructs such a model for pi or proves (10.1). In fact,
the shrinking-scale `L2` clause has essentially the target collision burden,
so it is rejected as a new mechanism rather than counted as a survivor. The
premise is displayed only to prevent an unstated transfer. Nothing in this
section asserts a fixed-pi estimate, C1, or C2.

## 11. Replay and scoped endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t135.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and five PDF hashes, page-scoped source
anchors, prior-archive member hashes and cited comparator anchors, exact finite
projection separators, and ordered diagonal-inclusive collision identities. It
also checks the report's structured count, scope, transfer, comparator, and
endpoint markers. Those marker checks are transcription checks, not semantic
proofs; direct inspection of the definitions, substitutions, comparisons, and
claim firewall remains necessary.

SCOPED_VERDICT: HOLD AS MODEL

The verdict retains only S4's separated independent-convolution mechanism as a
mathematically adjacent model of local-to-global Renyi-2 flattening. It does not
retain unconditional coordinate-projection tensorization, C-BOURGAIN's direct
global discrepancy conversion, or any transfer to the prescribed decimal
orbit. No bounded successor is selected. This report makes no fixed-pi, C1, or
C2 conclusion.
