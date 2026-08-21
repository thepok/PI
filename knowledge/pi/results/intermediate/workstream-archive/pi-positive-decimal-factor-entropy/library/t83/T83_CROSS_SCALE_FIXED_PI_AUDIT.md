# T83: Cross-scale fixed-pi signed-residual audit

Status: **INSUFFICIENT**.  This is a `proof sketch` with an exact finite
symbolic replay.  The imported T56, T58, and T61 interfaces are
`machine-checked`; the irrationality estimate quoted from T60 is
`literature-checked` with its existing pins; every new fixed-pi estimate below
is explicitly unproved.  No assertion of C7, C2, or C1 is made.

## 1. Provenance, normalized statement, and ambiguities

The canonical problem is locally formulated and has no original external
source URL.  Its byte-exact copy is delivered as
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It asks whether one fixed `eta>0` gives
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`.  T83 neither changes
nor resolves that question.

The phrase "averaged over the scale index" does not specify an interval or a
normalization.  We use the explicit dyadic integer block

```text
B_N={n in N : N<=n<2N},       |B_N|=N,                 (1.1)
```

and the Cesaro normalization `N^(-1)`.  Natural-number division is used in
every exponent and bandwidth.  The residual mask depends on `n`, so domains at
different scales are not assumed nested.  A result at one scale in each block
is weaker than C7's all-sufficiently-large-scale quantifier.  It can contribute
to C1 only if the separate arithmetic and long-sector estimates hold at those
same scales.

T82 is used only as motivation for which finite expansion to inspect.  No T82
claim is a premise.  Sections 3-5 rederive the expansion and collision classes
from the kernel-checked interfaces and elementary finite algebra.

## 2. Machine-checked boundary and source-pinned input

The exact imported interfaces are:

| Item | Declaration | Role | SHA-256 |
|---|---|---|---|
| T56 | `t56SampleLength`, `mem_sparse_short_sector_iff`, `sparse_Q_eq_diagonal_add_short_add_long` | `L_n`, strict short lags, and exact sector partition | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` |
| T58 | `bandwidth`, `mem_positiveFejerFrequencies_iff`, `mem_shortRectangle_iff`, `phi_collision_after_ten_reduction` | `H_n`, all finite endpoints, and ten-reduced frequencies | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` |
| T61 | `mem_residualShortRectangle_iff`, `vaalerCoefficient_explicit`, `structuredVaalerMajorantTotal_eq_completeExpression`, `strictResidualIncidenceCount_le_majorantTotal`, and the four endpoint theorems | mask, signed coefficient, exact finite expansion, majorization, and strict endpoints | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` |

These modules do not prove their fixed-pi signed premise.

T60's delivered inspection copy has SHA-256

```text
2a9aa7628b0611279e4b9d74659e744e8386da5308b196507e3fe47cd164b4ef.
```

We reuse, without reopening its literature audit, only the source-pinned
Zeilberger--Zudilin consequence recorded in T60 Section 7:

```text
mu=888/125=7.104,       lambda=mu-1=763/125=6.104,

there exists Q0>=2 such that for every positive D>=Q0 and P in Z,
  D^(-mu) < |pi-P/D|.                                  (2.1)
```

Replacing an eventual source onset by `max(Q0,2)` justifies `Q0>=2` without
changing its content.  The source prints no numerical `Q0`.  The DOI, PDF hash, and printed-page
locators are retained in `T60_SOURCE_MANIFEST.md`.  In T25's notation, (2.1)
supplies `EffectiveIrrationality Real.pi (888/125) 1 Q0`.  No other analytic
claim from the T60 proof-sketch note is treated as established.

## 3. Exact one-scale signed residual

Fix `n>=1` and put

```text
L_n=10^(floor(n/2)),       H_n=10^n/2,
R_r=10^r-1,                q_(j,r)=10^j R_r.            (3.1)
```

For fixed real `mu,c` and natural `Q0`, define the complete T61 residual label
set

```text
D_n(mu,c,Q0)={ (r,j) :
  0<r<n, r<L_n, 0<=j<L_n-r,
  not ArithmeticExcluded(mu,c,Q0,n,j,r) }.             (3.2)
```

For the pinned specialization, `mu=888/125` and `c=1`.  The mask is retained
symbolically because `Q0` is unknown.  Equality in the arithmetic comparison
is included in `ArithmeticExcluded`, while the near return itself is strict.

The complete positive frequency and signed Vaaler weight are

```text
1<=h<H_n,
Phi(h,j,r)=h*10^j*(10^r-1),                            (3.3)

a_n(h)=H_n^(-1)*[
  sin(pi*h/H_n)/pi
  +2*(1-h/H_n)*cos(pi*h/H_n)].                         (3.4)
```

T61 machine-checks that there is one `u` with `1/2<u<1` such that, throughout
the strict range (3.3), `a_n(h)` is positive, zero, or negative according as
`h/H_n` is below, equal to, or above `u`.  Thus no coefficient is replaced by
its absolute value in the exact expansion.

Write `d_n=|D_n(mu,c,Q0)|`.  T61's complete expression is exactly

```text
Z_n=2*d_n/H_n,

S_n(x)=2*sum_(1<=h<H_n) a_n(h)
          *sum_((r,j) in D_n) cos(2*pi*Phi(h,j,r)*x),

E_n(x)=Z_n+S_n(x).                                    (3.5)
```

At the prescribed seed, `x=pi`; the first `pi` in the cosine is the Fourier
angular constant and the final `pi` is the seed.  T61 proves

```text
strictResidualIncidenceCount_n <= E_n(pi),
shortResidualPairCount_n=2*strictResidualIncidenceCount_n.  (3.6)
```

It proves neither an upper bound on `E_n(pi)` nor cancellation in `S_n(pi)`.

Every endpoint is literal:

1. `n>=1`; the lag set is empty at `n=1`.
2. `0<r<n` and `r<L_n`; both upper endpoints are excluded.
3. `0<=j<L_n-r`; `j=L_n-r` is excluded.
4. `1<=h<H_n`; `h=H_n` is excluded.
5. The near-return radius is `circleDistance<1/(2H_n)=10^(-n)`.
6. At both `+/-1/(2H_n)`, the strict indicator is `0` and the T61 majorant is exactly `1`.
7. The zero Fourier coefficient is exactly `2/H_n`, giving `Z_n=2d_n/H_n`.

## 4. Complete cross-scale expansion

Fix `N>=2`.  Let

```text
I_N={alpha=(n,h,r,j):
  N<=n<2N, 1<=h<H_n, (r,j) in D_n}.                    (4.1)
```

For `alpha=(n,h,r,j)`, set

```text
m_alpha=Phi(h,j,r)>0,       w_alpha=a_n(h)/L_n.         (4.2)
```

The normalized scale average of the oscillatory residual is

```text
A_N(x)=N^(-1)*sum_(N<=n<2N) S_n(x)/L_n
      =(2/N)*sum_(alpha in I_N) w_alpha*cos(2*pi*m_alpha*x).  (4.3)
```

The pointwise product-to-sum identity gives the complete fixed-seed square

```text
A_N(pi)^2
 =(2/N^2)*sum_(alpha,beta in I_N) w_alpha*w_beta * [
    cos(2*pi*(m_alpha-m_beta)*pi)
   +cos(2*pi*(m_alpha+m_beta)*pi)].                    (4.4)
```

The pair sum is ordered.  Formula (4.4) includes every equal-frequency term,
every nonzero difference phase, and every sum phase.  No sign is discarded.

For comparison only, integrating the same finite polynomial over a variable
seed `x in [0,1)` and using elementary cosine orthogonality gives

```text
integral A_N(x)^2 dx
 =(2/N^2)*sum_(alpha,beta in I_N; m_alpha=m_beta)
       w_alpha*w_beta
 =(2/N^2)*sum_(m>=1) [sum_(alpha:m_alpha=m)w_alpha]^2. (4.5)
```

The factor `2` comes from the two outer cosine factors `4` and the integral
`1/2`.  An unordered distinct collision therefore contributes
`4*w_alpha*w_beta/N^2`.  The sum-frequency term integrates to zero because
all `m_alpha+m_beta` are positive.  Equation (4.5) is rederived finite algebra;
it does not specialize an almost-everywhere T82 statement to pi.

At the fixed seed, the exact remainder omitted by (4.5) is

```text
R_N(pi)=(2/N^2)*[
 sum_(m_alpha!=m_beta) w_alpha*w_beta
   cos(2*pi*(m_alpha-m_beta)*pi)
 +sum_(all alpha,beta) w_alpha*w_beta
   cos(2*pi*(m_alpha+m_beta)*pi)].                     (4.6)
```

Thus equal-frequency classification alone does not evaluate `A_N(pi)`.

## 5. Complete cross-scale collision classification

For a positive integer `h`, write

```text
h=10^v(h)*u(h),        10 does not divide u(h).         (5.1)
```

Since `gcd(10,10^r-1)=1`, two legal records
`alpha=(n1,h1,r1,j1)` and `beta=(n2,h2,r2,j2)` collide if and only if

```text
v(h1)+j1=v(h2)+j2,                                   (5.2)
u(h1)*(10^r1-1)=u(h2)*(10^r2-1).                     (5.3)
```

The scale indices do not enter the integer equality, but they independently
control legality, masks, bandwidths, and weights.

There is no omitted collision class.  Put

```text
g=gcd(r1,r2),       G=10^g-1,
U=(10^r1-1)/G,      V=(10^r2-1)/G.                    (5.4)
```

The Euclidean identity
`gcd(10^r1-1,10^r2-1)=10^gcd(r1,r2)-1` gives
`gcd(U,V)=1`.  Equation (5.3) holds exactly when there is a unique positive
integer `t`, not divisible by ten, such that

```text
u(h1)=V*t,             u(h2)=U*t.                     (5.5)
```

Equivalently, choose `v1,v2>=0`, `t>=1` with `10` not dividing `t`, and an
integer `s>=max(v1,v2)`, then set

```text
h1=10^v1*V*t,       j1=s-v1,
h2=10^v2*U*t,       j2=s-v2.                          (5.6)
```

These data produce one ordered collision precisely when, for each `i=1,2`,

```text
N<=n_i<2N,
0<r_i<n_i,        r_i<L_(n_i),
0<=j_i<L_(n_i)-r_i,
1<=h_i<H_(n_i),
not ArithmeticExcluded(mu,c,Q0,n_i,j_i,r_i).          (5.7)
```

This includes:

- `n1=n2` and `n1!=n2`;
- literal duplicates `(h1,r1,j1)=(h2,r2,j2)` at different scales;
- equal or unequal lags, starts, and multipliers;
- diagonal records and ordered off-diagonal records;
- weights `a_(n1)(h1)` and `a_(n2)(h2)` of either sign.

For a fixed unmasked triple `(h,r,j)`, define

```text
kappa(s)=min{k in N:s<10^k},
ell(h)=min{k in N:2h<10^k}.                            (5.8)
```

Its unmasked legal scales in the block are exactly

```text
max(N,r+1,2*kappa(r+j),ell(h)) <= n < 2N.              (5.9)
```

The residual mask may delete members of (5.9), but cannot create another
frequency collision class.

The replay exhausts all records at `n=2,3` for two deterministic masks.  In
the full rectangle it finds `8,924` records, `7,375` frequencies, `14,084`
ordered collision pairs, `1,970` oriented cross-scale pairs, and maximum fiber
size `6`.  Of the cross-scale pairs, `882` are literal duplicates and `1,088`
are nontrivial.  The independent direct-frequency, ten-reduced, ordered-matrix,
and fiber-square constructions agree exactly.  These are `experiment` data,
not proof of an asymptotic estimate.

## 6. The explicit spacing-relaxed one-row dual large-sieve test

Merge the cross-scale coefficients at each distinct positive frequency:

```text
b_N(m)=(1/N)*sum_(alpha in I_N:m_alpha=m) w_alpha,

A_N(pi)=2*Re sum_m b_N(m)*e(m*pi),
e(y)=exp(2*pi*i*y).                                    (6.1)
```

Let `F_N={m:b_N(m)!=0}` and, when `|F_N|>=2`,

```text
delta_N=min_(m!=m' in F_N)||m*pi-m'*pi||_T.            (6.2)
```

For `|F_N|<=1`, set `delta_N=1`; the following inequality is then immediate.

The one-row dual large sieve is

```text
|sum_(m in F_N)b_N(m)e(m*pi)|^2
 <= delta_N^(-1)*sum_(m in F_N)|b_N(m)|^2.             (6.3)
```

For this one-row case, Cauchy--Schwarz first gives the exact operator-norm
constant `|F_N|`.  Since `delta_N`-separated points on the circle have
cardinality at most `delta_N^(-1)`, (6.3) is the explicit spacing-relaxed
one-row dual large-sieve test.  No hidden multiplicative constant is used, but
`delta_N^(-1)` is not claimed to improve the exact constant `|F_N|`.

### 6.1 Exact use of (2.1)

For a nonzero integer `d` with `|d|>=Q0`, choose a nearest integer `P`.  Then
(2.1), with denominator `D=|d|`, gives exactly

```text
||d*pi||_T
 =|d|*|pi-P/|d||
 >|d|^(1-mu)=|d|^(-lambda).                            (6.4)
```

No reduced-fraction assumption is used.  Exact collisions have `d=0` and are
outside (6.4).

For the finitely many `1<=d<Q0`, irrationality gives the positive but
non-numerical constant

```text
delta_0=min_(1<=d<Q0)||d*pi||_T>0.                     (6.5)
```

Consequently, once the block maximum `M_N` is large enough that
`M_N^(-lambda)<delta_0`, every distinct positive-frequency pair obeys

```text
delta_N>M_N^(-lambda).                                 (6.6)
```

The onset remains unknown because `Q0` and `delta_0` are not numerical.

### 6.2 Exact full-rectangle block upper bound

For `N>=2`, the simultaneous maximum over the complete unmasked T56/T58
rectangle occurs at

```text
n_*=2N-1,                  L_*=10^(N-1),
H_*=10^(2N-1)/2,           r_*=2N-2,
j_*=L_*-r_*-1,             h_*=H_*-1,

q_*=10^(L_*-1)*(1-10^(-(2N-2))),
M_N=(H_*-1)*q_*.                                      (6.7)
```

Put

```text
epsilon_N=log10(1-2*10^(-(2N-1)))
          +log10(1-10^(-(2N-2))) < 0.                 (6.8)
```

Then exactly

```text
log10(M_N)=L_*+2N-2-log10(2)+epsilon_N.               (6.9)
```

Thus the spacing loss in (6.3) is

```text
M_N^lambda
=10^[(763/125)*(L_*+2N-2-log10(2)+epsilon_N)].        (6.10)
```

Every actual residual frequency is at most `M_N`; the maximizing label need
not survive the unknown pinned residual mask.  Thus (6.10) is an exact
full-rectangle spacing-loss upper bound, not a claim that an actual residual
frequency attains it.  Its leading base-ten exponent is
`(763/125)*10^(N-1)`, while the average has only `N` scales.

### 6.3 Coefficients, fibers, and constants

From (3.4), `pi>3`, and `|sin|,|cos|<=1`,

```text
|a_n(h)|
 <H_n^(-1)*[1/3+2*(1-h/H_n)]
 <7/(3H_n),                                             (6.11)

sum_(1<=h<H_n) H_n^(-1)*[1/3+2*(1-h/H_n)]
 =4*(H_n-1)/(3H_n)<4/3.                                (6.12)
```

Also

```text
d_n<=sum_(r=1)^(n-1)(L_n-r)<=(n-1)L_n.                (6.13)
```

Fix one frequency and one lag at scale `n`.  If it has `k` legal starts, the
corresponding multipliers differ successively by factors at least ten, so the
largest is at least `10^(k-1)`.  Since `h<H_n<10^n`, `k<=n`.  There are at
most `n-1` lags.  Hence each one-scale fiber has size at most `n(n-1)`, and an
aggregate cross-scale fiber has size at most

```text
R_N=sum_(n=N)^(2N-1)n(n-1)
   =N*(7N^2-9N+2)/3.                                  (6.14)
```

Cauchy--Schwarz inside every exact cross-scale frequency fiber, followed by
(6.11)-(6.14), gives

```text
sum_m |b_N(m)|^2
 <[49*R_N/(9N^2)]
   *sum_(n=N)^(2N-1) (n-1)(H_n-1)/(H_n^2 L_n).         (6.15)
```

Combining (6.1), (6.3), (6.6), and (6.15) yields the tested inequality

```text
|A_N(pi)|^2
 <[196/(9N^2)]*M_N^(763/125)*R_N
   *sum_(n=N)^(2N-1)(n-1)(H_n-1)/(H_n^2 L_n).          (LS_N)
```

Every constant is displayed: `4` is from `|2 Re z|^2<=4|z|^2`, `49/9` is the
squared coefficient envelope, and `R_N` is the complete cross-scale fiber
bound.

Using `H_n>=H_N`, `L_n>=L_N`, and `n-1<=2N-2`, `(LS_N)` is at most

```text
U_N=[392*R_N*(2N-2)/(9N)]
    *M_N^(763/125)*10^(-N-floor(N/2)).                 (6.16)
```

The exact base-ten exponent of this displayed output is

```text
Lambda_LS(N)
 =(763/125)*[L_*+2N-2-log10(2)+epsilon_N]
  -N-floor(N/2)
  +log10(392*R_N*(2N-2)/(9N)).                         (6.17)
```

It tends to positive infinity with dominant term
`(763/125)*10^(N-1)`.  This is the constant-preserving upper estimate obtained
from only the audited spacing, range, and fiber inputs.  Its growth does not
assert that the actual coefficient norm or `A_N(pi)` is large; it shows that
this spacing-relaxed argument alone has no useful implication.  In contrast,
(6.12)-(6.13) give the elementary bound

```text
|S_n(pi)|/L_n < (8/3)(n-1),
|A_N(pi)| < (8/(3N))*sum_(n=N)^(2N-1)(n-1).           (6.18)
```

Therefore the audited spacing-relaxed consequence of the tested large-sieve
inequality is asymptotically much worse than the elementary estimate.  From
the inputs used here it supplies no bounded normalized average and no good
scale.

The same loss already appears before harmonic averaging.  At the legal
`r=1`, `j=L_n-2` endpoint,

```text
q=9*10^(L_n-2),
Lambda_near(n)
 =(763/125)*[L_n-2+log10(9)]-n.                        (6.19)
```

The pinned estimate excludes a strict `10^(-n)` near return only when
`q^(763/125)<=10^n`; (6.19) is the exact exponent by which that comparison
fails.  This is the T60 pointwise loss, now retained inside the cross-scale
calculation rather than treated as cancellation.

## 7. Replayable finite abstract obstruction

The following obstruction isolates what scale averaging, coarse sector
budgets, signed coefficients, and equal-frequency control cannot prove by
themselves.  It is not asserted to arise from pi or from T61's structured
labels.

Given a proposed natural constant `C` and a block length `K>=2`, put

```text
n_s=C+2+s,              L_s=2*n_s,       0<=s<K,
short_s=2*(n_s-1)*(L_s-n_s),
total_s=L_s+short_s=n_s*L_s.                              (7.1)
```

Then exactly

```text
short_s<=2*L_s*n_s,
[sum_s total_s]/[sum_s L_s]>C.                           (7.2)
```

Assign globally distinct abstract nonzero frequencies.  Assign alternating
coefficient signs and matching abstract phase signs, so every coefficient--
phase product is positive.  Thus the family has no off-diagonal frequency
collisions and uses both coefficient signs, yet its normalized scale aggregate
exceeds `C`.  The replay checks `(C,K)=(1,2),(2,3),(4,4)`, obtaining exact
ratios `25/7`, `77/15`, and `23/3`.

This proves only a logical insufficiency: no implication can use solely the
retained `2L_n n` budgets, frequency injectivity, nonzero phases, and existence
of both coefficient signs.  It does not prove that pi realizes the abstract
family and does not rule out a stronger use of pi's arithmetic.

## 8. The fully quantified fixed-pi covariance still needed

Define the actual normalized fixed-pi oscillatory residual

```text
z_n=S_n(pi)/L_n.                                         (8.1)
```

For integers `N>=2` and `2<=K<=N`, pad `z_n` by zero outside `B_N` and define

```text
C_(N,K)(pi)
 =K*sum_(n=N)^(2N-1)|z_n|^2
  +2*Re sum_(s=1)^(K-1)(K-s)
       *sum_(n=N)^(2N-1-s) z_(n+s)*conj(z_n).           (8.2)
```

The sliding-window Cauchy--Schwarz inequality is exactly

```text
|sum_(n=N)^(2N-1)z_n|^2
 <=(N+K-1)/K^2 * C_(N,K)(pi).                           (8.3)
```

Every covariance in (8.2) expands as

```text
z_(n+s)*z_n
 =2/[L_(n+s)L_n]
  *sum_(1<=h'<H_(n+s),(r',j') in D_(n+s))
   sum_(1<=h <H_n,    (r,j)   in D_n)
    a_(n+s)(h')*a_n(h) * [
      cos(2*pi*(Phi(h',j',r')-Phi(h,j,r))*pi)
     +cos(2*pi*(Phi(h',j',r')+Phi(h,j,r))*pi)].          (8.4)
```

This retains every scale, sample length, bandwidth, lag, start, multiplier,
mask, signed Vaaler weight, exact collision, difference phase, sum phase,
strict endpoint, and normalization.

The next required fixed-pi statement is the explicit unproved hypothesis

```text
(Cov_pi)
there exist reals C>0 and an integer N0>=2 such that
for every integer N>=N0 there exists an integer K with 2<=K<=N and
  C_(N,K)(pi) <= C*K^2*N.                               (8.5)
```

Under `(Cov_pi)`, (8.3) gives

```text
|(1/N)*sum_(n=N)^(2N-1)z_n|
 <=sqrt(C*(2-1/N)) < sqrt(2C).                          (8.6)
```

The normalized zero mode satisfies

```text
0<=Z_n/L_n<=2(n-1)/H_n.                                 (8.7)
```

Since every T61 majorant total `E_n(pi)/L_n` is nonnegative, (8.6)-(8.7)
would give at least one `n in B_N` with

```text
E_n(pi)/L_n
 <=sqrt(C*(2-1/N))+2*(2N-2)/H_N
 <=sqrt(2C)+1                                             (8.8)
```

for all sufficiently large `N`.  By (3.6), such a scale would satisfy the
constant-preserving short bound

```text
shortResidualPairCount_n
 <=2*(sqrt(2C)+1)*L_n.                                  (8.9)
```

For calibration only, suppose additionally that the pinned effective
irrationality exclusion applies and the separate long-sector premise has the
literal uniform quantifiers

```text
there exist B>0 and N1>=1 such that for every n>=N1,
  longResidualPairCount_n<=B*L_n.                       (8.9a)
```

This applies in particular to every scale selected by (8.8); no independently
chosen long-good scale is substituted.  T56's exact partition would then give

```text
Q_pi(n,L_n)<=[3+2*sqrt(2C)+B]*L_n.                     (8.10)
```

For every fixed `eta<1/2`, (8.10) eventually implies

```text
Q_pi(n,L_n)<=L_n^2*10^(-eta*n),                         (8.11)
```

because `L_n=10^floor(n/2)`.  T2's machine-checked collision criterion would
then give `p_pi(n)>=10^(eta*n)` on one unbounded scale per dyadic block.  T1's
machine-checked convergence of entropy ratios would imply entropy at least
`eta`, and hence C1 with any fixed `0<eta'<eta`; the eventual conclusion is not
claimed with the endpoint rate `eta`.  This paragraph is a conditional implication only:
`(Cov_pi)`, the synchronized long bound, and their hypotheses are all unproved.
It does not assert C7, C2, or C1.

## 9. Verdict

**INSUFFICIENT.**  The complete cross-scale expansion is (4.4), and all exact
frequency collisions are (5.2)-(5.7).  The pinned irrationality estimate is
used only through the exact consequence (6.4).  In the audited spacing
relaxation of the one-row dual large sieve it yields the upper-bound loss
`M_N^(763/125)`, whose exact exponent is (6.17) and whose dominant term is
`(763/125)*10^(N-1)`.  Averaging over `N` scales cannot absorb that derived
loss; the resulting estimate is worse than (6.18).

The finite obstruction in Section 7 independently shows that coarse budgets,
injective frequencies, nonzero phases, and mixed signs do not force a bounded
scale average.  What remains is not another collision classification but the
fully quantified higher-order fixed-pi covariance estimate `(Cov_pi)`, with
the complete expansion (8.4).  No T82 sketch claim has been promoted, and no
unconditional C7, C2, or C1 claim is made.

## 10. Replay

From a directory containing only the delivered artifacts, run

```sh
sh ./verify.sh
```

The dependency-free replay uses exact integers and rational numbers.  It
checks the canonical and T60 hashes, all finite endpoints, direct and
ten-reduced collision partitions, the repunit-gcd parameterization, ordered
cross-scale collision categories, independent matrix and fiber-square
quadratics, coefficient-envelope constants, T60 exponent comparisons, exact
full-rectangle block upper bounds, and the finite abstract obstruction.  It does not evaluate
pi or trigonometric functions and is not evidence for a universal fixed-pi
estimate.
