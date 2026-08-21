# T50: centered dyadic square variation for the variable-phase six-row process

Status: `proof sketch`.  The T36 definitions and the T36 results explicitly
identified below are machine-checked.  The finite regrouping, Fourier analysis,
and probability argument in this note are self-contained prose proofs; they
have not been formalized in Lean.

## 1. Scope, provenance, and verdict

The canonical local statement is included byte-for-byte as
`CANONICAL_STATEMENT.txt`.  It has no external source URL.  Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That statement asks about ordered long-lag decimal collisions at `pi`.  This
note does not estimate those collisions.  It treats only the sibling obtained
by replacing `Real.pi` in the shell tests of T36's exact six-row
`ARI_super(36/5)` remainder by a Lebesgue-random phase `alpha` in `[0,1)`.

The sole discharged mathematical input is the kernel-checked module

```text
TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving
SHA-256 3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24
```

In particular, the exact row and shell definitions imported by T36, T36's
`canonical_blockLength_weight_budget`, and T36's quantifier audit
`ARI_super_iff_quantifiers` are machine-checked.  The T40, T41, and T44 notes
and the rejected T46 attempt are motivation only.  No claim from any of them
is used as a premise.

### Verdict

Fix arbitrary `Q0,Qstar : Nat`.  For every integer `ell>=2`, put

```text
s_ell = 1-1/ell,                 x_ell = 10^(-1/ell).
```

For T36's exact variable-phase six-row incidence `X(m,N;alpha)`, this note
proves the centered square-variation estimate

```text
sum_(r>=0) (r+1)^2 sum_(j>=0)
  ||U_m((j+1)2^r)-U_m(j2^r)||_2^2
    <= 40960 m^2 10^(-(1-s)m),                              (SV)
```

where `s` is any real in `(0,1)` and

```text
U_m(N) = [X(m,N)-E X(m,N)]/[N+N^2 10^(-s m)],  U_m(0)=0.
```

Every increment in `(SV)` is the difference of the two complete centered,
normalized processes.  It includes every change in the nonnested canonical
blocks, widths, hidden range, outer range, and six-row multiplicity.  It is not
an uncentered telescope and not an endpoint comparison.

Estimate `(SV)` implies T40's maximal-tail condition with an explicit constant
independent of its finite cutoff.  It then gives one full-measure set on which
the variable-phase sibling holds for every real `0<s<1`.  There is no terminal
conjecture or replacement inequality.

No statement in this note is specialized to `pi`.  No conclusion is stated
for C3, C2, C1, or the canonical collision count.

## 2. Exact finite T36 process

Fix `Q0,Qstar : Nat`.  Throughout Sections 2-10, `m,N` are natural numbers
with

```text
1 <= m,  1 <= N.                                           (2.1)
```

All sums below are finite unless an infinite range is displayed explicitly.

### 2.1 Records and arithmetic survival

A record is `(epsilon,(r,n))`, where `epsilon` is Boolean, `r` is its lag,
and `n` is its start.  Its frequency endpoint is `n+r`.  For an orientation,
start, and proposed endpoint, T34 defines

```text
record(epsilon,n,E) = (epsilon,(E-n,n)),                    (2.2)
```

where subtraction is natural subtraction.  A malformed endpoint order gives
lag zero and is rejected below; it is not repaired.

For natural `n,r`, put

```text
q(n,r) = 10^n(10^r-1).                                    (2.3)
```

At T36's literal parameters `(mu,c)=(8,1)`, the full arithmetic exclusion is

```text
Excluded(Q0,m;n,r) iff
  Q0 <= q(n,r) and 10^(-m) <= q(n,r) [1/q(n,r)^8],          (2.4)
```

where the second comparison is over the reals.  Thus its right side is
`q(n,r)^(-7)` whenever `q(n,r)>0`.

For a half-open dyadic block `B=[a,b)`, exact membership in T32's record
domain is

```text
(epsilon,(r,n)) in Q_B iff
  0 < r,
  m <= r,
  not Excluded(Q0,m;n,r),
  a <= n+r < b.                                             (2.5)
```

In the range `m<=r`, the exclusion in (2.5) is automatically false.  Here is
the complete elementary check.  Since `m>=1` and `r>=m`,

```text
q(n,r) >= 10^r-1 >= 10^m-1 >= 9^m.
```

The last inequality follows by induction from
`10^(t+1)-1 >= 9(10^t-1)` for `t>=1`, with equality at `t=1`.  Since
`9^7>10`,

```text
q(n,r)^7 >= 9^(7m) > 10^m,
q(n,r)^(-7) < 10^(-m).                                    (2.6)
```

Therefore the second conjunct in (2.4) is false, independently of `Q0`.
This observation is used only to evaluate the exact row cardinalities; no
arithmetic-survival condition is silently discarded.

### 2.2 Outer domain and source-exponent filter

T34's exact outer domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.               (2.7)
```

Put

```text
k = v+rho,
d(v,rho) = 10^v(10^rho-1) = 10^k-10^v.                    (2.8)
```

The map `(v,rho) -> (v,k)` is a bijection from (2.7) to

```text
0 <= v < k < N,                                            (2.9)
```

with inverse `rho=k-v`.  The separate condition `rho<N` follows from
`0<rho<=k<N`.  In particular, `d(v,rho)` is a positive integer.  T36's exact
supercritical filter is

```text
P_m(v,k) iff Qstar <= 10^k-10^v and 5m < 31k.              (2.10)
```

The height inequality is strict.

### 2.3 Canonical blocks and literal widths

A dyadic block `B=(a,j)` represents

```text
B.start = a,  B.finish = a+2^j.                            (2.11)
```

The exact canonical list is

```text
B_N = translatedCanonicalBlocks(N)
    = dyadicPartitionFrom(0,(N-1).bitIndices.reverse).      (2.12)
```

It is a nonduplicated consecutive partition of the integer endpoints
`[1,N)`.  Every block is half-open.  Its literal width is

```text
w_B = sqrt(B.finish^2-B.start^2).                           (2.13)
```

Every canonical width is positive.  T36's kernel-checked block budget is

```text
sum_(B in B_N) blockLength(B)/w_B < 3.                     (2.14)
```

For each `1<=k<N`, there is one unique canonical block containing `k`.
Write it as

```text
B_N(k)=[a_N(k),b_N(k)),
W_N(k)=sqrt(b_N(k)^2-a_N(k)^2).                            (2.15)
```

Then

```text
1 <= a_N(k) <= k < b_N(k) <= N.                           (2.16)
```

### 2.4 All six rows and the hidden range

For every hidden exponent `z` in the literal range `0<=z<N`, T34's six
ordered record pairs are

```text
row 1, positiveSameEndpoint:
  (record(true,k,z),  record(true,v,z));

row 2, positiveSameStart:
  (record(true,z,v),  record(true,z,k));

row 3, negativeSameEndpoint:
  (record(false,v,z), record(false,k,z));

row 4, negativeSameStart:
  (record(false,z,k), record(false,z,v));

row 5, mixedFirstEndpoint:
  (record(false,z,k), record(true,v,z));

row 6, mixedSecondEndpoint:
  (record(false,v,z), record(true,z,k)).                    (2.17)
```

For each named row, `cancellingRowDomain(8,1,Q0,m,B,...)` is the singleton
containing the displayed pair, filtered by `rho>0` and membership of both
records in (2.5).  Its cardinality is zero or one.  There is no implicit
reversal factor.

Define the exact hidden-exponent multiplicity

```text
M_(m,N,B)(v,k)
  = sum_(0<=z<N) sum_(r in all six rows)
      card(cancellingRowDomain(8,1,Q0,m,B,r,v,k-v,z)).      (2.18)
```

### 2.5 Exact coefficient and variable-phase incidence

Extend the following coefficient by zero unless (2.9) and (2.10) hold:

```text
a_(m,N)(v,k)
  = sum_(B in B_N) M_(m,N,B)(v,k)/w_B.                     (2.19)
```

For the moment, let `theta_m` denote the exact shell function reconstructed in
Section 3.  The exact variable-phase process is

```text
X(m,N;alpha)
  = sum_(0<=v<k<N; P_m(v,k))
      a_(m,N)(v,k) theta_m((10^k-10^v)alpha).              (2.20)
```

Formula (2.20) follows directly from T36's
`restrictedWeightedShellIncidence_eq_direct`, after replacing only the shell
argument `(d:Real)*Real.pi` by `(d:Real)*alpha`.  Every coefficient remains
the literal six-row, all-block, all-`z`, width-normalized coefficient.

## 3. Exact endpoint-pinned shell function

Put

```text
H=10^m,  K=K_m=clog_2(H)-1,  delta(x)=|x-round(x)|.         (3.1)
```

For `m>=1`, T36's shell audit gives

```text
1 <= K,  2^K < H <= 2^(K+1).                              (3.2)
```

The exact shells are

```text
S_0(m,x): 0 <= delta(x) <= 1/H,

S_j(m,x): 2^(j-1)/H < delta(x)
              <= min(2^j/H,1/2),  1<=j<=K.                (3.3)
```

Shell zero is closed at both ends.  Every positive shell is open below and
closed above, including the terminal cap.  The literal shell weight is

```text
theta_m(x)
  = 1_(S_0(m,x)) + sum_(j=1)^K 2^(-j) 1_(S_j(m,x)).       (3.4)
```

An exact pointwise form convenient for Fourier analysis is

```text
theta_m(x)
  = 2^(-K)
      + sum_(j=0)^(K-1) 2^(-j-1)
          1_{delta(x)<=2^j/H}.                             (3.5)
```

To check the endpoints, suppose
`2^(l-1)/H < delta(x) <= 2^l/H`.  In (3.5), precisely the indicators with
`j>=l` are active, and

```text
2^(-K)+sum_(j=l)^(K-1)2^(-j-1)=2^(-l).
```

At `delta(x)=2^l/H`, the `j=l` indicator remains active, matching the closed
upper endpoint in (3.3).  Thus (3.5) is pointwise exact, not an almost-
everywhere modification.

## 4. Exact moments and Fourier coefficients

Let `Omega=[0,1)` with restricted Lebesgue measure, which has total mass one.
Multiplication modulo one by any positive integer preserves this measure.

### 4.1 First and second shell moments

For every positive integer `d`, (3.5) gives

```text
integral_Omega theta_m(d alpha) d alpha = kappa_m,
kappa_m = K/H + 2^(-K).                                   (4.1)
```

Indeed, `{delta(x)<=2^j/H}` has measure `2^(j+1)/H`, so each
summand in (3.5) contributes exactly `1/H`.

The exact second moment is

```text
integral_Omega theta_m(d alpha)^2 d alpha
  = 3(1-2^(-K))/H + 4^(-K).                               (4.2)
```

For verification, shell zero contributes `2/H`.  The shells
`1<=j<K` contribute

```text
sum_(j=1)^(K-1) 4^(-j) [2^j/H]
  = (1-2^(-(K-1)))/H.
```

The terminal shell has measure `1-2^K/H` and contributes
`4^(-K)-2^(-K)/H`.  Their sum is (4.2).

Define the genuinely centered shell

```text
f_m(x)=theta_m(x)-kappa_m.                                 (4.3)
```

Its variance is exactly

```text
nu_m = ||f_m||_2^2
  = 3(1-2^(-K))/H + 4^(-K) - (K/H+2^(-K))^2
  < 4/H.                                                   (4.4)
```

For the last inequality, (3.2) gives `2^K>=H/2`, hence
`4^(-K)<=4/H^2<=1/H` because `H>=10`.  Discarding the nonnegative squared
mean in (4.4) now gives `nu_m<3/H+1/H=4/H`.

Also, from `10^m<=16^m=2^(4m)` and the least-exponent definition of `clog`,

```text
0 <= kappa_m <= (K+2)/H <= 5m/H.                          (4.5)
```

### 4.2 Fourier coefficients

Use the convention

```text
fhat_m(n)=integral_0^1 f_m(x) exp(-2 pi i n x) dx.
```

Then `fhat_m(0)=0`.  Since the Fourier coefficient of
`1_{delta(x)<=a}` at nonzero integer `n` is
`sin(2 pi n a)/(pi n)`, (3.5) gives the exact real, even coefficient

```text
c_m(n):=fhat_m(n)
 = [1/(pi n)] sum_(j=0)^(K-1) 2^(-j-1)
      sin(2 pi n 2^j/H),       n != 0.                    (4.6)
```

In particular,

```text
|c_m(n)| <= 1/(pi |n|).                                   (4.7)
```

The geometric sum of the coefficients in (4.6) is `<1`.

## 5. Exact covariance and the decimal gcd kernel

### 5.1 Covariance identities

Let `d,e` be positive integers and `g=gcd(d,e)`.  Expanding both centered
Fourier series and imposing the zero-frequency condition gives

```text
Cov_m(d,e)
 := integral_0^1 f_m(d alpha)f_m(e alpha) d alpha
  = 2 sum_(t>=1) c_m(te/g)c_m(td/g).                       (5.1)
```

This is an exact identity.  The two signs are the solutions
`(n_1,n_2)=(te/g,-td/g)` and their negatives.  Absolute convergence follows
from (4.7).

Equivalently, for any finitely supported real coefficients `beta_p` at
positive integer frequencies `d_p`, Parseval and finite regrouping give

```text
||sum_p beta_p f_m(d_p alpha)||_2^2
 = 2 sum_(h>=1)
      [sum_(p: d_p divides h) beta_p c_m(h/d_p)]^2.         (5.2)
```

Formula (5.2) is the complete covariance sum.  It makes no independence or
orthogonality assertion.

From (4.7),

```text
|Cov_m(d,e)|
 <= 2 sum_(t>=1) [g/(pi t e)][g/(pi t d)]
  = g^2/(3de).                                             (5.3)
```

Cauchy-Schwarz and (4.4) also give

```text
|Cov_m(d,e)| < 4/H.                                       (5.4)
```

Consequently

```text
|Cov_m(d,e)|
 <= min(4/H, gcd(d,e)^2/(3de)).                            (5.5)
```

### 5.2 Exact gcd of two cancelling values

Index a cancelling value by `p=(v,rho)`:

```text
d_p=10^v(10^rho-1),  v>=0, rho>=1.                         (5.6)
```

For `p'=(v',rho')`, the factors `10^rho-1` and `10^rho'-1` are coprime to
ten.  The standard Euclidean-algorithm identity

```text
gcd(10^rho-1,10^rho'-1)=10^gcd(rho,rho')-1
```

therefore yields the exact formula

```text
gcd(d_p,d_p')
 = 10^min(v,v') [10^gcd(rho,rho')-1].                     (5.7)
```

As `10^q-1 >= (9/10)10^q` for every positive `q`, and

```text
rho+rho'-2gcd(rho,rho') >= |rho-rho'|,
```

(5.7) implies

```text
gcd(d_p,d_p')^2/(d_p d_p')
 <= (100/81) 10^(-|v-v'|-|rho-rho'|).                     (5.8)
```

Combining (5.5) and (5.8),

```text
|Cov_m(d_p,d_p')|
 <= min(4/H,
        (100/243)10^(-|v-v'|-|rho-rho'|)).                 (5.9)
```

### 5.3 Explicit covariance row sum

For fixed `p`, at most four indices `p'` have prescribed distances

```text
|v-v'|=u,  |rho-rho'|=w.
```

This overcounts boundary cases and `(u,w)=(0,0)`, which is harmless.  Put
`t=u+w`.  There are `t+1` nonnegative pairs `(u,w)` with this sum.  For
`0<=t<m`, use `4/H` in (5.9); for `t>=m`, use the geometric term.  Thus

```text
sup_p sum_p' |Cov_m(d_p,d_p')|
 <= 4 sum_(t=0)^(m-1) (t+1) 4/H
    +4 sum_(t=m)^infinity (t+1)(100/243)10^(-t).           (5.10)
```

The first term is `8m(m+1)/H`.  For `m>=1`, the second is at most

```text
(400/243)10^(-m)
  [(m+1)/(1-1/10)+(1/10)/(1-1/10)^2]
 < 4(m+1)/H.                                               (5.11)
```

For `m=1`, the right side of (5.10) is less than `2=20m^2/H`; for `m>=2`,
`8m(m+1)+4(m+1) <= 20m^2`.  Hence in every positive range

```text
sup_p sum_p' |Cov_m(d_p,d_p')| <= 20m^2/H.                (5.12)
```

The symmetric Schur bound applied to the covariance matrix now proves, for
every finitely supported real family `beta_p`,

```text
||sum_p beta_p f_m(d_p alpha)||_2^2
  <= (20m^2/10^m) sum_p beta_p^2.                          (COV)
```

This is the analytic input to the square variation.  It explicitly includes
all nonzero covariances.

## 6. Exact six-row coefficient formula

This section reconstructs the coefficient (2.19), including all six rows.
For an integer `x`, write `[x]_+=max(x,0)`; every subtraction inside this
notation is signed integer subtraction.

Fix `0<=v<k<N`.  By (2.6), only lag and block-endpoint conditions remain in
the row domains.  Define the common exact filter

```text
chi_(m,N)(v,k)
 = 1 if Qstar<=10^k-10^v and 5m<31k, and 0 otherwise.      (6.0)
```

All row coefficients below include this factor.  Thus they are zero when the
onset or strict supercritical filter fails, exactly as in (2.19).

### 6.1 Rows 1 and 3

Rows 1 and 3 have common endpoint `z` and starts `k,v`.  Both lags are at
least `m` exactly when `z>=k+m`.  For `B=[a,b)`, define

```text
H_end(B;k) = [b-max(a,k+m)]_+.                             (6.1)
```

The upper condition `z<N` is automatic from `z<b<=N`.  The two orientations
have identical membership, so their exact combined coefficient is

```text
e_(m,N)(v,k)
 = 2 chi_(m,N)(v,k)
     sum_(B in B_N) H_end(B;k)/w_B.                        (6.2)
```

### 6.2 Rows 2 and 4

Rows 2 and 4 have common start `z` and endpoints `v,k`.  Both endpoints must
lie in the same canonical block, which by uniqueness is `B_N(k)=[a,b)`.
This occurs exactly when `a<=v<b`.  Since `v<k`, the two lag conditions reduce
to `z+m<=v`.  The exact number of hidden exponents is

```text
H_ss(m;v)=[v-m+1]_+.                                      (6.3)
```

### 6.3 Rows 5 and 6

Rows 5 and 6 have endpoints `z,k`.  Their lag conditions are
`v+m<=z` and `z+m<=k`.  Both endpoints lie in `B_N(k)=[a,b)` exactly when
`a<=z<b`.  Their exact common hidden-exponent count is

```text
H_mix(m,N;v,k)
 = [min(b,k-m+1)-max(a,v+m)]_+.                            (6.4)
```

Again `z<N` is automatic from `z<b<=N`.

### 6.4 Complete coefficient

The other four rows therefore contribute

```text
h_(m,N)(v,k)
 = [2 chi_(m,N)(v,k)/W_N(k)]
     [1_{a_N(k)<=v<b_N(k)} H_ss(m;v)
       + H_mix(m,N;v,k)].                                  (6.5)
```

Combining (6.2) and (6.5) gives the exact identity

```text
a_(m,N)(v,k)=e_(m,N)(v,k)+h_(m,N)(v,k).                    (6.6)
```

No row or orientation factor is omitted.

## 7. Phase-independent mass and coefficient-square bounds

### 7.1 First-power mass

For fixed `(v,k)`, (6.1) is at most the block length.  By (2.14),

```text
0 <= e_(m,N)(v,k) < 6.                                    (7.1)
```

There are `N(N-1)/2` pairs `0<=v<k<N`, so

```text
sum_(v,k) e_(m,N)(v,k) <= 3N(N-1).                         (7.2)
```

For the four other rows, decreasing `m` to one only enlarges both hidden
intervals.  For `B_N(k)=[a,b)` and `k=a+d`, `0<=d<b-a`, define

```text
Lambda_1(v,k;a,b)
 = 1_{a<=v<b} v + [k-max(a,v+1)]_+.
```

Directly,

```text
Lambda_1(v,k;a,b) = d,     0<=v<a,
Lambda_1(v,k;a,b) = k-1,   a<=v<k.                         (7.3)
```

Summing (7.3) over `v<k`, comparing with the literal width as in (7.6) below,
and then summing over `k` gives

```text
sum_(v,k) h_(m,N)(v,k) <= N(N-1).                          (7.4)
```

For completeness, the fixed-`k` numerator is
`ad+d(k-1)=d(a+k-1)`.  Since `d<L=b-a`, monotonicity of
`x(2a+x)/(a+x)` gives `d(2a+d)<=k sqrt(b^2-a^2)`, so the normalized sum over
`v` is at most `k`; summing `2k` over `1<=k<N` gives (7.4).

Thus the exact phase-independent mass

```text
A(m,N)=sum_(v,k) a_(m,N)(v,k)                              (7.5)
```

satisfies

```text
0 <= A(m,N) <= 4N(N-1) <= 4N^2.                           (MASS)
```

### 7.2 The needed coefficient-square bound

From (7.1), `e^2<=6e`, so (7.2) gives

```text
sum_(v,k) e_(m,N)(v,k)^2 <= 18N^2.                        (7.6)
```

For `h`, use the pointwise domination by `(2/W)Lambda_1`.  Fix one canonical
block `B=[a,b)`, put `L=b-a`, and write `k=a+d`, `0<=d<L`.  Formula (7.3)
gives the exact square sum

```text
sum_(v=0)^(k-1) Lambda_1(v,k;a,b)^2
 = a d^2 + d(k-1)^2.                                      (7.7)
```

Since `W^2=L(a+b)`, `k-1<b`,
`sum_(d=0)^(L-1)d^2<=L^3/3`, and
`sum_(d=0)^(L-1)d<=L^2/2`,

```text
sum_(k in B) sum_(v<k) [2Lambda_1(v,k;a,b)/W]^2
 <= 4[L^2/3+bL/2].                                        (7.8)
```

The canonical blocks partition `[1,N)`, so

```text
sum_B L=N-1,  sum_B L^2<=(N-1)^2,  b<=N.
```

Summing (7.8) gives

```text
sum_(v,k) h_(m,N)(v,k)^2 <= (10/3)N^2.                    (7.9)
```

Finally, `(e+h)^2<=2e^2+2h^2`, so

```text
sum_(v,k) a_(m,N)(v,k)^2
 <= 36N^2+(20/3)N^2
 = (128/3)N^2.                                             (COEF)
```

The onset and strict supercritical filters only remove nonnegative terms from
all estimates in this section.

## 8. Exact expectation and centered process

Every frequency `10^k-10^v` in (2.20) is a positive integer.  Finite
linearity and (4.1) give the exact expectation

```text
E X(m,N) = kappa_m A(m,N).                                 (8.1)
```

Define

```text
Y_(m,N)(alpha)
 = X(m,N;alpha)-E X(m,N)
 = sum_(v,k) a_(m,N)(v,k)
     f_m((10^k-10^v)alpha).                                (8.2)
```

For a fixed real `s` with `0<s<1`, put

```text
q_m=10^(-s m),
T_m(N)=N+N^2 q_m,
U_m(N)=Y_(m,N)/T_m(N) for N>=1,
U_m(0)=0.                                                   (8.3)
```

This centering is exact.  In particular, `E U_m(N)=0`.

## 9. Every centered dyadic increment

The lists `B_N` are not nested as `N` varies.  Accordingly, no endpoint
coefficient is reused and no monotone partial-sum assertion is made.

For arbitrary natural cutoffs `a<b`, extend every coefficient by zero outside
its finite outer domain and define

```text
beta_(m;a,b)(v,k)
 = a_(m,b)(v,k)/T_m(b) - a_(m,a)(v,k)/T_m(a),              (9.1)
```

where the second term is zero if `a=0`.  Then the exact centered increment is

```text
U_m(b)-U_m(a)
 = sum_(v,k) beta_(m;a,b)(v,k)
     f_m((10^k-10^v)alpha).                                (9.2)
```

Thus (9.2) includes every block split or merge, every changed width, every
new or removed hidden exponent, and every changed outer or filtered pair.

By `(COEF)`,

```text
E_(m,N):=sum_(v,k)[a_(m,N)(v,k)/T_m(N)]^2
 <= (128/3)/(1+Nq_m)^2.                                   (9.3)
```

The elementary inequality `(x-y)^2<=2x^2+2y^2` gives

```text
sum_(v,k) beta_(m;a,b)(v,k)^2
 <= 2E_(m,a)+2E_(m,b).                                    (9.4)
```

For every dyadic level `r>=0` and `j>=0`, use the aligned interval

```text
I_(r,j)=[j2^r,(j+1)2^r].                                  (9.5)
```

At a fixed level, each positive endpoint is counted in at most two adjacent
intervals.  Therefore (9.3)-(9.4) imply

```text
sum_(j>=0) sum_(v,k) beta_(m;I_(r,j))(v,k)^2
 <= 4 sum_(j>=1) E_(m,j2^r)
 <= (512/3) sum_(j>=1) [1+j2^r q_m]^(-2)
 <= (512/3)/(2^r q_m).                                    (9.6)
```

The last inequality is the decreasing-integral estimate

```text
sum_(j>=1)(1+jx)^(-2)
 <= integral_0^infinity (1+xt)^(-2)dt = 1/x.
```

Applying `(COV)` to every exact increment (9.2), then using (9.6), gives

```text
sum_(j>=0)||U_m((j+1)2^r)-U_m(j2^r)||_2^2
 <= (20m^2/H)(512/3)/(2^r q_m).                            (9.7)
```

Finally,

```text
sum_(r>=0)(r+1)^2/2^r=12.
```

Since `H q_m=10^((1-s)m)`, summing (9.7) proves the advertised explicit
square-variation estimate

```text
sum_(r>=0)(r+1)^2 sum_(j>=0)
  ||U_m((j+1)2^r)-U_m(j2^r)||_2^2
 <= 40960 m^2 10^(-(1-s)m).                               (SV)
```

## 10. Complete maximal-tail implication

Every finite integer interval `[0,N]` has its standard binary decomposition
into pairwise disjoint aligned intervals, with at most one interval of each
length `2^r`.  Telescoping the genuinely centered increments (9.2) over this
decomposition gives `U_m(N)`.  Weighted Cauchy-Schwarz therefore gives,
pointwise in `alpha`,

```text
sup_(N>=1)|U_m(N)|^2
 <= [sum_(r>=0)(r+1)^(-2)]
      sum_(r>=0)(r+1)^2 sum_(j>=0)|Delta_(r,j)U_m|^2
 <= (pi^2/6)
      sum_(r>=0)(r+1)^2 sum_(j>=0)|Delta_(r,j)U_m|^2.      (10.1)
```

This is not an uncentered restatement: the increments in the right side are
exactly (9.2), and their `L2` sum is bounded by `(SV)`.

Fix an integer `ell>=2`, set `s=s_ell=1-1/ell`, and put
`x=x_ell=10^(-1/ell)`.  Summing `(SV)` over `m>=1` is legitimate because

```text
C_ell
 := 40960 sum_(m>=1)m^2 x^m
  = 40960 x(1+x)/(1-x)^3 < infinity.                       (10.2)
```

For each positive integer `R`, first let

```text
W_(ell,R)(alpha)=max_(1<=m,N<=R)|U_m(N;alpha)|.
```

This is a finite measurable maximum.  Equations (10.1)-(10.2), Tonelli for
nonnegative sums, and `(SV)` give the bound, uniform in `R`,

```text
E W_(ell,R)^2 <= (pi^2/6) C_ell.                           (10.3)
```

The finite maxima increase pointwise to the countable extended supremum

```text
W_ell(alpha)=sup_(m,N>=1)|U_m(N;alpha)|.
```

Monotone convergence applied to `W_(ell,R)^2` proves both that `W_ell` is
finite almost everywhere and that (10.3) remains true with `W_ell` in place
of `W_(ell,R)`.

The deterministic mean is also uniform.  From `(MASS)`, (4.5), and (8.3),

```text
E X(m,N)/T_m(N)
 <= 4 kappa_m/q_m
 <= 20m x^m
 <= B_ell,

B_ell := 20 sum_(m>=1)m x^m
       = 20x/(1-x)^2.                                      (10.4)
```

For a finite cutoff `R`, define T40's exact normalized maximum

```text
Z_(ell,R)(alpha)
 = max_(1<=m<=R,1<=N<=R)
     X(m,N;alpha)/[N+N^2 10^(-s_ell m)].                  (10.5)
```

Equations (8.2), (8.3), and (10.4) give

```text
Z_(ell,R) <= B_ell+W_(ell,R) <= B_ell+W_ell.               (10.6)
```

T40's tail range has `L>=1`.  If also `L>=2B_ell`, Chebyshev and (10.3) give

```text
phaseMeasure{Z_(ell,R)>L}
 <= phaseMeasure{W_ell>L/2}
 <= [2pi^2 C_ell/3]/L^2
 <= [2pi^2 C_ell/3]/L,                                    (10.7)
```

where the last inequality uses `L>=1`.

If `1<=L<2B_ell`, the probability is at most one, hence at most
`2B_ell/L`.  Therefore T40's maximal-tail condition holds, uniformly in
`R`, with the explicit constant

```text
A_ell
 = max(2B_ell,2pi^2 C_ell/3)
 = max(
     40x/(1-x)^2,
     (81920 pi^2/3) x(1+x)/(1-x)^3).                      (MT-constant)
```

This constant is finite and, in fact, independent of `Q0,Qstar`.

## 11. Almost-everywhere variable-phase sibling

Equation (10.3) says that `W_ell(alpha)<infinity` outside a null set
`E_ell`.  The countable union over `ell>=2` is null.  Fix `alpha` outside
that union and any real `s` with `0<s<1`.  Choose `ell>=2` such that

```text
s < s_ell < 1.                                             (11.1)
```

Because ten is greater than one,

```text
10^(-s_ell m) <= 10^(-s m),
N+N^2 10^(-s_ell m) <= N+N^2 10^(-s m).                   (11.2)
```

From the definition of `W_ell`, (10.4), and (11.2), for all positive `m,N`,

```text
X(m,N;alpha)
 <= [B_ell+W_ell(alpha)]
      [N+N^2 10^(-s m)].                                  (11.3)
```

The bracketed constant is finite, nonnegative, and independent of `m,N`.
Thus, for the fixed arbitrary `Q0,Qstar`, one common full-measure phase set
works first, then every real `0<s<1`, then a phase- and exponent-dependent
constant, then every positive `m,N`.  This is the complete variable-phase
`ARI_super(36/5)` sibling.

## 12. Claim boundary and verification checklist

The positive verdict is only for the variable-phase sibling.  It uses no
irrationality-measure estimate and says nothing at the individual phase
`Real.pi`.  It proves no statement about C3, C2, C1, or the canonical decimal
collision count.

A skeptical check can proceed in this order:

1. Canonical source and hash: Section 1 and `CANONICAL_STATEMENT.txt`.
2. Exact record domain and vacuity of exclusion on long lags: (2.2)-(2.6).
3. Outer domain and strict supercritical filter: (2.7)-(2.10).
4. Canonical blocks and literal widths: (2.11)-(2.16).
5. All six rows and hidden range: (2.17)-(2.18).
6. Exact variable-phase incidence: (2.19)-(2.20).
7. Every shell endpoint and literal weight: (3.1)-(3.5).
8. Exact mean, second moment, and centering: (4.1)-(4.5).
9. Exact Fourier and covariance identities: (4.6), (5.1)-(5.2).
10. Gcd identity and covariance row sum: (5.3)-(5.12), `(COV)`.
11. Exact six-row coefficient reconstruction: (6.1)-(6.6).
12. Mass and coefficient-square constants: `(MASS)` and `(COEF)`.
13. Every normalized centered increment and dyadic range: (9.1)-(9.7).
14. Square-variation constant `40960`: `(SV)`.
15. Complete maximal implication and explicit tail constant: (10.1)-(10.7)
    and `(MT-constant)`.
16. Quantifier order for every real exponent: (11.1)-(11.3).
17. Lean declarations introduced: none.
18. Literature assertions introduced: none.
19. Independent statement and proof review: pending.
