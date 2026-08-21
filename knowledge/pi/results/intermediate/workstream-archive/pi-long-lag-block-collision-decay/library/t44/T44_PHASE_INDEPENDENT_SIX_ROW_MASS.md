# T44: quadratic bound for the phase-independent six-row mass

Status: `proof sketch`.  The definitions and named input theorems from T36 are
kernel-checked; the finite regrouping and elementary inequalities proved in
this note have not been formalized in Lean.

The result is only about the variable-phase sibling of T36's
`ARI_super(36/5)` incidence.  It proves no assertion at `Real.pi`, no bound for
the canonical collision count, and no conclusion for C3, C2, or C1.

## 1. Provenance, trusted input, and claim boundary

The canonical local problem has no external source URL.  Its byte-exact text
is delivered as `CANONICAL_STATEMENT.txt`, whose SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That problem asks about ordered long-lag decimal collisions at `pi`.  T44 does
not estimate those collisions.  It studies a deterministic finite mass which
occurs when the shell phase in T36 is changed from `Real.pi` to a uniformly
distributed real phase.

The sole mathematical library input is the kernel-checked module

```text
TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving
SHA-256 3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24
```

T36 imports the exact T34 row definitions and the T29/T31/T32 canonical-block
and record-domain interfaces.  In particular, the present note uses T36's
public audits `six_cancelling_domains_audit` and
`sourceExponent_shell_endpoint_audit`, its direct finite identity
`restrictedWeightedShellIncidence_eq_direct`, and its machine-checked bound

```text
sum_(B in B_N) blockLength(B)/widthWeight(B) < 3.           (1.1)
```

The last statement is `canonical_blockLength_weight_budget`.

The T40 and T41 notes are `proof sketch` motivation only.  No claim from
either note is used as a premise.  In particular, the definition, regrouping,
quadratic estimate, shell integral, and tail inequality below are all derived
again here.

### Ambiguities resolved

1. `Q0,Qstar` are arbitrary fixed natural numbers; neither is assumed
   positive.
2. Every estimate below has natural `m,N` in the positive range `1 <= m` and
   `1 <= N`.
3. The supercritical inequality is the strict inequality `5m < 31(v+rho)`.
4. The block interval is half-open, the shell-zero upper endpoint is closed,
   and every positive shell is open below and closed above.
5. The six T34 rows are counted exactly once.  No reversal factor is inserted.
6. The mass `A` contains the literal width denominator but no phase or shell
   factor.  This is the normalization which factors out of the variable-phase
   first moment.

## 2. Exact finite data

Fix `Q0,Qstar : Nat` and positive `m,N : Nat`.

### 2.1 Records and arithmetic survival

A record is `(epsilon,(r,n))`, where `epsilon` is Boolean, `r` is its lag,
and `n` is its start.  Its frequency endpoint is `n+r`.  T34's constructor is

```text
record(epsilon,n,E) = (epsilon,(E-n,n)),                    (2.1)
```

where `E-n` is natural subtraction.  Invalid endpoint order therefore creates
lag zero and is rejected by the record domain rather than silently repaired.

For `r>0`, put

```text
qden(n,r) = 10^n(10^r-1).                                  (2.2)
```

The transitive imported definition is
`Theory.PiDigits.PositiveLowerBlockDensity.T25.ArithmeticExcluded`, from
`TheoryLib/PiPositiveLowerBlockDensity/T25T25ResidualPairReduction.lean`
(SHA-256
`86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c`).
That same source defines `structuredDenominator n r` as (2.2).  At T36's
literal parameters `(mu,c)=(8,1)`, its full expansion is

```text
Excluded(Q0,m;n,r) iff
  Q0 <= qden(n,r) and
  10^(-m) <= qden(n,r) * (1/qden(n,r)^8),                  (2.3)
```

where the second line is over the real numbers.  Write

```text
sigma(n,r) = 1 if not Excluded(Q0,m;n,r), and 0 otherwise. (2.4)
```

For a dyadic block `B=[a,b)`, the exact T32/T36 record domain is

```text
(epsilon,(r,n)) in Q_B iff
  0 < r,
  m <= r,
  sigma(n,r)=1,
  a <= n+r < b.                                             (2.5)
```

Thus survival is independent of the Boolean orientation.

### 2.2 Outer parameters and supercritical filter

The exact outer domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.               (2.6)
```

Put

```text
k = v+rho,
d(v,rho) = 10^v(10^rho-1) = 10^k-10^v.                    (2.7)
```

On `D_N`, `d(v,rho)` is a positive integer.  The exact filter inherited from
T36 is

```text
P(Qstar,m;v,rho) iff
  Qstar <= d(v,rho) and 5m < 31(v+rho).                    (2.8)
```

The map `(v,rho) -> (v,k=v+rho)` is a bijection

```text
D_N  <->  {(v,k): 0 <= v < k < N},                         (2.9)
```

with inverse `rho=k-v`.  In particular,

```text
card(D_N) = sum_(k=1)^(N-1) k = N(N-1)/2.                 (2.10)
```

This includes the empty case `N=1`.

### 2.3 Canonical blocks and literal normalization

A dyadic block `B=(a,j)` represents

```text
B.start       = a,
B.blockLength = 2^j,
B.finish      = a+2^j.                                     (2.11)
```

The exact canonical list is

```text
B_N = translatedCanonicalBlocks(N)
    = dyadicPartitionFrom(0,(N-1).bitIndices.reverse).      (2.12)
```

It is a nonduplicated consecutive partition of the integer endpoints
`[1,N)`.  Its literal width is

```text
w_B = sqrt(B.finish^2-B.start^2).                           (2.13)
```

Every canonical width is positive.  Formula (1.1) says

```text
sum_(B in B_N) blockLength(B)/w_B < 3.                     (2.14)
```

For every `1<=k<N`, there is a unique canonical block containing `k`; denote
it by

```text
B_N(k)=[a_N(k),b_N(k)),
W_N(k)=sqrt(b_N(k)^2-a_N(k)^2).                            (2.15)
```

Its endpoints satisfy

```text
1 <= a_N(k) <= k < b_N(k) <= N.                           (2.16)
```

Existence follows from the consecutive partition (2.12), and uniqueness is
the kernel-checked canonical-block interval uniqueness imported by T36.

### 2.4 All six rows and the hidden range

For every `z` in the literal range `0<=z<N`, the six ordered record pairs are

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
records in (2.5).  Its cardinality is consequently zero or one.  Let

```text
c_r(B;v,rho,z)
  = card(cancellingRowDomain(8,1,Q0,m,B,r,v,rho,z)).        (2.18)
```

The exact six-row multiplicity is

```text
M_B(Q0,m,N;v,rho)
  = sum_(0<=z<N) sum_(r=1)^6 c_r(B;v,rho,z).                (2.19)
```

This is exactly T34/T36's `blockRepunitMultiplicity 8 1 Q0 m N B v rho`.

## 3. The phase-independent mass

Define

```text
A(Q0,Qstar;m,N)
  = sum_(B in B_N)
      sum_((v,rho) in D_N with P(Qstar,m;v,rho))
        M_B(Q0,m,N;v,rho)/w_B.                             (3.1)
```

All sums in (3.1) are finite, and every summand is nonnegative.  This is the
exact phase-independent normalized six-row mass requested in T44.  In
particular, (3.1) retains:

1. every pair in the outer domain (2.6);
2. both conditions in the supercritical filter (2.8);
3. every canonical block in (2.12);
4. every `z` in `Finset.range N`;
5. all six singleton-filtered row domains in (2.17);
6. every arithmetic-survival condition in (2.3)-(2.5); and
7. the literal width (2.13), with no asymptotic replacement.

Partition the six rows into the two same-endpoint rows `{1,3}` and the four
remaining rows `{2,4,5,6}`.  Finite distributivity gives the exact identity

```text
A = A_end + A_four,                                        (3.2)
```

where each term is obtained from (3.1) by restricting only the row sum.  No
limit, conditional rearrangement, or multiplicity estimate is involved in
(3.2).

## 4. The two same-endpoint rows

Fix `(v,rho)` and put `k=v+rho`.  For a canonical block `B=[a,b)`, define

```text
H_end(B;v,k)
  = #{z: 0<=z<N,
         k+m<=z,
         a<=z<b,
         sigma(k,z-k)=1,
         sigma(v,z-v)=1}.                                  (4.1)
```

For row 1, the two starts are `k,v` and their common endpoint is `z`.
Condition (2.5) is therefore exactly the list in (4.1).  Row 3 has the same
starts and endpoint in the opposite Boolean orientation, so orientation
independence gives the same indicator.  Hence the exact regrouping is

```text
A_end
  = 2 * sum_((v,rho) in D_N with P(Qstar,m;v,rho))
          sum_(B in B_N) H_end(B;v,v+rho)/w_B.              (4.2)
```

For each block, (4.1) is a subset of its `b-a=blockLength(B)` possible
integer endpoints.  Thus (2.14) gives, for every fixed outer pair,

```text
2 * sum_(B in B_N) H_end(B;v,k)/w_B
  <= 2 * sum_(B in B_N) blockLength(B)/w_B
   < 6.                                                     (4.3)
```

The filtered outer set is a subset of `D_N`.  Equations (2.10) and (4.3)
therefore imply

```text
0 <= A_end <= 6 card(D_N) = 3N(N-1).                       (4.4)
```

The weak inequality in (4.4) also covers the empty case without needing to
turn the strict block budget into a strict global assertion.

## 5. Exact regrouping of the other four rows

Fix `1<=k<N`, write its unique block as `B_N(k)=[a,b)`, and let `0<=v<k`.
Define the two exact surviving hidden-exponent counts

```text
H_ss(v,k)
  = #{z: 0<=z<N,
         z+m<=v,
         sigma(z,v-z)=1,
         sigma(z,k-z)=1},                                  (5.1)

H_mix(v,k)
  = #{z: 0<=z<N,
         a<=z<b,
         v+m<=z,
         z+m<=k,
         sigma(v,z-v)=1,
         sigma(z,k-z)=1}.                                  (5.2)
```

Rows 2 and 4 have common start `z` and endpoints `v,k`.  Both records can lie
in one canonical block only when `v` lies in `B_N(k)`.  Their two lag
conditions reduce to `z+m<=v`, and their Boolean orientations have the same
survival indicator.  Their combined multiplicity is therefore exactly

```text
2 * 1_(a<=v<b) * H_ss(v,k).                                (5.3)
```

Rows 5 and 6 have endpoints `z,k`; their lag conditions are `v+m<=z` and
`z+m<=k`.  Both endpoints lie in one canonical block exactly when `a<=z<b`.
Their combined multiplicity is exactly

```text
2 * H_mix(v,k).                                            (5.4)
```

The upper restriction `z<N` is automatic in (5.1), because
`z<=v-m<v<N`, and in (5.2), because `z<b<=N`.  Reindexing by the bijection
(2.9), using uniqueness of `B_N(k)`, and applying finite distributivity gives
the exact identity

```text
A_four
  = 2 * sum_(0<=v<k<N; Qstar<=10^k-10^v; 5m<31k)
        [1_(a_N(k)<=v<b_N(k))*H_ss(v,k)+H_mix(v,k)]/W_N(k).
                                                               (5.5)
```

No arithmetic-survival condition has been dropped in (5.5).

## 6. A uniform geometric envelope

For an integer `x`, write `[x]_+=max(x,0)`.  In every bracketed expression
below, the natural variables are first coerced to integers; subtraction is
therefore signed and is not natural truncated subtraction.  Dropping only the
two survival indicators in (5.1) gives

```text
H_ss(v,k) <= [v-m+1]_+.                                    (6.1)
```

The allowed integers in (5.2) form the half-open interval

```text
[max(a,v+m), min(b,k-m+1)),                                (6.2)
```

where all four endpoints in (6.2) are regarded as integers.  Thus

```text
H_mix(v,k)
  <= [min(b,k-m+1)-max(a,v+m)]_+.                          (6.3)
```

Define

```text
Lambda_m(v,k;a,b)
  = 1_(a<=v<b)[v-m+1]_+
      + [min(b,k-m+1)-max(a,v+m)]_+.                       (6.4)
```

Since `v<k<b` and `m>=1`, this simplifies without changing its value to

```text
Lambda_m(v,k;a,b)
  = 1_(a<=v)[v-m+1]_+
      + [k-m+1-max(a,v+m)]_+.                              (6.5)
```

Increasing `m` only shortens both integer intervals.  Thus

```text
Lambda_m(v,k;a,b) <= Lambda_1(v,k;a,b).                    (6.6)
```

Put `d=k-a`, so `0<=d<b-a`.  At `m=1`, formula (6.5) is elementary:

```text
Lambda_1(v,k;a,b) = d,      for 0<=v<a,
Lambda_1(v,k;a,b) = k-1,    for a<=v<k.                    (6.7)
```

Indeed, in the second range the same-start count is `v` and the mixed count
is `k-v-1`.  There are `a` values in the first range and `d` in the second,
so

```text
sum_(v=0)^(k-1) Lambda_m(v,k;a,b)
  <= ad+d(k-1)
   = d(a+k-1)
   = d(2a+d-1).                                            (6.8)
```

It remains to compare this numerator with the literal width

```text
W = sqrt(b^2-a^2).                                         (6.9)
```

If `d=0`, the right side of (6.8) is zero.  Suppose `d>0`, and put
`L=b-a`, so `0<d<L`.  The function

```text
f(x)=x(2a+x)/(a+x)=a+x-a^2/(a+x)                          (6.10)
```

is increasing for real `x>=0` (its derivative is
`1+a^2/(a+x)^2>0`).  Therefore

```text
d(2a+d)/(a+d)
  <= L(2a+L)/(a+L)
   = W^2/b
  <= W.                                                     (6.11)
```

For the last inequality, `0<W<=b` follows from
`W^2=b^2-a^2<=b^2`.  Since `a+d=k`, (6.11) gives

```text
d(2a+d) <= kW.                                             (6.12)
```

Combining (6.8) and (6.12), including the `d=0` case, proves the normalized
fixed-height estimate

```text
sum_(v=0)^(k-1) Lambda_m(v,k;a,b)/W <= k.                  (6.13)
```

All terms in (5.5) are nonnegative.  Removing its onset and supercritical
filters and then applying (6.1)-(6.4) and (6.13) yields

```text
0 <= A_four
  <= 2 * sum_(k=1)^(N-1) k
   = N(N-1).                                                (6.14)
```

## 7. Quadratic theorem

Combining the exact row split (3.2) with (4.4) and (6.14) gives the promised
absolute bound.

### Proposition 7.1

For every `Q0,Qstar : Nat` and every positive `m,N : Nat`,

```text
0 <= A(Q0,Qstar;m,N)
  <= 4N(N-1)
  <= 4N^2.                                                  (QB)
```

Thus the displayed absolute constant is

```text
C = 4.                                                      (7.1)
```

It is independent of `Q0,Qstar,m,N`.  The proof deliberately discards the
supercritical and arithmetic-survival filters only after deriving the exact
finite identities (4.2) and (5.5), so no enlarged domain is mistaken for the
definition of `A`.

This is a full power saving from the inherited coarse `O(N^3)` estimate.  No
claim of optimality of the constant `4` is made.

## 8. Exact shells and the variable-phase first moment

This section verifies that (3.1), with precisely its normalization, is the
mass underlying the variable-phase first moment.

Let

```text
Omega = [0,1),
phaseMeasure = Lebesgue measure restricted to Omega,
H_m = 10^m,
K_m = clog_2(H_m)-1,
delta(x)=|x-round(x)|.                                     (8.1)
```

For positive `m`, T36's endpoint audit gives

```text
1 <= K_m,
2^K_m < H_m <= 2^(K_m+1).                                 (8.2)
```

The literal shells are

```text
S_0(m,x): 0 <= delta(x) <= 1/H_m,

S_j(m,x): 2^(j-1)/H_m < delta(x)
              <= min(2^j/H_m,1/2),  1<=j<=K_m.            (8.3)
```

Shell zero is closed at both ends.  Every positive shell is open below and
closed above, including the terminal cap.  Define

```text
theta_m(x)
  = 1_(S_0(m,x))
      + sum_(j=1)^K_m 2^(-j) 1_(S_j(m,x)).                 (8.4)
```

For `0<=j<=K_m`, define the exact variable-phase shell incidence

```text
I_j(Q0,Qstar;m,N;alpha)
  = sum_(B in B_N)
      sum_((v,rho) in D_N with P(Qstar,m;v,rho))
        if S_j(m,d(v,rho)alpha)
        then M_B(Q0,m,N;v,rho)/w_B else 0,                 (8.5)
```

and

```text
X(Q0,Qstar;m,N;alpha)
  = I_0(Q0,Qstar;m,N;alpha)
      + sum_(j=1)^K_m 2^(-j) I_j(Q0,Qstar;m,N;alpha).      (8.6)
```

This changes only `d(v,rho)*Real.pi` in T36's shell tests to
`d(v,rho)*alpha`.  Every row domain remains the fixed arithmetic domain at
`(mu,c)=(8,1)`.  Finite distributivity gives the exact direct identity

```text
X(Q0,Qstar;m,N;alpha)
  = sum_(B in B_N)
      sum_((v,rho) in D_N with P(Qstar,m;v,rho))
        [M_B(Q0,m,N;v,rho)/w_B]
          theta_m(d(v,rho)alpha).                          (8.7)
```

No infinite interchange occurs.  The shell sets are Borel and the sums are
finite, so `X` is a nonnegative measurable function of `alpha`.

### 8.1 Exact shell mean

Fix a positive integer `d`.  Partition `[0,1)` into the `d` half-open
intervals `[r/d,(r+1)/d)`.  On the `r`th interval set `t=d alpha-r`.
The Jacobian is `1/d`, `t` traverses `[0,1)`, and integer translation does not
change `delta`.  Hence `delta(d alpha)` has the same distribution as
`delta(t)` for uniform `t` in `[0,1)`.

For `0<=u<v<=1/2`, the set

```text
{t in [0,1): u<delta(t)<=v}
```

has measure `2(v-u)`; its two components differ from `(u,v]` and
`[1-v,1-u)` only in endpoint conventions.  Individual endpoints have measure
zero.  Therefore the literal sets (8.3) have measures

```text
phaseMeasure{alpha: S_0(m,d alpha)} = 2/H_m,               (8.8)

phaseMeasure{alpha: S_j(m,d alpha)}
  = 2[min(2^j/H_m,1/2)-2^(j-1)/H_m]                       (8.9)
```

for `1<=j<=K_m`.

For `1<=j<K_m`, (8.2) makes the cap inactive, and the shell's weighted
contribution is exactly `1/H_m`.  At `j=K_m`, the cap is active, and the
weighted contribution is exactly `2^(-K_m)-1/H_m`.  Including shell zero,

```text
kappa_m
  := integral_Omega theta_m(d alpha) d alpha
   = 2/H_m + (K_m-1)/H_m + 2^(-K_m)-1/H_m
   = K_m/H_m + 2^(-K_m).                                  (8.10)
```

The result is independent of the positive integer `d`.  From (8.2),
`2^(-K_m)<=2/H_m`.  Also `10^m<=16^m=2^(4m)` implies
`K_m+2<=5m` for `m>=1`.  Consequently

```text
0 <= kappa_m <= 5m/H_m = 5m 10^(-m).                      (8.11)
```

Every `d(v,rho)` in (8.7) is positive.  Finite linearity of integration and
(8.10) now give the exact first-moment identity

```text
integral_Omega X(Q0,Qstar;m,N;alpha) d alpha
  = kappa_m A(Q0,Qstar;m,N).                               (8.12)
```

Combining (8.12), `(QB)`, and (8.11) gives the explicit quadratic moment

```text
integral_Omega X(Q0,Qstar;m,N;alpha) d alpha
  <= 4[K_m/10^m+2^(-K_m)]N(N-1)
  <= 20m N^2 10^(-m).                                     (8.13)
```

This is strictly `O(N^2)`, rather than the inherited `O(N^3)`, at fixed `m`.

## 9. One narrower terminal inequality

For real `s` and positive `m,N`, put

```text
T_s(m,N)=N+N^2 10^(-s m)>0.                               (9.1)
```

For every real `lambda>0`, Markov's inequality applied to the nonnegative
variable (8.6) and the first line of (8.13) gives

```text
phaseMeasure{alpha in [0,1):
    X(Q0,Qstar;m,N;alpha)/T_s(m,N) > lambda}

  <= 4[K_m/10^m+2^(-K_m)]N(N-1)
       / [lambda (N+N^2 10^(-s m))]

  <= 20m N^2 10^(-m)
       / [lambda (N+N^2 10^(-s m))].                      (TI_2)
```

The inequality holds for the fixed arbitrary natural `Q0,Qstar`, every
positive natural `m,N`, every real `s`, and every positive real `lambda`.
In particular it holds for `0<s<1`.  Its numerator is quadratic in `N`.

`(TI_2)` is only a fixed-scale variable-phase sibling statement.  It does not
provide a maximal inequality uniform over all `m,N`, and no almost-everywhere
all-scale consequence is asserted.

## 10. Verdict and verification map

T44's phase-independent sibling objective is met by the quadratic bound
`(QB)` with the absolute displayed constant `4`.  This is not the positive
alternative in the canonical fixed-`pi` question.  The proof also supplies
the exact variable-phase first moment (8.12) and the narrower fixed-scale
tail inequality `(TI_2)`.

The argument can be checked in this order:

1. Canonical source and hash: Section 1 and `CANONICAL_STATEMENT.txt`.
2. Record domain and exact arithmetic survival: (2.1)-(2.5).
3. Outer domain, strict supercritical filter, and exact count: (2.6)-(2.10).
4. Canonical blocks and literal width: (2.11)-(2.16).
5. All six rows and hidden range: (2.17)-(2.19).
6. Exact definition and finite row split: (3.1)-(3.2).
7. Same-endpoint regrouping and bound: (4.1)-(4.4).
8. Four-row exact regrouping: (5.1)-(5.5).
9. Independent geometric estimate: (6.1)-(6.14).
10. Quadratic conclusion and constant: `(QB)` and (7.1).
11. Every shell endpoint and exact shell mean: (8.1)-(8.11).
12. Variable-phase first moment and terminal inequality: (8.12)-(8.13) and
    `(TI_2)`.

No literature assertion or computational experiment is used.  No Lean
declaration is introduced.  Independent statement and proof review remain
pending.
