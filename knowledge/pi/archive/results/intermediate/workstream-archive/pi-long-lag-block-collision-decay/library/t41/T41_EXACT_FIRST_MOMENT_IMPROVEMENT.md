# T41: exact shell moment and a sharper fixed-scale tail

Status: `proof sketch` giving a strict quantitative improvement. The new
finite and measure calculations below are derived explicitly in prose, but have
not been formalized in Lean.

This note concerns only the variable-phase sibling of T36's exact
`ARI_super(36/5)` incidence. It neither proves nor refutes T40's maximal-tail
conjecture `(MT)`. It makes no assertion about `Real.pi`, the canonical
collision count, C3, C2, or C1.

## 1. Provenance, trusted input, and scope

The canonical local statement has no external source URL. A byte-exact copy
is delivered as `CANONICAL_STATEMENT.txt`; its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

It asks about ordered long-lag decimal collisions at `pi`. The present result
is a sibling result for a Lebesgue-random real phase and does not estimate
that collision count.

The kernel-checked input is

```text
TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving
SHA-256 3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24
```

In particular, this note uses T36's public theorem
`blockRepunitMultiplicity_block_sum_le`, whose conclusion is the exact
six-row bound (8.3) below. T36 imports the kernel-checked T34 definitions of
the six row domains and the shell endpoints. No external
irrationality-measure hypothesis is used.

The T40 note has SHA-256
`acdd09a0ae8354d7708e54c63334f2a33a1b6da447ef171e083232e1eeb1442c`.
It is unverified motivation only. Every claim needed here is reconstructed or
proved below rather than taken from T40.

Fix arbitrary natural numbers `Q0,Qstar`. There is no positivity assumption
on either onset. In all subsequent assertions, `m,N` are natural numbers with
`1 <= m` and `1 <= N` unless stated otherwise.

## 2. Exact records and arithmetic survival

A long-pair core is `(r,n)`, in literal `(lag,start)` order. An ordered record
is

```text
q = (epsilon,(r,n)),  epsilon in {false,true}.
```

Its frequency endpoint is `E(q)=n+r`. Given an orientation, a start, and an
endpoint, T34's record is

```text
record(epsilon,n,E) = (epsilon,(E-n,n)),                   (2.1)
```

where `E-n` is natural subtraction. Invalid endpoint order is not repaired:
it produces lag zero and is rejected by the condition `0<r` below.

For `r>0`, define the structured denominator

```text
qden(n,r) = 10^n (10^r-1).                                (2.2)
```

At the literal T36 parameters `(mu,c)=(8,1)`, the excluded predicate is

```text
ArithmeticExcluded(8,1,Q0,m,n,r) iff
  Q0 <= qden(n,r) and
  10^(-m) <= qden(n,r) * (1/qden(n,r)^8),                 (2.3)
```

where the second line of (2.3), including every occurrence of `qden`, is an
inequality of real numbers. For a dyadic block `B`, exact
membership in its record domain is

```text
(epsilon,(r,n)) in Q_B iff
  0 < r,
  m <= r,
  not ArithmeticExcluded(8,1,Q0,m,n,r),
  B.start <= n+r < B.finish.                              (2.4)
```

Thus both orientations are retained, the long-lag cutoff is weak, and the
block is half-open.

## 3. Canonical blocks and literal weights

A dyadic block is a pair `(a,j)` with

```text
B.start       = a,
B.blockLength = 2^j,
B.finish      = a+2^j.                                    (3.1)
```

The recursive list `dyadicPartitionFrom(q,js)` starts its first block at
`q+1` and advances by each preceding block length. T36's canonical list is

```text
B_N = translatedCanonicalBlocks(N)
    = dyadicPartitionFrom(0,(N-1).bitIndices.reverse).     (3.2)
```

It is a nonduplicated consecutive partition of the integer endpoints
`[1,N)`. Every `B` in this list has

```text
1 <= B.start < B.finish <= N.                             (3.3)
```

Its literal weight is never replaced in the definition:

```text
w_B = sqrt(B.finish^2-B.start^2).                         (3.4)
```

For later estimation, (3.3) gives `B.finish>=B.start+1`, so

```text
B.finish^2-B.start^2
  >= (B.start+1)^2-B.start^2
   = 2 B.start+1 >= 3.
```

Consequently

```text
w_B >= sqrt(3) >= 1.                                      (3.5)
```

Only the final inequality `1/w_B<=1` will be used. Formula (3.4) remains the
weight in every incidence.

## 4. Outer parameters and all six rows

The exact outer parameter domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.              (4.1)
```

Put

```text
k          = v+rho,
d(v,rho)   = 10^v(10^rho-1) = 10^k-10^v.                 (4.2)
```

Every `d(v,rho)` on `D_N` is a positive integer. T36's literal
supercritical filter is

```text
P_m(v,rho) iff
  Qstar <= d(v,rho) and 5m < 31(v+rho).                   (4.3)
```

For each hidden exponent `z` in `range N`, the six row pairs are exactly

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
  (record(false,v,z), record(true,z,k)).                   (4.4)
```

For a named row `r`, T34's `cancellingRowDomain` is the singleton containing
the corresponding pair in (4.4), filtered by `0<rho` and membership of both
records in the exact domain (2.4). Its cardinality is therefore zero or one.
No row is merged, omitted, or counted with an extra orientation factor.

Define the exact six-row, hidden-exponent multiplicity

```text
M_B(v,rho)
  = sum_(0<=z<N) sum_(r in all six rows)
      card(cancellingRowDomain(8,1,Q0,m,B,r,v,rho,z)).     (4.5)
```

All dependence on `Q0,m,N` in (4.5) is through the displayed literal row
domain and ranges.

## 5. Probability space and endpoint-pinned shells

Let

```text
Omega        = [0,1),
phaseMeasure = Lebesgue measure restricted to Omega,
H_m          = 10^m,
K_m          = clog_2(H_m)-1,
delta(x)     = |x-round(x)|.                              (5.1)
```

The total phase measure is one. T34's kernel-checked shell-depth audit gives,
for every positive `m`,

```text
1 <= K_m,
2^K_m < H_m <= 2^(K_m+1).                                (5.2)
```

The exact shells are

```text
S_0(m,x): 0 <= delta(x) <= 1/H_m,

S_j(m,x): 2^(j-1)/H_m < delta(x)
              <= min(2^j/H_m,1/2),  1<=j<=K_m.           (5.3)
```

Shell zero is closed at both ends. Every positive shell is open below and
closed above, including the terminal cap. Define the literal weight

```text
theta_m(x)
  = 1_(S_0(m,x))
      + sum_(j=1)^K_m 2^(-j) 1_(S_j(m,x)).                (5.4)
```

The shells partition every real argument according to its nearest-integer
distance. Formula (5.4), including its values on shell boundaries, is used
without an almost-everywhere alteration.

## 6. Exact variable-phase incidence

For `0<=j<=K_m`, define

```text
I_j(m,N;alpha)
  = sum_(B in B_N)
      sum_((v,rho) in D_N with P_m(v,rho))
        if S_j(m,d(v,rho) alpha)
        then M_B(v,rho)/w_B else 0.                       (6.1)
```

The variable-phase T36 sibling is

```text
X(m,N;alpha)
  = I_0(m,N;alpha)
      + sum_(j=1)^K_m 2^(-j) I_j(m,N;alpha).              (6.2)
```

The parameters `Q0,Qstar` remain fixed and suppressed in this notation.
Comparing with T36's `supercriticalIncidence`, only
`d(v,rho)*Real.pi` has been replaced by `d(v,rho)*alpha`.

All sums are finite. Distributing them gives the exact identity

```text
X(m,N;alpha)
  = sum_(B in B_N)
      sum_((v,rho) in D_N with P_m(v,rho))
        [M_B(v,rho)/w_B] theta_m(d(v,rho) alpha).          (6.3)
```

Every summand is nonnegative. Each shell is Borel, so `X` and all finite
maxima of such variables are measurable.

## 7. Exact shell measure and exact shell mean

Fix a positive integer `d`. Partition `[0,1)` into
`[a/d,(a+1)/d)`, `0<=a<d`. On the `a`th interval set
`t=d alpha-a`. The Jacobian is `1/d`, `t` traverses `[0,1)`, and integer
translation preserves `delta`. Summing the `d` branches proves that
`delta(d alpha)` has the same distribution as `delta(t)` for uniform
`t in [0,1)`.

For `0<=a<b<=1/2`, the set

```text
{t in [0,1): a < delta(t) <= b}
```

differs at most at endpoints from `(a,b] union [1-b,1-a)` and has measure
`2(b-a)`. Also `{delta(t)<=b}` has measure `2b`. These statements retain the
literal endpoint predicates because individual endpoints have measure zero.
It follows that

```text
phaseMeasure{alpha: S_0(m,d alpha)} = 2/H_m,               (7.1)

phaseMeasure{alpha: S_j(m,d alpha)}
  = 2[min(2^j/H_m,1/2)-2^(j-1)/H_m]                       (7.2)
```

for `1<=j<=K_m`.

We now evaluate, rather than merely bound, the shell mean. If `1<=j<K_m`,
then (5.2) gives `2^j/H_m<1/2`; hence the weighted contribution of shell `j`
is

```text
2^(-j) * 2[2^j/H_m-2^(j-1)/H_m] = 1/H_m.                 (7.3)
```

For `j=K_m`, (5.2) gives `2^K_m/H_m>=1/2`, so the terminal weighted
contribution is

```text
2^(-K_m) * 2[1/2-2^(K_m-1)/H_m]
  = 2^(-K_m)-1/H_m.                                       (7.4)
```

There are `K_m-1` middle shells. Adding shell zero, (7.3), and (7.4) yields
the exact formula

```text
kappa_m
  := integral_Omega theta_m(d alpha) d alpha
   = 2/H_m + (K_m-1)/H_m + 2^(-K_m)-1/H_m
   = K_m/H_m + 2^(-K_m).                                  (7.5)
```

This is independent of the positive integer `d`.

For later comparison, `H_m<=2^(K_m+1)` implies
`2^(-K_m)<=2/H_m`, so

```text
kappa_m <= (K_m+2)/H_m.                                   (7.6)
```

Also `10^m<=16^m=2^(4m)`. Monotonicity and the least-exponent definition of
`clog_2` give `clog_2(H_m)<=4m`; therefore

```text
K_m+2 = clog_2(H_m)+1 <= 4m+1 <= 5m.                     (7.7)
```

Combining (7.6)-(7.7),

```text
0 <= kappa_m <= 5m 10^(-m).                               (7.8)
```

## 8. Exact first moment and finite six-row count

Define the deterministic mass

```text
A(m,N)
  = sum_(B in B_N)
      sum_((v,rho) in D_N with P_m(v,rho))
        M_B(v,rho)/w_B.                                   (8.1)
```

Each coefficient `d(v,rho)` in (8.1) is positive. Finite linearity of the
integral, (6.3), and (7.5) give the exact identity

```text
integral_Omega X(m,N;alpha) d alpha = kappa_m A(m,N).      (8.2)
```

T36's kernel-checked theorem
`blockRepunitMultiplicity_block_sum_le` states, with the exact multiplicity
(4.5),

```text
sum_(B in B_N) M_B(v,rho) <= 6N                           (8.3)
```

for every natural `v,rho`. The constant six is exactly the cardinality of
T34's `CancellingRow` type. The proof also retains every `z` in `range N` and
uses uniqueness of the canonical block containing an active endpoint.

By (3.5), division by the literal width can only decrease each nonnegative
term. Thus, for each fixed `(v,rho)`,

```text
sum_(B in B_N) M_B(v,rho)/w_B <= 6N.                      (8.4)
```

It remains to count the exact outer domain rather than replace it by `N^2`.
For each `k=v+rho` with `1<=k<N`, positivity of `rho` gives exactly the `k`
pairs

```text
(v,rho)=(0,k),(1,k-1),...,(k-1,1).
```

All automatically satisfy the two individual `range N` restrictions in
(4.1). Conversely every pair in `D_N` appears once. Hence, including the
empty case `N=1`,

```text
card(D_N) = sum_(k=1)^(N-1) k = N(N-1)/2.                (8.5)
```

The supercritical set is a subset of `D_N`. Exchanging the two finite sums in
(8.1), then applying (8.4)-(8.5), gives

```text
0 <= A(m,N)
     <= 6N card{(v,rho) in D_N: P_m(v,rho)}
     <= 6N card(D_N)
      = 3N^2(N-1).                                        (8.6)
```

Combining (8.2), (8.6), and the exact value (7.5) gives

```text
integral_Omega X(m,N;alpha) d alpha
  <= 3 [K_m/10^m + 2^(-K_m)] N^2(N-1)
  <= 15m N^2(N-1) 10^(-m).                               (8.7)
```

The T40 note recorded the coarser, unverified bound
`30m N^3 10^(-m)`. Inequality (8.7) is derived independently here. It is
strictly narrower for every positive `m,N`, since

```text
15m N^2(N-1) 10^(-m) < 30m N^3 10^(-m).                 (8.8)
```

## 9. The narrower terminal tail inequality

For any real `s`, define the positive target

```text
T_s(m,N) = N + N^2 10^(-s m).                             (9.1)
```

Let `lambda>0`. Since `X` is nonnegative and measurable, Markov's inequality
and (8.7) give the promised single terminal estimate:

```text
(TI)

phaseMeasure{alpha in [0,1):
    X(m,N;alpha)/T_s(m,N) > lambda}
  <= 3 [K_m/10^m + 2^(-K_m)] N^2(N-1)
       / [lambda T_s(m,N)]
  <= 15m N^2(N-1) 10^(-m)
       / [lambda (N+N^2 10^(-s m))].                      (9.2)
```

Every quantifier in (9.2) is explicit: it holds for the fixed arbitrary
natural `Q0,Qstar`, every positive natural `m,N`, every real `s`, and every
real `lambda>0`. Its numerator is strictly smaller than the
`30mN^3 10^(-m)` numerator obtained by applying Markov to T40's displayed
coarse moment bound.

## 10. Why this does not prove `(MT)`

For completeness, T40's conjectural maximal statement fixes an integer
`ell>=2`, puts `s_ell=1-1/ell`, and defines

```text
Z_(ell,R)(alpha)
  = max_(1<=m<=R, 1<=N<=R)
      X(m,N;alpha)/T_(s_ell)(m,N).                         (10.1)
```

It asks for a finite `A_(Q0,Qstar,ell)`, independent of `R` and `L`, such
that for all real `L>=1` and integers `R>=1`,

```text
phaseMeasure{alpha in [0,1): Z_(ell,R)(alpha)>L}
  <= A_(Q0,Qstar,ell)/L.                                  (MT)
```

Inequality (9.2) is fixed-scale, not maximal. For fixed `m,s` and large `N`,
its last right-hand side is asymptotic to

```text
15m N 10^(-(1-s)m)/lambda,
```

so summing it over `N`, or merely taking its supremum over unbounded `N`,
does not produce an `R`-independent constant. The exact supercritical count
in the middle line of (8.6) might contain additional structure, but no such
uniform saving is proved here. Thus (9.2) strictly improves T40's displayed
coarse first-moment calculation while isolating the same missing cross-cutoff maximal
estimate. It supplies neither a proof nor a refutation of `(MT)`.

## 11. Claim boundary and verification map

The result of this note is the strict quantitative improvement (8.7), with
the narrower terminal tail inequality `(TI)` in (9.2). Its ingredients are
checkable as follows:

1. Exact record domain and arithmetic survival: (2.1)-(2.4).
2. Canonical blocks and literal width: (3.1)-(3.5).
3. Outer domain, supercritical filter, and all six rows: (4.1)-(4.5).
4. Probability space, every shell endpoint, and literal weight: (5.1)-(5.4).
5. Exact finite incidence and direct identity: (6.1)-(6.3).
6. Exact shell measures and mean: (7.1)-(7.8).
7. T36 kernel input, exact domain count, and improved moment: (8.1)-(8.8).
8. Sole terminal inequality: `(TI)` in (9.2).
9. Remaining conjectural maximal statement: (10.1)-(MT).

No almost-everywhere conclusion is asserted. No value of `alpha` is
specialized to `pi`. No conclusion is stated for C3, C2, C1, or the canonical
collision estimate. No literature claim and no finite experiment is used.
