# T27: a width-weighted canonical square-function frontier

Status: `proof sketch`. The deterministic inputs from T22 and T24 and the
finite weighted-GCD input from T16 are machine-checked, but the new prose
arguments in this note are not kernel-checked. The metric statements concern
only a Lebesgue-random phase sibling. This note proves no estimate at the fixed
phase `alpha=pi`, no estimate for the decimal digits of pi, and no claim about
C1.

## 1. Provenance, exact target, and claim boundary

The canonical problem is the locally formulated question vendored byte for
byte as `CANONICAL_STATEMENT.txt`. There is no original external source URL.
Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks whether, for every real `0<s<1`, one constant
`C_s` works simultaneously for every pair of integers `m,N>=1` in the ordered
long-lag collision estimate

```text
R_pi(m,N) <= C_s [N+N^2 10^(-s m)].
```

This note does not answer that question. It studies a conditional spectral
frontier that implies T12's scale-matched L1 predicate. The fixed arithmetic
parameters throughout the deterministic discussion are

```text
mu,c in R, Q0 in N.
```

No sign, positivity, or effective-irrationality assumption on these three
parameters is silently imposed.

The exact kernel-checked inputs are:

1. T22,
   `TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff`,
   SHA-256
   `73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713`.
   It supplies the admissible ordered domain, signed-frequency injectivity,
   both orientations, coefficient one, the strict endpoint cutoff, the
   variable-phase cutoff polynomial, and its equivalence at `alpha=pi` with
   T12.
2. T24,
   `TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction`,
   SHA-256
   `2795d228eab081360e236be14ae99c0dd8267153d39e680710732330ea586924`.
   It supplies the translated-grid canonical binary partition and the exact
   endpoint and block telescoping identities.
3. T16,
   `TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD`,
   SHA-256
   `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec`.
   Its theorem `longDifferenceMultiplicityWeightedGCD_le` has the explicit
   constant `574913232`.
4. T18,
   `TheoryLib.PiLongLagBlockCollisionDecay.T18T18AlmostEverywhereScaleMatchedL1`,
   SHA-256
   `3f171dc88208dec60f8ea33957223829585b220e5623138997e8d8b571244439`.
   Its kernel-checked character orthogonality and finite resonance formulas
   provide a consistency check on the independent derivation in Section 7.

The T26 note is an unverified `proof sketch`. It motivates avoiding a uniform
bound on every individual local block, but no assertion from T26 is used as a
premise here.

### Normalized scope and ambiguities

The following choices are binding in this note.

1. T22's endpoint cutoff is strict: endpoint `E` enters cutoff `E+1`, not
   cutoff `E`.
2. Both ordered orientations are present and have opposite nonzero signed
   frequencies.
3. Every frequency sum below is inclusive: `h=1,...,10^m`; neither `h=0` nor
   `h>10^m` occurs.
4. T24's blocks are half-open and aligned on the grid translated by one.
5. The deterministic condition is evaluated at a specified phase `alpha`.
   Only its conditional specialization at `alpha=pi` is connected to T12.
6. The metric test replaces that specified phase by Lebesgue-random
   `alpha in [0,1)`. It is a sibling, not evidence at `alpha=pi`.
7. Constants selected after `s` may depend on `mu,c,Q0,s` (and, in an
   almost-everywhere conclusion, on `alpha`) but never on `m,N`, a block, or
   a frequency.

There is no unresolved quantifier convention after these choices.

## 2. T22 domain and exact endpoint-layer vectors

Write an ordered T22 record as

```text
q=(epsilon,(r,n)) in Bool x (N x N).
```

Its lag is `r`, its lower orbit exponent is `n`, and its endpoint is

```text
E(q)=n+r.
```

For fixed `mu,c,Q0,m`, T22's exact `N`-independent admissibility condition is

```text
0<r,
m<=r,
not ArithmeticExcluded mu c Q0 m n r.                  (2.1)
```

The finite cutoff at `N` adds exactly

```text
n+r<N.                                                  (2.2)
```

The positive decimal frequency of the core `(r,n)` is

```text
k(r,n)=10^(n+r)-10^n=10^n(10^r-1)>0.                  (2.3)
```

The `true` orientation has signed frequency `+k(r,n)` and the `false`
orientation has signed frequency `-k(r,n)`. T22 proves that these signed
frequencies are injective on admissible ordered records and that every
surviving cutoff coefficient is exactly one.

Put

```text
e(x)=exp(2*pi*i*x),
P_N(h,alpha)=cutoffFourierSum mu c Q0 m N h alpha.
```

Equivalently, using coefficient one,

```text
P_N(h,alpha)
 = sum over q satisfying (2.1) and E(q)<N of
     e(h signedDecimalFrequency(q) alpha).               (2.4)
```

Here `h` is an integer. In every vector below it is the positive integer in
the inclusive range `1<=h<=H_m`, where

```text
H_m=10^m.                                                (2.5)
```

The exact endpoint-layer vector is

```text
d_E^(m,alpha)(h)=P_(E+1)(h,alpha)-P_E(h,alpha),
                  1<=h<=H_m.                            (2.6)
```

By T22's successor-cutoff theorem, (2.6) contains exactly, once each, the
records satisfying (2.1) and `n+r=E`. In particular, its left endpoint is
`E`, not `E+1`. No block equality or residual collision count occurs in this
definition.

## 3. T24's canonical binary partition and block vectors

Let `N>=1`. Write the nonzero binary digits of `N-1` in strictly decreasing
order

```text
j_1>j_2>...>j_t>=0,
N-1=sum_(i=1)^t 2^(j_i).                                (3.1)
```

For `i=1,...,t`, define

```text
L_i=2^(j_i),
a_i=1+sum_(u<i) L_u,
b_i=a_i+L_i.                                            (3.2)
```

Then T24's `canonicalDyadicPartition N` is the ordered list

```text
P(N)=([a_1,b_1),...,[a_t,b_t)).                         (3.3)
```

It has all of the following exact properties:

```text
[a_1,b_1) disjoint-union ... disjoint-union [a_t,b_t)=[1,N),
b_i=a_i+2^(j_i),
2^(j_i) divides a_i-1,
1<=a_i<b_i<=N.                                          (3.4)
```

For `N=1`, (3.1)-(3.3) are empty. The translated alignment in (3.4), rather
than `2^j | a`, is part of the definition.

For a block `B=[a,b)` in `P(N)`, define its canonical block vector and its
width weight by

```text
Delta_B^(m,alpha)(h)=P_b(h,alpha)-P_a(h,alpha)
                    =sum_(E=a)^(b-1) d_E^(m,alpha)(h),  (3.5)

w(B)=sqrt(b^2-a^2)=sqrt((b-a)(a+b)).                    (3.6)
```

The equality in (3.5) is T24's endpoint telescope. Every block is nonempty,
so `w(B)>0`. The weight records both the literal width `b-a` and the endpoint
location through `a+b`.

T24's canonical telescope also gives, for `m>=1` and `N>=1`,

```text
P_N(h,alpha)=sum_(B in P(N)) Delta_B^(m,alpha)(h).       (3.7)
```

At `N=1`, both sides of (3.7) are zero: the partition is empty and T22's
first cutoff is empty.

## 4. The width-weighted square-function condition

Define the scale

```text
T_s(m,N)=N+N^2 10^(-s m).                               (4.1)
```

For a specified phase `alpha`, define

```text
X_(m,N)(alpha)
 = sum_(B in P(N)) [1/w(B)]
     sum_(h=1)^(H_m) |Delta_B^(m,alpha)(h)|^2.           (4.2)
```

The proposed condition is

```text
WSF(mu,c,Q0,alpha):
  for every real s with 0<s<1,
    there exists a real A_s>=0 such that
      for every pair of integers m,N>=1,
        X_(m,N)(alpha) <= A_s H_m T_s(m,N).              (4.3)
```

The order is

```text
forall s, 0<s<1 -> exists A_s>=0 -> forall m,N>=1.       (4.4)
```

Thus `A_s` is independent of `m,N`, all blocks, and all frequencies. The
hypothesis (4.3) contains neither decimal block equality, residual counts,
nor T12's final cutoff L1 bound. It is a square-function packing condition on
the canonical partition only; it does not demand a bound for every aligned
block as T24's stronger local premise did.

## 5. Exact canonical weight budget

Set

```text
C_w=3/2+sqrt(2).                                        (5.1)
```

We prove the deterministic geometric estimate

```text
sum_(B in P(N)) w(B) <= C_w N                           (5.2)
```

for every `N>=1`.

For `N=1`, the sum is empty. Suppose `N>=2`, let `L_1` be the largest length
in (3.1), and put

```text
R=sum_(i=2)^t L_i=N-1-L_1.                              (5.3)
```

Because the later lengths are distinct powers of two strictly below `L_1`,

```text
0<=R<=L_1-1,
R<N/2.                                                   (5.4)
```

The first block is `[1,1+L_1)`, so

```text
w(B_1)=sqrt((L_1+1)^2-1)<=L_1+1=N-R.                   (5.5)
```

Every later block has `b<=N`, and hence

```text
w(B_i)^2=L_i(a_i+b_i)<=2N L_i.                          (5.6)
```

We need one elementary binary estimate. If distinct powers of two sum to
`R`, then

```text
sum sqrt(L_i) <= (1+sqrt(2)) sqrt(R).                   (5.7)
```

For completeness, induct on the number of powers. If `M` is the largest and
the rest sum to `r<M`, the induction hypothesis and `sqrt(Mr)<=M` give

```text
sqrt(M)+(1+sqrt(2))sqrt(r)
 <= (1+sqrt(2))sqrt(M+r),                               (5.8)
```

because `(1+sqrt(2))^2-1=2(1+sqrt(2))`; squaring the two
nonnegative sides reduces (5.8) to `sqrt(Mr)<=M`.

Combining (5.5)-(5.7),

```text
sum_B w(B)
 <= N-R+(2+sqrt(2))sqrt(NR).                            (5.9)
```

With `x=R/N in [0,1/2]`, the right side divided by `N` is

```text
f(x)=1-x+(2+sqrt(2))sqrt(x).                            (5.10)
```

For `0<=x<=y<=1/2`,

```text
f(y)-f(x)
 =(sqrt(y)-sqrt(x))
   [(2+sqrt(2))-(sqrt(y)+sqrt(x))]>=0.                  (5.11)
```

Therefore `f(x)<=f(1/2)=3/2+sqrt(2)`, proving (5.2). No
factor involving the number of binary blocks appears.

## 6. Deterministic implication to T12

Assume `WSF(mu,c,Q0,alpha)`, fix `0<s<1`, and choose `A_s` as in (4.3).
For `N>=2`, use (3.7), the triangle inequality, and weighted
Cauchy-Schwarz on the finite set of pairs `(B,h)`:

```text
[sum_(h=1)^H_m |P_N(h,alpha)|]^2
 <= [sum_(B,h) |Delta_B(h)|]^2
 <= [sum_(B,h) w(B)]
      [sum_(B,h) |Delta_B(h)|^2/w(B)]
 = H_m [sum_B w(B)] X_(m,N)(alpha).                     (6.1)
```

By (4.3), (5.2), and `N<=T_s(m,N)`,

```text
[sum_(h=1)^H_m |P_N(h,alpha)|]^2
 <= C_w A_s H_m^2 N T_s(m,N)
 <= C_w A_s H_m^2 T_s(m,N)^2.                          (6.2)
```

All quantities are nonnegative, so taking square roots gives

```text
sum_(h=1)^H_m |P_N(h,alpha)|
 <= B_s H_m T_s(m,N),                                  (6.3)

B_s=sqrt(C_w A_s).                                      (6.4)
```

For `N=1`, T22 gives `P_1=0`, so (6.3) also holds. This proves the following
conditional implication, with every multiplier displayed:

```text
WSF(mu,c,Q0,alpha)
  implies the scale-matched cutoff L1 estimate (6.3).    (6.5)
```

In particular, specializing only the implication to `alpha=pi`, T22's
kernel-checked identity

```text
P_N(h,pi)=spectralSum mu c Q0 m N h
```

and `cutoffScaleMatchedL1Bound_iff_T12` give

```text
WSF(mu,c,Q0,pi)
  implies T12.ScaleMatchedL1Bound(mu,c,Q0),              (6.6)
```

with witness `B_s=sqrt((3/2+sqrt(2))A_s)`. Statement
(6.6) is conditional: this note does not assert `WSF(mu,c,Q0,pi)` for any
parameters. It therefore supplies no fixed-pi spectral estimate.

The usual unweighted estimate would pay
`sqrt(|P(N)|)<=sqrt(1+log_2 N)`. Equations (5.2) and (6.1) show that the
width weight removes that deterministic binary-partition logarithm.

## 7. Independent Lebesgue-random phase test

This section fixes arbitrary `mu,c,Q0` and replaces the specified phase by a
Lebesgue-random `alpha in [0,1)`, with normalized measure `lambda`. This is a
sibling model only.

### 7.1 Exact block frequency sets and cardinalities

For `B=[a,b)`, let `Gamma_B` be the set of T22 signed frequencies belonging
to records satisfying the exact conditions

```text
0<r,
m<=r,
not ArithmeticExcluded mu c Q0 m n r,
a<=n+r<b.                                               (7.1)
```

Both orientations occur. T22's injectivity and coefficient-one theorem give

```text
Delta_B(h,alpha)=sum_(omega in Gamma_B) e(h omega alpha).
                                                                    (7.2)
```

Set `C_B=|Gamma_B|`. An exact count retaining the arithmetic exclusion is

```text
C_B=2 * |{(E,r): a<=E<b, m<=r<=E,
                    not ArithmeticExcluded mu c Q0 m (E-r) r}|.     (7.3)
```

No claim that the exclusion vanishes is needed. Dropping it gives

```text
C_B
 <= 2 sum_(E=a)^(b-1) max(E-m+1,0)
 <= 2 sum_(E=a)^(b-1) E
 = (b-a)(a+b-1)
 < (b-a)(a+b)=w(B)^2.                                  (7.4)
```

The second inequality uses `m>=1`. This tracks both ordered signs; there is
no missing factor of two.

### 7.2 Orthogonality and exact first moment

For every integer `z`, direct integration on the half-open probability
interval gives

```text
integral_[0,1) e(z alpha) d alpha
 = 1 if z=0, and 0 otherwise.                           (7.5)
```

Indeed, the `z=0` integrand is one, while for `z!=0` an antiderivative is
`e(z alpha)/(2*pi*i*z)` and its endpoint values agree. All sums here are
finite, so termwise integration is valid.

For every inclusive frequency `1<=h<=H_m`, expand (7.2). Since `h!=0` and
T22's signed frequencies are injective,

```text
integral |Delta_B(h,alpha)|^2 d lambda(alpha)=C_B.       (7.6)
```

Consequently the exact first moment of (4.2) is

```text
E X_(m,N)
 = H_m sum_(B in P(N)) C_B/w(B).                        (7.7)
```

Using (7.4) and (5.2),

```text
E X_(m,N)
 <= H_m sum_B w(B)
 <= C_w H_m N
 <= C_w H_m T_s(m,N).                                  (7.8)
```

Thus the proposed width normalization has exactly the correct random first
moment scale. This improves on a fixed cost per canonical block, which would
introduce a binary block-count logarithm.

### 7.3 Exact centered block covariance

Define

```text
E_B(alpha)=sum_(h=1)^H_m |Delta_B(h,alpha)|^2,
Z_B(alpha)=E_B(alpha)-H_m C_B.                           (7.9)
```

For a positive integer `d`, let

```text
nu_B(d)=|{(omega,omega') in Gamma_B^2:
                         omega-omega'=d}|.              (7.10)
```

Expanding (7.9), grouping positive and negative differences, and using the
symmetry of ordered differences gives the exact finite identity

```text
Z_B(alpha)
 = sum_(d>0) nu_B(d) sum_(h=1)^H_m
     [e(hd alpha)+e(-hd alpha)].                        (7.11)
```

For positive integers `d,e`, define the resonance number

```text
R_H(d,e)=|{(h,k):1<=h,k<=H, hd=ke}|.                    (7.12)
```

Writing `g=gcd(d,e)`, `d=g d_0`, and `e=g e_0`, coprimality forces

```text
h=e_0 ell, k=d_0 ell,
1<=ell<=floor(H g/max(d,e)).
```

Therefore

```text
R_H(d,e)=floor(H gcd(d,e)/max(d,e)).                    (7.13)
```

In the product of (7.11) for blocks `B,C`, orthogonality leaves exactly the
two opposite-sign equations `hd-ke=0` and `-hd+ke=0`. The two same-sign
equations cannot vanish. Hence the exact cross-block covariance is

```text
integral Z_B(alpha) Z_C(alpha) d lambda(alpha)
 = 2 sum_(d,e>0) nu_B(d) nu_C(e)
       floor(H_m gcd(d,e)/max(d,e)).                    (7.14)
```

In particular, every covariance in (7.14) is nonnegative. There is no hidden
probabilistic independence and no covariance cancellation to invoke.

Since

```text
X_(m,N)-E X_(m,N)=sum_B Z_B/w(B),                       (7.15)
```

(7.14) gives the exact variance

```text
Var X_(m,N)
 = 2 sum_(B,C in P(N)) 1/[w(B)w(C)]
     sum_(d,e>0) nu_B(d)nu_C(e)
       floor(H_m gcd(d,e)/max(d,e)).                    (7.16)
```

This independently rederives every finite moment identity used below.

### 7.4 What the present T16 estimate gives

Define the cross-block weighted resonance quantity

```text
G_(m,N)
 = sum_(B,C in P(N)) 1/[w(B)w(C)]
     sum_(d,e>0) nu_B(d)nu_C(e)
       gcd(d,e)/max(d,e).                               (7.17)
```

Each positive difference in (7.10) maps injectively to the T16 four-token
record. More explicitly, signed-frequency injectivity gives a unique
admissible ordered record `q_B(omega)` representing each `omega in Gamma_B`.
The map for a pair `(omega,omega')` is

```text
(first(q_B(omega)), second(q_B(omega')),
 second(q_B(omega)), first(q_B(omega'))).               (7.18)
```

All four exponents lie in the half-open box `0,...,N-1`, both represented
lags obey the weak inequality `m<=lag`, and the signed four-token value is
`omega-omega'=d>0`. Blocks are disjoint in endpoint, so summing their
within-block difference multiplicities gives a subfamily of T16's global
difference domain. The GCD kernel is nonnegative.

Every canonical block has `a>=1` and `b>=a+1`, so

```text
w(B)^2=(b-a)(a+b)>=3,
1/[w(B)w(C)]<=1/3.                                      (7.19)
```

T16's machine-checked theorem therefore gives

```text
G_(m,N)
 <= (574913232/3) N^4
 = 191637744 N^4.                                       (7.20)
```

Using `floor(x)<=x` in (7.16),

```text
Var X_(m,N)
 <= 2 H_m G_(m,N)
 <= 383275488 H_m N^4.                                 (7.21)
```

This is parameter-uniform and uses no phase estimate.

## 8. Exact metric obstruction from the available moments

Fix `0<s<1` and put

```text
rho=10^(-s m),
T_s(m,N)=N(1+N rho).                                    (8.1)
```

First-moment Markov applied to (7.8) gives, for `A>0`,

```text
lambda{X_(m,N)>A H_m T_s(m,N)}
 <= C_w/[A(1+N rho)].                                   (8.2)
```

For each fixed `m`, summing (8.2) over every `N` diverges harmonically.

For the centered estimate, suppose `A>=2C_w`. If
`X_(m,N)>A H_m T_s(m,N)`, then (7.8) implies

```text
X_(m,N)-E X_(m,N)>(A/2)H_m T_s(m,N).                   (8.3)
```

Chebyshev and (7.21) give the explicit bound

```text
lambda{X_(m,N)>A H_m T_s(m,N)}
 <= [8*574913232/(3 A^2 H_m)]
      N^2/(1+N rho)^2
 = [1533101952/(A^2 H_m)]
      N^2/(1+N rho)^2.                                 (8.4)
```

For fixed `m`, the last factor tends to `rho^(-2)` as `N` tends to infinity.
Thus the available upper bound does not even decay in `N`. Equations
(8.2)-(8.4) prove neither almost-everywhere compatibility nor refutation of
(4.3). They identify the failure precisely: the global T16 estimate discards
the canonical widths and leaves `N^4`, whereas summability needs a
width-sensitive cross-block estimate near `N^2`, allowing logarithmic loss.

This is not a logarithmic obstruction in the deterministic reduction:
Section 6 has none. It is a cross-block resonance obstruction in the present
metric proof.

## 9. One precisely quantified inequality sufficient for closure

The following is the exact missing arithmetic cancellation/sparsity estimate:

```text
There exists an absolute real K>=0 such that, for every
mu,c in R and Q0,m,N in N with m,N>=1,

  G_(mu,c,Q0;m,N) <= K N^2 log(2N).                     (CROSS)
```

Here `G_(mu,c,Q0;m,N)` is exactly (7.17), whose suppressed parameters are now
shown, with T22's arithmetic exclusions, both
ordered orientations, T24's canonical blocks, and the weight
`w(B)=sqrt(b^2-a^2)` retained. `(CROSS)` is not proved in this note.

We verify that it would close the metric test. Under `(CROSS)`, (7.16) gives

```text
Var X_(m,N)<=2K H_m N^2 log(2N).                        (9.1)
```

Take the fixed threshold

```text
A_0=C_w+1=5/2+sqrt(2).                                  (9.2)
```

By (7.8), the event `X_(m,N)>A_0 H_m T_s(m,N)` forces
`X_(m,N)-E X_(m,N)>H_m T_s(m,N)`. Consequently,

```text
lambda{X_(m,N)>A_0 H_m T_s(m,N)}
 <= 2K log(2N)/[H_m(1+rho N)^2].                        (9.3)
```

For completeness, the needed sum has an explicit bound. For `0<rho<=1`, let
`M=ceil(1/rho)`. Since `M<=2/rho`,

```text
sum_(N=1)^M log(2N)/(1+rho N)^2
 <= (2/rho) log(4/rho).                                 (9.4)
```

The function `log(2x)/x^2` decreases for `x>=1`. Therefore

```text
sum_(N=M+1)^infinity log(2N)/(1+rho N)^2
 <= rho^(-2) integral_M^infinity log(2x)/x^2 dx
 = rho^(-2)[log(2M)+1]/M
 <= rho^(-1)[log(4/rho)+1].                             (9.5)
```

Since `log(4/rho)>=log 4>1`, (9.4)-(9.5) imply

```text
sum_(N=1)^infinity log(2N)/(1+rho N)^2
 <= (4/rho) log(4/rho).                                 (9.6)
```

Substituting `H_m=10^m` and `rho=10^(-s m)` into (9.3)-(9.6) gives

```text
sum_(m,N>=1)
 lambda{X_(m,N)>A_0 H_m T_s(m,N)}
 <= 8K sum_(m>=1) 10^(-(1-s)m)
      [log 4+s m log 10]
 < infinity.                                            (9.7)
```

The first Borel-Cantelli lemma, requiring no independence, would then show
that almost every `alpha` violates the threshold for only finitely many
pairs `(m,N)`. All functions involved are finite sums of continuous
trigonometric functions, so the events are measurable. If `F_s(alpha)` is
the finite set of exceptional pairs, the explicit absorption is

```text
A_s(alpha)=max(A_0,
  max_{(m,N) in F_s(alpha)}
    X_(m,N)(alpha)/[H_m T_s(m,N)]),                     (9.8)
```

with the second maximum interpreted as zero when the set is empty. Its
denominators are positive, so this is finite and proves (4.3) for that `s`.

Finally, intersect the full-measure sets for rational `t in (0,1)`. Given a
real `0<s<1`, choose rational `s<t<1`. Since

```text
T_t(m,N)<=T_s(m,N),                                     (9.9)
```

the bound at `t` implies the bound at `s`. Thus `(CROSS)` would prove
`WSF(mu,c,Q0,alpha)` for almost every phase, simultaneously for every real
`0<s<1`.

The single `log(2N)` in `(CROSS)` is tolerated, not proved necessary. The
canonical partition can have `log_2 N` blocks when `N` is a power of two, but
the weight already removes that count from the deterministic and first-moment
arguments. The unresolved issue is the weighted interaction of positive
differences across distinct canonical blocks.

## 10. Terminal verdict

**Proved deterministic implication (artifact verification level: `proof
sketch`).** With the exact T22 endpoint layers, T24 canonical partition,
inclusive range `1<=h<=10^m`, and weights

```text
w([a,b))=sqrt(b^2-a^2),
```

the condition (4.3) implies T12's scale-matched L1 predicate with the explicit
constant transfer

```text
B_s=sqrt((3/2+sqrt(2)) A_s).                             (10.1)
```

There is no deterministic binary-partition logarithm.

**Metric sibling obstruction.** For Lebesgue-random phase, the independently
derived exact first moment and available variance estimate are

```text
E X_(m,N)=H_m sum_B C_B/w(B)
          <= (3/2+sqrt(2)) H_m N,

Var X_(m,N)<=383275488 H_m N^4.                         (10.2)
```

These finite estimates neither prove nor refute almost-everywhere (4.3).
They fail to close because the `N^4` cross-block weighted-GCD bound gives the
nonsummable probability estimate (8.4). The precisely quantified inequality
needed for the displayed Borel-Cantelli closure is `(CROSS)`:

```text
G_(m,N)<=K N^2 log(2N) for all m,N>=1.                  (10.3)
```

Thus the proposed width normalization passes the random first-moment test and
the deterministic T12 implication, while the remaining issue is exactly the
cross-block resonance estimate (10.3). No assertion in this note estimates
the fixed phase `alpha=pi`, establishes a property of pi's decimal digits, or
settles C1.
