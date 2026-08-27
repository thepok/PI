# T82: signed shift summation by parts before Cauchy

Claim label: `proof sketch`. The imported T69, T74, T76, and T81
declarations cited below are `machine-checked`; the new finite derivation in
this note is written for direct inspection but is not itself formalized.

Date: 2026-08-06 UTC.

## 1. Provenance, normalized statement, and scope

The canonical question is the locally formulated statement in
`CANONICAL_STATEMENT.txt`; it has no external source URL. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

It asks whether, for every real `s` with `0<s<1`, one constant `C_s>=1`
works simultaneously for all positive integers `m,N` in the ordered
long-lag collision estimate

```text
R_pi(m,N) <= C_s*(N+N^2*10^(-s*m)).
```

This note does not answer or alter that question. It concerns only T69's
residual-A12, `m=1`, dyadic primitive-sector sibling. Throughout,

```text
N = N_t = 4*2^t+1,
H = H_t = ceil(sqrt(N_t)),
t is a natural number.
```

Thus favorable dyadic scales here are not favorable scales for the canonical
collision count, and a constant in this calculation is not a canonical
`C_s`. No statement below concerns the full T29 predicate, C2, or C1.

The kernel interfaces used, rather than rederived, are

```lean
import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
import TheoryLib.PiLongLagBlockCollisionDecay.T74T74T74MultiplierNineCoefficientFiber
import TheoryLib.PiLongLagBlockCollisionDecay.T76T76VariablePhasePooledHalfArc
import TheoryLib.PiLongLagBlockCollisionDecay.T81T81AdjacentIndexPairing
```

Their retained source SHA-256 values are

```text
T69  09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
T74  8c56052df1deda2acdf01253ffe06ed8451a1647e834faf228a7edf003d9f896
T76  7e8c65c5dcae4232da496646e7e9778f5aaf8067feb18875beb04c0d6b794fe7
T81  6a85bb7cece8c58cc945fc850b0257a646211ce31215b8cbeda3cbd020337d76
```

T74 is comparison context: its obstruction occurs in a pooled Laurent square.
The obstruction in Section 8 below occurs in the linear, signed, pre-Cauchy
shift decomposition and is not an invocation or restatement of T74.

## 2. The exact T69 expression

Put

```text
e(x)       = exp(2*pi*i*x),
f_r        = 10^r-1,
L_r        = N-r,
w_r        = H-r,
x_(h,r,k)  = e(h*f_r*10^k*pi).
```

The first `pi` in the definition of `e` is the circle normalization. The last
`pi` in `x_(h,r,k)` is the prescribed real phase.

T69's `aggregateEnergy_literal` and
`aggregateEnergy_eq_real_aggregateShiftedSum` give the exact signed complex
sum

```text
A_t(pi)
  = sum_(h=1)^10 sum_(r=1)^(H-1) (H-r)
      sum_(k=0)^(N-r-1) x_(h,r,k),                       (2.1)

aggregateEnergy(t) = 10*H*N + 2*Re A_t(pi).              (2.2)
```

Equivalently, every domain is literal:

```text
1 <= h <= 10,
1 <= r < H,
0 <= k < N-r,
weight H-r.                                               (2.3)
```

There is no modulus or Cauchy step in (2.1). T69's `H_le_N` gives `H<=N`,
while the transitively imported T68 theorem `three_le_H` gives `3<=H`.
Consequently, for every `1<=r<=H-2`, one has `L_r=N-r>=2`; this fact
justifies all endpoint splits below, including when an indicated interior sum
is empty.

## 3. Compress exactly the T76/T81 equal-frequency classes

For fixed `h,r`, define

```text
F_(h,r) = sum_(k=0)^(L_r-1) x_(h,r,k).                   (3.1)
```

T76's `pooledFrequency_eq_iff` and
`literal_T69_frequencyClass_iff`, exposed in T81 as
`equalFrequencyClass_exact`, say that the only nontrivial equal-frequency
class in the complete domain is

```text
x_(10,r,k) = x_(1,r,k+1).                                (3.2)
```

There are no equal-frequency collisions between distinct shifts, and none
involving `h=2,...,9`. T81's `leftBoundary_frequencyClass` and
`rightBoundary_frequencyClass` certify the two singleton endpoints. Therefore

```text
F_(1,r)+F_(10,r)
  = x_(1,r,0)
    + 2*sum_(j=1)^(L_r-1) x_(1,r,j)
    + x_(1,r,L_r).                                       (3.3)
```

Define the compressed channel

```text
C_r = x_(1,r,0)
      + 2*sum_(j=1)^(L_r-1) x_(1,r,j)
      + x_(1,r,L_r)
      + sum_(h=2)^9 sum_(j=0)^(L_r-1) x_(h,r,j).         (3.4)
```

The `h=10` channel has not been discarded: its left-shifted interior supplies
the second copy in (3.3), and its terminal term is `x_(1,r,L_r)`. Equations
(3.1)--(3.4) give, before any other operation,

```text
C_r = sum_(h=1)^10 F_(h,r),
A_t(pi) = sum_(r=1)^(H-1) w_r*C_r.                       (3.5)
```

This is the only equal-frequency compression used in the note.

## 4. The adjacent-shift recurrence with exact common endpoints

The decimal recurrence is

```text
f_(r+1) = 10*f_r+9.                                      (4.1)
```

For `h>=1` and `k>=0`, put

```text
mu_(h,k) = e(9*h*10^k*pi).                               (4.2)
```

Additivity of `e` and (4.1) give the termwise identity

```text
x_(h,r+1,k) = x_(h,r,k+1)*mu_(h,k).                      (4.3)
```

The two shifts `r,r+1` are simultaneously active exactly for

```text
k < N-r and k < N-(r+1)
  iff k < N-max(r,r+1)
  iff 0 <= k <= N-r-2.                                  (4.4)
```

The first equivalence is T81's `unequalCutoff_iff`; no endpoint is replaced by
`N-r` or by `N`. Reindexing (4.4) by `j=k+1` gives
`1<=j<=L_r-1`.

For each unchanged channel `2<=h<=9`, (4.3) yields

```text
F_(h,r+1)-F_(h,r)
  = -x_(h,r,0)
    + sum_(j=1)^(L_r-1)
        x_(h,r,j)*(mu_(h,j-1)-1).                        (4.5)
```

The already-compressed `h=1,10` class must be treated with its unequal
endpoint coefficients. Applying (4.3) to (3.3), whose next length is
`L_(r+1)=L_r-1`, gives

```text
(F_(1,r+1)+F_(10,r+1))-(F_(1,r)+F_(10,r))
  = -x_(1,r,0)-x_(1,r,1)
    + x_(1,r,1)*(mu_(1,0)-1)
    + 2*sum_(j=2)^(L_r-1)
        x_(1,r,j)*(mu_(1,j-1)-1)
    + x_(1,r,L_r)*(mu_(1,L_r-1)-1).                     (4.6)
```

For a direct endpoint check, the positive part before subtraction is

```text
x_(1,r,1)*mu_(1,0)
  + 2*sum_(j=2)^(L_r-1) x_(1,r,j)*mu_(1,j-1)
  + x_(1,r,L_r)*mu_(1,L_r-1),                           (4.7)
```

whereas (3.3) is

```text
x_(1,r,0)+2*x_(1,r,1)
  +2*sum_(j=2)^(L_r-1)x_(1,r,j)+x_(1,r,L_r).
```

Their difference is exactly (4.6), including its two negative boundary terms
and the terminal coefficient one.

Define the boundary and multiplier-nine parts

```text
beta_r
  = -x_(1,r,0)-x_(1,r,1)-sum_(h=2)^9 x_(h,r,0),         (4.8)

Gamma_r
  = x_(1,r,1)*(mu_(1,0)-1)
    +2*sum_(j=2)^(L_r-1)
       x_(1,r,j)*(mu_(1,j-1)-1)
    +x_(1,r,L_r)*(mu_(1,L_r-1)-1)
    +sum_(h=2)^9 sum_(j=1)^(L_r-1)
       x_(h,r,j)*(mu_(h,j-1)-1).                         (4.9)
```

Equations (4.5)--(4.9) give the complete compressed adjacent-shift identity

```text
C_(r+1)-C_r = beta_r+Gamma_r,    1<=r<=H-2.              (4.10)
```

Every factor in `Gamma_r` is a fixed-`pi` multiplier-nine correlation. No
absolute value has been taken.

## 5. Discrete summation by parts in the shift variable

Define

```text
W   = H*(H-1)/2,
b_r = (H-r)*(H-r-1)/2,    1<=r<=H-2.                    (5.1)
```

The finite triangular sums are

```text
sum_(r=1)^(H-1) (H-r) = W,                              (5.2)

sum_(u=r+1)^(H-1) (H-u)
  = 1+2+...+(H-r-1)
  = b_r.                                                  (5.3)
```

Since

```text
C_r = C_1+sum_(u=1)^(r-1)(C_(u+1)-C_u),                 (5.4)
```

substitution into (3.5), followed only by exchanging finite sums, gives

```text
A_t(pi)
  = W*C_1
    +sum_(r=1)^(H-2)b_r*(C_(r+1)-C_r).                  (5.5)
```

This is discrete summation by parts with the original triangular weight; no
positive majorant has replaced it.

## 6. Complete boundary/correlation identity and constants

Substitute (4.10) into (5.5). The exact boundary term is

```text
B_t
  = W*C_1
    -sum_(r=1)^(H-2)b_r*
       (x_(1,r,0)+x_(1,r,1)+sum_(h=2)^9 x_(h,r,0)),      (6.1)
```

and the exact multiplier-nine correlation term is

```text
R_t = sum_(r=1)^(H-2)b_r*Gamma_r,                        (6.2)
```

with `Gamma_r` given literally by (4.9). Thus

```text
A_t(pi) = B_t+R_t,                                       (6.3)

aggregateEnergy(t)
  = 10*H*N + 2*Re(B_t+R_t).                              (6.4)
```

Equations (3.4), (4.8), (4.9), (5.1), and (6.1)--(6.4)
are the requested constant-tracked finite identity. They expose:

```text
h domain:               1,...,10 before exact compression;
r domain in A_t:        1,...,H-1;
r domain in R_t:        1,...,H-2;
common orbit cutoff:    k=0,...,N-r-2 in an (r,r+1) block;
compressed index:       j=k+1;
original weight:        H-r;
summation coefficient:  b_r=(H-r)*(H-r-1)/2;
initial boundary:       W*C_1, W=H*(H-1)/2;
local boundaries:       the three terms displayed in (4.8);
outer constants:        10*H*N and 2*Re in (6.4).
```

In particular, (6.3) is not T69 restated under a new name: (4.9) displays the
new adjacent-shift multiplier-nine factors and (6.1) displays every term left
outside them.

## 7. What counts as a two-shift block obstruction

The numerical value of `R_t(pi)` may exhibit cancellation. The quantitative
exit below therefore makes a narrower, purely algebraic statement about the
specific separated two-shift representation produced by (4.3)--(4.10).

An **admissible separated presentation** keeps each occurrence

```text
a*x_(h,r,j)*(mu_(h,j-1)-1)                               (7.1)
```

in (4.9) as its own adjacent-shift block, with its displayed multiplicity
`a=1` or `a=2`. It may display that block in either of the equivalent
orientations

```text
a*(x_(h,r+1,j-1)-x_(h,r,j))
```

or

```text
-a*(x_(h,r,j)-x_(h,r+1,j-1)).                           (7.2)
```

Both orientations have formal two-term coefficient mass `2*a`. Multiplication
by `b_r` makes it `2*b_r*a`. Hence every admissible orientation choice has the
same separated mass. Cross-block coefficient collection is deliberately not
part of this definition: such collection is a different cancellation
mechanism and may reduce formal mass.

At fixed `r`, the compressed `h=1,10` part of (4.9) has total multiplicity

```text
1 + 2*(L_r-2) + 1 = 2*(L_r-1).                          (7.3)
```

The eight unchanged channels have total multiplicity

```text
8*(L_r-1).                                               (7.4)
```

Thus all ten original channels are retained, and the total multiplicity is
exactly

```text
10*(L_r-1)=10*(N-r-1).                                  (7.5)
```

The separated two-shift coefficient mass is consequently

```text
P_t
  = sum_(r=1)^(H-2) 2*b_r*10*(N-r-1)
  = 10*sum_(r=1)^(H-2)
      (H-r)*(H-r-1)*(N-r-1).                            (7.6)
```

No inequality has been applied to `R_t` in deriving (7.6). In particular,
`P_t` is not used as a positive-weight majorant for `|R_t|`, and (7.6) does
not imply that `R_t(pi)`, `A_t(pi)`, or their real parts are large.

## 8. Quantitative exit: an explicit infinite supertarget family

Take the infinite even-scale family

```text
t=2*m,
q=2^(m+1),
m>=0.                                                     (8.1)
```

T81's `N_evenScale` and `H_evenScale` give

```text
N_(2m)=q^2+1,
H_(2m)=q+1,
q>=2.                                                     (8.2)
```

Substitute (8.2) into (7.6). The range `1<=r<=H-2` becomes
`1<=r<=q-1`, so

```text
P_(2m)
  = 10*sum_(r=1)^(q-1)
      (q+1-r)*(q-r)*(q^2-r).                            (8.3)
```

Set `j=q-r`. Then `1<=j<=q-1` and `q^2-r=q*(q-1)+j`, giving

```text
P_(2m)
  = 10*sum_(j=1)^(q-1) j*(j+1)*(q*(q-1)+j).             (8.4)
```

The two required elementary sums are

```text
sum_(j=1)^(q-1) j*(j+1)
  = q*(q-1)*(q+1)/3,                                    (8.5)

sum_(j=1)^(q-1) j^2*(j+1)
  = q*(q-1)*(3*q^2+q-2)/12.                             (8.6)
```

Using (8.5)--(8.6) in (8.4) yields the exact polynomial

```text
P_(2m)
  = (5/6)*q*(q-1)*(q+1)*(4*q^2-q-2).                    (8.7)
```

The divisibility implicit in (8.7) is automatic because its left side is the
integer sum (8.3); the equality is in the reals for normalization below.

Since `q>=2`,

```text
4*q^2-q-2 >= 2*(q^2+1),                                 (8.8)
```

because the difference is `2*q^2-q-4>=2`. Dividing (8.7) by the positive T69
target normalization from (8.2) gives

```text
P_(2m)/(H_(2m)*N_(2m))
  = (5/6)*q*(q-1)*(4*q^2-q-2)/(q^2+1)
  >= (5/3)*q*(q-1)
  >= (5/6)*q^2
  = (5/6)*4^(m+1).                                      (8.9)
```

Therefore, for every real `C`, there exists `m>=0` such that

```text
C*H_(2m)*N_(2m) < P_(2m).                               (8.10)
```

For `C>=0`, it suffices to choose `m` with
`4^(m+1)>6*C/5`; for `C<0`, every `m` works because `P_(2m)>0`.

Equations (8.1), (8.7), and (8.10) are the third quantitative exit requested
for T82. They show that every admissible orientation of the separated
adjacent two-shift blocks in the signed pre-Cauchy identity retains
supertarget coefficient mass on an explicit infinite scale family. This is
not T81's equal-frequency mass: T81 counts the positive equal-frequency
`h=1,10` pairs in the original linear sum, whereas (8.7) counts all ten
channels after the recurrence and the Abel coefficients `b_r`. It is also not
T74's post-square multiplier-nine Laurent fiber.

## 9. Exact conclusion and limitations

The finite identity (6.3) succeeds: equal-frequency compression is performed
first, all endpoints and signs are retained, and summation by parts converts
the shift change into the fixed-`pi` multiplier-nine correlations (4.9).

The proposed route does not by itself prove the T69 bound. The obstruction
(8.10) says that taking the two terms of each recurrence block separately,
in either orientation, leaves coefficient mass much larger than `H*N`.
Therefore a proof cannot finish by assigning a positive cost to each separated
two-shift block. It would need cancellation between different blocks, a direct
fixed-`pi` estimate for their combined signed value, or another mechanism.

Coefficient mass is not a lower bound after evaluation. Distinct blocks and
the boundary term (6.1) may cancel at `pi`. Accordingly, this note proves no
fixed-`pi` aggregate estimate, no failure of that estimate, no primitive
budget, no full T29 predicate, and no conclusion for C2, C1, or the canonical
ordered collision question.

## 10. Skeptic checklist

1. Hash `CANONICAL_STATEMENT.txt` and compare it with Section 1.
2. Compare (2.1)--(2.3) with T69's `aggregateEnergy_literal`.
3. Check that (3.2)--(3.4) use exactly the T76/T81 class and retain both endpoints.
4. Expand `10^(r+1)-1=10*(10^r-1)+9` to verify (4.3).
5. Check the common cutoff `k<N-max(r,r+1)=N-r-1` in (4.4).
6. Subtract the two compressed endpoint lists to verify every sign in (4.6).
7. Check the triangular sums (5.2)--(5.3) and the Abel identity (5.5).
8. Substitute (4.8)--(4.9) into (5.5) to verify (6.1)--(6.4).
9. Count the compressed multiplicities in (7.3)--(7.5); no phase estimate is used.
10. Verify the even-scale substitution, sums (8.5)--(8.6), polynomial (8.7), and constants in (8.8)--(8.10).
