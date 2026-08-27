# T72: pooled `(h,r)` dispersion and its diagonal barrier

Claim label: `proof sketch` (all arguments below are finite and elementary,
but this note is not machine-checked).

Date: 2026-08-03 UTC.

## 1. Provenance, statement, and scope

The canonical question is the locally formulated statement
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`; it has no external
source URL. A byte-exact copy is delivered as `CANONICAL_STATEMENT.txt`, with
SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks for one `C_s` before all positive `m,N`, for each
`0<s<1`, in an ordered long-lag decimal-block collision estimate. This note
does not answer or modify that question. Its target is the distinct residual
A12, `m=1`, dyadic primitive-sector sibling isolated by T69 and T70.

The established input is the kernel-checked module

```lean
import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
```

whose retained source has SHA-256

```text
09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
```

In particular, this note imports T69's finite identities and conditional
implications; it does not re-prove or assert any of T69's analytic hypotheses.
The T71 note is only unverified variable-phase motivation. No claim from T71
is used as a premise here.

The quantifier distinctions that cannot be changed are:

1. the phase in the target is the prescribed real number `pi`, not almost
   every phase and not an averaged phase;
2. one constant must work before every natural scale `t`;
3. the target is one-sided in the real part, not an absolute-value estimate;
4. pooling must retain cancellation between all `(h,r)` channels;
5. a failure of a particular dispersion majorant is not a failure of the
   original fixed-`pi` estimate.

## 2. Literal T69/T70 data

For every natural `t`, put

```text
N = N_t = 4*2^t+1,
H = H_t = ceil(sqrt(N)),
q_r = 10^r-1,
a_(h,r) = h*q_r,
w_r = H-r,
L_r = N-r,
e(x) = exp(2*pi*i*x).
```

The first `pi` in `e` is the circle normalization. The prescribed phase is the
second `pi` below. T70's literal fixed-point sum is

```text
A_t(pi)
  = sum_(h=1)^10 sum_(r=1)^(H-1) w_r
      sum_(k=0)^(L_r-1) e(a_(h,r)*10^k*pi).              (2.1)
```

Thus every domain and weight is literally

```text
1 <= h <= 10,  1 <= r < H,  0 <= k < N-r,  weight H-r. (2.2)
```

The fixed-`pi` estimate `(FP)` is

```text
there exists C >= 0 such that, for every natural t,
  Re A_t(pi) <= C*H_t*N_t.                               (FP)
```

T69's kernel-checked identity is

```text
aggregateEnergy(t) = 10*H_t*N_t + 2*Re A_t(pi).          (2.3)
```

Consequently `(FP)` would give T69's aggregate constant

```text
K = 10+2*C.                                              (2.4)
```

For audit purposes, the other T69 constants remain exactly as follows. Under
an aggregate hypothesis with constant `K`, T69 conditionally gives

```text
sum_(h=1)^10 X_h(N_t)^2 <= (9/4)*K^2*N_t^3.              (2.5)
```

Its selected-plus-defect expression has literal numerator

```text
sum_h X_h(N_t)^2 - 4*(N_t-1)*sum_h X_h(N_t)
  + 20*N_t^2 - 30*N_t,                                  (2.6)
```

and literal denominator `sqrt(N_t^2-1)`. For `0<s<1`, its conditional
specialized primitive-sector budget has constant and scale

```text
10*((45/16)*K^2+5) * (N_t+N_t^2*10^(-s)).               (2.7)
```

None of (2.4)--(2.7) is asserted unconditionally.

### 2.1 Half-open half-arcs

T69 represents the circle by `[-1/2,1/2)` and uses the centered translated
half-arc

```text
I_y = {x : centeredRepresentative(x-y) in [-1/4,1/4)}.   (2.8)
```

The left endpoint is included and the right endpoint is excluded. The
complementary orientation is literal nonmembership in (2.8), so it is also a
half-open half-arc with the opposite endpoint convention. For one common arc
center `y`, T69's pooled excess is

```text
P_t(y) = sum_(h=1)^10 sum_(r=1)^(H-1) (H-r) *
  (#{0 <= k < N-r :
       centeredRepresentative(a_(h,r)*10^k*pi-y)
         in [-1/4,1/4)} - (N-r)/2).                     (2.9)
```

The exact total pre-arc mass is

```text
M_t = 10*sum_(r=1)^(H-1) (H-r)(N-r)
    = 10*H*(H-1)*(3*N-H-1)/6.                           (2.10)
```

The kernel-checked T69 implications retain the distinct constants

```text
Delta >= 0 and |P_t(y)| <= Delta*H_t*N_t for all t,y
  implies K = 10+2*pi*Delta;                             (2.11)

Delta >= 0 and the stronger separate-shift T68 discrepancy premise
  implies K = 10*(1+pi*Delta).                           (2.12)
```

No discrepancy bound is assumed or proved in this note. Equations
(2.8)--(2.12) only pin the exact T69 interface, including its endpoints and
constants, before the separate dispersion calculation begins.

## 3. Exact finite regrouping in the pooled variables

Since `N>=5`, one has `H>=3` and `H<N`. The longest orbit in (2.1) is the
`r=1` orbit, with `0<=k<N-1`. Hence the union of all `k` domains is exactly

```text
0 <= k <= N-2.                                           (3.1)
```

For such a `k`, define the active endpoint

```text
R_k = min(H-1,N-k-1).                                    (3.2)
```

The condition `1<=r<=R_k` is equivalent to the original pair of conditions
`1<=r<H` and `k<N-r`. Define

```text
B_k(alpha)
  = sum_(h=1)^10 sum_(r=1)^(R_k)
      w_r*e(a_(h,r)*10^k*alpha).                         (3.3)
```

All sums are finite, so exchanging the `r` and `k` summations in (2.1) gives
the exact identity

```text
A_t(alpha) = sum_(k=0)^(N-2) B_k(alpha).                 (3.4)
```

There are exactly `N-1` values of `k`, not `N`. Cauchy--Schwarz gives

```text
|A_t(alpha)|^2 <= (N-1)*E_t(alpha),
E_t(alpha) = sum_(k=0)^(N-2) |B_k(alpha)|^2.             (3.5)
```

The exact Cauchy defect is

```text
(N-1)*E_t(alpha)-|A_t(alpha)|^2
  = sum_(0<=k<ell<=N-2) |B_k(alpha)-B_ell(alpha)|^2.     (3.6)
```

Thus (3.5) is the only inequality so far. This is dispersion in the pooled
`(h,r)` variables at each fixed `k`; it is not T65's differencing in `k`.

## 4. Exact double-shift expansion

For two channels `(h,r)` and `(h',r')`, put

```text
d(h,r;h',r')
  = a_(h,r)-a_(h',r')
  = h*(10^r-1)-h'*(10^r'-1).                            (4.1)
```

Both channels occur at a common `k` exactly when

```text
k < min(N-r,N-r') = N-max(r,r').                        (4.2)
```

Expanding every square in (3.5), then exchanging finite sums, gives

```text
E_t(alpha)
 = sum_(h=1)^10 sum_(h'=1)^10
    sum_(r=1)^(H-1) sum_(r'=1)^(H-1)
      w_r*w_r' *
      sum_(k=0)^(N-max(r,r')-1)
        e(d(h,r;h',r')*10^k*alpha).                     (4.3)
```

This proves the requested unequal-orbit expansion. In particular, replacing
the common length by `N-r`, `N-r'`, or a rectangular `N` would not be the
literal finite regrouping.

Although the right side of (4.3) is written as a complex ordered sum, it is
real and nonnegative: reversing the ordered pair negates `d` and supplies the
complex conjugate.

## 5. Complete frequency classification

For a nonzero integer `d`, define its decimal valuation and signed primitive
multiplier by

```text
v_10(d) = max{v>=0 : 10^v divides d} = min(v_2(d),v_5(d)),
p(d) = d/10^v_10(d).                                    (5.1)
```

Then `10` does not divide `p(d)`. This use of "primitive" does not require
`p(d)` to be coprime to `10`: it may still be divisible by `2` or by `5`.

### Lemma 5.1: the diagonal

For the domains in (2.2),

```text
d(h,r;h',r')=0 iff (h,r)=(h',r').                       (5.2)
```

Indeed, if `r>r'`, then

```text
(10^r-1)/(10^r'-1)
  >= (10^(r'+1)-1)/(10^r'-1) > 10,                     (5.3)
```

whereas equality in (5.2) would make this ratio `h'/h<=10`. The strict
inequality in (5.3) handles the endpoint pair `h=1,h'=10`. Interchanging the
channels excludes `r'<r` in the other direction. Thus `r=r'`, after which
`h=h'`.

### Lemma 5.2: off-diagonal classes

Every off-diagonal ordered pair belongs to exactly one of the following two
classes.

**Class O0: `h != h'`.** Since `10^r-1` and `10^r'-1` are both `-1` modulo
`10`,

```text
d(h,r;h',r') = h'-h (mod 10).                           (5.4)
```

The residues of `1,...,10` modulo `10` are distinct. Therefore

```text
v_10(d)=0,
p(d)=h*(10^r-1)-h'*(10^r'-1).                           (5.5)
```

This class allows all `1<=r,r'<H`. There are no hidden positive-valuation
subclasses.

**Class O+: `h=h'` and `r!=r'`.** Put

```text
m = min(r,r'),
delta = |r-r'|,
sigma = sign(r-r'),
epsilon_h = 1 if h=10 and 0 if 1<=h<=9,
h_0 = h/10^epsilon_h.                                   (5.6)
```

Direct factorization gives

```text
d = sigma*h*10^m*(10^delta-1),
v_10(d) = m+epsilon_h,
p(d) = sigma*h_0*(10^delta-1).                          (5.7)
```

Because `delta>=1`, `10^delta-1` is `-1` modulo `10`, so (5.7) has removed
the complete power of `10`. Classes D from (5.2), O0 from (5.5), and O+ from
(5.7) exhaust every ordered channel pair in (4.3).

For later display define the finite primitive correlation

```text
C_(v,p)(L;alpha)
  = sum_(k=0)^(L-1) e(p*10^(v+k)*alpha),                (5.8)
```

where `L>=1` and `10` does not divide `p`. Equations (4.1) and (5.1) imply the
exact identity

```text
sum_(k=0)^(L-1)e(d*10^k*alpha)
  = C_(v_10(d),p(d))(L;alpha).                          (5.9)
```

Its exponent interval is literally
`v_10(d) <= n <= v_10(d)+L-1`.

### 5.3 Explicit real form

Separate one representative from each conjugate pair. For `h<h'`, let

```text
d_(h,r;h',r') = h*(10^r-1)-h'*(10^r'-1).               (5.10)
```

Then (4.3) is exactly

```text
E_t(alpha) = D_t
 + 2*Re sum_(1<=h<h'<=10) sum_(r,r'=1)^(H-1)
     w_r*w_r' * C_(0,d_(h,r;h',r'))(N-max(r,r');alpha)
 + 2*Re sum_(h=1)^10 sum_(1<=r<r'<H)
     w_r*w_r' *
     C_(r+epsilon_h,-h_0*(10^(r'-r)-1))(N-r';alpha).
                                                               (5.11)
```

The diagonal in this formula is

```text
D_t = 10*sum_(r=1)^(H-1) (H-r)^2*(N-r).                (5.12)
```

The factor `10` counts the ten diagonal values of `h`; the orbit length is
`N-r`, and the squared triangular weight is `(H-r)^2`.

The same-`k` diagonal (5.2) must not be confused with frequency collisions in
the un-Cauchied full square of (2.1). In that full square, the elementary
identity

```text
(10^r-1)*10^j = 10*(10^r-1)*10^(j-1),  j>=1,           (5.13)
```

directly verifies an additional boundary-sensitive equality between
`(h,k)=(1,j)` and `(10,j-1)` at fixed `r`. T71 only motivated checking this
identity. It is absent from (4.3) because both sides there have the same `k`.
No T71 claim is needed for the classification (5.2)--(5.7).

## 6. Exact diagonal size

Changing variables `j=H-r` in (5.12) gives

```text
D_t = 10*sum_(j=1)^(H-1) j^2*(N-H+j).                  (6.1)
```

Using

```text
sum_(j=1)^(H-1) j^2 = (H-1)*H*(2*H-1)/6,
sum_(j=1)^(H-1) j^3 = ((H-1)*H/2)^2,                   (6.2)
```

one obtains the exact closed form

```text
D_t = (5/6)*H*(H-1)*((4*H-2)*N-H^2-H).                 (6.3)
```

As a separate check, replacing one factor `(H-r)` by `1` recovers the
triangle mass (2.10), while the exact undispersed triangle bound is

```text
|A_t(alpha)| <= M_t
 = (5/3)*H*(H-1)*(3*N-H-1).                             (6.4)
```

Thus no triangular weight or factor ten has been dropped.

## 7. The unsigned pooled-dispersion inequality

The direct way to turn (5.11) into a nonnegative upper bound is to take the
absolute value of every off-diagonal primitive correlation. Define

```text
U_t(alpha) = (N-1) * [D_t
 + 2*sum_(1<=h<h'<=10) sum_(r,r'=1)^(H-1)
     w_r*w_r' *
     |C_(0,d_(h,r;h',r'))(N-max(r,r');alpha)|
 + 2*sum_(h=1)^10 sum_(1<=r<r'<H)
     w_r*w_r' *
     |C_(r+epsilon_h,-h_0*(10^(r'-r)-1))(N-r';alpha)|].
                                                               (7.1)
```

Combining (3.5), (5.11), and `Re z<=|z|` proves the literal pooled-dispersion
inequality

```text
|A_t(alpha)|^2 <= U_t(alpha).                           (7.2)
```

Every term in the bracket in (7.1) is nonnegative, so

```text
U_t(alpha) >= (N-1)*D_t                                (7.3)
```

for every real `alpha`, including `alpha=pi`. The next theorem shows that this
particular dispersion inequality cannot reach the scale required by `(FP)`.
More generally, the same conclusion applies to any post-Cauchy upper bound of
the explicitly delimited form

```text
|A_t(alpha)|^2 <= (N-1)*(D_t+Q_t(alpha)),  Q_t(alpha)>=0, (7.3a)
```

because every such displayed right side retains the same diagonal floor. It
does not apply to the exact signed expression (5.11), where the off-diagonal
part need not be nonnegative.

### Theorem 7.1: explicit infinite obstruction family

Take every even scale

```text
t=2*m,  m>=0,  q=2^(m+1).                              (7.4)
```

Then

```text
N_t=q^2+1,
H_t=q+1,                                                (7.5)
```

because `q^2<N_t<(q+1)^2`. Substitution into (6.3) gives

```text
D_t = (5/6)*q^2*(q+1)*(4*q^2+q+1).                     (7.6)
```

Hence the exact squared diagonal ratio at the target scale is

```text
R_q = (N_t-1)*D_t/(H_t^2*N_t^2)
    = (5/6)*q^4*(4*q^2+q+1)/((q+1)*(q^2+1)^2).         (7.7)
```

For every `q>=2`,

```text
R_q > (5/3)*q.                                         (7.8)
```

After multiplying (7.8) by the positive denominator and by `6/5`, and then
canceling `q>0`, the needed inequality is

```text
q^3*(4*q^2+q+1) > 2*(q+1)*(q^2+1)^2.                  (7.9)
```

The left side minus the right side is

```text
2*q^5-q^4-3*q^3-4*q^2-2*q-2
 = (q-2)*(2*q^4+3*q^3+3*q^2+2*q+2)+2,                 (7.10)
```

which is positive for every `q>=2`. This proves (7.8).

Suppose one tried to deduce `|A_t(pi)|<=C*H_t*N_t` from (7.2) by proving that
its displayed nonnegative right side is at most `C^2*H_t^2*N_t^2`, with one
constant `C` before all `t`. Equations (7.3) and (7.8) would force

```text
C^2 > (5/3)*q                                           (7.11)
```

for every `q=2^(m+1)`, which is impossible for a fixed `C`. Therefore the
right side (7.1), and more generally any post-Cauchy upper bound of the precise
form (7.3a), cannot itself be bounded at the `O(H_t^2*N_t^2)` squared scale on
the explicit infinite family (7.4). Thus this delimited unsigned
pooled-dispersion route cannot prove `|A_t(pi)|=O(H_t*N_t)`.

The diagonal-only output has size

```text
sqrt((N_t-1)*D_t)/(H_t*N_t) > sqrt((5/3)*q),            (7.12)
```

so the loss is at least of order `H_t^(1/2)`, equivalently `N_t^(1/4)`,
relative to the desired absolute scale. In fact, the exact formula (7.7)
gives `R_q/((10/3)*q) -> 1` as `q -> infinity`.

This is a limitation of (7.2), not a lower bound for `|A_t(pi)|`. The exact
off-diagonal real parts in (5.11) can be negative and can cancel the diagonal.
In particular, Theorem 7.1 is not evidence against `(FP)`.

## 8. The signed fixed-`pi` correlation left open

For clarity, (5.11) identifies exactly what an argument retaining signs after
pooled dispersion would have to prove. Let `O_t(pi)` denote the two explicit
`2*Re` off-diagonal sums in (5.11). Then

```text
E_t(pi)=D_t+O_t(pi).                                    (8.1)
```

For one constant `C>=0`, the single lower-dimensional fixed-`pi` inequality

```text
O_t(pi) <= C^2*H_t^2*N_t^2/(N_t-1) - D_t               (SC_C)
```

for every natural `t` would, by (3.5), imply the stronger estimate

```text
|A_t(pi)| <= C*H_t*N_t.                                 (8.2)
```

Writing out the right side with no hidden constant, `(SC_C)` is

```text
2*Re sum_(1<=h<h'<=10) sum_(r,r'=1)^(H_t-1)
  (H_t-r)*(H_t-r') *
  C_(0,h*(10^r-1)-h'*(10^r'-1))
    (N_t-max(r,r');pi)

+ 2*Re sum_(h=1)^10 sum_(1<=r<r'<H_t)
  (H_t-r)*(H_t-r') *
  C_(r+epsilon_h,-h_0*(10^(r'-r)-1))(N_t-r';pi)

<= C^2*H_t^2*N_t^2/(N_t-1)
 - (5/6)*H_t*(H_t-1)*
     ((4*H_t-2)*N_t-H_t^2-H_t).                        (8.3)
```

This is a genuine fixed-`pi` signed-correlation assertion, not an estimate
proved here. Since `D_t` is of order `N_t*H_t^3`, (8.3) asks the off-diagonal
sum to cancel almost all of the diagonal, leaving order `H_t^2*N_t`. Taking
absolute values destroys exactly that required cancellation.

Even (8.3) is only a sufficient condition for the stronger absolute estimate
(8.2); it is not claimed necessary for the one-sided `(FP)`, because the
outer Cauchy step can lose sign information. T72's delivered outcome is instead
the explicit method-insufficiency family in Theorem 7.1.

## 9. Conclusion and claim boundary

The exact pooled `(h,r)` regrouping produces the double-shift frequencies

```text
h*(10^r-1)-h'*(10^r'-1)
```

with common orbit length `N_t-max(r,r')`, product weight
`(H_t-r)*(H_t-r')`, and the exhaustive diagonal/O0/O+ classification in
Section 5. The direct unsigned dispersion inequality has an unavoidable
diagonal floor. Along every even scale `t=2m`, its squared normalized floor is
larger than `(5/3)*2^(m+1)` and therefore cannot yield a uniform
`O(H_t*N_t)` estimate.

What remains open is signed, fixed-`pi` cancellation such as (8.3), or a
different method that avoids the outer Cauchy loss. This note does not prove
or refute `(FP)`, does not assert T69's aggregate premise, and asserts no full
T29 estimate or conclusion for C1, C2, or C3.
