# T80: universal positive-weighted Cauchy barrier

Claim label: `proof sketch` (the imported T69 interface is machine-checked;
the new finite argument in this note is not machine-checked).

Date: 2026-08-06 UTC.

## 1. Provenance, normalized statement, and scope

The canonical question is the locally formulated statement
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`. It has no external
source URL. A byte-exact copy is delivered as `CANONICAL_STATEMENT.txt`, with
SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks whether, for every real `s` with `0 < s < 1`,
there is one `C_s >= 1` that works simultaneously for every pair of positive
integers `m,N` in the ordered long-lag collision bound

```text
R_pi(m,N) <= C_s*(N+N^2*10^(-s*m)).
```

T80 does not answer or alter that question. It concerns only T69's residual
A12, `m=1`, dyadic primitive-sector sibling. The scale variable is `t in N`,
and the finite parameters are

```text
N = N_t = 4*2^t+1,
H = H_t = ceil(sqrt(N)).
```

The following quantifier and method choices are explicit.

1. A Cauchy weight may be chosen separately for every `t` and may even depend
   on the phase. The obstruction below is pointwise in every strictly positive
   weight vector, so this extra freedom does not help.
2. Cauchy--Schwarz is applied only after pooling all `(h,r)` channels at each
   fixed orbit index `k`. The Cauchy index is exactly `0 <= k <= N-2`.
3. "Diagonal" means equality of the two pooled channels `(h,r)=(h',r')`
   inside the same-`k` square. It does not mean every frequency collision in
   the un-Cauchied square of the full sum.
4. The barrier applies only after every off-diagonal correlation is replaced
   by a nonnegative absolute-value majorant. The exact signed weighted energy
   may have off-diagonal cancellation.
5. The target `O(H^2*N^2)` is the squared scale sufficient to deduce
   `|A_t(pi)|=O(H*N)`. T69 itself needs only a one-sided bound on `Re A_t(pi)`.
   Failure of this stronger absolute-value route is not failure of T69's
   premise.

### 1.1 Ambiguities and non-substitutions

The canonical quantifier order is one `C_s` for each `0<s<1`, followed by all
positive `m,N`. It is not replaced here by fixed `m`, favorable scales, an
almost-everywhere phase, or a constant depending on `m,N`. The present A12,
`m=1`, dyadic primitive-sector calculation is a sibling reduction target, not
the canonical A1 statement.

Within the method calculation, the universal quantifiers are also literal:
at each natural scale `t`, each real phase `alpha`, and each vector whose
entries are strictly positive, the weighted unsigned majorant has the stated
diagonal floor. The obstruction is witnessed on the infinite subfamily of
even `t`; this is enough to rule out one scale-uniform bound for that
majorant. The weights are placed on the regrouped orbit index `k`, not on the
original channels `(h,r)` and not on the full triples `(h,r,k)`.

This recovery revises the staged T78 artifact after a pipeline casualty. The
finite argument was rechecked against the retained kernel-checked T69 source;
the recovery status itself supplies no additional mathematical evidence.

The kernel-checked source used here is

```lean
import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
```

whose retained source SHA-256 is

```text
09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
```

The T72 note, SHA-256
`606eaebc3783db206665014ec25391b9132edd19c14f5dd798447f4e2d4e3bd7`,
is an unverified proof sketch used only as motivation. No T72 claim is a
premise below. T74, SHA-256
`8c56052df1deda2acdf01253ffe06ed8451a1647e834faf228a7edf003d9f896`,
is a kernel-checked coefficientwise multiplier-nine obstruction. It is not a
premise below: T80 addresses all positive Cauchy reweightings rather than
coefficientwise telescoping.

## 2. The exact T69 pooled expression

For a real phase `alpha`, define

```text
e(x)       = exp(2*pi*i*x),
a_(h,r)    = h*(10^r-1),
w_r        = H-r,
L_r        = N-r.
```

The first `pi` in `e` is the circle normalization. At the prescribed phase,
the second occurrence of `pi` below is the real number `pi`. T69's exact
pooled shifted sum is

```text
A_t(pi)
  = sum_(h=1)^10 sum_(r=1)^(H-1) (H-r)
      sum_(k=0)^(N-r-1) e(a_(h,r)*10^k*pi).              (2.1)
```

Thus the literal ranges and weights are

```text
1 <= h <= 10,
1 <= r < H,
0 <= k < N-r,
weight H-r.                                              (2.2)
```

No endpoint in (2.2) is replaced by a common rectangular range. T69's
machine-checked identity is

```text
aggregateEnergy(t) = 10*H*N + 2*Re A_t(pi).             (2.3)
```

Consequently, if some `C >= 0` satisfied

```text
|A_t(pi)| <= C*H*N                                      (2.4)
```

for every `t`, then `Re A_t(pi) <= |A_t(pi)|` and (2.3) would give T69's
aggregate hypothesis with the explicit constant

```text
K = 10+2*C.                                              (2.5)
```

Conditionally on that aggregate hypothesis, T69 gives the checked fourth
moment scale

```text
sum_(h=1)^10 X_h(N_t)^2 <= (9/4)*K^2*N_t^3.             (2.6)
```

For `0<s<1`, T69's checked specialized selected-plus-defect budget then has
constant and scale

```text
10*((45/16)*K^2+5)*(N_t+N_t^2*10^(-s)).                (2.7)
```

Equations (2.5)--(2.7) are conditional consequences only. This note supplies
no `C` in (2.4) and asserts no T69 aggregate estimate.

## 3. Exact regrouping at the Cauchy index

Since `N >= 5`, T69's checked elementary bounds give `H >= 3` and `H <= N`.
The longest range in (2.1) is the `r=1` range, so the union of the `k` ranges
is exactly

```text
0 <= k <= N-2.                                          (3.1)
```

For a `k` in (3.1), define the active endpoint

```text
R_k = min(H-1,N-k-1).                                   (3.2)
```

For natural `r,k`, the conjunction

```text
1 <= r < H  and  0 <= k < N-r
```

is equivalent to `1 <= r <= R_k`. Therefore define

```text
B_k(alpha)
  = sum_(h=1)^10 sum_(r=1)^(R_k)
      (H-r)*e(a_(h,r)*10^k*alpha).                      (3.3)
```

Exchanging only finite sums in (2.1) gives the exact identity

```text
A_t(alpha) = sum_(k=0)^(N-2) B_k(alpha).                (3.4)
```

There are exactly `N-1` terms in (3.4), including both endpoints.

## 4. Admissible positive weights and weighted Cauchy

For fixed `t` and `alpha`, an admissible Cauchy weight is a vector

```text
lambda = (lambda_0,...,lambda_(N-2))
such that lambda_k is real and lambda_k > 0 for every k. (4.1)
```

No upper bound, normalization, monotonicity, integrality, or independence
from `t` or `alpha` is imposed. Put

```text
S(lambda) = sum_(k=0)^(N-2) 1/lambda_k,
E(lambda;alpha) = sum_(k=0)^(N-2) lambda_k*|B_k(alpha)|^2. (4.2)
```

Apply complex Cauchy--Schwarz to

```text
A_t(alpha)
  = sum_k lambda_k^(-1/2) * (lambda_k^(1/2)*B_k(alpha)).
```

Strict positivity in (4.1) makes every displayed square root and reciprocal
valid. The result is the exact weighted inequality

```text
|A_t(alpha)|^2 <= S(lambda)*E(lambda;alpha).             (4.3)
```

This is the first inequality in the argument.

## 5. Exact unequal-length double expansion

For two channels define the signed integer difference

```text
d(h,r;h',r')
  = h*(10^r-1)-h'*(10^r'-1).                            (5.1)
```

Both channels are active at `k` exactly when

```text
k < N-r and k < N-r'
  iff k < min(N-r,N-r')
  iff k < N-max(r,r').                                  (5.2)
```

Expanding every square in (4.2), with no estimate, and taking real parts gives
the exact real identity

```text
E(lambda;alpha)
  = sum_(h=1)^10 sum_(h'=1)^10
      sum_(r=1)^(H-1) sum_(r'=1)^(H-1)
        (H-r)*(H-r')
        * Re(sum_(k=0)^(N-max(r,r')-1)
            lambda_k*e(d(h,r;h',r')*10^k*alpha)).       (5.3)
```

The endpoint in (5.3) is literally `k < N-max(r,r')`. In particular, it is
not `N-r`, `N-r'`, `N`, or a silently padded rectangular sum. Reversing the
ordered channel pair conjugates its inner sum, so the complete right side is
unchanged if conjugate pairs are combined. Equivalently, one may write (5.3)
as a complex ordered sum after coercing its real left side to the complexes.

### 5.1 Exact channel diagonal

Within the domains in (5.3),

```text
d(h,r;h',r')=0 iff (h,r)=(h',r').                       (5.4)
```

To prove the nontrivial direction, suppose first that `r>r'`. Then
`r>=r'+1`, and

```text
10^r-1 >= 10^(r'+1)-1
         = 10*(10^r'-1)+9
         > 10*(10^r'-1).
```

Thus `(10^r-1)/(10^r'-1)>10`. Equality of the two channel frequencies would
instead make this ratio `h'/h <= 10`, since `1<=h,h'<=10`, a contradiction.
The case `r<r'` is excluded by the same argument after swapping the channels.
Hence `r=r'`; cancellation of the positive factor `10^r-1` then gives
`h=h'`. The reverse implication in (5.4) is immediate.

It follows from (5.3)--(5.4) that the exact diagonal part is

```text
D(lambda)
  = 10*sum_(r=1)^(H-1) (H-r)^2
      * sum_(k=0)^(N-r-1) lambda_k.                     (5.5)
```

The factor `10` counts the ten diagonal choices of `h`. Exchanging the two
finite sums in (5.5) gives

```text
D(lambda) = sum_(k=0)^(N-2) c_k*lambda_k,               (5.6)

c_k = 10*sum_(r=1)^min(H-1,N-k-1) (H-r)^2.             (5.7)
```

Every `c_k` is strictly positive. Indeed, `k<=N-2` implies
`N-k-1>=1`, while `H>=3`, so the `r=1` term occurs and contributes
`10*(H-1)^2>0`.

## 6. The exact unsigned weighted inequality

Let `Q(lambda;alpha)` be the following explicitly nonnegative off-diagonal
majorant:

```text
Q(lambda;alpha)
  = sum over 1<=h,h'<=10 and 1<=r,r'<H with (h,r)!=(h',r') of
      (H-r)*(H-r')
      * |sum_(k=0)^(N-max(r,r')-1)
           lambda_k*e(d(h,r;h',r')*10^k*alpha)|.        (6.1)
```

Split the exact expansion (5.3) into the diagonal (5.5) and its ordered
off-diagonal terms. Applying `Re z <= |z|` to each off-diagonal inner sum
gives

```text
E(lambda;alpha) <= D(lambda)+Q(lambda;alpha).            (6.2)
```

Combining (4.3) and (6.2) proves, rather than assumes, the unsigned weighted
Cauchy inequality

```text
|A_t(alpha)|^2 <= U(lambda;alpha),                       (6.3)

U(lambda;alpha)
  = S(lambda)*(D(lambda)+Q(lambda;alpha)).               (6.4)
```

Since `S(lambda)>0` and `Q(lambda;alpha)>=0`, the displayed right side has
the diagonal floor

```text
U(lambda;alpha) >= F(lambda),                            (6.5)

F(lambda)
  = S(lambda)*D(lambda)
  = (sum_k 1/lambda_k)*(sum_k c_k*lambda_k).            (6.6)
```

The direction and scope of (6.5) are essential. The quantity `F(lambda)` is
not asserted to be a lower bound for the exact energy
`S(lambda)*E(lambda;alpha)`, nor for `|A_t(alpha)|^2`. Signed off-diagonal
terms in (5.3) can cancel the diagonal. It is a floor only for the explicit
unsigned majorant (6.4), where all additional terms are nonnegative.

## 7. Exact optimization over every positive weight

### Theorem 7.1

For the positive coefficients (5.7),

```text
inf_(lambda_k>0) F(lambda) = (sum_(k=0)^(N-2) sqrt(c_k))^2. (7.1)
```

The infimum is attained. The complete family of minimizers is

```text
lambda_k = rho/sqrt(c_k),  rho>0.                        (7.2)
```

### Proof

Apply real Cauchy--Schwarz to the two positive vectors

```text
x_k = 1/sqrt(lambda_k),
y_k = sqrt(c_k*lambda_k).
```

Their scalar product is `sum_k sqrt(c_k)`, so

```text
(sum_k sqrt(c_k))^2
  <= (sum_k 1/lambda_k)*(sum_k c_k*lambda_k)
   = F(lambda).                                          (7.3)
```

Equality in Cauchy--Schwarz holds exactly when the vectors are proportional:
`x_k=mu*y_k` for one `mu>0`. This is equivalent to
`lambda_k=1/(mu*sqrt(c_k))`, which is (7.2) after renaming the common positive
factor. Every weight in (7.2) is admissible because every `c_k>0`, and direct
substitution gives equality in (7.3). This proves both the identity and
attainment. The free factor `rho` also records the scale invariance of
`F(lambda)`.

## 8. Explicit infinite scale obstruction

Take every even scale

```text
t=2*m,  m>=0,  q=2^(m+1).                               (8.1)
```

Then `q>=2` and

```text
N = 4*2^(2*m)+1 = q^2+1.                                (8.2)
```

Because `q^2 < q^2+1 < (q+1)^2`,

```text
H = ceil(sqrt(N)) = q+1.                                (8.3)
```

For every

```text
0 <= k <= N-H,                                          (8.4)
```

one has `N-k-1>=H-1`, so every shift `1<=r<=H-1` is active
in (5.7). The inclusive range (8.4) has exactly

```text
L = N-H+1 = q^2-q+1                                    (8.5)
```

indices. On each of them,

```text
c_k = 10*sum_(r=1)^(H-1) (H-r)^2
    = 10*sum_(j=1)^q j^2
    = (5/3)*q*(q+1)*(2*q+1).                            (8.6)
```

Discarding only the remaining positive summands from (7.1) gives

```text
inf F(lambda)
  = (sum_(k=0)^(N-2) sqrt(c_k))^2
  >= L^2*(5/3)*q*(q+1)*(2*q+1).                        (8.7)
```

Divide by the positive target squared scale

```text
H^2*N^2 = (q+1)^2*(q^2+1)^2.
```

Equations (8.5)--(8.7) yield the explicit ratio

```text
inf F(lambda)/(H^2*N^2)
 >= (5/3)*[q*(2*q+1)/(q+1)]
      *[(q^2-q+1)/(q^2+1)]^2.                          (8.8)
```

For every `q>=2`,

```text
(2*q+1)/(q+1) >= 1,                                    (8.9)

(q^2-q+1)/(q^2+1) >= 1/2,                              (8.10)
```

where (8.10), after multiplying by `2*(q^2+1)>0`, is exactly
`(q-1)^2>=0`. Therefore

```text
inf F(lambda)/(H^2*N^2) >= (5/12)*q.                   (8.11)
```

Combining (6.5), (7.1), and (8.11), for every admissible positive weight
vector, even one selected separately at each scale and phase,

```text
U(lambda;alpha) >= (5/12)*q*H^2*N^2                    (8.12)
```

on every scale (8.1). Given any fixed `C>=0`, choose `m` so that

```text
q=2^(m+1) > (12/5)*C^2.                                (8.13)
```

Then every admissible positive weight satisfies

```text
U(lambda;alpha) > C^2*H^2*N^2.                         (8.14)
```

Thus no choice of strictly positive Cauchy weights can make the explicit
unsigned right side (6.4) uniformly `O(H^2*N^2)`. The optimized diagonal-only
output is at least

```text
sqrt(inf F(lambda))/(H*N) >= sqrt((5/12)*q),            (8.15)
```

so the unavoidable loss in this method grows at least like `H^(1/2)`,
equivalently `N^(1/4)`, along the infinite even-scale family.

## 9. What is and is not retired

At `proof sketch` status, the argument rules out the following precisely
delimited route:

1. regroup T69's exact pooled sum by the common orbit index `k`;
2. apply Cauchy--Schwarz with arbitrary strictly positive weights on that
   exact `k` index;
3. expand with the exact endpoint `k<N-max(r,r')`; and
4. replace all off-diagonal correlations by nonnegative absolute-value
   majorants before seeking an `O(H^2*N^2)` right-side estimate.

It does not retire a signed estimate for the exact energy (5.3), a method that
uses zero or signed coefficients rather than positive Cauchy weights, a direct
one-sided estimate for `Re A_t(pi)`, or a method avoiding this outer Cauchy
step. In particular, (8.12) is not a lower bound for `|A_t(pi)|`.

This note proves no fixed-`pi` FP estimate, no T69 aggregate premise, no T29
width-weighted square-function predicate, and none of C3, C2, C1, or the
canonical collision estimate. Those claims remain open.

## 10. Skeptic replay checklist

1. Verify the canonical statement copy has the SHA-256 in Section 1.
2. Compare (2.1)--(2.3) with T69's `aggregateShiftedSum`,
   `aggregateEnergy_literal`, and
   `aggregateEnergy_eq_real_aggregateShiftedSum`.
3. Check that (3.2) is equivalent to both original restrictions on `r,k` and
   that (3.1) contains exactly `N-1` indices.
4. Check strict positivity, with no hidden normalization, in (4.1).
5. Check the unequal-length endpoint (5.2) and every factor in (5.3).
6. Check the diagonal classification (5.4), the tenfold factor in (5.5), and
   the endpoint-dependent coefficient (5.7).
7. Check that the triangle inequality is used only in (6.2), so (6.5) is not
   misrepresented as a floor for the signed energy.
8. Check equality and attainment in the optimization (7.1)--(7.3).
9. Check the inclusive full-active range, its cardinality, and the sum of
   squares in (8.4)--(8.7).
10. Check the constant `5/12`, the fixed-constant contradiction, and the
    method-only conclusion in Sections 8--9.
