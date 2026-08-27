# T71: almost-everywhere pooled one-sided estimate

Claim label: `proof sketch` (the argument is intended to be complete at prose
level, but it is not machine-checked).

Date: 2026-08-03 UTC.

## 1. Provenance and scope

The canonical question is the locally formulated statement
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`; it has no external
source URL. A byte-exact copy is delivered as `CANONICAL_STATEMENT.txt`, with
SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That question concerns the single prescribed phase `pi`, all positive `m,N`,
and ordered long-lag block collisions. This note proves a distinct
almost-everywhere phase result for T69's residual-A12, `m=1`, dyadic
primitive-sector interface. It does not answer or weaken the canonical
question.

The only established research input used below is the kernel-checked module
`TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc`, whose
retained source is `knowledge_library/t69/T69AggregateShiftHalfArc.lean` with
SHA-256

```text
09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
```

The relevant exact interfaces are at lines 30-59, 63-128, 130-159, 201-275,
330-424, and 612-880 of that retained source. The T70 note motivates the
condition called `(FP)` but no mathematical assertion from T70 is used as a
premise.

## 2. Normalized statement and quantifiers

Let `lambda` be Lebesgue probability measure on `[0,1)`. For every natural
number `t`, set

```text
N_t = 4*2^t + 1,
H_t = ceil(sqrt(N_t)),
q_r = 10^r - 1,
e(x) = exp(2*pi*i*x).
```

The `pi` in the definition of `e` is the unchanged circle normalization. For
every real phase `alpha`, define

```text
A_t(alpha)
  = sum_{h=1}^{10} sum_{r=1}^{H_t-1} (H_t-r)
      sum_{k=0}^{N_t-r-1} e(h*q_r*10^k*alpha).          (2.1)
```

Thus frequencies are positive integers

```text
nu(h,r,k) = h*(10^r-1)*10^k,
```

and the complete domains are

```text
1 <= h <= 10,  1 <= r < H_t,  0 <= k < N_t-r.
```

The function is one-periodic in `alpha`. The random phase is its restriction
to `alpha in [0,1)` with Lebesgue probability measure; only the prescribed
phase in T69, not the circle normalization, has been replaced.

The literal random-phase version of `(FP)` is

```text
there is C_alpha >= 0 such that, for every natural t,
  Re A_t(alpha) <= C_alpha*H_t*N_t.                     (FP_alpha)
```

We prove the stronger eventual assertion with the universal constant `1`, and
then absorb the finitely many earlier scales into `C_alpha`.

The precise quantifier order is

```text
there is Omega subset [0,1) with lambda(Omega)=1 such that
  for every alpha in Omega there is t_0(alpha) such that
    for every t >= t_0(alpha), Re A_t(alpha) <= H_t*N_t;
  consequently, for every alpha in Omega there is C_alpha >= 1 such that
    for every natural t, Re A_t(alpha) <= C_alpha*H_t*N_t.
```

No common onset or common `C_alpha` is asserted for all phases. In particular,
no assertion is made that the prescribed number `pi` belongs to `Omega`.

## 3. T69's exact half-arc convention

Although `(FP_alpha)` is a direct Fourier estimate and does not require a
discrepancy replacement, the half-arc interface from which T69 arose is fixed
as follows. The circle `R/Z` is represented by the half-open fundamental
interval `[-1/2,1/2)`. If `rep(z)` denotes this representative, the centered
half-arc translated by `y` is

```text
I_y = {x in R/Z : rep(x-y) in [-1/4,1/4)}.             (3.1)
```

It includes the `-1/4` endpoint and excludes the `1/4` endpoint. T68/T69's
explicit complementary orientation is literal nonmembership in (3.1), so it
includes the excluded `1/4` endpoint and excludes the included `-1/4`
endpoint. Both orientations are therefore unambiguous half-open half-arcs;
they are not silently replaced by closed arcs.

After the phase substitution, the multiplicity-retaining pooled count excess
is

```text
P_t(alpha,y)
 = sum_{h=1}^{10} sum_{r=1}^{H_t-1} (H_t-r) *
     (#{0 <= k < N_t-r :
          rep(h*(10^r-1)*10^k*alpha-y) in [-1/4,1/4)}
       - (N_t-r)/2).                                   (3.2)
```

The exact total weighted pre-arc mass is

```text
M_t = 10*sum_{r=1}^{H_t-1}(H_t-r)(N_t-r)
    = 10*H_t*(H_t-1)*(3*N_t-H_t-1)/6.                 (3.3)
```

The second equality follows by expanding the product and using the sums of
the first two powers on `1,...,H_t-1`. Formula (3.2) is count minus `M_t/2`.
This note does not assert a pointwise bound for (3.2), and no endpoint-null-set
argument is used in the proof of `(FP_alpha)`.

For reference, T69's kernel-checked implications track these constants:

```text
|P_t(pi,y)| <= Delta*H_t*N_t for all t,y
  implies aggregate constant K = 10 + 2*pi*Delta;

the stronger separate T68 discrepancy premise
  implies K = 10*(1 + pi*Delta).
```

Neither premise is asserted here.

## 4. Exact equality-frequency classification

Fix `t`. Write

```text
L_r = N_t-r,   w_r = H_t-r.
```

Because `N_t >= 5`, we have

```text
sqrt(N_t) <= H_t < sqrt(N_t)+1 < 2*sqrt(N_t) < N_t.
```

Thus `L_r >= 2` whenever `1 <= r < H_t`.

### Lemma 4.1 (all frequency equalities)

Suppose two indices in the literal domain satisfy

```text
h*(10^r-1)*10^k = h'*(10^s-1)*10^ell.                 (4.1)
```

Then `r=s`, and either `(h,k)=(h',ell)`, or the two
`(h,k)` pairs are `(1,j)` and `(10,j-1)` for some `j>=1`.

**Proof.** Factor `h=2^a*5^b*u`, where `u` is coprime to `10`. The complete
table for the allowed frequencies is

| `h` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `a=v_2(h)` | 0 | 1 | 0 | 2 | 0 | 1 | 0 | 3 | 0 | 1 |
| `b=v_5(h)` | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 1 |
| `u` | 1 | 1 | 3 | 1 | 1 | 3 | 7 | 1 | 9 | 1 |

Since `10^r-1` is divisible by neither `2` nor `5`, taking the `2`- and
`5`-adic valuations of (4.1) gives

```text
k+a = ell+a',   k+b = ell+b'.                          (4.2)
```

After cancelling those powers, (4.1) also gives

```text
u*(10^r-1) = u'*(10^s-1).                              (4.3)
```

If `r<s`, then

```text
(10^s-1)/(10^r-1) >= (10^(r+1)-1)/(10^r-1) > 10,
```

whereas (4.3) says this ratio is `u/u' <= 9`. This is impossible;
interchanging the two indices excludes `s<r`. Hence `r=s`, after which (4.3)
gives `u=u'`.

Subtracting the two equalities in (4.2) shows `a-b=a'-b'`. Inspection of the
complete table with both `u` and `a-b` fixed leaves identical values of `h`,
except that `h=1` and `h=10` share `u=1` and `a-b=0`. In the identical case,
(4.2) gives `k=ell`. In the exceptional case,

```text
(10^r-1)*10^j = 10*(10^r-1)*10^(j-1),
```

and these are exactly the claimed pairs. This proves exhaustion, including
collisions between different `r` values. QED.

### Corollary 4.2 (classes with finite-range boundaries)

For each fixed `r`, the complete classes are

```text
{(1,r,0)},

{(1,r,j),(10,r,j-1)}       for 1 <= j <= L_r-1,

{(10,r,L_r-1)},

{(h,r,k)}                  for 2 <= h <= 9 and 0 <= k < L_r.
```

There are exactly `8*L_r+2` singleton classes and `L_r-1` double classes.
The first and third displayed classes are the two boundary singletons; dropping
either would change the exact moment by `w_r^2`.

## 5. Exact finite moments

All members of a fixed collision class have the same weight `w_r`. After
pooling equal characters, a singleton has coefficient `w_r` and a double
class has coefficient `2*w_r`. Corollary 4.2 therefore gives, for each `r`,

```text
(8*L_r+2)*w_r^2 + (L_r-1)*(2*w_r)^2
  = (12*L_r-2)*w_r^2.                                  (5.1)
```

For positive integers `m,n`, character orthogonality on `[0,1)` gives

```text
integral_0^1 e((m-n)*alpha) d alpha = 1 if m=n, and 0 otherwise,

integral_0^1 cos(2*pi*m*alpha) cos(2*pi*n*alpha) d alpha
  = 1/2 if m=n, and 0 otherwise.                        (5.2)
```

Every frequency in (2.1) is positive. Applying (5.2) to the exhaustive
classes yields the exact identities

```text
integral_0^1 |A_t(alpha)|^2 d alpha
 = sum_{r=1}^{H_t-1}
     (12*(N_t-r)-2)*(H_t-r)^2,                          (5.3)

integral_0^1 (Re A_t(alpha))^2 d alpha
 = sum_{r=1}^{H_t-1}
     (6*(N_t-r)-1)*(H_t-r)^2.                           (5.4)
```

Equivalently, (5.4) is half of (5.3). There is no extra constant term because
all frequencies are nonzero, and there are no positive-negative collisions
because (2.1) contains only positive frequencies.

Denote the right side of (5.4) by `V_t`. Since
`6*(N_t-r)-1 < 6*N_t`, changing variables `j=H_t-r` gives the explicit bound

```text
V_t
 < 6*N_t*sum_{j=1}^{H_t-1} j^2
 = N_t*(H_t-1)*H_t*(2*H_t-1)
 < 2*N_t*H_t^3.                                        (5.5)
```

No estimate for a different square function is substituted for (5.4).

## 6. Explicit tail summation

Define the one-sided bad event

```text
E_t = {alpha in [0,1) : Re A_t(alpha) > H_t*N_t}.
```

On `E_t`, `(Re A_t(alpha))^2 > H_t^2*N_t^2`. Markov's inequality applied to
the nonnegative square, followed by (5.4)-(5.5), gives

```text
lambda(E_t)
 <= V_t/(H_t^2*N_t^2)
 < 2*H_t/N_t.                                          (6.1)
```

The ceiling and dyadic definitions give, for every `t>=0`,

```text
H_t < sqrt(N_t)+1 < 2*sqrt(N_t),
N_t = 4*2^t+1 > 4*2^t,
sqrt(N_t) > 2*2^(t/2).
```

Consequently the complete numerical tail is

```text
lambda(E_t) < 4/sqrt(N_t) < 2*2^(-t/2),                (6.2)

sum_{t=0}^infinity lambda(E_t)
 < 2*sum_{t=0}^infinity 2^(-t/2)
 = 2/(1-2^(-1/2))
 = 4+2*sqrt(2)
 < infinity.                                           (6.3)
```

This summation covers every natural scale, including `t=0`.

## 7. Almost-everywhere proof of literal `(FP_alpha)`

The first Borel-Cantelli lemma, which requires no independence, and (6.3)
show that almost every `alpha` belongs to only finitely many `E_t`. Thus for
almost every `alpha` there is a finite `t_0(alpha)` such that

```text
Re A_t(alpha) <= H_t*N_t for every t >= t_0(alpha).     (7.1)
```

For such an `alpha`, define

```text
C_alpha = max(1,
  max_{0 <= t < t_0(alpha)} Re A_t(alpha)/(H_t*N_t)),   (7.2)
```

omitting the inner maximum if `t_0(alpha)=0`. Every denominator is positive,
and the inner set is finite, so `C_alpha` is a finite real number with
`C_alpha>=1`. Equations (7.1)-(7.2) prove, without an unresolved replacement
inequality,

```text
Re A_t(alpha) <= C_alpha*H_t*N_t for every natural t.   (7.3)
```

This is the literal all-scale `(FP_alpha)`; in particular it implies the
requested eventual form. Notice that negative early values cause no issue
because of the outer maximum with `1`.

## 8. Exact aggregate consequence and its scope

T69's kernel-checked literal identity at its prescribed phase is

```text
aggregateEnergy(t) = 10*H_t*N_t + 2*Re A_t(pi).         (8.1)
```

Replacing only that prescribed phase by `alpha` defines the exact random-phase
analogue

```text
aggregateEnergy_alpha(t)
  = 10*H_t*N_t + 2*Re A_t(alpha).                       (8.2)
```

For every `alpha` in the full-measure set from Section 7, (7.3) and (8.2)
give

```text
aggregateEnergy_alpha(t)
 <= (10+2*C_alpha)*H_t*N_t for every natural t.         (8.3)
```

Thus the exact T69 aggregate threshold is met in the random-phase analogue
with the single nonnegative constant

```text
K_alpha = 10+2*C_alpha.                                 (8.4)
```

No absolute-value estimate for `A_t` and no half-arc discrepancy estimate is
needed. The one-sided sign in `(FP_alpha)` is exactly what (8.2) requires.

For orientation only, if an aggregate bound with constant `K` is available at
the prescribed phase, T69's other kernel-checked constants are

```text
sum_{h=1}^{10} X_h(N_t)^2 <= (9/4)*K^2*N_t^3,           (8.5)

selected-plus-defect numerator
 = sum_h X_h(N_t)^2 - 4*(N_t-1)*sum_h X_h(N_t)
     + 20*N_t^2 - 30*N_t,                              (8.6)

conditional primitive-sector budget constant
 = 10*((45/16)*K^2+5).                                 (8.7)
```

These are recorded to make the constants auditable; this note does not assert
their fixed-`pi` hypotheses.

## 9. Conclusion

For Lebesgue-almost every phase `alpha`, the literal pooled one-sided estimate
`(FP_alpha)` holds at every sufficiently large scale with the universal
constant `1`, and at every scale with the finite phase-dependent constant
`C_alpha` in (7.2). Hence the phase-substituted T69 aggregate condition holds
with `K_alpha=10+2*C_alpha`.

The scope is exact: this is a random-phase compatibility theorem. It neither
proves nor refutes `(FP)` at `alpha=pi`; it does not establish T69's original
fixed-`pi` aggregate premise; and it states no conclusion for T29, C1, C2, or
C3.
