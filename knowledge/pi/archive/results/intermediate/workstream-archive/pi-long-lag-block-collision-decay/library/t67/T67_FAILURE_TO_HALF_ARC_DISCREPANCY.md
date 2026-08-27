# T67: failure of T66 and half-circle discrepancy

Status: **proof sketch**.  The T63 and T66 interfaces cited below are
machine-checked.  The new finite Fourier-to-interval argument in this note is
proved in prose and is not Lean-formalized.  No unconditional discrepancy or
shifted-correlation estimate is asserted for pi.

## 1. Provenance, normalized scope, and ambiguities

The byte-exact canonical statement is delivered as
`CANONICAL_STATEMENT.txt`.  It is a locally formulated question, so there is
no original external source URL.  Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks whether, for every real `0 < s < 1`, one
constant `C_s` controls the ordered long-lag collision count for every pair
of positive integers `m,N`.  T67 neither changes nor answers that question.
It concerns only T66's residual-A12, `m=1`, dyadic primitive-sector
condition.

All quantifiers used here are fixed as follows.

1. A scale is an integer `t >= 0`.
2. The endpoint and cutoff are literally

   ```text
   N_t = 4*2^t+1,                 H_t = ceil(sqrt(N_t)).       (1.1)
   ```

3. The frequency is one of the ten integers `1 <= h <= 10`.
4. A shift is an integer `1 <= r < H_t`; its orbit has exactly
   `n_{t,r}=N_t-r` terms indexed by `0 <= k < N_t-r`.
5. Every circle arc below is half-open.  Thus endpoint points are counted
   exactly once.  Counts retain multiplicity in the index `k`, even if two
   orbit points coincide.
6. A uniform discrepancy constant is chosen before `t,h,r` and the arc.
7. The phrase "literal failure of T66's premise" means that no finite
   nonnegative `K` works simultaneously for every displayed `t,h`.

T67 does not vary `m`, does not control other endpoints `N`, and does not
assert T29, C2, C3, C1, or the canonical collision bound.

## 2. Kernel-checked interfaces consumed

The accumulated library provides the kernel-checked modules

```text
TheoryLib.PiLongLagBlockCollisionDecay.T63T63ExactFiniteFourthMoment
TheoryLib.PiLongLagBlockCollisionDecay.T66T66DeterministicShiftedFrequencyVdC
```

T66 imports T63.  The following are imported facts, not new prose premises.

* T66 defines `N t=4*2^t+1` and
  `H t=Nat.ceil (Real.sqrt (N t : Real))`.
* T66's `shiftedCharacter_eq_orbitCorrelation` identifies the character at
  shift `r` and index `k` with the literal integer frequency
  `h*(10^r-1)*10^k`.
* T66's `triangularEnergy_literal` exposes the exact half-open endpoint,
  shifts, and weights used in (3.3) below.
* T66's `finite_van_der_corput`, `endpointMultiplier_le`,
  `X_sq_le_of_shiftedCorrelation`, and
  `fourthMoment_le_of_shiftedCorrelation` give respectively the exact
  endpoint multiplier, the `3/2` endpoint estimate, the one-frequency
  constant `9/4`, and the ten-frequency constant `45/2`.
* T63's `complete_selected_defect_recombination`, exposed in T66 as
  `selectedDefectContribution_eq_T63Polynomial`, retains the exact polynomial

  ```text
  F_t - 4*(N_t-1)*M_t + 20*N_t^2 - 30*N_t                  (2.1)
  ```

  and the literal width `sqrt(N_t^2-1)`.  Here
  `M_t=sum_{h=1}^{10} X_h(N_t)` and
  `F_t=sum_{h=1}^{10} X_h(N_t)^2`.
* T66's final conditional primitive-sector theorem has constant

  ```text
  10*((225/8)*K^2+5)                                       (2.2)
  ```

  against `N_t+N_t^2*10^(-s)`, for every `Q0,t` and every `0<s<1`.

The new argument below acts directly on T66's displayed triangular energy.
It does not rederive T63 or T66 and does not treat (2.1) as a fixed-pi
estimate.

## 3. Literal T66 sums and premise

Write

```text
e(x) = exp(2*pi*i*x),
N = N_t,
H = H_t,
n_r = N-r.                                                  (3.1)
```

For the displayed `t,h,r`, define

```text
x_k = {h*(10^r-1)*10^k*pi} in R/Z,       0 <= k < n_r,

S_{t,h,r}
  = sum_{0<=k<n_r} e(h*(10^r-1)*10^k*pi).                   (3.2)
```

Braces in (3.2) mean reduction modulo one only in the definition of `x_k`;
periodicity of `e` makes the two expressions identical.  In particular,
there is no omitted factor of 10 or pi.

T66's exact triangular energy is

```text
E_{t,h}
  = H*N + 2*sum_{1<=r<H} (H-r)*Re(S_{t,h,r}).               (3.3)
```

Its fixed-pi shifted-correlation premise at a specified `K` is

```text
K >= 0 and
for every t>=0 and every integer 1<=h<=10,
  E_{t,h} <= K*H_t*N_t.                                    (3.4)
```

The unresolved uniform premise is the existence of such a `K`.  Its literal
logical failure is therefore

```text
for every real K>=0, there exist t>=0 and 1<=h<=10 such that
  E_{t,h} > K*H_t*N_t.                                     (3.5)
```

This is a negation of a uniform bound, not a claim that one predetermined
scale fails every `K`.

## 4. Cutoff and triangular-weight audit

For every `t>=0`, `N=4*2^t+1>=5`.  Hence
`sqrt(N)>2`, so `H=ceil(sqrt(N))>=3`.  Also `sqrt(N)<=N`, and because `N` is
an integer, `H<=N`.  It follows that

```text
1 <= r < H  implies  1 <= n_r=N-r.                          (4.1)
```

The triangular weights have the exact sums

```text
sum_{1<=r<H} (H-r) = H*(H-1)/2,                             (4.2)

W(N,H) := sum_{1<=r<H} (H-r)*(N-r)
        = H*(H-1)*(3*N-H-1)/6
        <= N*H*(H-1)/2.                                    (4.3)
```

For (4.3), put `j=H-r`.  Then

```text
W = sum_{j=1}^{H-1} j*(N-H+j)
  = (N-H)*H*(H-1)/2 + H*(H-1)*(2*H-1)/6,
```

which simplifies to the displayed equality.  The final inequality also
follows termwise from `N-r<=N`.  Only that termwise upper bound is needed
below.

## 5. Failure at one scale selects one literal shift

**Lemma 5.1 (weighted pigeonhole).**  Let `K>1`.  If, for one displayed
`t,h`,

```text
E_{t,h} > K*H*N,                                            (5.1)
```

then there is an integer `r` with `1<=r<H` such that

```text
Re(S_{t,h,r}) > (K-1)*(N-r)/(H-1).                          (5.2)
```

**Proof.**  Suppose instead that every displayed shift satisfies the reverse
weak inequality in (5.2).  Since `K-1>0`, (4.3) gives

```text
2*sum_{1<=r<H} (H-r)*Re(S_{t,h,r})
  <= 2*(K-1)/(H-1)
       *sum_{1<=r<H} (H-r)*(N-r)
  <= 2*(K-1)/(H-1) * N*H*(H-1)/2
   = (K-1)*H*N.                                             (5.3)
```

Adding the diagonal term `H*N` proves `E_{t,h}<=K*H*N`, contrary
to (5.1).  Thus (5.2) holds for at least one of the literal shifts.  Notice
that neither the triangular weight nor the varying orbit length `N-r` was
replaced by an unweighted average.  QED.

## 6. A Fourier coefficient forces a literal half-circle excess

The next lemma is independent of pi and is proved here rather than cited as
a discrepancy theorem.

**Lemma 6.1 (half-circle extraction).**  Let `x_0,...,x_{n-1}` be any finite
list in the circle `T=R/Z`, with repetitions allowed, and let

```text
S = sum_{0<=k<n} e(x_k).                                    (6.1)
```

For `y in T`, define the half-open half-circle

```text
A_y = y + [-1/4,1/4)  (mod 1),        length(A_y)=1/2,       (6.2)
```

and its centered count

```text
D(y) = #{0<=k<n : x_k in A_y} - n/2.                        (6.3)
```

There exists `y in T` such that

```text
D(y) >= |S|/(2*pi).                                         (6.4)
```

More precisely, if `|S|/(2*pi)>a`, then some `y` satisfies `D(y)>a`.

**Proof.**  Integrals below use normalized Lebesgue measure on `T`.  A fixed
point `x_k` belongs to `A_y` for exactly a half-circle's worth of centers
`y`.  Finite summation therefore gives

```text
integral_T D(y) dy = 0.                                     (6.5)
```

Let `I=[-1/4,1/4)`.  Since `x_k in A_y` exactly when `x_k-y in I`, the change
of variable `u=x_k-y` gives

```text
integral_T 1_I(x_k-y)*e(y) dy
  = e(x_k)*integral_I e(-u) du
  = e(x_k)/pi.                                              (6.6)
```

The last equality is exact:

```text
integral_{-1/4}^{1/4} cos(2*pi*u) du = 1/pi,
integral_{-1/4}^{1/4} sin(2*pi*u) du = 0.                   (6.7)
```

The constant `n/2` has zero first Fourier coefficient.  Summing (6.6) thus
proves

```text
integral_T D(y)*e(y) dy = S/pi.                             (6.8)
```

Write `D_+=max(D,0)`.  Equation (6.5) implies
`integral |D|=2*integral D_+`.  Hence, if
`M=sup_y D(y)`, then

```text
|S|/pi
  = |integral_T D(y)*e(y) dy|
  <= integral_T |D(y)| dy
   = 2*integral_T D_+(y) dy
  <= 2*M.                                                   (6.9)
```

This proves (6.4).  If the right side of (6.4) is strictly greater than
`a`, the definition of the supremum supplies a center with `D(y)>a`.
For the non-strict statement, `D(y)` belongs to the finite set
`{j-n/2 : 0<=j<=n}`, so its supremum is attained.
Half-open endpoints affect only finitely many centers and do not affect any
integral; the selected arc itself still has an unambiguous literal count.
QED.

## 7. Failure-to-discrepancy certificate

**Theorem 7.1 (one-scale certificate).**  Fix `K>1`.  If (5.1) holds at a
scale `t` and frequency `1<=h<=10`, then there are a shift `1<=r<H_t` and a
half-open circle arc `A` of exact length `1/2` such that

```text
#{0<=k<N_t-r :
    {h*(10^r-1)*10^k*pi} in A}
  - (N_t-r)/2
  > (K-1)*(N_t-r)/(2*pi*(H_t-1)).                           (7.1)
```

**Proof.**  Lemma 5.1 selects `r` with (5.2).  Apply Lemma 6.1 to the
`n=N_t-r` points in (3.2).  Since
`|S_{t,h,r}|>=Re(S_{t,h,r})`, its strict form yields (7.1).  QED.

This is an interval count, not a renamed correlation: the left side is the
literal number of orbit indices in one displayed half-circle minus its
uniform expected count.

**Corollary 7.2 (frequency and shift from a failed scale).**  Fix `K>1` and
`t>=0`.  If the all-frequency assertion at this scale fails, explicitly if

```text
there exists an integer h with 1<=h<=10 and
  E_{t,h}>K*H_t*N_t,                                       (7.2)
```

then there exist one frequency `1<=h<=10`, one shift `1<=r<H_t`, and one
half-open arc of length exactly `1/2` satisfying (7.1).

**Proof.**  Choose the frequency supplied by (7.2) and apply Theorem 7.1.
QED.

The restriction `K>1` is explicit and necessary for this argument to force
a positive excess from the diagonal baseline `H_t*N_t`.  Literal failure of
the uniform premise is stronger: it supplies failed scales for arbitrarily
large `K`, as used next.

**Corollary 7.3 (literal global failure).**  If the uniform T66 premise
fails in the sense of (3.5), then for every real `Delta>0` there exist

```text
t>=0,  1<=h<=10,  1<=r<H_t,
and a half-open arc A of length exactly 1/2
```

such that

```text
#{0<=k<N_t-r :
    {h*(10^r-1)*10^k*pi} in A}
  - (N_t-r)/2
  > Delta*(N_t-r)/(H_t-1).                                 (7.3)
```

**Proof.**  In (3.5), choose the nonnegative constant

```text
K_Delta = 1+2*pi*Delta > 1.                                 (7.4)
```

The resulting failed scale and frequency satisfy Theorem 7.1, whose
right side becomes exactly the right side of (7.3).  QED.

Thus failure forces arbitrarily large discrepancy after normalization by
the explicit single-shift scale `(N_t-r)/(H_t-1)`.  It does not assert that
any such certificate actually occurs for pi.

## 8. Discrepancy-to-T66 converse

**Theorem 8.1 (uniform half-circle converse).**  Suppose there is a real
`Delta>=0` such that, for every

```text
t>=0,  integer 1<=h<=10,  integer 1<=r<H_t,
and every half-open circle arc A of length 1/2,
```

the literal single-shift count satisfies

```text
abs(#{0<=k<N_t-r :
       {h*(10^r-1)*10^k*pi} in A}
    - (N_t-r)/2)
  <= Delta*(N_t-r)/(H_t-1).                                (8.1)
```

Then T66's fixed-pi shifted-correlation premise holds with the explicit
constant

```text
K = 1+pi*Delta.                                             (8.2)
```

**Proof.**  Fix `t,h,r` in the displayed ranges and use the notation of
Lemma 6.1.  The identity (6.8), followed directly by (8.1), gives

```text
|S_{t,h,r}|/pi
  = |integral_T D(y)*e(y) dy|
  <= integral_T |D(y)| dy
  <= Delta*(N_t-r)/(H_t-1).
```

Consequently,

```text
Re(S_{t,h,r})
  <= pi*Delta*(N_t-r)/(H_t-1).                              (8.3)
```

Insert (8.3), with no change to T66's shifts or triangular weights, into
(3.3).  Equation (4.3) gives

```text
E_{t,h}
  <= H*N
     + 2*pi*Delta/(H-1)
         *sum_{1<=r<H}(H-r)*(N-r)
  <= H*N
     + 2*pi*Delta/(H-1) * N*H*(H-1)/2
   = (1+pi*Delta)*H*N.                                     (8.4)
```

The chosen `K` is nonnegative, and `t,h` were arbitrary.  This is exactly
T66's proposition `FixedPiShiftedCorrelation K`.  QED.

In particular, (8.1) rules out every certificate (7.3) at its own value of
`Delta`, and it rules out literal global failure.  The factor two difference
between (7.4) and (8.2) is accounted for explicitly: extraction uses
`integral |D|=2*integral D_+` to obtain a one-sided excess, while the converse
assumes an absolute discrepancy bound.

## 9. Conditional composition with T63 and T66

Under (8.1), Theorem 8.1 supplies T66 with
`K=1+pi*Delta`.  The already kernel-checked T66 consequences therefore give

```text
sum_{h=1}^{10} X_h(N_t)^2
  <= (45/2)*(1+pi*Delta)^2*N_t^3,                           (9.1)
```

and, for every `Q0>=0`, `t>=0`, and `0<s<1`, the exact complete
selected-plus-unmatched-defect primitive contribution is bounded by

```text
10*((225/8)*(1+pi*Delta)^2+5)
  *(N_t+N_t^2*10^(-s)).                                    (9.2)
```

The contribution in (9.2) is the T63 polynomial (2.1) divided by the literal
width `sqrt(N_t^2-1)`, with both signed orientations and all frequencies
`1,...,10` retained.  Equations (9.1)-(9.2) are conditional compositions of
kernel-checked theorems with hypothesis (8.1).  This note supplies no witness
for `Delta` at pi.

## 10. Verdict and exact frontier

The new, lower-dimensional fixed-pi frontier is the uniform single-shift
half-circle estimate (8.1).  It concerns one shift and one interval count at
a time.  Theorem 8.1 proves that it implies T66's multi-shift triangular
condition, while Corollary 7.3 proves that literal failure of that condition
forces arbitrarily large normalized half-circle excess certificates.

This is not a finite computation and uses no unsupported fixed-pi estimate.
It proves neither (8.1) nor any weaker discrepancy estimate for pi.  It also
does not prove the full T29 predicate, C2, C3, C1, or the canonical ordered
long-lag collision estimate.

## 11. Local integrity check

From a directory containing only the delivered artifacts, run

```sh
sha256sum -c SHA256SUMS
```

This checks the byte-exact canonical statement and this note.
