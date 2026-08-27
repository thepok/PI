# T65: shifted-frequency van der Corput condition and its metric sibling

Status: **proof sketch**.  The T63 finite identity used in Sections 3 and 6 is
machine-checked.  All new reductions and metric calculations are proved in
prose below and are not Lean-formalized.  The metric theorem is only a
variable-phase residual-A12 sibling.  Nothing here estimates the fixed phase
`pi`, proves C2 or C3, proves C1, or answers the canonical collision question.
The T64 note was used only as sketch-level motivation; no T64 claim is taken
as an established premise.

## 1. Statement pin, normalized scope, and ambiguities

The byte-exact canonical statement is included as `CANONICAL_STATEMENT.txt`.
It is a locally formulated question, so there is no original external source
URL to preserve.  Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks for one constant `C_s`, for each `0<s<1`, that
simultaneously controls all positive `m,N` for the ordered long-lag collision
count of the fixed decimal expansion of pi.  T65 does not change or answer
that question.  It treats only the following residual-A12 primitive-sector
subproblem:

* `m=1`;
* `Q0` is any nonnegative integer, fixed before `t`; the exact final
  polynomial is independent of `Q0`;
* `t` is any nonnegative integer;
* `N=N_t=4*2^t+1`, so in particular `N>=5`;
* the frequencies are the ten integers `1<=h<=10`;
* the dyadic block is the literal half-open block `[1,N)`;
* both signed orientations and both the selected and unmatched-defect pieces
  are retained through T63's exact recombination;
* the fixed-pi statement below is conditional on a new shifted-correlation
  hypothesis;
* the unconditional conclusion is instead for Lebesgue-almost every variable
  phase `alpha` in `[0,1)` and is always labeled a sibling conclusion.

The potentially ambiguous quantifiers are therefore fixed as follows.  In the
fixed-phase condition, one `K` must work before every `t>=0` and every
`1<=h<=10`; it is independent of `Q0` because the orbit sums contain no `Q0`.
In the metric theorem, `K_alpha` may depend on `alpha`, but not on `Q0`, `t`,
`h`, or `s`.  The contribution identity and budget hold for every `Q0>=0`.
The metric theorem is simultaneous in all displayed `t,h` and every `0<s<1`,
but it says nothing about other `m,N`.  Only the orbit phase is replaced by
`alpha`; the Fourier factor `2*pi` is unchanged.

## 2. Exact sums, shifts, weights, and cutoff

Write

```text
e(x) = exp(2*pi*i*x),
N = N_t = 4*2^t+1,
H = H_t = ceil(sqrt(N)).
```

Thus `H` is the unique positive integer satisfying

```text
H-1 < sqrt(N) <= H.                                         (2.1)
```

Because `N>=5`, this also gives `3<=H<=N`.  Hence every displayed shift has
`1<=r<H<=N`, and `N-r` is a positive integer.

For real `alpha` and `1<=h<=10`, define

```text
z_k = e(h*10^k*alpha),
T_h,alpha(N) = sum_{0<=k<N} z_k,
X_h,alpha(N) = |T_h,alpha(N)|^2,

C_h,r(N;alpha)
  = sum_{0<=k<N-r} z_(k+r)*conj(z_k)
  = sum_{0<=k<N-r} e(h*(10^r-1)*10^k*alpha)                 (2.2)
```

for every shift `1<=r<H`.  Equation (2.2) audits the shifted
frequency literally: it is `h*(10^r-1)*10^k`, with no omitted factor of 10,
and the half-open summation endpoint is `k<N-r`.

The weighted shifted energy is

```text
V_h,t(alpha)
  = H*N + 2*sum_{r=1}^{H-1} (H-r)*Re C_h,r(N;alpha).         (2.3)
```

The weight is the integer triangular weight `H-r`, not a normalized or
unweighted substitute.  Define the shifted-frequency van der Corput condition

```text
SFVdC(K,alpha):
  K >= 0 and, for every t>=0 and 1<=h<=10,
  V_h,t(alpha) <= K*H_t*N_t.                                (2.4)
```

Condition (2.4) is the new fixed-pi frontier when `alpha=pi`.  This note does
not assert it at pi.

### The stated cutoff optimization

For a general integer `1<=H<=N`, the argument in Section 4 gives, under
`V<=K*H*N`,

```text
X <= K*N*(N+H-1)/H.                                        (2.5)
```

For `H<=N`, its leading term is `K*N^2/H`.  The explicit optimization criterion
used in this note is: require `H>=sqrt(N)`, so that this diagonal term is at
most `K*N^(3/2)` with coefficient one, and then minimize the integer `H` to
use the fewest shifted sums.  The unique optimizer for that stated constrained
problem is `H=ceil(sqrt(N))`.  More generally, any fixed positive multiple of
`sqrt(N)` gives the same exponent with a different constant, so no global
optimality over constants and shift count is claimed.  Section 8 gives a
metric exceptional probability of order `H/N`; the chosen cutoff makes this
order `N^(-1/2)`, summable on the dyadic family.  Larger sublinear cutoffs also
work but are not needed for the stated criterion.

## 3. The exact T63 polynomial and literal T29 budget

Define, for any phase `beta`,

```text
S_t(beta) = sum_{h=1}^{10} X_h,beta(N),
F_t(beta) = sum_{h=1}^{10} X_h,beta(N)^2,
W_t = sqrt(N^2-1).                                         (3.1)
```

The width is literally `sqrt(N^2-1)`.  It is not replaced by `N`, by the
block length `N-1`, or by an asymptotic equivalent.

For a primitive record pair `p`, write `d_p=blockDifferenceValue(p)`.  For
every `Q0>=0`, define the actual variable-phase complete selected-plus-defect
primitive contribution by the finite sums

```text
J_sd(Q0,t;beta)
  = (2/W_t) * [
      sum_{p in selectedRecordDomain(t)}
        sum_{h=1}^{10} cos(2*pi*h*d_p*beta)
      +
      sum_{p in unmatchedDefect(Q0,t)}
        sum_{h=1}^{10} cos(2*pi*h*d_p*beta)].                (3.2)
```

The factor `2` in (3.2) restores both signed orientations.  T63's
kernel-checked `complete_selected_defect_recombination`, specialized at its
fixed phase `beta=pi`, identifies (3.2) exactly as

```text
J_sd(Q0,t;pi)
  = [F_t(pi) - 4*(N-1)*S_t(pi) + 20*N^2 - 30*N]/W_t.        (3.2-pi)
```

Every term comes directly from summing T63's one-frequency polynomial

```text
X_h^2 - 4*(N-1)*X_h + 2*N^2 - 3*N                         (3.3)
```

over the inclusive ten-frequency set.  In particular, this identity retains the
linear correction `-4*(N-1)*S_t`, the quadratic term `+20*N^2`, the linear
term `-30*N`, the factor restoring both orientations, and the literal width.

For `0<s<1`, put

```text
T_s(1,N) = N + N^2*10^(-s).                                (3.4)
```

The specialized primitive-sector share of T29's right-hand budget is

```text
J_sd(Q0,t;beta) <= 10*A*T_s(1,N).                           (3.5)
```

This uses T29's literal frequency factor 10 and right-hand scale.  It is only
a budget for the complete primitive selected-plus-defect contribution, not a
claim about T29's cancelling sector, diagonal term, or full square function.

## 4. Constant-tracked van der Corput reduction

Fix `N,H,h,alpha` as above.  Extend `z_k` by zero outside `0<=k<N`, and for
`0<=n<=N+H-2` define

```text
A_n = sum_{j=0}^{H-1} z_(n-j).
```

Every `z_k` occurs in exactly the `H` sums with `n=k,...,k+H-1`; hence

```text
sum_{n=0}^{N+H-2} A_n = H*T_h,alpha(N).                     (4.1)
```

There are exactly `N+H-1` values of `n`.  Cauchy-Schwarz therefore gives

```text
H^2*|T_h,alpha(N)|^2
  <= (N+H-1)*sum_{n=0}^{N+H-2} |A_n|^2.                    (4.2)
```

Expanding the last sum, the diagonal pairs `j=l` contribute `H*N`.  For a
fixed positive difference `r=|j-l|`, there are exactly `H-r` ordered choices
in each orientation.  Zero extension leaves exactly `N-r` index products,
which are `C_h,r` in one orientation and its conjugate in the other.  Thus

```text
sum_n |A_n|^2
  = H*N + 2*sum_{r=1}^{H-1}(H-r)*Re C_h,r(N;alpha)
  = V_h,t(alpha).                                           (4.3)
```

In particular, `V_h,t(alpha)>=0`; the apparently signed expression (2.3) is
an exact sum of squares.  Combining (4.2) and (4.3) proves the explicit
van der Corput inequality

```text
X_h,alpha(N) <= (N+H-1)/H^2 * V_h,t(alpha).                 (4.4)
```

Assume `SFVdC(K,alpha)`.  Then

```text
X_h,alpha(N) <= K*N*(N+H-1)/H.                             (4.5)
```

By (2.1), `H-1<sqrt(N)` and `H>=sqrt(N)`.  Since `N>=5`,
`1<=sqrt(N)/2`, so

```text
(N+H-1)/H
  < (N+sqrt(N))/sqrt(N)
  = sqrt(N)+1
  <= (3/2)*sqrt(N).                                        (4.6)
```

Consequently, for each of the ten frequencies,

```text
X_h,alpha(N) <= (3/2)*K*N^(3/2),                            (4.7)
```

and after squaring and summing exactly ten terms,

```text
F_t(alpha) <= 10*(9/4)*K^2*N^3
             = (45/2)*K^2*N^3.                             (4.8)
```

This is the requested exact `N^3` sufficient scale.  It is a consequence of
the second-degree shifted-correlation condition (2.4), not a restatement of
the fourth-moment target.

## 5. From (4.8) to the literal primitive-sector budget

Set

```text
B = (45/2)*K^2,
A = (5/4)*(B+4) = (225/8)*K^2+5.                           (5.1)
```

All `X_h` are nonnegative, so `S_t>=0`.  Using the identity (6.5), proved
independently for variable phase below, without deleting any term from the
identity, and only then taking an upper bound, gives

```text
W_t*J_sd(Q0,t;alpha)
  = F_t(alpha)-4*(N-1)*S_t(alpha)+20*N^2-30*N
  <= F_t(alpha)+20*N^2
  <= B*N^3+4*N^3
  = (B+4)*N^3.                                              (5.2)
```

Here `20*N^2<=4*N^3` uses the literal fact `N>=5`.  For every `0<s<1`,

```text
W_t = sqrt((N-1)*(N+1)) >= N-1 >= (4/5)*N,                 (5.3)
T_s(1,N) >= N^2*10^(-s) >= N^2/10.                         (5.4)
```

The last inequality may be strict for `s<1`; the weak form is sufficient.
Equations (5.3)-(5.4) give

```text
10*A*W_t*T_s(1,N) >= (4/5)*A*N^3 = (B+4)*N^3.              (5.5)
```

Since `W_t>0`, (5.2) and (5.5) prove

```text
J_sd(Q0,t;alpha) <= 10*A*(N+N^2*10^(-s))                    (5.6)
```

for every `Q0>=0`, displayed `t`, and `0<s<1`, whenever (2.4) holds.  At
`alpha=pi`, T63 makes `J_sd(Q0,t;pi)` exactly the selected-plus-defect
primitive contribution, so (5.6) is a conditional fixed-pi reduction.  No
claim that (2.4) holds at pi is made.

## 6. Independent variable-phase audit of the polynomial

The T63 theorem itself is instantiated at pi.  To avoid silently applying it
at a new phase, this section independently derives (3.2) for every real
`beta`, using only the same finite domains.

Fix `h,N,beta`, write `z_k=e(h*10^k*beta)`, `T=sum_{k<N}z_k`, and
`X=|T|^2`.  Since `|z_k|=1`, the sum over ordered unequal pairs is

```text
Q = sum_{a,b<N; a!=b} z_a*conj(z_b) = X-N.                 (6.1)
```

The square `Q*conj(Q)` sums all two-record quartets.  The primitive domain
removes the attacks `a=c` and `b=d`.  For the first attack, summing by its
shared coordinate gives

```text
sum_{a<N} |T-z_a|^2
  = sum_a [X+1-2*Re(T*conj(z_a))]
  = N*X+N-2*X.                                              (6.2)
```

The second attack has the same value.  Their intersection has exactly
`N*(N-1)` ordered unequal pairs, each of weight one.  Finite
inclusion-exclusion is therefore

```text
(X-N)^2 - 2*(N*X+N-2*X) + N*(N-1)
  = X^2-4*(N-1)*X+2*N^2-3*N.                               (6.3)
```

This proves every term of (3.3) for arbitrary `beta`.  Here is the complete
finite reindexing from (3.2), rather than an appeal to the fixed-pi theorem at
a new phase:

1. The kernel-checked imported lemma `selected_defect_exhaustive_partition`,
   consumed explicitly in T63's proof of
   `complete_selected_defect_recombination`, says that
   `selectedRecordDomain(t)` and `unmatchedDefect(Q0,t)` are disjoint and their
   union is the positive primitive record domain, for every `Q0,t`.
2. Applying the two orientations to that positive domain gives T63's
   `signedPrimitiveDomain(Q0,t)`.  Its kernel-checked
   `signedPrimitive_coordinates_image` maps onto the literal nonattacking
   ordered-quartet domain, and `recordPairCoordinates_injOn` makes the map a
   bijection rather than a quotient with hidden multiplicity.
3. For a positive record `p`, the kernel-checked integer relation used in
   T63's `recordPairCharacter_eq_phase` says that the difference of the two
   record frequencies is exactly `d_p`.  This relation is independent of the
   value of the phase.  Therefore the general-beta character of one
   orientation is `e(h*d_p*beta)`, while reversing the orientation gives its
   conjugate.

Consequently, reversing a positive primitive difference replaces
`e(h*d_p*beta)` by its conjugate, and

```text
e(h*d*beta)+e(-h*d*beta)=2*cos(2*pi*h*d*beta).              (6.4)
```

By steps 1-3, the left side of (6.3) over the nonattacking quartet domain is
exactly the numerator of (3.2), with no missing orientation or multiplicity.
Summing (6.3) for the literal ten values `h=1,...,10` and dividing by the
unchanged width `W_t` proves, for every `Q0,t,beta`,

```text
J_sd(Q0,t;beta)
  = [F_t(beta)-4*(N-1)*S_t(beta)+20*N^2-30*N]/W_t.          (6.5)
```

In particular, the right side is independent of `Q0`.  This is a finite
algebra identity, not an estimate at pi.

## 7. Every finite metric moment used

Let `alpha` be uniformly distributed on `[0,1)`.  We use only the elementary
orthogonality identities, valid for integers `q,q'>0`,

```text
integral_0^1 e(q*alpha) d alpha = 0,                         (7.1)

integral_0^1 cos(2*pi*q*alpha)*cos(2*pi*q'*alpha) d alpha
  = 1/2  if q=q',
  = 0    if q!=q'.                                          (7.2)
```

They follow by integrating the exponential characters; no independence
assumption is used.

For fixed nonzero `h`, the positive integers

```text
q_h,r,k = h*(10^r-1)*10^k,
1<=r<H, 0<=k<N-r,                                           (7.3)
```

are pairwise distinct as `(r,k)` varies.  Indeed, equality of two such
integers permits cancellation of `h`.  Since `10^r-1` is odd, its 2-adic
valuation is zero, while the 2-adic valuation of `10^k` is `k`; hence equality
first forces `k=k'`, and then `10^r-1=10^r'-1` forces `r=r'`.

By (7.1), every cosine in (2.3) has mean zero, so the first moment is exactly

```text
E[V_h,t] = H*N.                                             (7.4)
```

Moreover,

```text
V_h,t-H*N
  = 2*sum_{r=1}^{H-1} sum_{k=0}^{N-r-1}
      (H-r)*cos(2*pi*q_h,r,k*alpha).                        (7.5)
```

Pairwise distinctness and (7.2) kill every cross term in the square.  Thus
the second centered moment, with every multiplicity and weight retained, is

```text
E[(V_h,t-H*N)^2]
  = 2*sum_{r=1}^{H-1} (H-r)^2*(N-r).                        (7.6)
```

In particular,

```text
E[(V_h,t-H*N)^2]
  <= 2*N*sum_{j=1}^{H-1} j^2
  = N*(H-1)*H*(2*H-1)/3.                                   (7.7)
```

This is the complete finite-moment input to the metric argument.  No moment
of `|C_h,r|`, no cross-frequency independence, and no unproved cross-shift
covariance estimate is being hidden.

## 8. Almost-everywhere compatibility

Chebyshev's inequality applied to (7.4)-(7.7) gives

```text
Leb{alpha: V_h,t(alpha)>2*H*N}
  <= E[(V_h,t-H*N)^2]/(H^2*N^2)
  <= (H-1)*(2*H-1)/(3*H*N)
  < 2*H/(3*N).                                              (8.1)
```

From `H<sqrt(N)+1` and `N>=5`, we have `H<(3/2)*sqrt(N)`, hence

```text
Leb{alpha: V_h,t(alpha)>2*H*N} < 1/sqrt(N).                 (8.2)
```

Taking the union over the ten literal frequencies costs at most a factor 10.
Since `N_t=4*2^t+1>4*2^t`,

```text
sum_{t>=0} 10/sqrt(N_t)
  < 5*sum_{t>=0} 2^(-t/2) < infinity.                       (8.3)
```

The first Borel-Cantelli lemma now implies that, for Lebesgue-almost every
`alpha`, there is `t_0(alpha)>=1` such that

```text
V_h,t(alpha) <= 2*H_t*N_t                                  (8.4)
```

for every `t>=t_0(alpha)` and all `1<=h<=10`.  Independence is not needed.
Absorb the finitely many earlier scales by defining

```text
K_alpha = max(2,
  max { V_h,t(alpha)/(H_t*N_t) :
        0<=t<t_0(alpha), 1<=h<=10 }).                       (8.5)
```

The set in (8.5) is finite and every denominator is positive, so
`K_alpha<infinity`.  Equations (8.4)-(8.5) prove `SFVdC(K_alpha,alpha)` for
all displayed scales and frequencies.

Combining this with Sections 4-6 yields the explicit consequences

```text
F_t(alpha) <= (45/2)*K_alpha^2*N_t^3,                       (8.6)

J_sd(Q0,t;alpha)
  <= 10*A_alpha*(N_t+N_t^2*10^(-s))                        (8.7)

A_alpha = (225/8)*K_alpha^2+5,                              (8.8)
```

simultaneously for every `Q0>=0`, `t>=0`, and every `0<s<1`.

## 9. Verdict and fixed-pi frontier

**Proved variable-phase sibling verdict.**  For Lebesgue-almost every
`alpha`, the explicit triangularly weighted shifted-frequency condition
`SFVdC(K_alpha,alpha)` holds with one finite phase-dependent constant across
all `t>=0` and `1<=h<=10`.  It implies the exact `N_t^3` fourth-moment scale
and, with every T63 polynomial term and the literal width retained, the
specialized selected-plus-defect primitive budget (8.7).

The strictly narrower unresolved fixed-pi statement exposed by this note is

```text
there exists K>=0 such that, for every t>=0 and 1<=h<=10,

H_t*N_t
  + 2*sum_{r=1}^{H_t-1}(H_t-r)
      Re sum_{k=0}^{N_t-r-1}
        exp(2*pi*i*h*(10^r-1)*10^k*pi)
  <= K*H_t*N_t,                                             (9.1)

where N_t=4*2^t+1 and H_t=ceil(sqrt(N_t)).
```

No estimate for (9.1) is asserted.  In particular, the metric theorem cannot
be specialized to pi, and this note proves neither C2, C3, C1, nor the
canonical ordered long-lag collision bound.

## 10. Local integrity check

From a directory containing only the delivered artifacts, run

```sh
sha256sum -c SHA256SUMS
```

This checks the byte-exact canonical statement and this note.
