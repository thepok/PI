# Mixed-order Fejer boundary kernels

Status: `proof sketch`

Date: 2026-08-24 UTC

This note records an independently audited, repository-new extension of the
boundary-matched kernel. It has not been literature-checked or Lean-formalized.
It improves two finite sufficient criteria, but proves no cancellation estimate
for the decimal orbit of pi and therefore does not prove V1.

## Kernel and exact coefficients

For

```text
a_m(j) = 1 - |j|/m  when |j| < m, and 0 otherwise,
F_m(t) = sum_j a_m(j) exp(2*pi*i*j*t),
gamma_q = cos(pi/q),   d_q = 1 - gamma_q,
```

fix integers `q >= r >= 1` and define

```text
A_(q,r)(t) = (cos(2*pi*t) - gamma_q) F_q(t) F_r(t).
B_(q,r)(h) = sum_j a_q(j) a_r(h-j).
C_(q,r)(h) = (B_(q,r)(h-1) + B_(q,r)(h+1))/2
             - gamma_q B_(q,r)(h).
```

Then

```text
A_(q,r)(t) = sum_(|h| <= q+r-1) C_(q,r)(h) exp(2*pi*i*h*t),
B_(q,r)(0) = (3*q*r - r^2 + 1)/(3*q),
B_(q,r)(1) = B_(q,r)(0) - 1/q.
```

The signed zero coefficient and total signed coefficient sum are exactly

```text
mu_(q,r)  = C_(q,r)(0)
          = d_q (3*q*r - r^2 + 1)/(3*q) - 1/q,
tau_(q,r) = sum_h C_(q,r)(h) = A_(q,r)(0) = d_q*q*r.
```

The convolution calculation, including the overlapping-support case
`r > q/2`, gives the useful positivity implication

```text
mu_(q,r) > 0  ==>  C_(q,r)(h) > 0 for every |h| <= q+r-1.
```

Consequently the nonzero coefficient mass is exactly `tau_(q,r)-mu_(q,r)`.
For a `q`-cell interval with centre `c`, `A_(q,r)(x-c) <= 0` outside the
interval and is positive in its open interior. The half-open endpoints both
have value zero, so a positive empirical kernel sum forces an interior hit.

## Finite directional hit and worst-mode threshold

For a nonempty finite sample `x_0,...,x_(N-1)`, write

```text
S_h(N) = sum_(n<N) exp(2*pi*i*h*x_n),
D_(q,r)(N,c) = -(1/N) Re sum_(0<|h|<=q+r-1)
                 C_(q,r)(h) exp(-2*pi*i*h*c) S_h(N).
```

The exact identity

```text
(1/N) sum_(n<N) A_(q,r)(x_n-c) = mu_(q,r) - D_(q,r)(N,c)
```

therefore proves, whenever `mu_(q,r)>0`,

```text
D_(q,r)(N,c) < mu_(q,r)  ==>  the target interval is hit.
```

With

```text
M_(q+r-1)(N) = max_(0<|h|<=q+r-1) |S_h(N)|/N,
rho_(q,r) = mu_(q,r)/(tau_(q,r)-mu_(q,r)),
```

an empty target implies `M_(q+r-1)(N) >= rho_(q,r)`.

## Decimal support and threshold gain

At every decimal scale `q=10^k`, take `r=4*q/5`. Then

```text
support H = 9*q/5 - 1,
mu_mix = d_q (44*q/75 + 1/(3*q)) - 1/q,
tau_mix = (4/5) d_q q^2.
```

Let `rho_sym` be the corresponding ratio for the existing symmetric choice
`r=q`, and define

```text
Theta_q = 1/(2*q)    if q=10,
          12/(25*q)  if q>=100.
```

The audited exact estimates give the strict sandwich

```text
rho_mix > Theta_q > rho_sym,
```

while the active support falls from `2*q-1` to `9*q/5-1`. Thus the corrected
pointwise sufficient premise is the non-strict condition

```text
M_(9*q/5-1)(N) <= Theta_q,
```

or, at the exact threshold, `M_(9*q/5-1)(N) < rho_mix`. Either contradicts
the empty-target lower bound. Using `< Theta_q` is sufficient but needlessly
stronger.

For the exact decimal pi orbit, the conditional premise

```text
for every k>=1, there is N_k>0 with
M_(9*10^k/5-1)(N_k) <= Theta_(10^k)
```

therefore hits every cylinder of length `k` and implies V1. This remains a
conditional implication because the displayed bound is not known for pi.

This pointwise improvement has an exact finite separator. On the uniform grid

```text
N = 9*q/5,   x_n = n/N,
```

all mixed active sums vanish, whereas `|S_N(N)|/N=1` and `N<=2*q-1`, so the
still-active symmetric pointwise condition fails. This is a separator for
finite predicates only, not a statement about the actual pi orbit.

## Directional separator and conditional V1 consumer

The order can instead depend on the target word. For a word `s`, let
`q_s=10^|s|`, let `c_s` be the centre of its exact decimal cylinder, and use
the corresponding directional defect above. Then

```text
for every nonempty word s,
there exist N_s>0 and 1<=r_s<=q_s such that
mu_(q_s,r_s)>0 and D_(q_s,r_s)(N_s,c_s)<mu_(q_s,r_s)
```

implies canonical V1: the finite directional hit supplies an occurrence of
each requested word. The existing boundary-directional premise is the special
case `r_s=q_s`.

Strict weakening at the level of finite predicates already occurs for
`q=10`, target `[0,1/10)`, centre `c=1/20`, `r=4`, and `N=130`: take one
sample at `c` and 129 samples at `c+1/4=3/10`. Here

```text
mu_(10,4) = (7/2)(1-cos(pi/10)) - 1/10 > 17/250,
```

and `F_4(1/4)=0`, so the mixed empirical kernel sum is
`40*(1-cos(pi/10))>0`; hence `D_(10,4)<mu_(10,4)`. For the symmetric
`r=10` kernel the same sum is

```text
(2500 - 2629*cos(pi/10))/25 < -179/25000 < 0,
```

so `D_(10,10)>mu_(10,10)`. The zero mode is included on both sides.

## Claim boundary

Novelty here means only that this mechanism was not previously recorded in
the repository; no literature novelty claim is made. No actual-pi
cancellation estimate is proved, and the finite separators do not establish
any strict nonimplication for the actual pi orbit. This does not control the
primitive sums left open after T139, prove T124 for pi, establish density or
normality, or prove V1.
