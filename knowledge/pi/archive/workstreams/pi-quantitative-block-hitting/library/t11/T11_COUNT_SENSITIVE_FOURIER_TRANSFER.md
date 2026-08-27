# T11: Count-sensitive Fourier transfer away from decimal boundaries

Status: `proof sketch` (a self-contained rigorous paper proof, not a Lean
formalization).

## 1. Provenance, scope, and quantifiers

- Agenda item: T11, serving G9.
- Canonical source: `knowledge/pi/statements/pi-quantitative-block-hitting.txt`.
- Canonical source SHA-256:
  `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
- Original source URL: none; the problem is locally formulated and its source
  file records the provenance.
- Reused accepted literature audit: `knowledge_library/t9/T9_DETERMINISTIC_ORBIT_AUDIT.md`,
  SHA-256
  `9734cd424f252b6f166a601c1d6f6bd1297645b6d39d6a276d2ba2b90118c350`.
- The only primary-source fact about pi used below is the Salikhov theorem
  pinned by T9 as [SAL2008], DOI
  `10.1070/RM2008v063n03ABEH004543`, PDF SHA-256
  `a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d`.

This note proves a **conditional reduction** for an arbitrary finite set of
points that stays a known positive distance from the decimal-cylinder
boundaries. It then calculates only the extremely small separation that T9's
source-pinned irrationality statement permits for pi. It supplies no
cancellation bound for pi, no natural-scale frequency estimate, and no claim
that C1 is true or false.

The quantifiers in the general result are the following. Fix integers `k >= 1`
and `N >= 1`, put `q=10^k`, choose a cylinder label
`a in {0,...,q-1}`, and let `x_0,...,x_(N-1)` be points of the circle
`T=R/Z`. Assume that one specified real number `eta>0` satisfies

```text
dist_T(x_n, B_q) >= eta                 (0 <= n < N),
B_q = {j/q mod 1 : 0 <= j < q}.
```

Distance is circular distance. Cylinders are the half-open arcs
`I_a=[a/q,(a+1)/q)` modulo one; in particular, `I_(q-1)` ends at the same
circle point as `I_0` begins. Since `N>=1`, the hypothesis itself implies
`eta <= 1/(2q) <= 1/2`. No assertion is made when `N=0`, since count
separation is then vacuous.

## 2. Preliminary exact Fourier identity for the quantized histogram

Write `{x}` for the representative of `x in T` in `[0,1)`, and define its
length-`k` label

```text
ell_q(x) = floor(q*{x}) in {0,...,q-1}.
```

If `x_n={10^n*x}` and `x` has a nonterminating decimal expansion not ending
in repeating nines, then `ell_q(x_n)` is exactly the base-10 integer encoded
by the next `k` digits after position `n`; leading zeros are retained by
viewing the label as a padded length-`k` word. Thus the counts below are the
length-`k` block histogram. The later separation hypothesis excludes q-adic
endpoint ambiguity for every point used by the estimator.

The exact number of points in `I_a` is

```text
A_a = #{0 <= n < N : x_n in I_a}
    = sum_(n=0)^(N-1) 1_{ell_q(x_n)=a}.
```

Let `e(t)=exp(2*pi*i*t)`. Character orthogonality on `Z/qZ` gives, for every
pair of integer labels `ell,a`,

```text
1_{ell=a} = (1/q) sum_(r=0)^(q-1) e(r*(ell-a)/q).
```

Indeed, the right side is `1` if `ell-a` is divisible by `q`; otherwise it is
the geometric sum `(1-z^q)/(q*(1-z))=0` with
`z=e((ell-a)/q) != 1`. Summing over the points gives the exact finite identity

```text
A_a = (1/q) sum_(r=0)^(q-1) e(-r*a/q)
                    sum_(n=0)^(N-1) e(r*ell_q(x_n)/q).        (2.1)
```

This identity is only preliminary. Its inner phase contains the discontinuous
quantization `floor(q*{x_n})`; it is not an ordinary orbit sum
`sum_n e(h*x_n)`. The next construction replaces the quantized characters by
ordinary circle characters while retaining the integer count to error less
than `1/2`.

## 3. The explicit polynomial

For an integer `M>=0`, use the normalized Fejer kernel

```text
F_M(t) = (1/(M+1)) * (sin(pi*(M+1)*t)/sin(pi*t))^2
       = sum_(|h|<=M) (1-|h|/(M+1))*e(h*t).                  (3.1)
```

At integral `t`, the quotient is defined by continuity. Thus `F_M>=0` and
`integral_T F_M(t) dt=1`. Set

```text
M = ceil(N/eta),
P_(a,M)(x) = integral_T 1_{I_a}(x-t) F_M(t) dt.              (3.2)
```

The polynomial is completely explicit. With the Fourier convention

```text
hat(f)(h) = integral_T f(x)e(-h*x) dx,
```

its expansion is

```text
P_(a,M)(x) = sum_(|h|<=M) c_h e(h*x),                       (3.3)
c_h = (1-|h|/(M+1))*hat(1_{I_a})(h),
```

where

```text
hat(1_{I_a})(0) = 1/q,

hat(1_{I_a})(h)
  = [e(-h*a/q)-e(-h*(a+1)/q)]/(2*pi*i*h)
  = e(-h*(a+1/2)/q) * sin(pi*h/q)/(pi*h)       (h != 0).    (3.4)
```

Consequently

```text
c_0 = 1/q,
|c_h| <= min(1/q, 1/(pi*|h|))                 (0<|h|<=M),  (3.5)
c_(-h) = conjugate(c_h).
```

For the first bound in (3.5), use
`|hat(1_{I_a})(h)| <= integral_(I_a) 1 dx=1/q`; for the
second use `|sin(pi*h/q)|<=1` in (3.4). The Fejer multiplier has modulus at
most one. In particular `P_(a,M)` is real-valued and has degree at most

```text
M = ceil(N/eta) <= N/eta+1.                                  (3.6)
```

The sharp displayed degree bound is independent of `q`; the dependence on
`q` is in the interval and coefficients. This is stronger than inserting an
unnecessary extra factor of `q` into the degree.

## 4. Boundary separation and strict total error

We first record a tail bound with all constants. Represent `t in T` by
`u in [-1/2,1/2]`, so `||t||_T=|u|`. The elementary inequality
`|sin(pi*u)| >= 2|u|` on this interval and `|sin(pi*(M+1)*u)|<=1` imply

```text
F_M(u) <= 1/(4*(M+1)*u^2)                    (0<|u|<=1/2).
```

Hence, for `0<eta<=1/2`,

```text
integral_(||t||_T>=eta) F_M(t) dt
 <= 2 * integral_eta^(1/2) [1/(4*(M+1)*u^2)] du
 =  (1/(2*(M+1))) * (1/eta-2)
 <= 1/(2*(M+1)*eta).                                          (4.1)
```

Fix one of the points `x_n`. Whenever `||t||_T<eta`, the circular arc from
`x_n` to `x_n-t` meets no point of `B_q`, by the separation hypothesis.
Therefore the two points lie in the same connected component of
`T\B_q`, and

```text
1_{I_a}(x_n-t) = 1_{I_a}(x_n).
```

Using positivity and unit mass of `F_M`, the possible discrepancy is confined
to the tail:

```text
|P_(a,M)(x_n)-1_{I_a}(x_n)|
 <= integral_(||t||_T>=eta) F_M(t) dt
 <= 1/(2*(M+1)*eta).                                         (4.2)
```

The sets where `||t||_T=eta` or an endpoint is met have measure zero, so the
half-open endpoint convention introduces no missing term. Summing (4.2), and
using `M=ceil(N/eta)`, gives

```text
|sum_(n=0)^(N-1) P_(a,M)(x_n) - A_a|
 <= N/(2*(M+1)*eta)
 <  1/2,                                                       (4.3)
```

because `M+1>N/eta`. The last inequality is strict, as required.

## 5. Expansion into ordinary orbit exponential sums

Define the ordinary finite sums

```text
S_h(x;N) = sum_(n=0)^(N-1) e(h*x_n),             h in Z.
```

The polynomial is finite, so interchanging its frequency and point sums in
(3.3) is purely algebraic. The estimator in (4.3) is

```text
E_a(x;N,eta)
 := sum_(n=0)^(N-1) P_(a,M)(x_n)
  = N/q + sum_(1<=|h|<=M) c_h S_h(x;N),                       (5.1)
```

with `c_h` given exactly by (3.4) and the Fejer multiplier. Equations (4.3)
and (5.1) prove the count-sensitive transfer:

```text
|E_a(x;N,eta)-A_a| < 1/2.                                    (5.2)
```

Since `A_a` is an integer, it is the unique nearest integer to the real number
`E_a`. In particular:

```text
A_a=0  implies  -1/2 < E_a < 1/2,
A_a=1  implies   1/2 < E_a < 3/2.
```

Thus zero occurrences and one occurrence lie in disjoint estimator ranges.
More generally, (5.1) recovers the complete histogram count in the specified
cylinder, not merely whether a normalized discrepancy is small.

## 6. The pi specialization permitted by T9, and no more

This section uses no claim about pi beyond the source-pinned statement in T9.
Fix `mu>7.60630852`. T9, Section 5.1, extracts from [SAL2008] that there is a
denominator threshold. Salikhov prints `q>q_0`; increasing and integerizing
that unspecified threshold lets us write it as `Q_0=Q_0(mu)` such that, for
every integer `Q>=Q_0`,

```text
||Q*pi|| >= Q^(1-mu).                                        (6.1)
```

The source and T9 do not supply a numerical value of `Q_0`, so none is asserted
here. Let

```text
x_n = {10^n*pi},             0 <= n < N,
q   = 10^k,
```

and suppose `10^k>=Q_0`. For every such `n`, elementary scaling of the q-adic
grid gives the exact identity

```text
dist_T(x_n,B_q)
 = (1/q) * ||q*x_n||
 = (1/q) * ||10^(n+k)*pi||.                                 (6.2)
```

Applying (6.1) to `Q=10^(n+k)` and using `1-mu<0` yields the uniform separation

```text
dist_T(x_n,B_q)
 >= (1/q)*(10^(n+k))^(1-mu)
 >= eta_pi(k,N,mu),

eta_pi(k,N,mu)
 := 10^(-k) * 10^(-(mu-1)*(N-1+k)).                          (6.3)
```

The last value corresponds to the largest index `n=N-1`, where the lower
bound is smallest. The general theorem therefore permits

```text
M_pi(k,N,mu)
 := ceil(N/eta_pi(k,N,mu))
  = ceil(N * 10^k * 10^((mu-1)*(N-1+k))),                    (6.4)
```

and

```text
deg P_(a,M_pi)
 <= M_pi
 <= N * 10^k * 10^((mu-1)*(N-1+k)) + 1.                     (6.5)
```

At frequencies `|h|<=M_pi`, formula (5.1) involves exactly the ordinary pi
orbit sums

```text
S_h(pi;N) = sum_(n=0)^(N-1) exp(2*pi*i*h*10^n*pi),           (6.6)
```

because replacing `10^n*pi` by its fractional part does not change an
integer-frequency exponential.

For `10^k<Q_0`, Salikhov still implies that pi is irrational and therefore no
finite point `x_n` is exactly a q-adic boundary, but the pinned statement does
not provide the numerical onset needed to replace (6.3) by a fully explicit
uniform numerical bound. This note makes no stronger finite-`k` claim.

The scale (6.4) is intentionally reported even though it is unusably large.
For example, inserting a canonical-size horizon `N` comparable to
`k*10^k` puts `N` itself in the exponent `(mu-1)N`. This is not a frequency
bound at the natural cylinder scale `10^k`, nor at T3's `10^(2k)` scale. T9
explicitly warns that Salikhov supplies pointwise lower bounds on
`||Q*pi||`, not cancellation upper bounds for (6.6); this note does not infer
such cancellation.

## 7. Exact conclusion and limitations

The proved conditional statement is:

> If `N` circle points have known distance at least `eta>0` from every
> length-`k` decimal-cylinder boundary, then every specified cylinder count is
> the unique integer within distance `1/2` of the explicit ordinary Fourier
> estimator (5.1). Its coefficients satisfy (3.4)-(3.5), and frequencies only
> through `ceil(N/eta)` occur.

For the pi orbit, T9's Salikhov input instantiates only the boundary-separation
premise, above its unspecified denominator threshold, and produces the huge
frequency scale (6.4). It does not estimate the ordinary sums (6.6). Therefore
this conditional reduction neither proves nor refutes C1, gives no
natural-scale estimate, and does not promote the canonical problem from
`open`.

## References

- [T9] `knowledge_library/t9/T9_DETERMINISTIC_ORBIT_AUDIT.md`, especially
  Sections 3 and 5.1; SHA-256
  `9734cd424f252b6f166a601c1d6f6bd1297645b6d39d6a276d2ba2b90118c350`.
- [SAL2008] V. Kh. Salikhov, *On the irrationality measure of pi*, Russian
  Math. Surveys 63 (2008), 570-572. DOI
  `10.1070/RM2008v063n03ABEH004543`; retained PDF SHA-256
  `a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d`.
