# T122 actual-forcing noncanonical survivor

Date: 2026-08-22 UTC

Status: `proof sketch`

Let the audited BBP scalar forcing be

```text
C_n=R_(n+1)-10*R_n,
h_n=C_(n+1)-C_n.
```

For `n>=2`, (40av) gives `h_n<0` and

```text
sum_(m>=N) |h_m| = C_N-144*pi
                       < (5/8)^(N+1)/(N+1)^2.
```

Define the stable future-weighted difference

```text
d_n = -sum_(r>=0) 10^(-r-1)*h_(n+r)  > 0.
```

Absolute convergence and reindexing give the exact identity

```text
d_(n+1)=10*d_n+h_n.
```

Fix `N=2` and choose

```text
e_2=(455-C_2+d_2)/9,
e_(n+1)=e_n+d_n.
```

If `F_n=e_(n+1)-10*e_n`, then

```text
F_(n+1)-F_n=h_n=C_(n+1)-C_n,
F_2=C_2-455.
```

Consequently

```text
e_(n+1)-10*e_n=C_n-455                 (n>=2).
```

For any integer `q_2`, define

```text
q_(n+1)=10*q_n+455,
R*_n=q_n+e_n.
```

Then this noncanonical orbit preserves the complete actual first-order forcing:

```text
R*_(n+1)-10*R*_n=C_n                   (n>=2).
```

Its first-order integer carry is constantly `455`, and its T122 second-order
carry is exactly zero:

```text
kappa_n=q_(n+2)-11*q_(n+1)+10*q_n=0.
```

## Permanent survivor bound

At `N=2`, put `g_2=C_2-144*pi`.  Equation (40av) gives

```text
0<g_2<125/4608,
0<d_2<g_2/10<25/9216,
sum_(n>=2)d_n<g_2/9<125/41472.
```

Using the elementary enclosure `3.14159<pi<3.14160` yields, for every `n>=2`,

```text
7437523/25920000 < e_n < 76057327/259200000,
0.286941...       < e_n < 0.293432.
```

Thus every `e_n` is already the half-open centered representative, every
nearest integer is `q_n`, and the trajectory remains uniformly outside even
the survivor hole `|e|<0.28` forever.

## Exact scope

This is stronger in one direction than the modified-forcing separator (40ay):
it preserves every actual rational `C_n` and hence every actual four-pole
`h_n`, together with the centered interval constraint at every intermediate
index and admissible carries.  Since both the canonical and constructed rows
have the same first-order forcing,

```text
R*_n-R_n=10^(n-2)*(R*_2-R_2).
```

This explicit homogeneous freedom is consistent with the coboundary identity
(40ax), but the survivor construction additionally chooses its phase and
checks every centered bound.

The initial phase is a freely chosen real phase, not required or shown to be
rational; it is not the canonical rational BBP value `R_2`.  Therefore this
closes only claims that the actual forcing, centering, or abstract carry
language compels every compatible phase to return.  It does not close an
argument that essentially selects the canonical rational initial phase through
the full BBP numerator/denominator.  It proves neither `(D)` nor V1, and V1
remains open.
