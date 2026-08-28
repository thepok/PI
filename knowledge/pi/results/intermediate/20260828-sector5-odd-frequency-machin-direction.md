# Sector-5 retention and one-sided Machin direction

Date: 2026-08-28 UTC

Claim boundary: the T169/T179/T189 inputs are `machine-checked`. The sector-5
collapse, sharp Machin bracket, and Taylor implication below are `proof
sketch`. The node computation is an independently reproduced `experiment`,
not a directed-interval certificate. No unbounded transport theorem is proved.

## Why sector 5 must remain live

At the actual-π root `(q,A)=(1000,334)`, the literal child `d=1` is an
experimental FMR witness and legally reaches `(10000,1334)`. Independent
60-decimal replay of the T174 closed kernel and T139 endpoint identity gives

```text
B(1000,334,1000)          = 3671.258027925608...
G_1                       = -4845.137892060974...
D_1                       = 17344.376761789067...
B(10000,1334,10000)       = 16170.496897653700...
```

At the reached node, `d=5` is the unique FMR witness:

```text
G_5                       = -38482.458905115444...
D_5                       = 105639.815585471334...
G_5 + D_5                 = 67157.356680355889...
```

All ten cyclic adjacent averages of `Y_d=D_d-(-G_d)_+` are negative. More
generally, for a convex mask `w`, put

```text
mu5(w) = sum_d w_d*(-1)^d.
```

Every sector-5-annihilating mask has `mu5=0`, hence equal even and odd mass.
The experimental extrema

```text
E = max_(d even) Y_d = -93553.778220620540...
O = max_(d odd)  Y_d =  67157.356680355889...
```

give

```text
sum_d w_d Y_d <= (E+O)/2 = -13198.210770132325... < 0.
```

Any positive convex statistic at this node therefore needs
`mu5 < -0.164247620779...`, equivalently odd mass greater than
`0.582123810389...`. This closes uniform adjacent-pair and parity-neutral
convex transport, but not the deterministic greedy path.

The replay is
[`t189_parity_sector5_separator.py`](../../../../workflows/experiments/t189_parity_sector5_separator.py).
It uses 72 suffix digits and is deliberately labelled `experiment`. Three
independent high-precision/extended-precision implementations reproduced the
sign pattern. They did **not** reproduce the original Pro memo's claimed
sub-`10^-6` outward intervals, so those intervals are rejected.

## Exact sector-5 collapse

Let `x_n={10^n*pi}`, `y_n={5*x_n}={10^n*(5*pi)}`, and let `K_(q,5)` be T179's
suffix kernel. Its half-integer frequencies give

```text
K_(q,5)(t+1) = -K_(q,5)(t).
```

Writing `5*x_n=j_n+y_n` and `epsilon_n=floor(2*y_n)` yields

```text
predecessorDigit(n)=2*j_n+epsilon_n,
x_(n+1)=2*y_n-epsilon_n.
```

The parity factor cancels the branch shift exactly, so

```text
Sector_5(q,A,N)
  = sum_(n<N) K_(q,5)(2*y_n-c_(q,A))
  = 10 * sum_(ell<2q) alpha_(10q,10ell+5)
      * e(-(ell+1/2)c_(q,A))
      * sum_(n<N) e((2ell+1)y_n).
```

This is the complex predecessor sector. Its contribution to a literal
`Xi_d` additionally takes the `H-N` block difference, multiplies by
`(-1)^d`, and takes the real part. The identity removes the predecessor-digit
discontinuity, but supplies no sign by itself.

## One-sided principal-Machin rung

For the registered lower Machin approximants `m_t`, write `s=t+1` and
`a_p(r)=1/((2r+1)p^(2r+1))`. The exact increment is

```text
Delta_t = m_(t+1)-m_t
        = 16*(a_5(2s)-a_5(2s+1))
          + 4*(a_239(2s+1)-a_239(2s+2)) > 0.
```

Alternating remainders give the sharper oriented bracket

```text
0 < Delta_t < pi-m_t < U_t,
U_t = 16*a_5(2s)+4*a_239(2s+1).
```

For a separable finite Fourier score

```text
F(x) = c + Re sum_(n,h) c_(n,h)e(h*x_n),
```

evaluate at `x~_n=10^n*m_(n+ell)`. With

```text
lambda_n = 10^n*Delta_(n+ell),
u_n      = 10^n*U_(n+ell),
A_n      = partial_n F(x~),
C_n      = (2*pi)^2 sum_h h^2*|c_(n,h)|,
```

coordinatewise Taylor expansion yields

```text
F(pi-orbit) >= F(x~)
  + sum_n (lambda_n*A_n^+ - u_n*A_n^-)
  - (1/2)*sum_n C_n*u_n^2.
```

The strict orientation `10^n*pi-x~_n > lambda_n > 0` is the actual-π input.
For convex digit weights, lower bounds derived this way imply FMR when

```text
lower(D_w) - sum_d w_d*(-lower(G_d))_+ > 0.
```

## First fatal line and next rung

The moving Machin correction is exponentially tiny in the fresh block. No
theorem currently signs the rational carrier's fresh odd-frequency score.
The strongest live question is therefore:

> Can the sector-5 odd-frequency `5*pi` block, on a principal moving Machin
> carrier and a parity-biased same-child mask, be signed along a noncircular
> deterministic path while absorbing that child's inherited deficit?

The correct consumer order is

```text
T179/T189 rewriting -> oriented carrier bound -> FMR
  -> positive literal child surplus -> T178/T176 -> T148/T153/T156.
```

A single ray still requires branching or word coverage before V1.
