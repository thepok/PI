# Sector-5 retention and one-sided Machin direction

Date: 2026-08-28 UTC

Claim boundary: the T169/T179/T189 inputs are `machine-checked`. The sector-5
collapse, sharp Machin bracket, Taylor implication, and private-prime parity
separation below are independently audited `proof sketch`. The node
computation is an independently reproduced `experiment`, not a
directed-interval certificate. No unbounded transport theorem is proved.

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

## Private-prime parity separation

Uniform averaging over even or odd children annihilates every predecessor
sector except `r=0,5`. Let `R5` be the real fresh sector-5 block, let
`h_d=(-G_d)_+`, and let `H_p` average `h_d` over parity `p`. Then the two
deficit-corrected parity margins satisfy exactly

```text
M_p = q*(Delta0+(-1)^p*R5) - 21/10 - H_p,
max(M_0,M_1) = C + |q*R5-deltaH|,
C = q*Delta0 - 21/10 - (H_0+H_1)/2,
deltaH = (H_0-H_1)/2.
```

For the rational moving carrier `10^n*m_(n+s)`, fix `N<H`, put
`K=H-1+s`, and choose `p=4K+5` prime with `p>max(239,40q)`. The final
`239`-branch term of `m_K` has the private denominator `p*239^p`; every
earlier carrier phase and every target/coefficient root of unity has conductor
coprime to `p`. The terminal sector-5 contribution is therefore

```text
sum_(h in {5,15,...,20q-5}) b_h*eta^h,
```

where `eta` is a primitive `p`-th root and the top coefficient is nonzero.
After adding the conjugate and shifting by `20q-5`, a hypothetical
`q*R5-deltaH=0` would give a nonzero polynomial over the `p`-free cyclotomic
field of degree at most `40q-10<p-1` vanishing at `eta`, impossible. Hence

```text
q*R5-deltaH != 0,
M_0 != M_1.
```

The depth can be selected deterministically: if `B` dominates `239`, `40q`,
and `4H+4k+5`, any least prime divisor of `(2*B!)^2+1` is greater than `B`
and congruent to `1 mod 4`, so it defines a valid `K` and `s`. This selector
is target-independent and tie-free, but computational feasibility is
irrelevant to the theorem.

The exact sector-5 kernel used in this proof also has the closed form

```text
psi_q(t) = sin(qz)^4*cos(z)/(2q^2*sin(z)^4)
           * (100*a_q-(16*a_q+2)*sin(z)^2),
z=pi*t,  a_q=1-cos(pi/(10q)),
```

extended through removable singularities by continuity.  The normalization
`z=pi*t` is the literal T179 argument: direct root filtering gives
`2*Re K_(q,5)(t) = sum_(j<10) (-1)^j B_(10q)((t+j)/10)`.  In particular,
for every `q>=2`,

```text
psi_q(t) > 0  for 0<t<=1/(4q),
psi_q(t) < 0  for 2/(3q)<=t<1/q.
```

Both chambers lie on the same positive side of the target, and their sizes
do not vanish: along `t=lambda/q` the limit is
`sin(pi*lambda)^4*(1-4lambda^2)/(4*pi^2*lambda^4)`.  Thus a one-bit
target-side orientation, including the tautological zero-lattice sign from
`sin(10^(n+1)*pi)=0`, cannot orient even the literal sector-5 leaf.  A
weighted actual-pi chamber-occupancy theorem could still do so.  This makes
the sign changes explicit; the positive Machin displacement alone cannot
orient the kernel.
T169 transfers the carrier sector to actual pi with an exponentially small
explicit error, but bare cyclotomic nonvanishing gives no lower bound relative
to that error.

An ordered audit explains why the private coordinate itself is quantitatively
inert. For the natural block `N=q`, `H=10q`, write
`p=4*(H-1+s)+5=40q+4s+1` and delete the terminal `239` term:

```text
tau_p = 4/(p*239^p),
r_K   = m_K+tau_p.
```

Equal-length alternating truncations give the actual-pi-specific identity

```text
m_K < r_K < pi,
pi-r_K = 16*integral_0^(1/5) t^(p-1)/(1+t^2) dt
         -4*integral_0^(1/239) t^(p-1)/(1+t^2) dt,
(pi-r_K)/(r_K-m_K) > (50/13)*(239/5)^p-1.
```

Thus inserting the private term moves the carrier slightly **away** from pi.
Although its isolated `p`-coordinate can have a large angle, the complementary
`239^p` coordinate cancels it in the distinguished real embedding. If
`M_tilde` is the complete preferred parity margin and `M_circ` its `p`-deleted
counterpart, the audited coefficient load and T169 normalization give

```text
|M_tilde-M_circ| < epsilon_priv,
epsilon_priv/E_D < 10^(-82q-7s),
E_D = 20*pi*(10q)*rho^(q+s)/(1-rho),  rho=2/125.
```

This is a **conditional** separator: if `M_circ` lies at least
`epsilon_priv` below the full transfer threshold `E_D+E_G`, private insertion
cannot rescue it. It does not exclude tipping an already
`epsilon_priv`-close comparator, and it does not sign `M_circ`. The carrier
versions of the DFT/margin algebra are proof-sketch generalizations, not new
Lean declarations.

## Preferred-parity closure from the certified seed

An independently rebuilt outward-interval `experiment` exhausts the seven
literal FMR children of `(q,A,N)=(1000,334,1000)`.  The root witness set is

```text
{0,1,2,3,4,8,9}.
```

At every reached node `(10000,334+1000*d,10000)`, both complete parity means
of `Y_d=D_d-(-G_d)_+` are negative, with the uniform strict bound

```text
max(M_even,M_odd) < -8424.30118897787522947.
```

For actual and carrier arrays within digitwise buffers `E_D,E_G`, clipping is
one-Lipschitz, hence `|Y_d-Y_d°|<=E_D+E_G` and the same bound survives parity
averaging.  Therefore every such carrier satisfies

```text
max(M_even°,M_odd°) < E_D+E_G-8424,
```

so the p-free preferred-parity premise is false at the very next recursion
from this seed.  This deterministic reduction is a `proof sketch`; the finite
interval leaves remain an `experiment`.  The corrected reproducer and exact
claim boundary are in
[`audit/computational/t189-pfree-parity`](../../../../audit/computational/t189-pfree-parity/README.md).
It does not close literal FMR: at the reached node `A=1334`, `d=5` is still the
unique literal witness.

## First fatal line and next rung

The moving Machin correction is exponentially tiny in the fresh block. The
private-prime theorem selects one parity without a tie, but it proves only
`|q*R5-deltaH|>0`; both parity margins may remain negative. No theorem proves
the needed ordered comparison

```text
|q*R5-deltaH| > -C
```

with transfer room to actual pi.

Moreover, the private coordinate contributes less than
`10^(-82q-7s)*E_D`; it cannot repair the finite parity failure above.  The
preferred-parity phase-chamber question is closed from this seed, not merely
unsigned.  The strongest live question is therefore:

> Can a π-specific theorem sign and transport the complete literal
> multi-sector `Y_d`, retaining the unique favorable child and its inherited
> deficit, without averaging it with the four losing digits of its parity?

The correct consumer order is

```text
T179/T189 rewriting -> oriented carrier bound -> FMR
  -> positive literal child surplus -> T178/T176 -> T148/T153/T156.
```

A single ray still requires branching or word coverage before V1.
