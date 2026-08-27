# Weighted Jackson L2 and pair-collision bridge

Status: `machine-checked` symbolic bridge; closed coefficient formulas below
remain `proof sketch`

Date: 2026-08-24 UTC

Provenance: user-supplied GPT Pro result, independently checked against
`T6`, `T120`, and `T121`. The symbolic bridge is formalized in
`T122T122JacksonCollisionBridge.lean`; the Lean source and axiom audit, not
this note, are proof authority.

## Exact proposed bridge

For

```text
S_h(x;N) = sum_{n<N} exp(2*pi*i*h*x_n),
```

aggregate the absolute Jackson coefficient mass at frequency `h` as

```text
w_q(h) = (2/q^4) m_q(h) + (1/(2q^2)) tau_(2q)(h),
```

where `tau_r(h)=(r-|h|)_+` and `m_q=tau_q*tau_q`. The claimed exact support is
`|h| <= 2q-1`; the formal source's coarser endpoint `2q` has zero mass.

The resulting linear and quadratic loads are

```text
J_q = sum_(h!=0) w_q(h) |S_h|/N,
Q_q = sum_(h!=0) w_q(h) |S_h|^2/N^2.
```

The following exact closed form for the nonzero absolute mass remains a
`proof sketch` calculation:

```text
W_q = 4 - 7/(3q) - 2/(3q^3),
```

and weighted Cauchy--Schwarz gives

```text
J_q^2 <= W_q Q_q.
```

This constant is sharp for the chosen quadratic moment. It follows that the
quadratic premise

```text
Q_q < delta_q,
delta_q = (1/(3q)+2/(3q^3))^2 / W_q,
```

implies the already verified T120 strict weighted threshold. A simpler
non-strict sufficient premise is `Q_q <= 1/(36q^2)`.

## Pair kernel

Let `D_r(t)=sum_(j<r) exp(2*pi*i*j*t)` and

```text
P_q(t) = (2/q^4)|D_q(t)|^4 + (1/(2q^2))|D_(2q)(t)|^2.
```

The Lean theorem `sum_jacksonCollisionKernel_eq_weighted_normSq` checks the
finite coefficient-indexed kernel expansion, and
`jacksonQuadraticFourierLoad_eq_pairAverage_sub_zeroMass` checks the centered
pair identity. The following closed Dirichlet-kernel form remains a
`proof sketch` calculation with coefficients `w_q(h)`:

```text
Q_q = (1/N^2) sum_(m,n<N) P_q(x_m-x_n)
      - (7/(3q)+2/(3q^3)).
```

The machine-checked T122 consumer uses the safe mass bound `W_q <= 4`: its
same-scale centered collision premise implies the T120 threshold and hence
canonical V1. With the still-informal closed mass evaluation above, the
cleaner proposed estimate is

```text
(1/N^2) sum_(m,n<N) P_q(x_m-x_n)
  <= 7/(3q) + 1/(36q^2) + 2/(3q^3)
```

would imply the verified weighted hitting criterion. The uniform `2q`-grid
has `J_q=Q_q=0`, showing that the criterion is algebraically non-vacuous at
`N=Theta(q)`. This says nothing about whether the decimal orbit of pi attains
it.

For `x_n=fract(10^n*pi)`, the remaining premise of this route is an explicit
Jackson-kernel bound on

```text
P_q(10^n*(10^ell-1)*pi).
```

No such fixed-pi estimate is proved here.

## Claim boundary

The symbolic Cauchy--Schwarz, collision identity, finite interval-hit consumer,
and conditional implication to V1 are `machine-checked`. The explicit
triangular multiplicities, closed masses, Dirichlet-kernel formula, uniform-grid
witness, and claimed optimal constant remain `proof sketch`.

This is a stronger sufficient premise for the weighted load, not a strict
weakening of that premise. It therefore does not by itself satisfy the README
frontier-admission test. The phrase "sharp threshold" applies only to the
informal closed-form calculation for this chosen `Q_q`; no global optimality
among collision criteria is claimed.

The full moving-mesh collision-plus-pseudo-orbit consumer is not refuted or
superseded. It yields qualitative Haar convergence and therefore decay in
each fixed finite Fourier window. The bridge above instead asks for direct
quantitative control with Jackson order tied to the current moving mesh.

V1 remains open.
