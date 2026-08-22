# Exact scalar target and known boundary

Define

```text
c_k = (120*k^2+151*k+47)/((2*k+1)*(4*k+3)*(8*k+1)*(8*k+5))
A_N = sum_{k=0}^N c_k/16^k
y_N = (10^N-16)*A_N.
```

Then `A_(N+1)=A_N+c_(N+1)/16^(N+1)`. The proved tail estimate is

```text
0 < pi-A_N <= 16^(-N)/(15*(N+1)^2),
| ||(10^N-16)pi||-||y_N|| | <= (5/8)^N/(15*(N+1)^2).
```

The audited fixed-return/Furstenberg bridge reduces V1 to

```text
(D)  liminf_(N->infinity) ||y_N|| = 0.
```

Write `y_N=P_N/Q_N` in lowest terms with `Q_N>0`. If `a_N` is a
nearest integer, define the centered numerator

```text
Delta_N = P_N-a_N*Q_N,
|Delta_N|/Q_N = ||y_N||.
```

Retain gcd reductions and the carry `a_N`. The identity

```text
y_(N+1) = 10*y_N + 144*A_N
          + (10^(N+1)-16)*c_(N+1)/16^(N+1)
```

is exact, but may only repackage the original times-ten orbit. A positive
mechanism must use explicit cross-index coupling in the complete BBP
numerator. A negative result must identify an exact cancellation/conjugacy or
give a globally coupled countermodel preserving every hypothesis used.

## Exact one-step centered reduction

Let the next increment be reduced as

```text
A_(N+1)-A_N = u_N/v_N,  gcd(u_N,v_N)=1,  v_N>0.
```

For `A_N=P_N/Q_N`, put

```text
X_N = P_N*v_N + u_N*Q_N
Y_N = Q_N*v_N
h_N = gcd(X_N,Y_N)
P_(N+1)=X_N/h_N
Q_(N+1)=Y_N/h_N.
```

Write `t_N=10^N-16`, choose the fixed nearest-integer convention
`Delta_N=t_N*P_N-a_N*Q_N`, and let `center_m(z)` be the corresponding centered
integer representative modulo positive `m`. Direct expansion gives

```text
h_N*Delta_(N+1)
  = center_(Y_N)(10*v_N*Delta_N
                 + 144*v_N*P_N
                 + t_(N+1)*u_N*Q_N).
```

This identity is exact. It also exposes an information-loss issue: from
`(Delta_N,Q_N)` one knows only

```text
t_N*P_N = Delta_N (mod Q_N).
```

If `d_N=gcd(t_N,Q_N)`, the unrestricted solution set for `P_N mod Q_N`, when
nonempty, is a coset with `d_N` lifts. Thus `(Delta_N,Q_N)` is not generally a
closed Markov state; the next centered residue and reduction gcd can depend on
the missing lift of `P_N`. Determine whether the actual BBP coupling controls
that lift, whether a minimal augmented state gives descent, or whether this
produces a rigorous no-go for centered-pair-only arguments.

Already inadequate: denominator/gcd growth alone, any finite set of p-adic
coordinates, same-fiber replacement, ordinary hypergeometric telescoping,
base-16 normality, generic lacunary almost-everywhere theorems, sampled forcing
as randomness, T119/T120, and generic cell energy.
