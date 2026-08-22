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

Already inadequate: denominator/gcd growth alone, any finite set of p-adic
coordinates, same-fiber replacement, ordinary hypergeometric telescoping,
base-16 normality, generic lacunary almost-everywhere theorems, sampled forcing
as randomness, T119/T120, and generic cell energy.
