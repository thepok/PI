# Oversampled singular-modulus phase transfer

Claim status: `proof sketch`.

This compact note preserves the one new valid estimate from the audited Pro
memo `workflows/state/chatgpt-pro/20260828-signed-transport-proof-au/answer.md`.
It repairs the false bound `sigma_3(m) <= m^3` used in an earlier CM draft.
It supplies exceptionally accurate one-sided approximation to `pi`, but no
target-signed T189 child information.

## Corrected Lambert bound

For `N >= 1`, set

```text
t_N = exp(-2*pi*N),
J_N = j(i*N),
S_N = log(J_N)/2,
epsilon_N = S_N-pi*N.
```

The standard product and Eisenstein expansions give, for `t=t_N`,

```text
epsilon_N
  = (3/2)*log(E_4(i*N)) - 12*sum_(m>=1) log(1-t^m) > 0.
```

The needed correction is the Lambert identity

```text
sum_(m>=1) sigma_3(m)*t^m
  = sum_(d>=1) d^3*t^d/(1-t^d)
  <= t*(1+4*t+t^2)/(1-t)^5.
```

Together with `log(1+u) <= u` and

```text
-sum_(m>=1) log(1-t^m) <= t/(1-t)^2,
```

this yields

```text
12*t_N < epsilon_N <= U(t_N),

U(t) = 360*t*(1+4*t+t^2)/(1-t)^5 + 12*t/(1-t)^2.
```

For `t_N < 1/400`, the same inequalities imply

```text
0 < epsilon_(10*N) < 10*epsilon_N,
```

so `10*pi*N < S_(10*N) < 10*S_N`.  The modular-polynomial relation between
`J_N` and `J_(10*N)` is exact, but it is not by itself a recurrence without
specifying the distinguished real root.

## Oversampled fresh-horizon corollary

For a decimal scale `q`, define

```text
pi_q = S_(4*q)/(4*q) = log(j(4*i*q))/(8*q).
```

Then

```text
pi < pi_(10*q) < pi_q,
0 < pi_q-pi < (11532/q)*exp(-8*pi*q).
```

Every literal source frequency in the `q -> 10q` fresh block satisfies

```text
|m| <= (20*q-1)*10^(10*q-1) < 20*q*10^(10*q).
```

Hence

```text
|exp(2*pi*i*m*pi_q)-exp(2*pi*i*m*pi)|
  < 461280*pi*exp(-(8*pi-10*log(10))*q).
```

Since `8*pi-10*log(10)>0`, this controls all fresh-block phases despite their
frequency growth.

## Exact fatal line

Write `eta_q=pi_q-pi>0`.  A literal real Fourier mode obeys

```text
c_m*cos(2*pi*m*pi_q-phi_m,d) - c_m*cos(2*pi*m*pi-phi_m,d)
 = -2*c_m*sin(pi*m*eta_q)
      * sin(2*pi*m*pi-phi_m,d+pi*m*eta_q).
```

The first sine has known sign once `0 < m*eta_q < 1`.  Neither the nested
real order nor the modular relation orders the second, target-rotated sine.
Thus the construction transports a pre-existing literal sign with negligible
error but does not produce `D_d>0`, `G_d+D_d>0`, or an FMR child.

Independent audits also found a principal-log branch-sign error later in the
source memo: with `L_a=Log((a-i)/(a+i))` on the principal branch,
`8*L_5-2*L_239=-i*pi`, not `+i*pi`.  The source's subsequent squared identity
survives, but that section contributes no signed bridge and is not retained
here.

## Research boundary

This result is not actual-pi target-signed progress in the repository sense.
Reopen the CM carrier only with an independent theorem ordering the complete
distinguished midpoint phase for a literal child; approximation precision,
algebraicity, modular recursion, and scalar one-sidedness do not provide it.
