# All-three fixed-point separator for the T189 correlation

Date: 2026-08-27 UTC

Claim labels: the T179/T189 identities are `machine-checked`; the directed
numerical enclosure is an `experiment`; the finite-prefix and transcendental
continuation arguments are `proof sketch`. Nothing here is a negative result
about pi or V1.

## Exact specialization

Take the generalized decimal orbit fixed at `x_n=1/3`. Its predecessor digit
is always `3`, because

```text
fract(10/3)=1/3,  floor(10/3)=3.
```

For the current T189 candidate `q=1000`, `A=334`, and `d=3`, put

```text
Q=10000,  c=669/2000,  t=1/3-c=-7/6000.
```

The target character and predecessor-digit character cancel. Thus every
fresh index has the same contribution

```text
K = Re[10 * sum_(r=1)^9 e(r*t/10)
  * sum_(ell=0)^1999 alpha_Q(10*ell+r)e(ell*t)],
```

where `alpha_Q` is T142's exact positive boundary coefficient.

The directed replay
[`t189_xi3_fixed_point_separator.py`](../../../../../workflows/experiments/t189_xi3_fixed_point_separator.py)
gives

```text
K in
[-0.03418163774658197014864546356039472414214449153916396039749097911026918958686490527474194766099698658,
 -0.03418163774658197014864546356039472414214449153916396039749097911026918958686490527474194576235609259].
```

Therefore `Xi_3(N,H)=(H-N)K` on this orbit. Forty-eight terms remain just
above the current robust sufficient threshold `-1.6411755067`, but forty-nine
terms satisfy

```text
49*K < -1.67490024958 < -1.6411755067.
```

The fixed point does not already hit the desired child cylinder:
`1/3 < 0.3334`, whereas the target is `[0.3334,0.3335)`.

## What this rules out

Let `P=floor(10^N*pi)` and set

```text
alpha=(P+1/3)/10^N.
```

This rational number shares pi's certified decimal prefix through `N`; from
orbit time `N` onward it is exactly fixed at `1/3`. Hence a finite pi prefix
plus the decimal recurrence alone cannot prove the required T189 fresh-block
lower bound.

Bare transcendence—even the stronger Liouville property—does not repair the
inference. For a fixed tested block choose `M>N`, put

```text
R = P*10^(M-N) + (10^(M-N)-1)/3,
alpha_M = (R+tau)/10^M,
```

and take any Liouville `tau` in `(0,1)`. Then `alpha_M` is Liouville and has
the original prefix followed by the prescribed run of threes. If `F(y)`
denotes the displayed one-step polynomial, T142's formula
gives the crude explicit bounds

```text
abs(alpha_Q(h)) <= 11/Q,
abs(F'(y)) < 17,424,000/7.
```

Eleven further prescribed threes beyond a 49-step block make the perturbation
of `Xi_3` less than `0.00122`, leaving it below `-1.67368`. This constructs a
transcendental continuation for each fixed block; it does not claim that one
fixed continuation defeats every horizon.

The necessary new pi input must therefore control the joint predecessor-digit
and suffix transition statistic strongly enough to exclude this adjacent
target-locked behavior. Digit counts, non-hitting, a finite Machin prefix,
the decimal recurrence, or bare transcendence do not supply that sign.
