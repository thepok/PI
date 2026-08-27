# T148 negative: fixed-puncture and Sidon shortcuts fail for P20

Status: `experiment`  
Last audited: 2026-08-22

Two exact finite certificates supplied by ChatGPT Pro and independently
replayed rule out several proposed shortcuts for the frozen P20 criterion.
They do not refute the `ceil(sqrt(p))` threshold.

## Primitive-root five-puncture certificate

For `p=599`, `m=299`, `N_p=598`, and
`I_p={55,...,239}`, exact Legendre recurrence and polynomial gcd give

```text
gcd(P_59,P_92,P_149,P_173,P_179)=T^2+180  in F_599[T].
```

Under `tau^2=(X+X^(-1)+2)/4`, this becomes

```text
X^2+123X+1,
```

whose roots are `88` and `388`.  Direct evaluation gives
`F_j(88)=F_j(388)=0` at all five displayed indices, and both roots have
multiplicative order `598`.  Thus fixed-five, nearest-gap, isolated Schur or
transfer factors, and low common-factor degree implying low multiplicative
order are false.  This is not a frozen counterexample because `5<k_p=25`.

## High-order repeated-difference certificate

For `p=839`, `N_p=838`, exact computation gives

```text
gcd(P_104,P_209,P_295,P_314)=T^2+417.
```

The corresponding factor is `X^2-8X+1`, with roots `320` and `527`, both of
order `419`.  All four displayed `F_j` vanish, and `104,209,314` form a
three-term arithmetic progression with common difference `105`.  Hence the
zero set of a high-order root need not be Sidon.  This is not a frozen
counterexample because `4<k_p=29`.

Reproducer:
[`workflows/research/pi/t148_p20_legendre_certificates.py`](../../../../workflows/research/pi/t148_p20_legendre_certificates.py)

Audited script SHA-256:
`e272d607d4e1b25b81f86da17f980956c0d283f9d5ea064073b7dcb122e3d708`.

These certificates close only the named shortcut classes.  P20 and V1 remain
open.
