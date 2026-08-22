# T146: Gauss root-resultant collapse

Status: `proof sketch`  
Last audited: 2026-08-22

## Exact identity

Let

```text
A_r=[z^r](1-4z-4z^2)^(-1/2)
```

and, in `Q(sqrt(2))`, put

```text
lambda=2+2sqrt(2),       mu=2-2sqrt(2),
rho=lambda/mu=-(3+2sqrt(2)).
```

Then

```text
1-4z-4z^2=(1-lambda z)(1-mu z),
rho^2+6rho+1=0.
```

Define the palindromic integer polynomial

```text
H_r(X)=sum_(j=0)^r binom(2j,j) binom(2r-2j,r-j) X^j.
```

Expanding each inverse square root by
`(1-t)^(-1/2)=sum_(j>=0) binom(2j,j)t^j/4^j` gives the exact equality

```text
A_r=4^(-r) mu^r H_r(rho).                         (1)
```

The conjugate of `rho` is `rho^(-1)`, and `N(mu)=-4`.  With the standard
resultant convention in which the monic polynomial is listed first, (1)
therefore gives

```text
Res_X(X^2+6X+1,H_r)
  =H_r(rho)H_r(rho^(-1))
  =N(H_r(rho))
  =(-4)^r A_r^2.                                  (2)
```

Choosing the inverse root-ratio convention replaces `rho` by `rho^(-1)` and
does not change (2).  Palindromicity also gives
`X^r H_r(X^(-1))=H_r(X)`.

## Consequence for the P19 route

For every odd prime `p`, the factors `4` and `mu` are units in the relevant
split algebra or quadratic field.  Thus (1) yields

```text
p divides A_r  iff  H_r(rho)=0 modulo p.
```

But (2) shows that the associated resultant condition is exactly the original
divisibility condition, squared and multiplied by a power of `2`.  It is not
an independent algebraic obstruction.  Replacing the quadratic by a
cyclotomic polynomial for the actual order of `rho mod p` likewise records
that the same element is simultaneously a root; without a separate theorem
relating many coefficient zeros to small order, it supplies no
anti-concentration estimate.

## Endpoint warning for the character moment

The valid character-moment identity is

```text
A_r = -sum_(y in F_p) chi_p(y^2-4y-4)y^r  (mod p),
                                                  1<=r<p-1.
```

It does not generally extend to `r=p-1`.  At `p=5`, `r=4`,

```text
A_4=136=1 (mod 5),
-sum_(y in F_5) chi_5(y^2-4y-4)y^4=2 (mod 5).
```

The missing endpoint term comes from the exceptional behavior of the
zeroth/nonzero-field moment at exponent `p-1`.

## Scope

This is a negative result for the bare `H_r`/root-resultant reformulation.  It
does not rule out a genuinely new order-sensitive or coefficient-family
argument.  It proves no P19 GO or STOP outcome, no diagonal power saving, and
no `(D)` or `V1` progress.

V1 remains open.
