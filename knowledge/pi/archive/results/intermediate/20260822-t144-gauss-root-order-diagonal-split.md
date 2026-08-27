# T144: root-order split for the Gauss diagonal

Status: `proof sketch`  
Last audited: 2026-08-22

## Exact coefficient toolkit

For

```text
A_r=[z^r](z^2+2z+2)^r=CT(x+2+2/x)^r
```

one has

```text
A_r=sum_(0<=k<=r/2) r!/(k!k!(r-2k)!) 2^(r-k),
sum_(r>=0) A_r z^r=(1-4z-4z^2)^(-1/2),
(r+1)A_(r+1)=2(2r+1)A_r+4rA_(r-1)   (r>=1).
```

In odd characteristic `p`, the following normalizations are exact in their
stated ranges:

```text
A_r = -sum_(y in F_p) chi_p(y^2-4y-4)y^r       (mod p),
                                                    1<=r<p-1;
A_r = [z^r](1-4z-4z^2)^((p-1)/2)              (mod p),
                                                    0<=r<p.
```

For the Legendre generating function
`sum P_r(t)w^r=(1-2tw+w^2)^(-1/2)`, choose `i` in `F_(p^2)` with `i^2=-1`.
Substitution `w=2iz`, `t=-i` gives

```text
A_r=(2i)^r P_r(-i).
```

Changing `i` to `-i` gives the same value because
`P_r(-t)=(-1)^rP_r(t)`.

## The quadratic-unit order

Let `K=Q(sqrt(2))`, `O_K=Z[sqrt(2)]`, and let the two roots of
`1-4z-4z^2` be

```text
alpha=(-1+sqrt(2))/2,  beta=(-1-sqrt(2))/2.
```

Their ratio is the norm-one unit

```text
rho=alpha/beta=2sqrt(2)-3,
rho'= -2sqrt(2)-3=rho^(-1),
N_(K/Q)(rho)=1.
```

For every odd rational prime `p`, define `ord_p(rho)` as follows.

- If `(2/p)=1`, then `O_K/pO_K=F_p x F_p`; the two components of `rho` are
  inverses and therefore have the same multiplicative order.
- If `(2/p)=-1`, then `O_K/pO_K=F_(p^2)` and Frobenius sends
  `rho` to `rho'=rho^(-1)`.  Thus `rho` lies in the norm-one subgroup of
  order `p+1`.

The ramified prime `p=2` is excluded.  This gives an unambiguous order for
all medium odd primes in T143/P19.

## Small-order primes have small total log weight

If `ord_p(rho)=d<=D`, then `p` divides the nonzero rational integer
`N(rho^d-1)`.  Hence the distinct such primes satisfy

```text
sum_(ord_p(rho)<=D) log p
 <= sum_(d<=D) log|N(rho^d-1)|.
```

Since `|rho|<1`, `|rho'|=3+2sqrt(2)`, and

```text
N(rho^d-1)=2-rho^d-(rho')^d,
```

the right side is `O(sum_(d<=D)d)=O(D^2)`.  This bound is independent of
any finite P19 profile.

For the diagonal zero counts `Z_p=Z_p^D+Z_p^R`, the ray geometry gives only
`Z_p=O_delta(X)` for `X/2<p<2X`.  Therefore the small-order contribution is

```text
sum_(ord_p(rho)<=D) Z_p(log p)^2
 =O_delta(X D^2 log X).                            (1)
```

Taking `D=X^kappa`, (1) is
`O_delta(X^(1+2kappa)log X)`.

## Exact missing implication

The large-order side still needs a genuine anti-concentration theorem.  One
possible precise gate is a punctured confluent-Vandermonde implication with
explicit `eta,kappa>0`:

```text
Z_p^D+Z_p^R > C_delta p^(1-eta)
    ==> ord_p(rho) <= p^kappa,                     (2)
```

uniformly for every sufficiently large odd `p` and the exact P19 ray
intervals.  “Punctured” matters: only the actual ray indices are available,
and zeros of coefficients are not roots of the quadratic denominator.
Neither the recurrence, Parseval, nor a fixed-degree Weil estimate proves
(2).  No nonsingularity or rank theorem strong enough for (2) is currently
established.

If (2) were proved, primes with order `>X^kappa` would contribute
`O_delta(X^(2-eta)log X)`, while (1) handles the complementary primes.
After absorbing logarithms, the diagonal would have a power saving
`X^(2-epsilon)` for every

```text
epsilon < min(eta,1-2kappa).
```

This ledger requires `kappa<1/2`.

## Scope

The norm-product estimate is an exact reduction, not the missing
anti-concentration theorem.  It does not prove a P19 GO or STOP outcome, does
not settle the T143 diagonal, and gives no first-band, `(D)`, or `V1` result.
The unresolved implication (2) is not yet sharp or supported enough to trigger
a Pro-model call.

V1 remains open.
