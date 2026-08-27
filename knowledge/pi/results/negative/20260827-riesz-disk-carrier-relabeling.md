# Integer Riesz disk carrier: exact orbit relabeling

Claim status: `literature-checked` for the cited Riesz--Bessel and asymptotic
formulas; `proof sketch` for the specialized shell algebra and narrow
separator.  Nothing here is machine-checked and no general lattice-shell
method is excluded.

For integer `r>=1` and integer `X>=1`, define

```text
W_r(X) = sum_(v in Z^2) (X-||v||^2)_+^r,
I_r(X) = (r+1)*W_r(X),
D_r(X) = I_r(X)-pi*X^(r+1).
```

Since `I_r(X)` is an integer,

```text
{-D_r(X)} = {pi*X^(r+1)}.                            (1)
```

Thus `X=10^j` samples the ordinary decimal orbit at stride `r+1`.

## Correct Riesz--Bessel formula

With Fourier normalization
`fhat(xi)=integral f(x)*exp(-2*pi*i*x·xi) dx`, radial integration gives

```text
fhat_(r,X)(xi)
  = (r!/pi^r)*X^((r+1)/2)*||xi||^(-(r+1))
      *J_(r+1)(2*pi*sqrt(X)*||xi||).
```

Consequently

```text
D_r(X)
  = ((r+1)!/pi^r)*X^((r+1)/2)
      *sum_(m>=1) r_2(m)/m^((r+1)/2)
        *J_(r+1)(2*pi*sqrt(mX)).                     (2)
```

For `r>=1` the grouped series is absolutely convergent.  Equation (2) is the
`k=2,q=r` specialization of the Riesz identity in Berndt--Dixit--Kim--
Zaharescu, [Sums of squares and products of Bessel
functions](https://arxiv.org/abs/1701.07460), equation (1.16).

## Phase-locked square shells

Set `X=R^2` with integer `R` and split (2) into square `m=s^2` and nonsquare
shells.  For

```text
H(z)=sum_(s>=1) r_2(s^2)/s^z,
```

Euler factors give

```text
H(z)=4*zeta(z)^2*L(z,chi_-4)/((1+2^(-z))*zeta(2z)),
Re z>1.                                              (3)
```

Nemes's fixed-order Bessel expansion
([arXiv:1606.07961](https://arxiv.org/abs/1606.07961)) then yields, with
`nu=r+1` and `phi_nu=pi*nu/2+pi/4`,

```text
Q_r(R)
  = ((r+1)!/pi^(r+1))*cos(phi_nu)*H(r+3/2)*R^(r+1/2)
      +O_r(R^(r-1/2)).                               (4)
```

The leading square-shell sign is fixed because
`cos(phi_nu)=+/-1/sqrt(2)`.  The complementary nonsquare expansion has the
phase-blind bound

```text
U_r(R)=O_r(R^(r+1/2)).                               (5)
```

Equation (5) does **not** prove that the nonsquare sector has this order, is
nonzero, or cannot cancel.  It only shows that absolute estimates do not make
it lower order.  A future pointwise signed theorem for that sector is not
excluded.

## Exact narrow separator

The integer main term gives

```text
D_(r+1)(X)-X*D_r(X)=I_(r+1)(X)-X*I_r(X) in Z.
```

Therefore, for `Y_r(X)={-D_r(X)}`,

```text
Y_(r+1)(X) = {X*Y_r(X)},
Y_r(10^(j+1)) = {10^(r+1)*Y_r(10^j)}.                (6)
```

The complete integer Riesz-discrepancy carrier is thus exactly the same
decimal-orbit sample under a changed index.  A theorem asserting prescribed
cylinder hits solely for its full modulo-one value is V1 on a subsequence,
not an independent bridge.

This conclusion is deliberately narrow.  Equivalent representations can
enable proofs; (6) does not rule out useful one-sided cancellation in a
partial shell decomposition, other weights, or other geometric identities.
No unreproduced numerical claims from the Pro memo are used.
