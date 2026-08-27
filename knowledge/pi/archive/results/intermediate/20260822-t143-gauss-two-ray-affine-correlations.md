# T143: exact affine reduction and finite Gauss two-ray census

Status: `proof sketch`  
Last audited: 2026-08-22

## Actual record domains

Let

```text
A_r=[z^r](z^2+2z+2)^r
   =sum_(0<=c<=r/2) binom(r,2c)binom(2c,c)2^(r-c),
```

so `A_2=8`.  Fix rational `0<delta<1/6`.  For an odd prime `p|A_r`, retain
the direct record `(p,r,D)` only when

```text
n=p+r,  X<n<=2X,  delta*n<=r<=(1/3-delta)*n,
2r<=p-1,
```

and retain the reflected record `(p,r,R)` only when

```text
n=2p-1-r,  X<n<=2X,  delta*n<=r<=(1/3-delta)*n,
2r<p-1.
```

These inequalities encode `n/2<p<n` and the prescribed tie-goes-direct rule;
keeping them in every correlation is essential.

## Four exact affine correlations

Expanding the square gives ordered record pairs with weight
`log(p)log(p')`.  Eliminating their common `n` gives

```text
DD: p'=p+r-r',
DR: p'=(p+r+r'+1)/2,
RD: the slot-reversal of DR,
RR: p'=p+(r'-r)/2.
```

The last two displayed quotients require the corresponding parity condition.
Slot reversal preserves the actual domains and weights, hence `E_DR=E_RD`
and

```text
E_delta(X)=E_DD(X)+2E_DR(X)+E_RR(X).                 (1)
```

Equivalently, the off-diagonal part of (1) is a sum of three named, actual-zero
affine divisor correlations: for each admissible first record `(p,r)`, vary
`r'`, substitute the displayed affine candidate for `p'`, and require that
the candidate is prime, divides the cross-characteristic integer `A_(r')`,
and belongs to the appropriate actual record domain.  This is not an ordinary
`gcd(A_r,A_(r'))` problem: generally `p'!=p`, and dropping the actual-domain
constraints destroys equality with `E_delta(X)`.

The diagonal can be bounded from coefficient size alone.  Since
`A_r<=5^r`,

```text
sum_(p|A_r, p<=2X) (log p)^2
 <= log(2X) log rad(A_r)
 <= r log(5) log(2X).
```

Each `(p,r)` produces at most one record of each branch, so a harmless factor
of at most two accounts for record multiplicity.  Summing the relevant
`r=O_delta(X)` gives only
`E_diagonal=O_delta(X^2 log X)`.  It does not provide the power saving
`E_delta(X)=O_delta(X^(2-eta))`; that saving must come from the three exact
off-diagonal affine correlations together with a sharper diagonal argument.

## Exact finite census at delta=1/12

Status: `experiment`

The reproducer uses integer primality, exact divisibility `p|A_r`, exact
window inequalities, and the direct tie rule.  It retains `E` as a formal
dictionary

```text
sum_(p,p') c_(p,p') log(p)log(p')
```

without evaluating logarithms.  For dyadic `(X,2X]` it obtains:

| `X` | records | `DD/DR/RD/RR` | diagonal/off-diagonal |
|---:|---:|---:|---:|
| 32 | 5 | 4 / 0 / 0 / 1 | 5 / 0 |
| 64 | 6 | 6 / 0 / 0 / 2 | 6 / 2 |
| 128 | 15 | 11 / 0 / 0 / 8 | 15 / 4 |
| 256 | 26 | 19 / 1 / 1 / 11 | 26 / 6 |
| 512 | 24 | 14 / 1 / 1 / 10 | 24 / 2 |
| 1024 | 66 | 36 / 2 / 2 / 32 | 66 / 6 |

Reproducer:
[`workflows/research/pi/t143_gauss_two_ray_census.py`](../../../../workflows/research/pi/t143_gauss_two_ray_census.py)

Audited script SHA-256:

```text
7603950f28a06411500613af2880fdc7705d520d5b2736fd74ab9f1c2aa5d7e6
```

## Provenance and scope

The first worker artifact was
`workflows/state/runs/t131-p18-oxzen-6/work/oxzen-pi-t131-p18-gauss-two-ray-second-moment/MEMO.md`
(SHA-256 `e889b465fb3f3ee507d27ba68c60ba135c3d9de6e2eb35143e3208554d0c5474`).
Its normalization and four collision equations were useful, but its claimed
screen script was absent, its RR shifted-sum sign was wrong, and its displayed
sums omitted actual record constraints.  The retained reproducer and reduction
above independently repair those defects.

The reduction is `OPEN`: no power-saving estimate for the actual affine
correlations is proved.  The census is finite evidence only, and neither its
sparsity nor the absence of many mixed collisions proves GO or STOP.  This is
not a first-band result, not `(D)` or `V1` progress, and by itself does not
justify a Pro-model call.

V1 remains open.
