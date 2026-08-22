# T148: Legendre transfer and repeated-difference obstruction for P20

Status: `proof sketch`  
Last audited: 2026-08-22

The frozen P20 universal-`J` criterion remains open.  The following exact
reduction and bounds were supplied by ChatGPT Pro, checked independently by
the direction and integration agents, and algebraically replayed where they
have finite certificates.

Pro answer SHA-256: `f691410c7231171ed6f5fddd0737ebe2d51d5a24e401ee2d03f2eb6ee20c99ec`.

## Legendre normalization

Let `p>=7` be prime and `m=(p-1)/2`.  For every `0<=j<p` define

```text
G_j(X)=sum_(r=0)^j binom(m,r)binom(m,j-r)X^r.
```

For `j` in `I_p=[ceil(p/11),floor(2p/5)]`, so that `j<m`, one has

```text
F_j(X)=X^(m-j)G_j(X).
```

Over an algebraic closure choose `u^2=X` and put
`tau=-(u+u^(-1))/2`.  Comparing in `F_p[[Z]]` modulo `Z^p`,

```text
sum_(0<=j<p) G_j(X)Z^j
 == ((1+Z)(1+XZ))^(-1/2) (mod Z^p)
```

through degree `<p` with the Legendre generating function gives

```text
G_j(X)=u^j P_j(tau).
```

The change `u -> -u` changes both sides by `(-1)^j`, so the zero condition is
well defined.  Squaring the generating function also gives, for `n<p`,

```text
sum_(r=0)^n G_r(X)G_(n-r)(X)=(-1)^n(1+X+...+X^n).
```

Thus for `x!=1` the left side vanishes exactly when `x^(n+1)=1`.

## Transfer-polynomial degree bound

For `a>=1`, define `K_(a,0)=0`, `K_(a,1)=1`, and

```text
(a+r+1)K_(a,r+1)(T)
  =(2a+2r+1)T K_(a,r)(T)-(a+r)K_(a,r-1)(T).
```

All denominators are nonzero in the frozen interval.  The Legendre recurrence
shows that

```text
P_a(tau)=P_(a+h)(tau)=0  =>  K_(a,h)(tau)=0,
deg K_(a,h)=h-1.
```

Using the parity of `K` and
`tau^2=(x+x^(-1)+2)/4`, at most `h-1` values of nonzero `x` can arise.
Because `X^N_p-1` is squarefree, every `J={j_1<...<j_k}` in `I_p` obeys

```text
deg gcd(X^N_p-1,{F_j:j in J})
 <= floor((floor(2p/5)-ceil(p/11))/(k-1))-1.
```

At `k=ceil(sqrt(p))` this is at most `(17/55)sqrt(p)+O(1)`.  This controls
the number of common torsion roots, not their multiplicative orders.

The first transfer polynomials additionally show that a high-order zero set
has no gap `1` or `2`, and that gaps `3` and `4` occur at most once in the
frozen interval.  The negative note registered alongside this result shows
why no analogous fixed-gap or fixed-puncture conclusion can close P20.

## Linear repeated-difference obstruction

For an `N_p`-torsion root `x`, put

```text
Z_x={j in I_p:F_j(x)=0},
r_h(x)=#{a:a,a+h in Z_x},
E(Z_x)=sum_(h>=1) max(r_h(x)-1,0).
```

Here `E` is repeated-difference excess, not the standard additive energy.
Every unordered pair contributes one positive difference, and at most

```text
L_p=floor(2p/5)-ceil(p/11) <= 17p/55
```

different positive differences are available.  Hence

```text
E(Z_x)>=binom(|Z_x|,2)-L_p.
```

In particular, a frozen counterexample with
`|Z_x|>=ceil(sqrt(p))` and `ord(x)>D_p` must satisfy

```text
E(Z_x)>=21p/110-sqrt(p)/2.
```

This exact linear lower bound is the useful global obstruction.  The Pro
proposal `E(Z_x)<=C*p/ord(x)` is only a `conjecture`; no proof or asymptotic
evidence for it is registered.

## Local multiplicity limitation

If distinct `j_1,...,j_k` have a common Legendre root `tau`, then the values
`lambda_i=j_i(j_i+1)` are distinct in the frozen interval.  Differentiating
the Legendre equation and applying barycentric weights in the `lambda_i`
constructs a nonzero linear combination of the `P_(j_i)` with a zero of
exact multiplicity `2k-1` at `tau`.  For `k` of order `sqrt(p)`, this is only
of order `sqrt(p)` while the combination may have degree of order `p`.
Orbit products scale available degree and forced multiplicity together.
This closes that displayed local-jet construction as a route to order
control; it does not exclude every possible multiplicity method.

## Fixed-rho target

To avoid ambiguous notation, put

```text
a_j=[z^j](z^2+2z+2)^j.
```

The frozen coefficient satisfies `A_j == a_j (mod p)`, and with
`r_+=2+2sqrt(2)` one has, in the relevant field modulo `p`,

```text
a_j == (-r_+)^j G_j(rho) (mod p).
```

Moreover

```text
sum_(j>=0) a_j T^j=(1-4T-4T^2)^(-1/2).
```

For `b_n=sum_(r=0)^n a_r a_(n-r)`, squaring this series gives

```text
b_n=0 (mod p)  iff  rho^(n+1)=1 (mod p).
```

Consequently the distinguished-root implication needed for the T144
diagonal is equivalently a fixed-sequence zero/short-convolution statement.
This is a target identification, not a proved anti-concentration theorem.

## Next gate

P21 freezes one concrete sufficient statement: when
`b_0,...,b_(D_p-1)` are all nonzero modulo `p`, the repeated-difference
excess of `{j in I_p:p|a_j}` is at most `p^(3/4)` (interpreted exactly as
`E^4<=p^3`) for all odd `p>503`.  Together with the linear lower bound this
would exclude `ceil(sqrt(p))` zeros outside an explicit finite range.

No P20 GO or STOP, diagonal power saving, `(D)`, or V1 result is claimed.

V1 remains open.
