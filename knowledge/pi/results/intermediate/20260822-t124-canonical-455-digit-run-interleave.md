# T124 canonical 455 carries and decimal five-runs

Date: 2026-08-22 UTC

Status: `proof sketch`

Source candidate:
`workflows/state/runs/t124-455-wave-oxzen-r2/work/oxzen-pi-t124-canonical-455-blocks/MEMO.md`.
The formulas below retain only the independently corrected part of that
artifact; its claimed obstruction to using the full BBP numerator is rejected.

For the canonical BBP diagonal, write

```text
R_n=(10^n-16)*A_n=a_n+e_n,
a_n=floor(R_n+1/2),                 e_n in [-1/2,1/2),
b_n=a_(n+1)-10*a_n,
x_n=10^n*pi-a_n,
rho_n=(10^n-16)*(pi-A_n).
```

For `n>=2`, the audited tail estimate gives `0<=rho_n<0.002`, and

```text
x_n in W_n=[16*pi+rho_n-1/2, 16*pi+rho_n+1/2).
```

Put `alpha=455/9-16*pi`, so `0.29<alpha<0.291`.  For the half-open
window above, the unique integer selected at one step is

```text
B_n(x)=floor(10*x-16*pi-rho_(n+1)+1/2).
```

The constant point `x*=455/9` has selected carry `455` at every index
`n>=2`.  If

```text
Delta_N=x_N-455/9,
L_455(N)=max{L>=0 : b_(N+r)=455 for every 0<=r<L},
```

then for `N>=2` and `L>=1` the exact half-open criterion is

```text
b_N,...,b_(N+L-1) are all 455
iff
Delta_N in 10^(-L) *
  [rho_(N+L)-alpha-1/2, rho_(N+L)-alpha+1/2).
```

Indeed, during such a block,
`x_(N+r)-x*=10^r*Delta_N`.  Membership at the final endpoint implies all
earlier memberships: the final interval lies inside `[-0.791,0.212)`, while
one backward decimal scaling lies inside every earlier window.  This also
retains the strict coarse shadowing estimate

```text
|Delta_N|<10^(-L).
```

Finiteness of `L_455(N)` follows from the canonical carry-tail
nonperiodicity result: an infinite 455 tail would be eventually periodic.
At the maximal length `L=L_455(N)`, inclusion at depth `L` and failure at
depth `L+1` give the corrected sharp bounds

```text
10^(-L-1)*(1/2-alpha+rho_(N+L+1)) <= |Delta_N|
  <= 10^(-L)*(1/2+alpha-rho_(N+L)).
```

The upper inequality is non-strict because the left endpoint of the centered
window is included.

Let `d_m` denote the nonterminating decimal digits of `pi`, and put

```text
D5(N)=max{M>=0 : d_(N+1)=...=d_(N+M)=5}.
```

A run of `M` fives is exactly

```text
{10^N*pi}-5/9 in
  [-(5/9)*10^(-M), (4/9)*10^(-M)).
```

Comparing this interval with the corrected carry window proves, pointwise for
every `N>=2`,

```text
D5(N)-1 <= L_455(N) <= D5(N)+1,
```

equivalently `|L_455(N)-D5(N)|<=1`.  Consequently their normalized limsup and
liminf agree, and in particular

```text
L_455(N)=o(N)  iff  D5(N)=o(N).
```

## Claim boundary

This is an exact target identification up to one index.  It does not show
that arithmetic of the full BBP numerator `S_n` can reach the carry statistic
only through `rho_n`, nor that such arithmetic cannot prove a decimal
five-run bound.  The canonical quantities `a_n`, `x_n`, and `Delta_N` still
depend directly on `A_n` and hence on `S_n`; cross-depth numerator information
could in principle constrain their alignment.

No sublinear run bound is proved here.  The result proves neither `(D)` nor
V1, and it supplies no progress on decimal occurrence or density.  V1 remains
open.
