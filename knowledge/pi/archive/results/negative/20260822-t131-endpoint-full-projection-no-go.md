# T131 endpoint full-projection no-go

Status: `proof sketch`

For every registered first-supercritical block in the four tested offset
classes, the endpoint pair-bad set projects onto the entire full block
quotient.  Therefore the actual fresh residue `U_L mod B_L` alone cannot force
escape.  The result does not preserve intermediate bad constraints and says
nothing about the single canonical entry.

V1 remains open.

## Block and endpoint state

Let

```text
alpha=log_10(8/5),
E6(N)=alpha N+2log_10(N+1)+log_10 6,
H_N=min{h in Z:h>E6(N)}.
```

Fix `N>=6`, `c in {0,1,2,3}`, and put

```text
L=H_N+c,
m=N+L,
B=M_m/M_N,
T=M_N/48,
W=M_m/48=B T,
U=S_m-BS_N.
```

For the closed T130 coordinate `e_n=E_n mod (M_n/48)`, every compatible
entry obeys

```text
e_m=B e_N+U (mod W),
e_m=U (mod B).                                    (1)
```

Let `O_m` be the endpoint pair-bad set: both strict sufficient-hit tests at
`J_m-1` and `J_m` fail.

## Exact fiber count

Fix any residue `r mod B`.  Its endpoint lifts are

```text
e=r+B t,  t in Z/TZ.
```

For `s in {-1,0}` write

```text
k_s=J_m+s,
a_s=q_(k_s)/48,
d_s=gcd(a_s,T),
D_s=T/d_s.
```

As `t` varies, the phase contribution `a_s t/T` visits a uniformly spaced
`D_s`-point grid, each point with multiplicity `d_s`; all terms involving
`r`, `delta`, and `1/4` are only a fixed translation.

The strict good arc has length `1/2-2eps_(k_s)`.  Its closed bad complement
has length

```text
1/2+2eps_(k_s).
```

Uniformly in the translation,

```text
#Bad_s(r)
 >= d_s floor(D_s(1/2+2eps_(k_s))).               (2)
```

For `k_s>=5`, `q_(k_s)/48` is odd.  Since every `D_j` is odd,

```text
v_2(T)=4N-4.
```

Thus `d_s` is odd, `D_s` is even, and `D_s>=2^(4N-4)`.  From (2), the exact
sufficient condition

```text
2D_s eps_(k_s)>=1                                (3)
```

gives `#Bad_s(r)>T/2`.  If (3) holds for both `s=-1,0`, the two bad preimages
intersect by pigeonhole.  This conclusion is uniform in `r`.

## Uniform supercritical bound

The T129 localization with the audited wrap constant `K_5<18` gives

```text
J_m<=2N+8.                                        (4)
```

Here is an inspectable certificate for (4).  The exact pins

```text
alpha<5/24,
K_5<18
```

follow from

```text
8^24 < 10^5*5^24
```

and, using the exact numerator and denominator of `K_5`,

```text
18*denominator(K_5)-numerator(K_5)
=12200193382253304732681544866>0.
```

Put `b=29/24` and

```text
g(N)=bN+2log_10(N+1)+log_10 6+4,
F(N)=b g(N)+2log_10(g(N)+1)+log_10 18+1.
```

Since `H_N<=E6(N)+1` and `c<=3`, `m<g(N)` and the T129 upper envelope gives
`J_m<F(N)`.  At `N=10`,

```text
g(10)=193/12+log_10 726<19,
F(10)<671/24<28=2*10+8.
```

Here `726^12<10^35`, while `20^3<10^4` and `18^3<10^4` bound the logarithms.
For `N>=10`,

```text
g'=b+2/((N+1)ln 10),
F'=g'[b+2/((g+1)ln 10)].
```

Using `ln 10>2`, one has

```text
g'<343/264,
b+2/((g+1)ln 10)<29/24+12/205,
F'<2137919/1298880<2.
```

Thus `F(N)<2N+8` for every `N>=10`.  The four remaining exact `K_5`-envelope
checks are

```text
N=6: H_N=4, max_(c<=3) J_upper=20,
N=7: H_N=5, max_(c<=3) J_upper=22,
N=8: H_N=5, max_(c<=3) J_upper=23,
N=9: H_N=5, max_(c<=3) J_upper=25.
```

Each row is certified by the adjacent integer inequalities for
`6(N+1)^2(8/5)^N` and `K_5(m+1)^2(8/5)^m` after clearing denominators.

Using (4), the harder wrap phase satisfies

```text
D_s eps_(k_s)
 >= G_N
 =2^(4N-4)(5/8)^(2N+8)/[15(2N+9)^2].             (5)
```

Exactly

```text
G_9=298023223876953125/153896443516551168>1/2,
G_(N+1)/G_N=(25/4)((2N+9)/(2N+11))^2>1.
```

Hence (3) holds for all `N>=9`.  Direct exact base certificates for the
minimum of `2D_s eps_(k_s)` over `c=0..3`, `s=-1,0` are

```text
N=6: 216726982990264892578125/2281701376,
N=7: 137259882706150352954864501953125/50577534877696,
N=8: 1668321338582884371280670166015625/211106232532992,
```

all greater than one.  Therefore (3) holds for every `N>=6` in all four
supercritical offset classes.

## Full projection theorem

For every `N>=6`, `c in {0,1,2,3}`, and every `r mod B`, there is an endpoint
lift `e=r+Bt` belonging to `O_m`.  Equivalently,

```text
projection_B(O_m)=Z/BZ.                           (6)
```

Taking `r=U mod B` and using (1), some compatible entry `e_N` reaches an
endpoint that is bad at both pair tests.  Thus no argument using only the
endpoint bad-set projection and the complete fresh residue `U mod B` can
force a hit, even just beyond T129's safe horizon.

## Scope

The theorem is a `proof sketch` closing only endpoint full-projection
separation.  The selected compatible lift in (6) may be noncanonical.  It is
not shown to remain bad at any intermediate base state, and individual fresh
numerators before the endpoint are discarded.  Canonical component-address,
multi-time survivor, T130, T125, and V1 questions remain open.
