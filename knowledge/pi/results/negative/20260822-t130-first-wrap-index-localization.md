# T130 first-wrap index localization is cofinite

Status: `proof sketch`

Conclusion: the first-wrap windows provide no index
sparsification: even their two-point subwindows cover every sufficiently late
depth with bounded overlap.  This does not prove or refute T130, and it does
not show that the induced canonical coordinates are arithmetically useless.

V1 remains open.

## Provenance and audit

The creative derivation came from the single ChatGPT Pro job
`t130-canonical-first-wrap-transversality-pro-20260822`, answer SHA-256

```text
d77ee6428d5f3d4905e4a059d58fe1651aa113e84be61fd7c3a120b7879696fd
```

Three independent audits checked the polynomial identities, strict ratio
bounds, interlacing, cover, multiplicities, and claim scope.  The repairs
below include the separate `i=0` case and avoid identifying the rational
sufficient condition with all actual T125 returns.

## Definitions

Use the registered reduced BBP data

```text
nu_n=120n^2+151n+47,
D_n=(2n+1)(4n+3)(8n+1)(8n+5),
tau_n=16^(-n)nu_n/D_n,
q_j=10^j-16.
```

For `N>=6`, `i>=0`, put

```text
delta_(N,i)=q_(N+i) sum_(h=N+1..N+i) tau_h,
ell_N=min{i>=1: delta_(N,i)>=1/4},
J_N=N+ell_N.
```

The minimum exists because the positive partial tail tends to
`pi-A_N>0` while `q_(N+i)` tends to infinity.

For the canonical numerator define

```text
X_N=64S_N-191M_N,
x_N=X_N/(64M_N)=A_N-191/64.
```

Since `q_j*191/64 = 1/4 (mod 1)` for `j>=6`, the exact selector identity is

```text
R_(N+i)/M_(N+i)
 = center_1(1/4+delta_(N,i)+q_(N+i)x_N),          (1)
```

with `center_1` taking values in the half-open interval `[-1/2,1/2)`.

## Exact summand ratios

Direct expansion gives

```text
nu_n D_(n+1)-nu_(n+1)D_n
=3(40960n^5+220672n^4+453632n^3
   +443480n^2+206712n+36903)>0.                  (2)
```

With `m=n-1>=0`, the polynomial

```text
25nu_(n+1)D_n-4nu_nD_(n+1)
=1290240m^6+14034432m^5+61791936m^4
 +140358024m^3+172376886m^2+107354877m
 +25945605>0.                                    (3)
```

Therefore, for every `n>=1`,

```text
1/100 < tau_(n+1)/tau_n < 1/16.                 (4)
```

Also

```text
q_(j+1)=10q_j+144 <16q_j  (j>=2),
q_(j+2)=100q_j+1584 >100q_j.                    (5)
```

## Interlacing and step law

For `N>=6`, `i>=1`, shifting every term once and applying (4)-(5) proves

```text
delta_(N+1,i) < delta_(N,i) < delta_(N+1,i+1).  (6)
```

If `1<=i<ell_N`, the left inequality keeps `delta_(N+1,i)<1/4`;
the omitted `i=0` case is separately
`delta_(N+1,0)=delta_(N,0)=0<1/4`.  Hence
`ell_(N+1)>=ell_N`.  Applying the right inequality at `i=ell_N` gives
`delta_(N+1,ell_N+1)>delta_(N,ell_N)>=1/4`, hence

```text
ell_(N+1) in {ell_N,ell_N+1},
J_(N+1)-J_N in {1,2}.                            (7)
```

## Cofinite bounded-overlap normal form

Let `P_N={J_N-1,J_N}`.  Because consecutive `J_N` have gap one or two,
induction gives the exact cover

```text
union_(N>=6) P_N = {J_6-1,J_6,J_6+1,...}.        (8)
```

Every integer belongs to at most two pairs `P_N`.  It belongs to at most
three original windows `{J_N-1,J_N,J_N+1}`.

Consequently, for every pointwise predicate `P(j)`,

```text
P(j) holds for infinitely many j
iff
P(j) holds at some j in P_N for infinitely many N. (9)
```

Take the strict rational sufficient-hit set

```text
G={j>=6: |R_j/M_j| < 1/4-eps_j},
eps_j=(5/8)^j/[15(j+1)^2].
```

Equation (1) and bounded overlap show

```text
T130 iff G is infinite,                           (10)
```

and the `J_N+1` index in the original three-point formulation is redundant.
Thus first-wrap index localization alone is only a bounded-overlap reindexing
of the already-open strict rational sufficient-hit problem.

Membership in `G` implies the actual central return `||q_j pi||<1/4` by the
strict tail margin.  The converse is not proved, so (10) is not an
equivalence with all actual T125 returns or with T125 as a whole.

## Remaining canonical problem

Writing `rho_N=Lambda_(N+1)/Lambda_N` and
`u_(N+1)=nu_(N+1)Lambda_(N+1)/D_(N+1)` gives the exact selected recurrence

```text
X_(N+1)=16rho_N X_N+64u_(N+1).
```

Since `64|M_N` for `N>=6`, `E_N=X_N/64` is integral and

```text
E_(N+1)=16rho_N E_N+u_(N+1),
x_N=E_N/M_N.                                      (11)
```

The open step is still a moving-full-modulus return theorem for the actual
selected `E_N`.  Equations (7)-(10) control only the index naming and do not
control this canonical phase.

## Claim audit

- Selector identity, summand ratios, interlacing, step law, and cofinite
  cover: `proof sketch`.
- First-wrap index localization as a sparsification method: `proof sketch`
  showing that it gives only a cofinite bounded-overlap reindexing.
- T130 and T125: `conjecture`; both remain open.
- No machine-checked, candidate-resolution, or verified-resolution claim is
  made.
