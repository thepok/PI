# T35: a strict subcritical saving and the supercritical cancelling sector

Status: `proof sketch`.

This note gives a self-contained finite proof of a strict improvement over the
exponent-eight pointwise majorant used in the T33 note, audits all six literal
cancelling domains, sums the saving over the only rows active at low height,
and reduces `ARI_cancel` to one strictly smaller named sector. It does not
prove the remaining sector. It does not assert the all-scale T29 predicate,
the canonical collision estimate, C2, or C1.

The definitions imported from T24, T29, and T32 are machine-checked. The T33
note is unverified and is used only to motivate notation: every combinatorial
identity and estimate needed here is derived again below. The one external
input is the source-pinned irrationality-measure assertion in Section 7.

## 1. Provenance and exact scope

The canonical question is copied byte-for-byte as
`CANONICAL_STATEMENT.txt`. It is a locally formulated problem and has no
original external source URL. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

It asks whether, for every real `0<s<1`, one constant `C_s` works for all
positive integers `m,N` in

```text
R_pi(m,N) <= C_s [N+N^2 10^(-s m)].                     (1.1)
```

The pairs in (1.1) are ordered and have lag at least `m`. This note does not
estimate `R_pi`. It treats the cancelling off-diagonal part of T29's residual
width-weighted square-function sibling, so its result remains in the recorded
sibling/reduction scope A12.

### Normalized quantifiers and ambiguities

Fix throughout

```text
Q0,m,N in N, Q0>=0, m>=1, N>=1, H=10^m.                 (1.2)
```

For the literal `ARI_cancel` under attack, `Q0` is fixed to the particular
onset supplied by the source-level exponent-eight consequence used in T33,
and is the onset present in T32's record domain at `(mu,c)=(8,1)`. Section 7
fixes a second onset `Q_*>=1`, for the independently chosen source exponent
`36/5`; `Q0` and `Q_*` are not identified. The combinatorial bounds below do
not use the source property of `Q0`, but the comparison with the exponent-eight
majorant in Section 10 does.

The following conventions are binding.

1. Every block is left-closed and right-open.
2. Both Bool orientations of every surviving T32 record are retained.
3. Frequencies are exactly `h=1,...,H`, including `h=H` and excluding `h=0`.
4. The block weight is exactly `sqrt(b^2-a^2)`.
5. A positive difference is taken in the order `lambda(q1)-lambda(q0)>0`.
6. Cancellation means equality of oppositely signed decimal-power tokens.
7. The reduced factor is `10^rho-1=9R_rho`, not `R_rho` alone.
8. Every sum in this note is finite. Empty domains contribute zero.
9. All results include every positive `m,N`; no favorable scale is selected.
10. The terminal inequality remains an unproved orbit-specific premise.

## 2. Machine-checked interfaces and literature log

The definitions used below are available in the retained knowledge library:

| item | verification | interface used |
|---|---|---|
| T24 | machine-checked through the T29 import | canonical dyadic partition |
| T29 | machine-checked | inclusive frequencies and literal width weights |
| T32 | machine-checked | exact record domain, orientations, and finite energy identity |
| T33 | unverified `proof sketch` | motivation only; no claim imported |

The external source is Doron Zeilberger and Wadim Zudilin, *The Irrationality
Measure of Pi is at most 7.103205334137...*, Moscow Journal of Combinatorics
and Number Theory 9 (2020), 407-419,
<https://doi.org/10.2140/moscow.2020.9.407>. The retained publisher PDF has
SHA-256
`3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
The definition is on PDF page 2 (journal page 407), and the displayed bound
`7.10320533413700172750577342281...` is on PDF page 13 (journal page 418).

Literature search log, 2026-08-02: the retained source supports an exponent
strictly below `36/5=7.2`. No source found in the accumulated T21 or T33
material supplies the terminal decimal-orbit correlation inequality defined
in Section 11.

## 3. Exact T32 records and block weights

For a lag `ell>0` and start `n>=0`, set

```text
E(ell,n)=n+ell,
A(ell,n)=10^(n+ell)-10^n=10^n(10^ell-1)>0.              (3.1)
```

An oriented record is `q=(epsilon,(ell,n))`, with

```text
lambda(+,ell,n)= A(ell,n),
lambda(-,ell,n)=-A(ell,n).                               (3.2)
```

For a canonical block `B=[a_B,b_B)`, the exact record set is

```text
Q_B={q=(epsilon,(ell,n)):
       ell>0, m<=ell,
       not ArithmeticExcluded 8 1 Q0 m n ell,
       a_B<=n+ell<b_B}.                                  (3.3)
```

The exclusion in (3.3) is literally

```text
ArithmeticExcluded 8 1 Q0 m n ell
 iff Q0<=q(n,ell) and H^(-1)<=q(n,ell)^(-7),
q(n,ell)=10^n(10^ell-1).                                (3.4)
```

No survival condition will be dropped from an exact multiplicity. We only
drop it when taking an upper bound.

Write the nonzero binary positions of `N-1` in decreasing order as

```text
j_0>j_1>...>j_(r-1), L_i=2^(j_i),
q_i=sum_(u<i) L_u.                                       (3.5)
```

T24's canonical list is exactly

```text
B_i=[q_i+1,q_i+1+L_i), 0<=i<r.                           (3.6)
```

It partitions `[1,N)`. For `N=1`, `r=0` and the list is empty. Its literal
weight is

```text
w_i=sqrt((q_i+1+L_i)^2-(q_i+1)^2)
   =sqrt(L_i(2q_i+2+L_i))>0.                             (3.7)
```

The frequency range is the inclusive set `{1,...,H}`. With

```text
K_H(x)=sum_(h=1)^H exp(2 pi i h x),
C_H(x)=Re K_H(x),                                        (3.8)
```

the exact block expansion is

```text
sum_(h=1)^H |sum_(q in Q_B) exp(2 pi i h lambda(q) alpha)|^2
 =H #Q_B+
   sum_(q0,q1 in Q_B; q0!=q1)
     K_H((lambda(q1)-lambda(q0))alpha).                  (3.9)
```

Both orientations are already in `Q_B`; there is no later orientation
multiplier.

## 4. Exhaustive six-row cancellation partition

Let `q_i=(epsilon_i,(ell_i,n_i))` be distinct records in one block and put
`E_i=n_i+ell_i`. Define

```text
(X_i,Y_i)=(E_i,n_i) if epsilon_i=+,
(X_i,Y_i)=(n_i,E_i) if epsilon_i=-.                      (4.1)
```

For a positive ordered difference,

```text
d=lambda(q1)-lambda(q0)
 =10^(X_1)+10^(Y_0)-10^(Y_1)-10^(X_0)>0.                (4.2)
```

The within-record equalities `X_1=Y_1` and `Y_0=X_0` are impossible because
both lags are positive. Thus an opposite-sign cancellation in (4.2) is
exactly `X_1=X_0` or `Y_0=Y_1`. Both cannot occur: they would make the signed
frequencies equal, and the decimal representation
`10^n(10^ell-1)` is injective in `(n,ell)` by its exact ten-adic valuation and
primitive factor.

Deleting the unique equal pair leaves

```text
d=10^(v+rho)-10^v=10^v(10^rho-1)=9*10^v R_rho,          (4.3)
rho>=1, v>=0, R_rho=(10^rho-1)/9.
```

The six possibilities are the following. The table defines the finite set
`C_(B,j)(v,rho,z)`: in addition to its displayed row, both records must belong
to the literal set `Q_B` in (3.3).

| `j` | `(epsilon_0,epsilon_1)` | cancellation and positivity | parameters |
|---|---|---|---|
| 1 | `(+,+)` | `E_0=E_1`, `n_1<n_0` | `n_1=v`, `n_0=v+rho`, `E_0=z` |
| 2 | `(+,+)` | `n_0=n_1`, `E_0<E_1` | `E_0=v`, `E_1=v+rho`, `n_0=z` |
| 3 | `(-,-)` | `E_0=E_1`, `n_0<n_1` | `n_0=v`, `n_1=v+rho`, `E_0=z` |
| 4 | `(-,-)` | `n_0=n_1`, `E_1<E_0` | `E_1=v`, `E_0=v+rho`, `n_0=z` |
| 5 | `(-,+)` | `E_1=n_0` | `n_1=v`, `E_0=v+rho`, `E_1=z` |
| 6 | `(-,+)` | `E_0=n_1` | `n_0=v`, `E_1=v+rho`, `E_0=z` |

There is no positive `(+,-)` row because its difference is `-A_1-A_0<0`.
Rows 1-4 have exactly the displayed strict order. In row 5,
`v=n_1<E_1=n_0<E_0=v+rho`; row 6 is its reflected chain. Different
orientation patterns are disjoint. Rows 1 and 2, or 3 and 4, cannot overlap
without equal records. Rows 5 and 6 cannot overlap because that would give a
strict cyclic order. Hence the six rows are exhaustive and pairwise disjoint.

Put `k=v+rho`. Every positive cancelling pair has

```text
(v,rho) in D_N={(v,rho): rho>=1 and k<N},                (4.4)
```

and the exact hidden-exponent restrictions are

```text
rows 1,3: z>=m+k; both endpoints are z in B;
rows 2,4: 0<=z<=v-m; both endpoints v,k are in B;
rows 5,6: v+m<=z<=k-m; both endpoints z,k are in B.      (4.5)
```

The last interval is empty unless `rho>=2m`. Every row additionally retains
both clauses `not ArithmeticExcluded ...` from (3.3).

The base-ten valuation of (4.3) is exactly

```text
v_10(d)=v, tenPrimitivePart(d)=10^rho-1.                 (4.6)
```

This is valid although base ten is composite: `10^rho-1` is coprime to ten.
Consequently `(v,rho)` is uniquely determined by `d`.

Define

```text
M_(B,j)(v,rho,z)=#C_(B,j)(v,rho,z),
M_B(v,rho)=sum_(z=0)^(N-1) sum_(j=1)^6 M_(B,j)(v,rho,z),
W(v,rho)=sum_B M_B(v,rho)/w_B.                           (4.7)
```

These are record-pair multiplicities, not counts of distinct coefficients.

## 5. Exact cancelling sum and shells

Swapping a pair negates its nonzero difference and preserves its block and
cancellation status. Since `K_H(x)+K_H(-x)=2C_H(x)`, the finite partition in
Section 4 gives

```text
Can(pi)=2 sum_((v,rho) in D_N)
              W(v,rho) C_H(d(v,rho) pi),                (5.1)
d(v,rho)=10^v(10^rho-1).
```

The factor two in (5.1) is only the swap/conjugation factor.

Let `delta(d)=||d pi||_T`. Let `K_m` be the least integer `K>=1` with
`2^(K+1)>=H`, and define disjoint shells

```text
S_0={d: 0<=delta(d)<=1/H},
S_j={d: 2^(j-1)/H<delta(d)<=min(2^j/H,1/2)},
    1<=j<=K_m.                                           (5.2)
```

Thus equality at `1/H` belongs to `S_0`, and each later upper dyadic endpoint
belongs to the lower-index shell. Minimality of `K_m` makes the final upper
endpoint `1/2`, so (5.2) covers every distance exactly once.

Define the literal incidences

```text
I_j=sum_B 1/w_B sum_((v,rho) in D_N) M_B(v,rho)
      1_{d(v,rho) in S_j}.                               (5.3)
```

All six rows, hidden exponents, survival conditions, and literal weights
remain inside (5.3). Define the exact `ARI_cancel` left side

```text
A(m,N)=I_0+sum_(j=1)^K_m 2^(-j) I_j.                    (5.4)
```

Equivalently, if

```text
theta_m(d)=1 for d in S_0,
theta_m(d)=2^(-j) for d in S_j, j>=1,                   (5.5)
```

then the finite shell partition gives the exact identity

```text
A(m,N)=sum_((v,rho) in D_N) W(v,rho)theta_m(d(v,rho)).   (5.6)
```

The geometric-series bound

```text
|C_H(x)|<=min(H,1/[2||x||_T])                            (5.7)
```

and (5.1) imply `|Can(pi)|<=2H A(m,N)`.

## 6. A literal canonical-block budget

Set

```text
F_N=sum_(B in canonical blocks) blockLength(B)/w_B.      (6.1)
```

We prove, for every `N>=1`,

```text
F_N<3.                                                   (6.2)
```

For `N=1`, the sum is empty. Otherwise use (3.5)-(3.7). The first term is

```text
L_0/w_0=sqrt(L_0/(2+L_0))<1.                            (6.3)
```

For `i>=1`, strict decrease of the integer levels gives
`L_i<=L_0/2^i`, while `q_i>=L_0`. Therefore

```text
L_i/w_i
 =sqrt(L_i/(2q_i+2+L_i))
 <=sqrt(L_i/(2q_i))
 <=2^(-(i+1)/2).                                        (6.4)
```

The infinite geometric tail is exactly

```text
sum_(i=1)^infinity 2^(-(i+1)/2)
 =(1/2)/(1-1/sqrt(2))=1+1/sqrt(2).                      (6.5)
```

Hence `F_N<2+1/sqrt(2)<3`, proving (6.2). This proof uses the
literal `sqrt(b^2-a^2)` weights.

## 7. The source exponent 36/5 and pointwise saving

The retained paper defines the irrationality-measure quantifiers and gives an
upper bound `7.103205334137...<36/5`. We use the following source-pinned
consequence and enlarge its onset to at least one:

```text
(P_36/5) There exists Q_*>=1 such that for every integer p and
every integer d>=Q_*,
  |pi-p/d|>d^(-36/5).                                    (7.1)
```

This is an external literature premise, not a Lean theorem or a new axiom in
the verified track.

Choosing a nearest integer `p` to `d pi` in (7.1) gives

```text
delta(d)>d^(-31/5).                                      (7.2)
```

Consequently

```text
|C_H(d pi)|<=min(H,d^(31/5)/2), d>=Q_*.                 (7.3)
```

On the common domain `d>=max(Q0,Q_*)`, T33's exponent-eight insertion is
`min(H,d^7/2)`. Before either cap reaches `H`, (7.3) improves its nontrivial
term by the exact factor

```text
(d^(31/5)/2)/(d^7/2)=d^(-4/5)<1.                        (7.4)
```

This is a strict pointwise quantitative saving, not merely a renamed
incidence premise.

There is also a normalized shell consequence. If `d>=Q_*` and
`d^(31/5)<H`, then (7.2) excludes `S_0`. If `d` lies in `S_j`, `j>=1`, its
upper endpoint and (7.2) give

```text
d^(-31/5)<delta(d)<=2^j/H,
theta_m(d)=2^(-j)<d^(31/5)/H.                            (7.5)
```

## 8. Exact six-row multiplicity envelopes

Fix `(v,rho)` and write `k=v+rho`. Each row and hidden exponent uniquely
determines its two records; discarding survival conditions can only increase
the count.

For rows 1 and 3, the eligible `z` in a block form a subset of that block, so

```text
sum_B [number of eligible z in B]/w_B<=F_N.
```

Together those two rows contribute at most `2F_N`.

For rows 5 and 6, eligible `z` again form a subset of the block containing
both `z` and `k`. Dropping the condition that `k` is in the same block gives
another upper bound `2F_N`.

For rows 2 and 4, `z` has at most `(v-m+1)_+` values. Because the canonical
blocks are disjoint, at most one block contains both endpoints `v,k`. Every
canonical weight is at least `sqrt(3)`: from (3.7), `L_i>=1` and the block
start is at least one, so `w_i^2=L_i(2q_i+2+L_i)>=3`.

Combining the three row pairs and (6.2) gives the all-row envelope

```text
W(v,rho)
 <=4F_N+2(v-m+1)_+/sqrt(3)
 <12+2(v+1)/sqrt(3).                                    (8.1)
```

If `k<m`, rows 2 and 4 are impossible because they require `v>=m`, and rows
5 and 6 are impossible because they require `rho>=2m`. In that range only
rows 1 and 3 remain, and

```text
W(v,rho)<=2F_N<6.                                        (8.2)
```

Both (8.1) and (8.2) retain multiplicity before taking the displayed upper
bound; no coefficient is counted only once by fiat.

## 9. The finite pre-onset sector

Define the explicit finite constant

```text
C_fin(Q_*)=
 sum_(v>=0,rho>=1; 10^v(10^rho-1)<Q_*)
   [12+2(v+1)/sqrt(3)].                                  (9.1)
```

The sum is finite because its condition bounds both `v` and `rho`. Since
`theta_m(d)<=1`, (8.1) proves for all positive `m,N`

```text
sum_(d(v,rho)<Q_*) W(v,rho)theta_m(d(v,rho))
 <=C_fin(Q_*).                                           (9.2)
```

This explicitly handles hidden-exponent multiplicity; finiteness of the set
of coefficients alone would not prove (9.2).

## 10. Summing the low valuation-height sector

Let

```text
t=floor(5m/31),
L={(v,rho) in D_N: d(v,rho)>=Q_* and 31(v+rho)<=5m}.      (10.1)
```

For `(v,rho)` in `L`, `k=v+rho<=t<m`, so only rows 1 and 3 occur. Moreover

```text
d(v,rho)<10^k,
d(v,rho)^(31/5)<10^(31k/5)<=10^m=H.                     (10.2)
```

Equations (7.5), (8.2), and the exactly `k` decompositions
`k=v+rho` with `v>=0,rho>=1` give

```text
A_low(m,N)
 :=sum_((v,rho) in L) W(v,rho)theta_m(d(v,rho))
 <=6*10^(-m) sum_(k=1)^t k*10^(31k/5).                  (10.3)
```

When `t=0`, both sides of (10.3) are zero. Assume `t>=1` for the next two
displays.

Put `R=10^(31/5)>10^6`. For `t>=1`, the finite sum satisfies

```text
sum_(k=1)^t kR^k
 <=tR^t sum_(u=0)^(t-1) R^(-u)
 <tR^t/(1-R^(-1)).                                      (10.4)
```

Because `31t<=5m`, `R^t<=10^m`; because `R^(-1)<10^(-6)`, (10.3)-(10.4)
give, when `t>=1`,

```text
A_low(m,N)<6t/(1-10^(-6)).                               (10.5)
```

If `t=0`, the set `L` is empty and `A_low=0<N`. If `t>=1` and `N<=m`, every
T32 record domain is empty: an endpoint is `n+ell>=m` but must lie in `[1,N)`.
Thus again `A_low=0`. If `t>=1` and `N>m`, then

```text
t<=5m/31<5N/31,
6t/(1-10^(-6))<30N/[31(1-10^(-6))]<N,                  (10.6)
```

where the last strict inequality is the integer check

```text
30<31(1-10^(-6))=30.999969.                              (10.7)
```

Therefore the all-range conclusion is

```text
A_low(m,N)<N for every m,N>=1.                           (10.8)
```

### Displayed asymptotic saving over exponent eight

The saving is also visible before absorption into `N`. Put
`Q_hat=max(Q0,Q_*)`. On the common domain where both pointwise bounds apply,
retain the exact coefficient

```text
d_(k,rho)=10^(k-rho)(10^rho-1).
```

The exponent-eight normalized pointwise majorant is

```text
U_8(m)=6 sum_(k=1)^t sum_(rho=1)^k
          1_{d_(k,rho)>=Q_hat}
          min(1,d_(k,rho)^7/10^m),                       (10.9)
```

whereas (7.5) gives

```text
U_(36/5)(m)=6 sum_(k=1)^t sum_(rho=1)^k
                1_{d_(k,rho)>=Q_hat}
                d_(k,rho)^(31/5)/10^m
             <=6*10^(-m) sum_(k=1)^t k*10^(31k/5).
```

This is zero when `t=0`; when `t>=1`, (10.4) bounds it strictly by
`6t/(1-10^(-6))`.

For the infinite family `m=217u`, take all sufficiently large `u` so that
`9*10^(31u)>=Q_hat`; then `t=35u`. The layers
`31u+1<=k<=35u` satisfy, for every `1<=rho<=k`,

```text
d_(k,rho)^7/10^m
 >=10^7(1-10^(-rho))^7
 >=10^7(9/10)^7=9^7>1.
```

There are `4u` such layers, and hence

```text
U_8(217u)>=6(4u)(31u+1)>744u^2,                          (10.11)
U_(36/5)(217u)<210u/(1-10^(-6))<211u.                   (10.12)
```

Thus the new aggregate majorant saves at least a factor
`(744/211)u` on this explicit infinite scale family. Equations (7.4) and
(10.11)-(10.12) provide respectively pointwise and summed strict savings.
They do not claim the actual kernels attain either majorant.

## 11. One strictly smaller terminal inequality

Insert the following indicator into the literal incidence (5.3):

```text
T(m)={(v,rho) in D_N:
       d(v,rho)>=Q_* and 31(v+rho)>5m}.                  (11.1)

I_j^super=
 sum_B 1/w_B sum_((v,rho) in T(m)) M_B(v,rho)
   1_{d(v,rho) in S_j}.                                  (11.2)
```

Call the following statement `ARI_super(36/5)`:

```text
For every real s with 0<s<1, there exists C_s^super>=0
such that for every m,N>=1,

I_0^super+sum_(j=1)^K_m 2^(-j)I_j^super
 <=C_s^super [N+N^2 10^(-s m)].                         (11.3)
```

This is one named sector, not a list of unresolved cases. It is strictly
smaller than `ARI_cancel`: it excludes every pre-onset coefficient and every
valuation-height pair with `31(v+rho)<=5m`. This deletes actual nonzero
incidences, not just unused outer parameters. Choose `rho` with
`Q_*<=10^rho-1`, choose `m` with `31rho<=5m`, put `z=m+rho`, and choose
`N>z`. Row 1 with `(v,rho,z)=(0,rho,m+rho)` consists of starts `0,rho`, common
endpoint `z`, and lags `m+rho,m`. Both records survive (3.4), since each
structured denominator `q` satisfies `q^7>10^m`; their common endpoint lies
in one canonical block. Thus this gives positive original multiplicity but is
excluded from (11.1).

The three disjoint conditions

```text
d<Q_*,
d>=Q_* and 31(v+rho)<=5m,
d>=Q_* and 31(v+rho)>5m                                 (11.4)
```

partition the exact sum (5.6). Equations (9.2) and (10.8) therefore prove

```text
A(m,N)
 <=A_super(m,N)+C_fin(Q_*)+N
 <=A_super(m,N)+[C_fin(Q_*)+1]N.                         (11.5)
```

Since `N>=1`, `ARI_super(36/5)` implies `ARI_cancel`, with the explicit
constant conversion

```text
C_s=C_s^super+C_fin(Q_*)+1.                              (11.6)
```

Conversely, every summand is nonnegative, so `A_super<=A`; `ARI_cancel`
implies (11.3) with the same constant. Thus, under the source-pinned premise
(7.1), `ARI_cancel` is equivalent to the strictly narrower
`ARI_super(36/5)`, up to the explicit additive constant in (11.6).

At the Dirichlet-kernel level, (5.7) and (11.5) also give

```text
|Can_sub(pi)|
 <=2*10^m [C_fin(Q_*)+1]N,                               (11.7)
```

where `Can_sub` contains exactly the first two parts of (11.4), with every
literal weight and multiplicity retained.

## 12. Terminal status and verification boundary

The new argument has status `proof sketch`. It establishes the following
checkable reduction in prose:

1. The six exact cancelling rows give (4.7) and the shell identity (5.6).
2. The literal canonical weights satisfy the all-range budget `F_N<3`.
3. The pinned exponent `36/5` improves T33's exponent-eight nontrivial
   pointwise term by `d^(-4/5)`.
4. The complete pre-onset and low-height contribution is at most
   `[C_fin(Q_*)+1]N` for every positive `m,N`.
5. The sole remaining condition is the strictly narrower inequality
   `ARI_super(36/5)` in (11.3).

No estimate for (11.3) is supplied. Accordingly this note is not a proof or
refutation of `ARI_cancel`, T29's all-scale fixed-pi premise, the canonical
collision estimate, C2, or C1. No finite computation is used as evidence for
a universal claim.

## 13. Formalization and independent review map

- Existing machine-checked definitions: T24, T29, and T32.
- New prose lemmas suitable for later formalization: the six-row multiplicity
  envelope (8.1), block budget (6.2), shell saving (7.5), and low-height sum
  (10.8).
- Missing theorem: `ARI_super(36/5)`.
- Axiom audit: not applicable; this artifact contains no Lean declarations.
- Independent statement review: pending.
- Independent proof review: pending.
- Novelty/attribution review: pending.
