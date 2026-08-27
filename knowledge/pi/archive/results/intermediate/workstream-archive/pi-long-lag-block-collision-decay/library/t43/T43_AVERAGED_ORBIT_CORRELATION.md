# T43: weighted four-row orbit correlation without a maximum

Status: `proof sketch` giving a strict quantitative refinement of the
max-based four-row domination and isolating one narrower averaged
orbit-correlation inequality. The finite arguments are fully displayed, but
they have not been formalized in Lean.

This note does not prove the four-row bound. It does not assert `ARI_super`,
`ARI_cancel`, C3, C2, C1, or the canonical collision estimate.

## 1. Provenance, normalized target, and ambiguities

The canonical local problem has no external source URL. A byte-exact copy is
delivered as `CANONICAL_STATEMENT.txt`; its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That problem asks about the ordered long-lag decimal collision count at
`pi`. T43 instead concerns sibling A12: the residual sparse-Fourier incidence
after arithmetic exclusions. Within A12 it treats only T34 rows 2, 4, 5, and
6, not all six rows.

Fix arbitrary natural numbers `Q0,Qstar`. The four-row target would say:

```text
for every real s with 0 < s < 1, there is a real C >= 0 such that,
for every natural m,N with 1 <= m and 1 <= N,

  A_4(Q0,Qstar;m,N)
    <= C [N + N^2 10^(-s m)].                              (1.1)
```

All powers and products in the bracket in (1.1) are real. The constant may
depend on `Q0,Qstar,s`, but not on `m,N`, a block, a row, `v,k,z`, or a shell.
The two target terms are literal.

The following ambiguities are resolved explicitly.

1. This is not the canonical count `R_pi(m,N)` and does not settle A1.
2. `Q0,Qstar` are fixed before `s,m,N`.
3. The strict supercritical cutoff is `5m < 31k`, not a weak inequality.
4. Every block is half-open and every positive shell is open below and closed
   above. Shell zero is closed at `10^(-m)`.
5. A fixed `m` family cannot refute (1.1), because the target still contains
   a quadratic term in `N`.
6. The T39--T42 notes are sketch-level motivation only. No claim from them is
   used as a discharged premise.

## 2. Machine-checked input and sketch boundary

The sole accumulated file used as kernel-checked input is

```text
TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving
SHA-256 3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24
```

T36 imports the kernel-checked T34 row and shell definitions. The interfaces
used here are `six_cancelling_domains_audit`,
`sourceExponent_shell_endpoint_audit`,
`restrictedWeightedShellIncidence_eq_direct`, and
`ARI_super_iff_quantifiers`. The exact four-row restriction and every
regrouping below are reconstructed in this note and remain `proof sketch`.

For audit only, the motivation notes have hashes

```text
T39 029b2be54cf45f334f82f016ec92d8cc9efbfead3c47ac444ae90c8f46ebce05
T40 acdd09a0ae8354d7708e54c63334f2a33a1b6da447ef171e083232e1eeb1442c
T41 8a542ed3d887edad6876fe3e7521d07f1a72fbfe05fc44bd3eeed9563ef34c67
T42 665a2c00ed54ab183f55b0b0d808b9f0359927e1a1241e11f774e0d2d6587754
```

They are not machine-checked inputs.

## 3. Every finite domain, record, weight, and shell

In Sections 3--8, `m,N` are natural numbers with `1<=m` and `1<=N`.

### 3.1 Outer parameters and supercritical filter

T34's exact outer domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.               (3.1)
```

Set

```text
k = v+rho,
d(v,k) = 10^v(10^(k-v)-1) = 10^k-10^v.                    (3.2)
```

The map `(v,rho) -> (v,k)` is a bijection from (3.1) to

```text
0 <= v < k < N,                                            (3.3)
```

with inverse `rho=k-v`. The separate condition `rho<N` follows from
`0<rho<=k<N`. The literal T36 filter is

```text
P_(Qstar,m)(v,k):
  Qstar <= 10^k-10^v  and  5m < 31k.                       (3.4)
```

### 3.2 Arithmetic survival and block records

For natural `n,r`, put

```text
q(n,r) = 10^n(10^r-1).                                    (3.5)
```

At T36's exact parameters `(mu,c)=(8,1)`, the excluded predicate is

```text
ArithmeticExcluded(8,1,Q0,m,n,r) iff
  Q0 <= q(n,r) and
  10^(-m) <= q(n,r) [1/q(n,r)^8],                          (3.6)
```

where (3.6) is a real inequality after the onset comparison. Define the
literal survival indicator

```text
sigma_(Q0,m)(n,r)
  = 1 if not ArithmeticExcluded(8,1,Q0,m,n,r),
    0 otherwise.                                           (3.7)
```

For orientation `eps`, start `n`, and endpoint `E`, T34 uses

```text
record(eps,n,E) = (eps,(E-n,n)),                            (3.8)
```

with natural subtraction. If `E<n`, its lag is zero and the record is
rejected; no malformed endpoint is repaired. For a half-open dyadic block
`B=[a,b)`, this record belongs to the exact T32 block domain precisely when

```text
0 < E-n,
m <= E-n,
sigma_(Q0,m)(n,E-n)=1,
a <= E < b.                                                (3.9)
```

Both Bool orientations have the same membership conditions.

### 3.3 Canonical blocks and widths

The exact canonical list is

```text
B_N = translatedCanonicalBlocks N
    = dyadicPartitionFrom 0 ((N-1).bitIndices.reverse).     (3.10)
```

It is the consecutive binary partition of the integer endpoints `[1,N)`.
Every block `B=(a,j)` represents

```text
B=[a,a+2^j),
w(B)=sqrt((a+2^j)^2-a^2).                                  (3.11)
```

Thus every integer `k` with `1<=k<N` lies in one unique canonical block.
Write

```text
B_N(k)=[a_N(k),b_N(k)),
W_N(k)=sqrt(b_N(k)^2-a_N(k)^2)>0.                           (3.12)
```

The endpoints satisfy

```text
1 <= a_N(k) <= k < b_N(k) <= N.                            (3.13)
```

No estimate below changes the literal denominator `W_N(k)`.

### 3.4 The four literal rows

For every hidden exponent `z` in `Finset.range N`, equivalently `0<=z<N`,
the four rows are

```text
row 2, positiveSameStart:
  (record(true,z,v),  record(true,z,k));

row 4, negativeSameStart:
  (record(false,z,k), record(false,z,v));

row 5, mixedFirstEndpoint:
  (record(false,z,k), record(true,v,z));

row 6, mixedSecondEndpoint:
  (record(false,v,z), record(true,z,k)).                    (3.14)
```

For each row, T34's domain is the singleton containing the displayed pair,
filtered by `0<rho` and membership of both records in (3.9). Its cardinality
is exactly zero or one. The factor two that appears later counts rows 2 and 4,
or rows 5 and 6. It is not T34's separate reversal factor, which is absent
from T36's `supercriticalIncidence`.

### 3.5 Endpoint-pinned shells

For real `x`, define

```text
delta(x) = |x-round(x)|,
K_m = clog_2(10^m)-1.                                      (3.15)
```

For positive `m`, T34 gives

```text
1 <= K_m,  2^K_m < 10^m <= 2^(K_m+1).                     (3.16)
```

The exact shells are

```text
S_0(m,x): 0 <= delta(x) <= 10^(-m),

S_j(m,x): 2^(j-1)/10^m < delta(x)
              <= min(2^j/10^m,1/2),  1<=j<=K_m.           (3.17)
```

They partition every real argument. Define the literal shell weight

```text
theta_m(d)
  = 1_(S_0(m,d*pi))
      + sum_(j=1)^K_m 2^(-j) 1_(S_j(m,d*pi)).              (3.18)
```

Exactly one indicator in (3.18) is active. Hence
`0<theta_m(d)<=1`; shell-boundary values retain (3.17)'s conventions.

## 4. Exact four-row contribution

Define `A_4(Q0,Qstar;m,N)` by taking T36's direct formula for
`supercriticalIncidence` and restricting its row sum to the four rows in
(3.14). Before regrouping, it is exactly

```text
A_4
 = sum_(B in B_N)
     sum_((v,rho) in D_N; P_(Qstar,m)(v,v+rho))
       theta_m(10^(v+rho)-10^v) / w(B)
       * sum_(0<=z<N) sum_(row in {2,4,5,6})
           card(cancellingRowDomain(8,1,Q0,m,B,
                                      row,v,rho,z)).        (4.1)
```

Every sum is finite, so the changes of order below require no convergence
argument.

For `0<=v<k<N`, with `B_N(k)=[a,b)`, define

```text
H_ss(Q0,m;v,k)
 = #{z: 0<=z, z+m<=v,
        sigma_(Q0,m)(z,v-z)=1,
        sigma_(Q0,m)(z,k-z)=1},                            (4.2)

H_mix(Q0,m,N;v,k)
 = #{z: a<=z<b, v+m<=z, z+m<=k,
        sigma_(Q0,m)(v,z-v)=1,
        sigma_(Q0,m)(z,k-z)=1}.                            (4.3)
```

The omitted condition `z<N` is automatic in (4.2), because
`z<=v-m<v<N`, and in (4.3), because `z<b<=N`.

Rows 2 and 4 have the same two unoriented records. They contribute only when
both endpoints `v,k` lie in `B_N(k)`, which is exactly `a<=v<b`. Rows 5 and 6
have endpoints `z,k`, so they contribute exactly when `z` lies in that block.
Orientation invariance in (3.9) makes the members of each pair equal. Thus
(4.1) becomes the exact identity

```text
A_4(Q0,Qstar;m,N)
 = 2 * sum_(0<=v<k<N; P_(Qstar,m)(v,k))
       theta_m(10^k-10^v) / W_N(k)
       * [1_(a_N(k)<=v<b_N(k)) H_ss(Q0,m;v,k)
          + H_mix(Q0,m,N;v,k)].                            (4.4)
```

This identity retains all arithmetic-survival conditions.

## 5. Geometric envelope, with no shell maximum

For an integer `x`, write `[x]_+=max(x,0)`. Before survival is imposed, the
`z` interval in (4.2) has size `[v-m+1]_+`. The interval in (4.3) is

```text
[max(a_N(k),v+m), min(b_N(k),k-m+1)),                      (5.1)
```

and has size equal to its positive-part length. Define

```text
Lambda_(m,N)(v,k)
 = 1_(a_N(k)<=v<b_N(k)) [v-m+1]_+
   + [min(b_N(k),k-m+1)-max(a_N(k),v+m)]_+.                (5.2)
```

Then `H_ss<= [v-m+1]_+` and `H_mix` is at most the second term of (5.2).
Consequently

```text
A_4(Q0,Qstar;m,N) <= E_4(Qstar;m,N),                       (5.3)

E_4(Qstar;m,N)
 = 2 * sum_(0<=v<k<N;
            Qstar<=10^k-10^v;
            5m<31k)
       [Lambda_(m,N)(v,k)/W_N(k)]
       theta_m(10^k-10^v).                                 (5.4)
```

Only (5.3), not (4.4), discards arithmetic survival. No `v`-dependent shell
weight has been replaced by a maximum.

## 6. Sharp geometric mass, rederived

Fix `1<=k<N` and abbreviate `a=a_N(k)`, `b=b_N(k)`, `L=b-a`, and `d=k-a`.
Then `L>0` and `0<=d<L`. Define the onset-filtered set and coefficients

```text
V_(Qstar)(k) = {v: 0<=v<k, Qstar<=10^k-10^v},              (6.1)

g_v = Lambda_(m,N)(v,k)/W_N(k),

G_(Qstar,m,N)(k) = sum_(v in V_(Qstar)(k)) g_v.            (6.2)
```

All `g_v` are nonnegative. Increasing `m` only shortens the two intervals in
(5.2), so `Lambda_(m,N)(v,k)<=Lambda_(1,N)(v,k)`. At `m=1`, direct evaluation
gives

```text
Lambda_(1,N)(v,k)
 = d,    if 0<=v<a,
 = k-1,  if a<=v<k.                                       (6.3)
```

There are `a` values in the first range and `d` in the second. Hence

```text
sum_(v=0)^(k-1) Lambda_(1,N)(v,k)
 = ad+d(k-1)
 = d(2a+d-1).                                              (6.4)
```

The literal width satisfies

```text
W_N(k)^2 = L(2a+L).                                        (6.5)
```

For real `x>=0`, the function

```text
f(x)=x(2a+x)/(a+x)=a+x-a^2/(a+x)                           (6.6)
```

is increasing. Since `d<L`, `a+d=k`, `a+L=b`, and `W_N(k)<=b`,

```text
d(2a+d)/k <= L(2a+L)/b = W_N(k)^2/b <= W_N(k).             (6.7)
```

If `d=0`, (6.4) is zero. If `d>0`, then
`d(2a+d-1)<d(2a+d)`. Combining (6.2)--(6.7), including the possible onset
restriction, proves the strict geometric-mass bound

```text
0 <= G_(Qstar,m,N)(k) < k.                                 (6.8)
```

This is a complete proof-sketch derivation from the canonical block geometry,
not an invocation of the T42 note.

The same calculation gives an explicit contraction factor. Define

```text
gamma_(N)(k)
 = 0,                                      if d=0,
 = d(2a+d-1)/[k W_N(k)],                   if d>0.           (6.9)
```

The numerator in (6.9) is the complete unfiltered `m=1` geometric mass from
(6.4), before division by the width. Equations (6.2)--(6.7) therefore give

```text
0 <= G_(Qstar,m,N)(k)/k <= gamma_(N)(k) < 1.               (6.10)
```

Unlike a bare strict inequality, (6.9) records exactly how much canonical
block geometry is lost before any orbit-shell estimate is attempted. The
factor can approach one, so no uniform gap from one is claimed.

## 7. Strict refinement of the maximum step

Call `k` active when

```text
1<=k<N,  5m<31k,  and  G_(Qstar,m,N)(k)>0.                 (7.1)
```

For active `k`, define a probability weight and its weighted shell average by

```text
p_v = g_v/G_(Qstar,m,N)(k),  v in V_(Qstar)(k),

Avg_(Qstar,m,N)(k)
 = sum_(v in V_(Qstar)(k)) p_v theta_m(10^k-10^v).         (7.2)
```

The `p_v` are nonnegative and sum to one. If `k` is not active, its
contribution to (5.4) is zero. Therefore (5.4) has the exact non-maximal
factorization

```text
E_4(Qstar;m,N)
 = 2 * sum_(k active)
       G_(Qstar,m,N)(k) Avg_(Qstar,m,N)(k).                 (7.3)
```

For comparison only, let

```text
M_(m,Qstar)(k)
 = max_(v in V_(Qstar)(k)) theta_m(10^k-10^v),
   with value 0 when V_(Qstar)(k) is empty.                 (7.4)
```

The maximum is not used after this paragraph. Every active set contains a
positive `g_v`, and every shell weight is positive, so `M>0`. Equations
(6.8) and (7.2) give the strict, termwise comparison

```text
[G_(Qstar,m,N)(k) Avg_(Qstar,m,N)(k)]/[k M_(m,Qstar)(k)]
 = [G_(Qstar,m,N)(k)/k]
     [Avg_(Qstar,m,N)(k)/M_(m,Qstar)(k)]
 <= gamma_(N)(k)
      [Avg_(Qstar,m,N)(k)/M_(m,Qstar)(k)]
 < 1.                                                       (7.5)
```

Thus each active summand in (7.3) is strictly smaller than T42's corresponding
`2kM(k)` summand. A nonactive `k` contributes zero to (7.3), while its T42
term can remain positive when `V_(Qstar)(k)` is nonempty but all geometric
coefficients vanish. Consequently the whole sum (7.3) is no larger than
T42's domination and is strict whenever the latter has at least one nonzero
term; if every relevant onset set is empty, both sums are zero. The saving is
quantified by the explicit product in (7.5). In particular, T42 enlarged the
onset-filtered geometric sum to all `0<=v<k` before taking a maximum, whereas
(7.2)--(7.5) retain both the onset-filtered mass and its complete weighted
`v`-average.

## 8. The centered orbit-correlation attack

Fix an active `k` and put

```text
n_k = card(V_(Qstar)(k)),
t_v = theta_m(10^k-10^v),

mu_k = (1/n_k) sum_(v in V_(Qstar)(k)) t_v,

Var_k = (1/n_k) sum_(v in V_(Qstar)(k)) (t_v-mu_k)^2,

Xi_k = n_k sum_(v in V_(Qstar)(k)) (p_v-1/n_k)^2.          (8.1)
```

Because activity implies `n_k>=1`, every denominator in (8.1) is positive.
Here `mu_k` is the unweighted fixed-`k` orbit-shell average, `Var_k` measures
its shell clustering, and `Xi_k` is the exact chi-square concentration of the
canonical geometric weights relative to the uniform measure on the onset
set. In particular,

```text
Xi_k = n_k [sum_v g_v^2/G_(Qstar,m,N)(k)^2] - 1,
0 <= Xi_k <= n_k-1.                                        (8.2)
```

The upper bound follows from `sum_v p_v^2<=sum_v p_v=1`; the lower bound is
Cauchy--Schwarz applied to `sum_v p_v=1`.

Since `sum_v(p_v-1/n_k)=0`, there is an exact centered decomposition

```text
Avg_(Qstar,m,N)(k)
 = mu_k + sum_(v in V_(Qstar)(k))
     (p_v-1/n_k)(t_v-mu_k).                                (8.3)
```

Finite Cauchy--Schwarz and (8.1) give

```text
|sum_v (p_v-1/n_k)(t_v-mu_k)|
 <= sqrt[sum_v(p_v-1/n_k)^2] sqrt[sum_v(t_v-mu_k)^2]
 = sqrt(Xi_k Var_k).                                       (8.4)
```

Combining (5.3), (7.3), and (8.4) yields the fully explicit non-maximal bound

```text
A_4(Q0,Qstar;m,N)
 <= 2 * sum_(k active)
      G_(Qstar,m,N)(k) [mu_k+sqrt(Xi_k Var_k)].             (8.5)
```

This attacks exactly the correlation lost by a maximum: `mu_k` is the
ordinary orbit average, while `sqrt(Xi_k Var_k)` is the finite centered cost
of aligning large shell values with large canonical geometric weights.

## 9. Claim boundary and terminal narrower inequality

The strict saving (7.5) is unconditional within the proof-sketch finite
reconstruction. It does not establish the required scale bound. Inequality
(8.5) shows that one sufficient remaining statement is a joint estimate for
the orbit mean and its centered correlation. This is narrower than the raw
double sum (5.4): the block, row, hidden-`z`, and shell-index sums are gone,
and the `v` dependence survives only through the four inspectable statistics
`G_k`, `mu_k`, `Var_k`, and `Xi_k`. It is not a renamed `(OSC_4)`: (8.4)
replaces the exact weighted average by a mean plus an unsigned covariance
majorant. It is therefore a sufficient strengthening, not an equivalence.

The following statement is a `conjecture`, not a conclusion of T36 or of this
note. It is the sole terminal fixed-`pi` input. The constant precedes both
positive scale variables, and the target is literal:

```text
(AOC_4)

For every fixed natural Qstar and every real s with 0<s<1, there exists a
real C_(s,Qstar)>=0 such that, for every natural m,N with 1<=m and 1<=N,

  2 * sum_(1<=k<N;
           5m<31k;
           G_(Qstar,m,N)(k)>0)
        G_(Qstar,m,N)(k)
        [mu_k + sqrt(Xi_k Var_k)]

  <= C_(s,Qstar) [N + N^2 10^(-s m)].                      (AOC_4)
```
