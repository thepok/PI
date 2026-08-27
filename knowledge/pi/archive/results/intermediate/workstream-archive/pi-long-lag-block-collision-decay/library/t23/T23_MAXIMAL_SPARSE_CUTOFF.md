# T23: endpoint maximality for the sparse decimal cutoff

Status: `proof sketch` (the reduction below is proved in prose from the
machine-checked T22 interface; the terminal fixed-point block estimate is
explicitly unresolved).

## 1. Provenance and scope

- Canonical source: `knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`.
- External source URL: none is recorded; this is a locally formulated
  canonical question.
- Canonical source SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
- Imported kernel input:
  `TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff`, source
  SHA-256
  `73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713`.
- Imported scale notation: T12 source SHA-256
  `a4108ff862c13ee0f9fa3fc877723856eb34497430cde36d85f7943ce0347bcf`.
- Phase definition source:
  `TheoryLib/PiDigits/T27FiniteExponentialCylinderCoverage.lean`, SHA-256
  `fd9c730e411dd7fb12b5b1a103c683238595c68bbea0f06af0250b4d13a8ee4e`.

This note takes the following T22 theorems as established kernel input and
does not reprove them:

1. `mem_orderedLongPairDomain_iff_admissible_endpoint`;
2. `both_orientations_exact`;
3. `mem_sparseFrequencyCutoff_iff`;
4. `sparseFrequencyCutoff_mono`;
5. `mem_cutoff_succ_not_cutoff_iff_endpoint`;
6. `sparseFrequencyCutoff_one_eq_empty`;
7. `coefficientMultiplicity_eq_one_of_mem_cutoff`;
8. `spectralSum_eq_cutoffFourierSum_pi`;
9. `cutoffScaleMatchedL1Bound_iff_T12`.

Items 8 and 9 are cited only to identify the frontier at the end. Their
equivalence proofs are not repeated. No estimate in this note is asserted at
`alpha = pi`, and no conclusion about C1 is asserted.

## 2. Normalized canonical statement and ambiguities

The canonical question asks whether, for each real `s` with `0 < s < 1`, one
constant `C_s >= 1` works simultaneously for every pair of integers
`m,N >= 1` in

```text
R_pi(m,N) <= C_s (N + N^2 10^(-s m)).
```

Here `R_pi` counts ordered pairs `(i,j)` in `{0,...,N-1}^2`, uses the inclusive
long-lag condition `|i-j| >= m`, and excludes the diagonal and overlapping
length-`m` blocks. The additive `N` term and the order
`forall s, exists C_s, forall m,N` are part of the statement.

The only ambiguity relevant to T23 is the distinction between:

1. a bound for one selected cutoff `N`;
2. a maximal bound simultaneous in all `1 <= n <= N`;
3. a bound with a constant allowed to depend on `m` or `N`.

Only constants independent of `m,N` are useful. T23 analyzes (2) as a route to
(1). It does not replace the fixed point `pi` by an almost-everywhere phase,
does not change the ordered-pair convention, and does not remove the additive
term.

## 3. Imported cutoff notation

Fix throughout this section

```text
mu,c,alpha in R,   Q0,m in N,   m >= 1,
H := 10^m.
```

No sign, irrationality, or size hypothesis on `mu,c,alpha` is used. Write

```text
Lambda_N := sparseFrequencyCutoff mu c Q0 m N subset Z
```

and, for every integer `h` with `1 <= h <= H`, write

```text
P_N(h;alpha) := cutoffFourierSum mu c Q0 m N h alpha.
```

Thus `P_N(alpha)=(P_N(h;alpha))_(1<=h<=H)` is a vector in `C^H`. The inclusive
frequency range has exactly `H`, not `H+1`, coordinates.

For `z=(z_h)_(1<=h<=H)` define

```text
||z||_1     := sum_(h=1)^H |z_h|,
||z||_2     := (sum_(h=1)^H |z_h|^2)^(1/2),
||z||_infty := max_(1<=h<=H) |z_h|.
```

All scalar absolute values below are the complex norm. Let

```text
phi_h(x) := exp(2*pi*i*h*x).
```

The definition of `phase` in
`TheoryLib/PiDigits/T27FiniteExponentialCylinderCoverage.lean` is exactly
`phi_h`; hence `|phi_h(x)|=1` for real `x`. This elementary unit-modulus fact
is the only analytic input in the deterministic bounds below.

## 4. Exact endpoint layers

For an integer endpoint `E >= 1`, define the surviving lag set

```text
A_E := {r in N : m <= r <= E and
                   not ArithmeticExcluded mu c Q0 m (E-r) r},
a_E := #A_E.
```

If `E < m`, this set is empty. If `E >= m`, it is a subset of the
`E-m+1` integers `m,m+1,...,E`, so

```text
0 <= a_E <= E-m+1.                                      (4.1)
```

For `r in A_E`, put

```text
n := E-r,
k_(E,r) := 10^E - 10^(E-r) = 10^(n+r)-10^n > 0.
```

The endpoint layer is

```text
L_E := Lambda_(E+1) \ Lambda_E.
```

T22's exact successor-layer theorem, its injectivity result, and its
both-orientations theorem give the disjoint description

```text
L_E = { k_(E,r), -k_(E,r) : r in A_E },
#L_E = 2 a_E.                                           (4.2)
```

There is no hidden endpoint: `n=E-r` ranges from `0` to `E-m`; the lag ranges
inclusively from `m` to `E`; and the cutoff changes from endpoint `< E` to
endpoint `< E+1`. Positive and negative orientations are distinct because
`k_(E,r)>0`.

Define the endpoint increment vector by

```text
Delta_E(alpha) := P_(E+1)(alpha)-P_E(alpha).
```

The cutoffs are nested, all coefficients on a cutoff have multiplicity one,
and (4.2) is the exact set difference. Subtracting the two finite sums
therefore gives, coordinate by coordinate,

```text
Delta_E(h;alpha)
  = sum_(r in A_E)
      [phi_h(k_(E,r)*alpha) + phi_h(-k_(E,r)*alpha)].    (4.3)
```

Equation (4.3) is a consequence of the imported T22 layer interface, not a
new encoding of the T8 domain.

T22 also gives `Lambda_1=empty` when `m>=1`. Consequently

```text
P_1(alpha)=0,
P_N(alpha)=sum_(E=1)^(N-1) Delta_E(alpha)               (4.4)
```

for every `N>=1`, where the sum is empty at `N=1`.

## 5. Constant-tracked layer and variation bounds

By (4.3), the triangle inequality, and `|phi_h|=1`,

```text
|Delta_E(h;alpha)| <= 2 a_E.                            (5.1)
```

There are exactly `H` coordinates, so (without suppressed constants)

```text
||Delta_E(alpha)||_infty <= 2 a_E,
||Delta_E(alpha)||_2     <= 2 sqrt(H) a_E,
||Delta_E(alpha)||_1     <= 2 H a_E.                    (5.2)
```

For an integer `t>=1`, set

```text
x_t := max(t-m,0).
```

For every `1 <= a <= b`, summing (4.1) exactly over `E=a,...,b-1` gives

```text
sum_(E=a)^(b-1) 2 a_E
  <= x_b(x_b+1)-x_a(x_a+1).                            (5.3)
```

Indeed, the nonzero summands are `2,4,...,2x_b`, with the first `x_a`
terms removed. Combining (4.4), (5.2), and (5.3) yields

```text
||P_b-P_a||_infty
  <= x_b(x_b+1)-x_a(x_a+1),

||P_b-P_a||_2
  <= sqrt(H)[x_b(x_b+1)-x_a(x_a+1)],

||P_b-P_a||_1
  <= H[x_b(x_b+1)-x_a(x_a+1)].                         (5.4)
```

For a block of `L>=1` successive endpoint layers starting at `a>=1`, (5.4)
and `2a_E<=2E` also give the convenient rough bound

```text
||sum_(E=a)^(a+L-1) Delta_E(alpha)||_1
  <= H L(2a+L-1).                                      (5.5)
```

At a full cutoff, (5.4) gives

```text
||P_N(alpha)||_1 <= H x_N(x_N+1) <= H N(N-1) < H N^2   (5.6)
```

for `N>=2`; it is zero for `N=1`.

## 6. Exact binary decomposition

Let `N>=2`, put `L=N-1`, and let

```text
L = sum_(j=0)^J epsilon_j 2^j,
epsilon_j in {0,1},
J=floor(log_2 L),
epsilon_J=1.
```

List the nonzero binary positions in strictly decreasing order

```text
j_1 > j_2 > ... > j_t >= 0.
```

Then `1 <= t <= J+1`. Define

```text
b_0 := 1,
b_i := 1 + sum_(u=1)^i 2^(j_u)       (1<=i<=t),
I_i := {b_(i-1),...,b_i-1}.
```

These are half-open integer intervals `[b_(i-1),b_i)` of lengths `2^(j_i)`.
They are pairwise disjoint, consecutive, and satisfy

```text
b_t=N,
{1,...,N-1} = disjoint union_(i=1)^t I_i.               (6.1)
```

They are also grid-aligned relative to the left endpoint `1`: because all
previous selected powers are larger than `2^(j_i)`, the integer
`b_(i-1)-1` is divisible by `2^(j_i)`. Thus these are genuine dyadic blocks
on the endpoint grid translated by one.

For `a>=1` and `j>=0`, define the binary block vector

```text
D_(a,j)(alpha) := sum_(E=a)^(a+2^j-1) Delta_E(alpha)
                 = P_(a+2^j)(alpha)-P_a(alpha).          (6.2)
```

Equations (4.4), (6.1), and (6.2) imply the exact vector identity

```text
P_N(alpha)=sum_(i=1)^t D_(b_(i-1),j_i)(alpha).           (6.3)
```

Thus the triangle and Cauchy-Schwarz inequalities give, with constant one,

```text
||P_N(alpha)||_1
 <= sum_(i=1)^t ||D_(b_(i-1),j_i)(alpha)||_1            (6.4)

 <= sum_(j=0)^J sup_{1<=a, a+2^j<=N} ||D_(a,j)(alpha)||_1

 <= sqrt(J+1)
    [sum_(j=0)^J
      (sup_{1<=a, a+2^j<=N} ||D_(a,j)(alpha)||_1)^2]^(1/2).  (6.5)
```

No endpoint occurs twice in these formulas. The supersets used in (6.4)-(6.5)
may include blocks not selected by the binary digits, but all terms are
nonnegative, which is the only reason those enlargements are valid.

## 7. Comparison with the scale-matched target

Fix `s` with `0<s<1` and abbreviate

```text
rho := 10^(-s m),
F(N) := N + N^2 rho.
```

The required spectral scale is exactly `H F(N)`.

### 7.1 Total variation loses the additive regime

The deterministic variation majorant (5.6) cannot be compared with `H F(N)`
using a constant independent of `m,N`. To see the failure with exact
quantifiers, choose `N=2m` and let `m` tend to infinity. The ratio of the
sharper numerator in (5.6) to the target is

```text
x_N(x_N+1)/F(N)
  = m(m+1)/(2m+4m^2 10^(-s m))
  = (m+1)/(2+4m 10^(-s m)),                             (7.1)
```

which tends to infinity. Here `N rho=2m 10^(-s m)` tends to zero, so this is
precisely the additive-`N` regime. Statement (7.1) says that the proved
triangle-variation upper bound does not close the target; it is not a lower
bound for the actual Fourier sum.

### 7.2 A global logarithmic loss also fails

If binary decomposition is used only after bounding every selected block by
one copy of `K H F(N)`, (6.4) yields `(J+1)K H F(N)`. No constant independent
of `N` absorbs `J+1`. The square-function form (6.5) similarly leaves a
factor `sqrt(J+1)` unless its right side has matching inverse-logarithmic
control.

Exponent slack does not repair a logarithm multiplying the additive term.
For example, for any `s'>s`, along `N=2m` one has

```text
N+N^2 10^(-s' m) = (1+o(1))N,
N+N^2 10^(-s m) = (1+o(1))N.
```

Therefore multiplying the first expression by either `J+1` or
`sqrt(J+1)` still gives an unbounded ratio to the second. Any successful
binary argument must allocate the additive budget across blocks rather than
pay it once per block.

### 7.3 The telescoping local budget

For `a,L>=1`, define

```text
G_(s,m)(a,L)
  := L + [(a+L)^2-a^2] rho
   = L + (2aL+L^2) rho.                                 (7.2)
```

If `[a_i,a_i+L_i)` are consecutive and partition `[1,N)`, then both parts of
this budget telescope:

```text
sum_i L_i = N-1,
sum_i [(a_i+L_i)^2-a_i^2] = N^2-1,

sum_i G_(s,m)(a_i,L_i)
  = (N-1)+(N^2-1)rho
  <= N+N^2 rho = F(N).                                  (7.3)
```

Thus (7.2), unlike a global block budget, pays neither a logarithmic nor a
square-root logarithmic maximality loss. It also assigns exactly one unit of
additive budget per endpoint layer.

## 8. Proved reduction to localized binary blocks

**Proposition (deterministic binary-block reduction).** Fix real
`mu,c,alpha`, a natural `Q0`, and `s` with `0<s<1`. Suppose there is a real
`B_s>=0`, independent of `m,a,j`, such that for every `m>=1`, every `a>=1`,
and every `j>=0` satisfying `2^j | (a-1)`, with `H=10^m` and
`rho=10^(-s m)`, one has

```text
||D_(a,j)(alpha)||_1
 <= B_s H {2^j + [(a+2^j)^2-a^2] rho}.                  (LDB)
```

Then for every `m,N>=1`,

```text
sum_(h=1)^(10^m) |P_N(h;alpha)|
 <= B_s 10^m [N+N^2 10^(-s m)].                         (8.1)
```

**Proof.** If `N=1`, T22 gives `P_1=0`, so (8.1) holds. If `N>=2`, use the
binary partition (6.1). Apply (LDB) to each block in (6.4), then use (7.3):

```text
||P_N(alpha)||_1
 <= sum_(i=1)^t ||D_(b_(i-1),j_i)(alpha)||_1
 <= B_s H sum_(i=1)^t G_(s,m)(b_(i-1),2^(j_i))
 =  B_s H [(N-1)+(N^2-1)rho]
 <= B_s H [N+N^2 rho].
```

Every constant is displayed; in particular, the reduction multiplies `B_s`
by exactly `1`. This proves the proposition. `square`

Because (8.1) holds separately for every `n`, the same hypothesis also gives
the two maximal statements

```text
max_(1<=n<=N) ||P_n(alpha)||_1
  <= B_s 10^m [N+N^2 10^(-s m)],

max_(1<=n<=N)
  {||P_n(alpha)||_1 /
   (10^m [n+n^2 10^(-s m)])}
  <= B_s.                                                (8.3)
```

The denominators in the second line are positive since `m,n>=1`. The first
line uses that `n+n^2 10^(-s m)` is increasing in `n`; neither line incurs a
maximality constant.

The proposition holds for every real `alpha`; its hypothesized `B_s` may
depend on the fixed `mu,c,Q0,alpha,s`, but not on `m,a,j,N`. T22's
machine-checked identity
shows that specializing its conclusion to `alpha=pi` would be the cutoff form
of the T12 frontier. This note does not assert the premise (LDB) at `pi`, does
not assert any spectral estimate for `pi`, and does not assert C1.

The deterministic estimate (5.5) is far too large to prove (LDB). Already at
`j=0`, (LDB) asks for

```text
||Delta_a(alpha)||_1
 <= B_s 10^m [1+(2a+1)10^(-s m)],                       (8.2)
```

whereas direct variation gives at best `2*10^m*a_a`, which may be as large as
`2*10^m(a-m+1)`. Hence the remaining input is localized cancellation, not a
further manipulation of cutoffs. For each fixed `mu,c in R` and `Q0 in N`,
the exact terminal unresolved inequality is

```text
forall s in (0,1), exists B_s>=0, forall m>=1, a>=1, j>=0
  with 2^j | (a-1):
sum_(h=1)^(10^m)
  |sum_(E=a)^(a+2^j-1) sum_(r in A_E)
    [phi_h((10^E-10^(E-r))*pi)
     + phi_h(-(10^E-10^(E-r))*pi)]|
<= B_s 10^m
   {2^j + [(a+2^j)^2-a^2]10^(-s m)}.                   (T23-terminal)
```
