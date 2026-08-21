# T82: Metric scale of the signed structured-denominator residual

Status: `proof sketch` (rigorous prose plus exact finite symbolic replay; not a
Lean formalization).

## 1. Scope and source

This is a **metric sibling benchmark**.  The seed below is a variable
`x in R/Z` distributed according to normalized Lebesgue measure.  The result
says that almost every seed has a property; it says nothing about the one
prescribed seed `x = pi mod 1`.  In particular, this note proves no estimate
for `pi` and no instance of C7, C2, or C1.

The immutable canonical problem statement is vendored as
`pi-positive-decimal-factor-entropy.txt`, with SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The canonical question is fixed-`pi` positive decimal factor entropy.  Its
recorded ambiguities explicitly distinguish almost-everywhere sibling results
from the canonical problem.  T82 does not change that statement.

## 2. Exact imported interfaces

The following are kernel-checked library interfaces.  T82 reuses them rather
than replacing their conventions.

| Item | Module and declaration | Exact role | Source SHA-256 |
|---|---|---|---|
| T56 | `DecimalFactorComplexity.T56LagSectorAudit.t56SampleLength` | `L_n = 10^(n/2)`, with natural-number division | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` |
| T56 | `mem_sparse_short_sector_iff` | `0 < r`, `r < n`, and `r < L_n` | same |
| T56 | `sparse_repunit_eq_structuredDenominator_cast` | `q_(j,r) = 10^j(10^r-1)` | same |
| T58 | `bandwidth` and `mem_positiveFejerFrequencies_iff` | `H_n = 10^n/2` and `1 <= h < H_n` | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` |
| T58 | `shortRectangle` and `mem_shortRectangle_iff` | `0 < r < n`, `j < L_n-r` | same |
| T58 | `phi` and `phi_collision_after_ten_reduction` | exact positive frequency and collision reduction | same |
| T58 | `collisionSecondMoment_eq_diagonal_add_offDiagonal` | exact ordered diagonal/off-diagonal split | same |
| T61 | `residualStartDomain` and `mem_residualShortRectangle_iff` | the arithmetic residual mask | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` |
| T61 | `vaalerCoefficient_explicit` | the signed Vaaler coefficient | same |
| T61 | `signedStructuredDenominatorSum` | the complete fixed-seed positive-frequency sum | same |
| T61 | `residualStructuredCard` and `completeStructuredVaalerExpression` | label count and zero mode | same |
| T61 | `structuredVaalerMajorantTotal_eq_completeExpression` | exact finite majorant expansion | same |
| T61 | `decimalCutoff_eq_centralRadius` | `10^(-n) = (2H_n)^(-1)` for `n >= 1` | same |
| T61 | the four endpoint theorems | strict indicator is `0`, majorant is `1`, at both endpoints | same |

The source locations are T56 lines 31-53 and 68-72; T58 lines 26-101 and
103-163; and T61 lines 615-663, 1682-1737, 1741-1778, 1837-1870, and
1894-2094 in the pinned files.  The T61 formula contains two occurrences of `Real.pi`: the outer
`2*pi` is the Fourier angular constant and is retained, while only the final
fixed seed in `q_(j,r)*pi` is replaced by `x`.

## 3. Normalized finite statement

Fix real parameters `mu,c`, a natural number `Q0`, and an integer `n >= 1`.
Put

```text
L = L_n = 10^(n/2),       H = H_n = 10^n/2,
R_r = 10^r-1,             q_(j,r) = 10^j R_r.
```

All divisions in the exponents and in `H` are natural-number divisions.  Since
`10^n` is even for `n >= 1`, `2H=10^n` exactly.

Let `D_n = D_n(mu,c,Q0)` be T61's masked residual label set:

```text
D_n = {(r,j): 0 < r < n, r < L, 0 <= j < L-r,
                not ArithmeticExcluded(mu,c,Q0,n,j,r)}.
```

The mask is independent of the metric seed `x`.  Write `N_n = |D_n|`.  Define

```text
a_(H,h) = H^(-1) [sin(pi h/H)/pi
                    + 2(1-h/H) cos(pi h/H)]       (1 <= h < H),
Phi(h,j,r) = h 10^j(10^r-1),
S_n(x) = 2 sum_(1<=h<H) a_(H,h)
             sum_((r,j) in D_n) cos(2 pi Phi(h,j,r) x),
Z_n = 2N_n/H,
E_n(x) = Z_n + S_n(x).
```

Thus `E_n` is exactly T61's complete structured Vaaler expression with the
terminal fixed seed `pi` replaced by `x`.  It retains every `n,L,H,h,j,r`, the
residual mask, the signed coefficient, the strict frequency cutoff, the
factor two joining positive and negative frequencies, and the zero-mode
normalization.

The metric quantifiers are

```text
for Lebesgue-almost every x in R/Z, there exists N_x such that
for every n >= N_x, the asserted bound holds for that same fixed x.
```

There is no assertion for every `x`, and no specialization to `x=pi mod 1`.

## 4. Complete finite L2 identity

Let

```text
I_n = {(h,r,j): 1 <= h < H and (r,j) in D_n}.
```

All frequencies `Phi(i)` are positive integers.  For every positive integer
`m`, define the complete frequency fiber and its signed weight by

```text
F_m = {i in I_n : Phi(i)=m},
A_m = sum_(i in F_m) a_(H,h(i)).
```

Only finitely many fibers are nonempty.  The elementary orthogonality formulas
on `[0,1)` are

```text
integral cos(2 pi k x) dx = 0                         (k >= 1),
integral cos(2 pi k x) cos(2 pi l x) dx
  = 1/2 if k=l, and 0 otherwise                      (k,l >= 1).
```

Expanding every finite sum before integrating gives the exact identity

```text
integral S_n(x)^2 dx
  = 2 sum_(i,i' in I_n; Phi(i)=Phi(i'))
        a_(H,h(i)) a_(H,h(i'))                       (4.1)
  = 2 sum_(m>=1) A_m^2.                              (4.2)
```

The factor is `2`: the two outer factors in `S_n` contribute `4`, and cosine
orthogonality contributes `1/2`.  Formula (4.1) uses ordered pairs.  Therefore
an unordered off-diagonal collision appears twice in (4.1), for a net factor
`4`.  This is precisely the cross-term convention that would be lost by
keeping only the diagonal.

T58's finite split becomes

```text
integral S_n^2
  = 2 N_n sum_(1<=h<H) a_(H,h)^2
    + 2 sum_(i != i'; Phi(i)=Phi(i'))
          a_(H,h(i))a_(H,h(i')),                    (4.3)
```

where the second sum is ordered.  Fixed-`h` injectivity from T58 shows that the
first term is exactly the full-index diagonal, but does not remove collisions
with different `h`.

The zero mode has no cross term with `S_n`, so the other exact identities are

```text
integral E_n(x) dx = Z_n,
integral (E_n(x)-Z_n)^2 dx = 2 sum_m A_m^2,
integral E_n(x)^2 dx = 4N_n^2/H^2 + 2 sum_m A_m^2.   (4.4)
```

These are finite identities, not asymptotic approximations.

## 5. Complete collision classification

For a positive integer `h`, let `v(h)` be the largest `v` such that `10^v`
divides `h`, and put `u(h)=h/10^v`.  Thus `10` does not divide `u(h)`.  Since
`gcd(10,10^r-1)=1`, T58's ten-reduced formula gives the following exact
classification:

```text
Phi(h1,j1,r1)=Phi(h2,j2,r2)
if and only if
v(h1)+j1 = v(h2)+j2                              (5.1)
and
u(h1)(10^r1-1) = u(h2)(10^r2-1).                (5.2)
```

Indeed, after T58's reduction neither primitive factor is divisible by `10`
(although it need not be coprime to `10`).  If the displayed powers differed,
the side with the smaller power would have a remaining factor divisible by
`10`, while its primitive factor is not.  Thus equality forces equality of the
powers and then equality of the primitive factors.  The converse is immediate.

There is also a parameterization with no hidden collision class.  Put

```text
d = gcd(r1,r2),     G = 10^d-1,
U = (10^r1-1)/G,    V = (10^r2-1)/G.
```

The standard Euclidean identity

```text
gcd(10^r1-1,10^r2-1) = 10^gcd(r1,r2)-1           (5.3)
```

follows by repeatedly using
`10^a-1 = 10^(a-b)(10^b-1) + (10^(a-b)-1)` for `a>=b`.
Consequently `gcd(U,V)=1`.  Equation (5.2) holds if and only if there is one
positive integer `t`, not divisible by `10`, such that

```text
u(h1)=Vt,             u(h2)=Ut.                   (5.4)
```

Thus every ordered collision, including equal lags, unequal lags, equal
starts, shifted starts, equal multipliers, and unequal multipliers, is uniquely
described by

```text
h1 = 10^v1 Vt,        h2 = 10^v2 Ut,
v1+j1 = v2+j2,
1 <= h1,h2 < H,
(r1,j1),(r2,j2) in D_n.                           (5.5)
```

Conversely every tuple satisfying (5.5) is a collision.  This is the complete
collision list used in (4.1); no cross term is discarded.

## 6. Collision multiplicity and constants

Fix a frequency `m` and one lag `r`.  Suppose its fiber contains starts
`j_1 < ... < j_k`.  The corresponding multipliers obey

```text
h_(j_1) = 10^(j_k-j_1) h_(j_k) >= 10^(k-1).
```

Since `h_(j_1)<H<10^n`, this gives `k<=n`.  There are at most `n-1` short
lags.  Therefore, for every positive `m`,

```text
|F_m| <= n(n-1).                                    (6.1)
```

Also

```text
N_n <= (n-1)L,              |I_n|=(H-1)N_n.         (6.2)
```

For `y=h/H in (0,1)`, `|sin(pi y)|<=1`, `|cos(pi y)|<=1`, and `pi>3` give

```text
|a_(H,h)|
 <= H^(-1)[1/3+2(1-h/H)]
 < 7/(3H).                                           (6.3)
```

The replay checks the exact rational envelope and its sum

```text
sum_(1<=h<H) H^(-1)[1/3+2(1-h/H)]
  = 4(H-1)/(3H).                                    (6.4)
```

By Cauchy-Schwarz in each frequency fiber, followed by (6.1)-(6.3),

```text
integral S_n^2
 = 2 sum_m A_m^2
 <= 2 sum_m |F_m| sum_(i in F_m) |a_(H,h(i))|^2
 <= (98/9) n(n-1)(H-1)N_n/H^2
 <= (98/9) n(n-1)^2(H-1)L/H^2
 <= (98/9) n(n-1)^2 L/H
 <= (196/9) n^3 10^(-ceil(n/2)).                   (6.5)
```

Here the exact scale identity is

```text
L/H = 2*10^(-ceil(n/2)).                            (6.6)
```

The final series in (6.5) converges.  Notice that the collision terms have not
been assigned a sign or dropped; they were first grouped into the exact
nonnegative fiber squares and then bounded with their full multiplicity.

## 7. Measure-theoretic passage

Each `S_n` is a finite trigonometric polynomial and hence Lebesgue measurable.
By (6.5),

```text
sum_(n>=1) integral_[0,1) S_n(x)^2 dx < infinity.
```

Tonelli's theorem applied to the nonnegative measurable functions `S_n^2`
therefore gives

```text
integral_[0,1) sum_(n>=1) S_n(x)^2 dx < infinity.
```

Hence `sum_n S_n(x)^2` is finite for Lebesgue-almost every `x`, and for every
such fixed `x`,

```text
S_n(x) -> 0.                                         (7.1)
```

The deterministic zero mode satisfies

```text
0 <= Z_n = 2N_n/H
   <= 2(n-1)L/H
   = 4(n-1)10^(-ceil(n/2)) -> 0.                    (7.2)
```

Combining (7.1) and (7.2) proves the metric conclusion

```text
E_n(x) -> 0 for Lebesgue-almost every x in R/Z.      (7.3)
```

Thus the unnormalized complete residual is `o(1)` almost everywhere.  This is
strictly stronger than the T61-normalized eventual upper bound: for almost
every fixed seed `x`, there is an `N_x` such that

```text
E_n(x) <= 1 <= L_n          for every n >= N_x.      (7.4)
```

The constant `1` is universal; the cutoff `N_x` is allowed to depend on the
seed.  No fixed-`pi` conclusion follows because a conull set need not contain
the prescribed point `pi mod 1`.

For completeness, T61's proved majorization makes each metric majorant total
nonnegative, but nonnegativity is not used to suppress any term in the L2
calculation.  It only confirms that (7.3) is compatible with the interpretation
as a sum of majorants.

## 8. Endpoint audit

All endpoint conventions are retained:

1. `n>=1`; for `n=1`, the short-lag domain is empty.
2. `1<=h<H`; frequency `H` is excluded.
3. `0<r<n` and `r<L`.
4. `0<=j<L-r`.
5. The near-return radius is strict: `circleDistance < (2H)^(-1)`.
6. At both points `+-(2H)^(-1)`, T61's strict indicator is `0` while its
   Vaaler majorant is exactly `1`.

The endpoint discrepancy is intentional majorization, not equality.  The
countable union of endpoint preimages over all finite labels is null, but this
null-set observation does not alter the finite strict convention.

## 9. Symbolic replay

Run from a directory containing only the delivered artifacts:

```sh
sh ./verify.sh
```

The dependency-free `t82_symbolic_replay.py` checks, with integer or rational
arithmetic:

1. the vendored canonical statement hash;
2. every finite domain endpoint for five deterministic cases;
3. the direct frequency partition against T58's ten-reduced partition;
4. the repunit gcd formula and parameterization for every collision in those
   cases;
5. the full ordered collision matrix, diagonal, and off-diagonal counts;
6. the exact formal quadratic L2 polynomial coefficientwise by independent
   fiber and ordered-matrix constructions, plus three rational substitutions;
7. the factor `2` for the real cosine sum after taking the displayed cosine
   orthogonality rule as an exact symbolic rewrite;
8. the zero coefficient `2/H`, total zero mode `2N_n/H`, and normalization;
9. the rational envelope algebra, fiber multiplicity, and constants in (6.5).

The replay does not prove the analytic inequalities `|sin|<=1`, `|cos|<=1`,
or cosine orthogonality; those are proved directly in the note.  It uses their
displayed exact consequences as symbolic rewrite rules and verifies all finite
coefficient and collision algebra following those rules.

The replay output is pinned as `replay_expected.json`.  It includes the
visible `n=2` identity

```text
Q = 9 sum_(h=1)^49 c_h^2
    + 16(c_1 c_10 + c_2 c_20 + c_3 c_30 + c_4 c_40),
integral S_2^2 = 2Q,
```

so the cross terms are directly inspectable.  The finite replay is a symbolic
verification of the displayed finite algebra, not evidence for a universal
number-theoretic assertion.

## 10. Exact conclusion

**Metric sibling result.**  For each fixed `mu,c,Q0`, using the seed-independent
T61 residual masks, the complete signed structured-denominator Vaaler residual
with seed `x` tends to zero for Lebesgue-almost every `x in R/Z`.  In
particular it eventually satisfies the T61 `O(L_n)` normalization, indeed with
the universal coefficient `1` and an `x`-dependent cutoff.

This proves no estimate for the fixed seed `pi`, no C7, no C2, and no C1.
