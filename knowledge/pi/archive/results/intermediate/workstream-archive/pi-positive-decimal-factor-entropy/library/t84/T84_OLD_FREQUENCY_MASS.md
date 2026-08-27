# T84: Old-frequency mass in the exact T61 signed residual

Status: **DIVERGENCE**.  This note gives an explicit adjacent-scale literal-
duplicate family and a numbered proof that its contribution is bounded below
at every sufficiently large scale.  Consequently the series of old-frequency
masses does not converge.  T56, T58, and T61 are used only through their
`machine-checked` interfaces.  The T83 note is unverified motivation and no
claim from it is a premise.  This note makes no fixed-pi estimate and no C7,
C2, or C1 claim.

## 1. Provenance, normalized statement, and ambiguities

The canonical problem is locally formulated and has no original external
source URL.  Its byte-exact delivered copy is
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It asks whether one fixed `eta>0` gives
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`.  T84 neither changes
nor resolves that question.

There are three T84-specific quantifier choices.

1. T61 permits arbitrary real `mu,c` and natural `Q0`.  The definitions below
   retain those parameters.  The divergence theorem assumes only `mu>1` and
   `c>0`; it is uniform in `Q0` after an onset depending on all three.
2. A frequency "occurs" when at least one legal T61 tuple maps to it.  Earlier
   occurrence is not defined by nonvanishing of an already-grouped coefficient,
   because cancellation at an earlier scale is irrelevant to literal tuple
   duplication.
3. The factor `2/L_n` in `B_n(q)` is fixed by the exact identity (3.2), not by
   convention.  The zero Fourier mode is not part of `B_n` or `V_n`.

The conclusion determines the growth of the explicit counterfamily: its mass
per scale is `Theta(1)` and its cumulative mass is `Theta(N)`.  It does not
claim an asymptotic formula for the possibly larger full mass `V_n`.

## 2. Machine-checked boundary

The exact imported interfaces are:

| Item | Declaration | Exact role | SHA-256 |
|---|---|---|---|
| T56 | `t56SampleLength`, `mem_sparse_short_sector_iff` | `L_n=10^(n/2)` with natural division and strict short lags | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` |
| T58 | `bandwidth`, `mem_positiveFejerFrequencies_iff`, `phi_collision_after_ten_reduction` | `H_n=10^n/2`, strict `h` range, and ten reduction | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` |
| T61 | `mem_residualShortRectangle_iff`, `vaalerCoefficient_explicit`, `structuredVaalerMajorantTotal_eq_completeExpression` | residual mask, signed weight, and exact complete finite expansion | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` |

T61's use of `ArithmeticExcluded` imports its machine-checked definition from
T25.  No unproved signed estimate in T61 is used.

## 3. Exact definitions of `B_n(q)` and `V_n`

Fix reals `mu,c`, a natural `Q0`, and an integer `n>=1`.  Put

```text
L_n = 10^(floor(n/2)),       H_n = 10^n/2,
D(j,r) = 10^j*(10^r-1),      Phi(h,j,r) = h*D(j,r).     (3.1)
```

Natural-number division is used in `floor(n/2)` and `H_n`.  Define

```text
ArithmeticExcluded_n(j,r) iff
  Q0 <= D(j,r) and
  10^(-n) <= D(j,r) * (c / D(j,r)^mu).
```

The complete T61 residual tuple set is

```text
Omega_n = {(h,r,j):
  1 <= h < H_n,
  0 < r < n,
  0 <= j < L_n-r,
  not ArithmeticExcluded_n(j,r)}.                       (3.2a)
```

The start inequality is strict and, since subtraction is natural, it also
forces `r<L_n`.  Thus (3.2a) preserves every T61 endpoint and its complete
residual mask.  For `1<=h<H_n`, let the literal signed T61 weight be

```text
a_n(h) = H_n^(-1) * [
  sin(pi*h/H_n)/pi
  + 2*(1-h/H_n)*cos(pi*h/H_n)].                          (3.2b)
```

Here every displayed `pi` is the angular constant.  No absolute value is put
inside this signed coefficient.  For every positive integer `q`, define

```text
B_n(q) = (2/L_n) *
  sum_{(h,r,j) in Omega_n, Phi(h,j,r)=q} a_n(h).         (3.2c)
```

Let

```text
Q_n   = {Phi(h,j,r):(h,r,j) in Omega_n},
Old_n = Q_n intersect union_{1<=m<n} Q_m,
V_n   = sum_{q in Old_n} |B_n(q)|.                       (3.2d)
```

All sets and sums are finite.  If `S_n(x)` denotes T61's
`signedStructuredDenominatorSum`, then finite regrouping, with no analytic
interchange, gives exactly

```text
S_n(x)/L_n = sum_{q in Q_n} B_n(q)*cos(2*pi*q*x).        (3.2e)
```

Indeed T61 has one outer factor `2`, and each tuple contributes
`a_n(h) cos(2*pi*Phi(h,j,r)*x)`.  Grouping the finite tuple set by the integer
map `Phi` proves (3.2e).  The zero mode remains separately
`2*residualStructuredCard/H_n` in T61 and is absent from (3.2c)-(3.2e).

## 4. Complete collision identity

For a positive integer `h`, write uniquely

```text
h = 10^v(h)*u(h),       10 does not divide u(h).
```

Since `10` is coprime to every `10^r-1`, two tuples collide exactly when

```text
v(h1)+j1 = v(h2)+j2,
u(h1)*(10^r1-1) = u(h2)*(10^r2-1).                     (4.1)
```

For completeness, put `g=gcd(r1,r2)`,

```text
G=10^g-1, U=(10^r1-1)/G, V=(10^r2-1)/G.
```

The identity
`gcd(10^r1-1,10^r2-1)=10^gcd(r1,r2)-1` gives
`gcd(U,V)=1`.  The second equality in (4.1) holds if and only if there is a
unique positive `t`, not divisible by ten, for which

```text
u(h1)=V*t,             u(h2)=U*t.                       (4.2)
```

Equations (4.1)-(4.2), together with the two independent copies of all the
membership conditions in (3.2a), are a sound and complete collision
parameterization.  Scale indices affect legality and weights, not the integer
equality.

## 5. Explicit all-scale counterfamily

Assume from now on

```text
delta = mu-1 > 0,       c>0.                            (5.1)
```

Choose a natural `kappa` with `c<=10^kappa`.  Exponential growth supplies an
integer `K>=2` such that

```text
delta*(10^(K-1)/2-1) > 2K+kappa,
(9*delta/2)*10^(K-1) > 2.                              (5.2)
```

Set `N0=2K`, enlarged if necessary so all elementary integer estimates below
hold.  For every `n>=N0`, monotonic induction in `floor(n/2)` gives

```text
delta*(L_(n-1)/2-1) > n+kappa.                          (5.3)
```

The second inequality in (5.2) makes the left side gain more than `2` when the
half-scale exponent increases; the odd scale between two even scales has a
larger `L_(n-1)` and costs only one on the right.  Thus (5.3) holds at every
scale, not merely on one parity.

Put

```text
A_n = H_(n-1)/10 = H_n/100,
V_r = (10^r-1)/9  for r>=1.                             (5.4)
```

Define the multiplier and start sets

```text
M_n = {h in Z:
  A_n <= h < 2*A_n,
  10 does not divide h,
  V_r does not divide h for every 2<=r<n},

J_n = {J in Z: L_(n-1)/2 <= J <= L_(n-1)-2}.            (5.5)
```

For `(h,J) in M_n x J_n`, define the selected frequency

```text
q_n(h,J) = 9*h*10^J.                                    (5.6)
```

## 6. Numbered proof of divergence

1. **Multiplier count.**  Since
   `V_r=(10^r-1)/9 >= 10^(r-1)` for `r>=2`,

   ```text
   sum_{r=2}^infinity 1/V_r <= sum_{s=1}^infinity 10^(-s)=1/9.
   ```

   An interval of `A_n` consecutive integers contains at most `A_n/d+1`
   multiples of `d`.  A union bound for divisibility by `10,V_2,...,V_(n-1)`
   therefore gives

   ```text
   |M_n| >= A_n*(1-1/10-1/9)-(n-1)
          = 71*A_n/90-(n-1) >= A_n/2 = H_(n-1)/20.      (6.1)
   ```

   The final inequality holds after enlarging `N0`.

2. **Start count and strict endpoints.**  Powers of ten here are even, so

   ```text
   |J_n|=L_(n-1)/2-1 >= L_(n-1)/4.                     (6.2)
   ```

   Every `J in J_n` satisfies `0<=J<L_(n-1)-1`, hence `(r,j)=(1,J)` is
   strictly inside the earlier rectangle.  Both `J` and `J-1` are strictly
   inside the current rectangle.

3. **The residual masks survive.**  Every label needed below has `r=1` and
   `j>=L_(n-1)/2-1`.  Its structured denominator is `D=9*10^j`.  From
   (5.3), using `9^(-delta)<=1`,

   ```text
   c*D^(1-mu) = c*D^(-delta)
     <= 10^(kappa-delta*j) < 10^(-n).                  (6.3)
   ```

   Hence the second conjunct of `ArithmeticExcluded_n` is false, regardless
   of `Q0`.  It is also false at scale `n-1`, because
   `10^(-n)<10^(-(n-1))`.  Thus `(1,J)` survives at scale `n-1`, while
   `(1,J)` and `(1,J-1)` survive at scale `n`.

4. **The complete current fiber has exactly two tuples.**  Suppose a current
   tuple `(g,r,j)` has frequency `q_n(h,J)`.  Write `g=10^v*u` with
   `10` not dividing `u`.  Cancelling decimal valuations and the factor `9`
   gives

   ```text
   v+j=J,              u*V_r=h.                         (6.4)
   ```

   If `r>=2`, (6.4) contradicts the definition of `M_n`.  Therefore `r=1`,
   `u=h`, and every representation is `(10^v*h,1,J-v)`.  From
   `A_n<=h<2A_n` and `H_n=100A_n`,

   ```text
   h < H_n, 10h < H_n, 100h >= H_n.                    (6.5)
   ```

   The strict multiplier cutoff therefore leaves exactly

   ```text
   (h,1,J),            (10h,1,J-1).                    (6.6)
   ```

   Step 3 proves that neither tuple is removed by the mask.  This also proves
   there is no hidden negative-coefficient representation in the grouped
   coefficient.

5. **The earlier fiber is a literal duplicate.**  At scale `n-1`,
   `H_(n-1)=10A_n`, so `h<H_(n-1)` but `10h>=H_(n-1)`.  Repeating Step 4 gives
   the unique earlier representation `(h,1,J)`.  Thus every frequency (5.6)
   belongs to `Old_n`.

6. **Selected frequencies are distinct.**  If
   `9h10^J=9h'10^J'` for selected pairs, ten-primitivity gives `J=J'` by
   decimal valuation, and then `h=h'`.  Hence no selected pair is counted
   twice in `V_n`.

7. **Both current coefficients are positive with an explicit lower bound.**
   For either current multiplier `g` in (6.6), (6.5) gives
   `0<g/H_n<1/5`.  On this interval,

   ```text
   sin(pi*g/H_n)>0,
   cos(pi*g/H_n)>cos(pi/3)=1/2,
   1-g/H_n>4/5.
   ```

   Substitution into the literal signed coefficient (3.2b) yields

   ```text
   a_n(g) > 4/(5H_n).                                   (6.7)
   ```

   Consequently the complete grouped fiber, not merely selected summands,
   satisfies

   ```text
   B_n(q_n(h,J))
     = (2/L_n)*(a_n(h)+a_n(10h))
     > 16/(5L_nH_n).                                   (6.8)
   ```

8. **Uniform lower bound.**  Summing (6.8) over the distinct old frequencies
   and using (6.1)-(6.2) gives

   ```text
   V_n >= (1/25)*(L_(n-1)/L_n)*(H_(n-1)/H_n).           (6.9)
   ```

   Exactly `H_n/H_(n-1)=10`, while

   ```text
   L_n/L_(n-1) = 10 if n is even, and 1 if n is odd.
   ```

   Therefore, for every `n>=N0`,

   ```text
   V_n >= 1/2500 if n is even,
   V_n >= 1/250  if n is odd.                           (6.10)
   ```

9. **Linear cumulative lower growth.**  For `N>=N0`, put
   `T=N-N0+1`, let `E` be the number of even integers in `[N0,N]`, and put
   `O=T-E`.  Since `O>=(T-1)/2`, (6.10) gives

   ```text
   sum_{n=N0}^N V_n
     >= E/2500+O/250
     = (E+10O)/2500
     >= (11T-9)/5000.                                  (6.11)
   ```

   In particular `V_n` does not tend to zero and `sum_n V_n` diverges.

10. **Correct growth of the explicit family.**  The elementary bound
    `|a_n(g)|<7/(3H_n)` gives at most `28/(3L_nH_n)` for each two-tuple
    selected fiber.  Also `|M_n|<=A_n` and
    `|J_n|<=L_(n-1)/2`.  Thus its mass is bounded above by

    ```text
    (7/15)*(L_(n-1)/L_n)*(H_(n-1)/H_n) <= 7/150.        (6.12)
    ```

    Equations (6.9) and (6.12) show that the counterfamily has `Theta(1)` mass
    at every scale and `Theta(N)` cumulative mass.  This is the requested
    growth statement.  The full `V_n` may contain additional old frequencies.

The alternative convergence branch is false under the literal definitions
(3.2c)-(3.2d), so no convergence-derived duplicate-square bound is asserted.

## 7. Consequence and exact scope

The obstruction is algebraic and independent of the value at which T61's
trigonometric polynomial is evaluated.  It says that literal frequency reuse
is not a summable error after the stated `L_n` normalization.  It does **not**
say that T61's signed polynomial is large at `Real.pi`: different frequencies
still carry fixed-pi phases, and this note estimates only grouped coefficient
mass.  It proves no incidence bound, covariance bound, C7, C2, C1, or statement
about the decimal digits of pi.

## 8. Replay

From a directory containing only the delivered artifacts, run

```sh
sh ./verify.sh
```

The dependency-free checker uses exact integers and rational numbers.  It
exhausts every tuple at scales `2,3` for two literal T61 masks; independently
generates and compares direct, ten-reduced, and repunit-gcd collision partitions; checks the formal
coefficient grouping and ordered fiber-square identities; and exhausts the
selected counterfamily and every representation of its frequencies at scales
`4,5`.  The finite output is an `experiment`, not the proof of the universal
growth statement; Steps 1-10 above are the proof.
