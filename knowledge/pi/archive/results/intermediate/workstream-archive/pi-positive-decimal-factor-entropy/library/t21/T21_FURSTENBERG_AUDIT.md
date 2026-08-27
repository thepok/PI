# T21: Quantitative times-10/times-16 Furstenberg audit

Audit date: 2026-07-24 UTC

Status: `literature-checked` within the source and subject scope stated below. This is
a negative applicability audit, not a proof of C6 and not a claim about the decimal
factor entropy of pi.

## 1. Scope and immutable target

The immutable workspace canonical problem statement is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`, with SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
The exact byte stream is packaged as `pi-positive-decimal-factor-entropy.txt` so
`verify.sh` can check the canonical pin from a standalone replay directory.
The canonical question remains open. The present item audits the separate conditional
route C6; it does not replace the canonical question.

Write `T_m(x) = m*x mod 1` on the circle `T = R/Z`, put

```
alpha = pi mod 1,
K_pi = closure {T_10^n(alpha) : n >= 0},
U_R = union {T_16^j(K_pi) : 0 <= j <= R}.
```

The exact C6 quantifier order is

```
exists A > 0, exists B in R, exists eps_0 > 0,
  for every eps with 0 < eps < eps_0,
    exists R in N such that
      R <= A*log(1/eps) + B
      and U_R is eps-dense in T.
```

The target is about the one fixed set `K_pi`, not every nonempty closed invariant set.
The structural facts available without C6 are:

1. `K_pi` is closed by definition.
2. `T_10(K_pi) subset K_pi` by continuity and the definition as an orbit closure.
3. `alpha` is irrational, and `10` and `16` are multiplicatively independent.
4. C6 asks for every sufficiently small `eps` with one uniform pair `A,B`.
5. Only the times-16 depth is charged: every times-10 iterate has already been
   absorbed into `K_pi`.

These five points are the comparison standard in every row below.

## 2. Rate dictionary

The distinction between the rates is decisive.

| Class | Guaranteed density statement | Bound visible after inversion |
|---|---|---|
| Qualitative | `for every eps > 0, some R(eps)` | no modulus |
| BLMV point-orbit rate | radius `(log log N)^(-kappa)` using exponents `s,t <= N` | the stated modulus gives a sufficient times-16 depth of double-exponential order in a power of `1/eps` |
| BLMV finite-grid rate | radius `(log N)^(-c)` using multipliers `a^s b^t < N` | since `t < log_b N`, this is polynomial depth `R = O(eps^(-1/c))`, but only under the finite-grid and cardinality hypotheses |
| C6 | radius reached by depth `R <= A log(1/eps)+B` | exponential improvement of covering radius with `R` |

For the BLMV point-orbit row, setting
`(log log N)^(-kappa) <= eps` gives the sufficient choice

```
N >= exp(exp(eps^(-1/kappa))).
```

For the BLMV finite-grid row, put `c = kappa_2*rho/100` in Corollary
1.6. At the displayed radius `eps = (log N)^(-c)`, every multiplier
`a^s b^t < N` has `t < log_b N`, hence

```
R < log_b N = (1/log b)*eps^(-1/c).
```

This is a genuine polynomial comparison, but its varying rational grid `S` is not
`K_pi`. A polynomial bound would in any event still be weaker than C6's logarithmic
bound.

## 3. Hypothesis matrix

`YES*` means that the feature can be connected to `K_pi` by the elementary
times-10 absorption in Section 4, but the theorem still fails another C6 requirement.
Every verdict answers the question "does the cited result, as stated, prove C6?"

| ID and exact locator | Input type | Closed `K_pi` accommodated? | Uses only forward times-10 invariance? | All small `eps` for this fixed input? | Times-16 depth from the statement | Verdict |
|---|---|---|---|---|---|---|
| F67, Theorem IV.1, printed/PDF p.48 | one irrational point; nonlacunary integer semigroup | YES*, through `alpha in K_pi` | YES*, times-10 powers are absorbed | YES, after compactness, but ineffectively | no bound at all | **DOES NOT APPLY** |
| BLMV09, Theorem 1.8, printed p.1707/PDF p.3 | a Diophantine-generic irrational point | YES*, through the point | YES* | YES only under its Diophantine hypothesis | stated modulus gives `R` of sufficient double-exponential order in a power of `1/eps`, not logarithmic | **DOES NOT APPLY** |
| BLMV09, Corollary 1.6, printed p.1707/PDF p.3 | `S subset N^(-1)Z/Z`, `(N,ab)=1`, `|S|>N^rho` | NO: it is a varying finite rational grid, not `K_pi` | only if an additional inclusion `S subset K_pi` were supplied | NO for one fixed closed input | polynomial `R=O(eps^(-100/(kappa_2*rho)))` at its displayed scales | **DOES NOT APPLY** |
| HS12, Theorem 1.3, printed p.1005/PDF p.5 | two separately invariant probability measures | NO: no measure on `K_pi` with the needed properties is furnished | NO: it also requires a separate times-16 invariant measure | NO density conclusion | projection dimension only; no `R` | **DOES NOT APPLY** |
| HS15, Theorem 1.10, printed/PDF p.8 | times-10 invariant ergodic positive-entropy measure (take `gamma=10`, `beta=16`) | only if such a measure supported on `K_pi` is supplied | YES, but with extra ergodicity and positive entropy | qualitative equidistribution for almost every point | no effective first hitting time or uniform `R(eps)` | **DOES NOT APPLY** |
| W19, Theorem 1.4, printed p.711/PDF p.5 | two separately invariant closed sets | not in the required role: one set is times-10 invariant and another is times-16 invariant | NO: a second invariant set is required | NO density conclusion | intersection-dimension bound only; no `R` | **DOES NOT APPLY** |
| BG24, Theorem 1.5, printed/PDF p.5 | generic continuous times-10 invariant measures | NO: a measure theorem, not a theorem about the images of `K_pi` | times-10 invariance is present, but the conclusion is Fourier nonconvergence | NO set-density conclusion | no transversal bound | **DOES NOT APPLY** |

No row is `APPLIES`. The first two rows reach the correct semigroup orbit but miss
the logarithmic rate; the remaining rows change the object, add an entropy/dimension
hypothesis, or have no density conclusion.

## 4. The exact qualitative consequence of Furstenberg

Source F67, Theorem IV.1, states that if `Sigma` is a nonlacunary multiplicative
semigroup of integers and `alpha` is irrational, then `Sigma*alpha` is dense in the
circle. The locator is printed and PDF page 48. Take

```
Sigma = {10^s * 16^t : s,t >= 0}.
```

The semigroup is nonlacunary because 10 and 16 are not powers of one common integer.
For every `s,t`,

```
T_10^s(alpha) in K_pi,
T_16^t(T_10^s(alpha)) in T_16^t(K_pi).
```

Thus the dense semigroup orbit is contained in `union_{t>=0} T_16^t(K_pi)`.
For each circle point `y`, choose a semigroup-orbit point `z_y` within `eps/2` of
`y`. The balls of radius `eps/2` centered at all `y` have a finite subcover, say with
centers `y_1,...,y_m`. Every circle point is then within `eps` of one of
`z_(y_1),...,z_(y_m)`. Taking the largest times-16 exponent among those finitely many
orbit points gives an `R(eps)` for which `U_R` is `eps`-dense.

This deduction proves only

```
for every eps > 0, there exists R(eps).
```

Neither Theorem IV.1 nor the compactness step bounds that `R`. The precise missing
hypothesis/conclusion is an effective modulus uniform over all sufficiently small
`eps`, specifically `R(eps) <= A log(1/eps)+B` for fixed `A,B`.

Verdict for F67: **DOES NOT APPLY** to C6; it applies only to C6's qualitative
precursor.

## 5. Effective orbit density: BLMV

### 5.1 Diophantine-generic point orbit

Source BLMV09, Theorem 1.8, printed page 1707/PDF page 3, assumes multiplicative
independence and an irrational `alpha` satisfying

```
there exists k such that |alpha-p/q| >= q^(-k)
for q>=2 and p,q in Z.
```

It concludes that

```
{a^s b^t alpha : s,t <= N}
```

is `(log log N)^(-kappa_6)`-dense for `N >= N_0(k,a,b)`.

With `a=10`, `b=16`, all `a^s alpha` lie in `K_pi`, so the theorem conditionally
places its orbit set inside `U_N`. It therefore has the correct one-sided absorption
shape. But its stated modulus gives only the double-exponential sufficient depth in
Section 2. It also retains the displayed Diophantine hypothesis and dependence of
`N_0` on its exponent. This audit does not re-audit or invoke irrationality-measure
results for pi, because that ground is explicitly outside T21; even granting the
hypothesis, the rate remains far too weak.

Precise gap: replace the theorem's `(log log N)^(-kappa_6)` covering radius by a
uniform bound of exponential type `C exp(-cN)` after the times-10 exponent is
absorbed into `K_pi`.

Verdict for BLMV09 Theorem 1.8: **DOES NOT APPLY**.

### 5.2 Polynomial finite-grid comparator

Source BLMV09, Corollary 1.6, at the same printed/PDF page, assumes

```
N >= N_0(a,b), (N,ab)=1,
S subset N^(-1)Z/Z, and |S| > N^rho.
```

It concludes that the set of `m*s` with `m=a^u b^v<N` and `s in S` is
`(log N)^(-kappa_2*rho/100)`-dense. Section 2 shows that the corresponding
times-`b` exponent is polynomial in `1/eps`.

This is the cleanest polynomial-rate near-match, but it is not a theorem about one
fixed orbit closure. C6 supplies no rational grid `S subset K_pi`, no denominator
coprimality condition, and no uniform lower bound `|S|>N^rho` across scales. Snapping
points of `K_pi` to the grid is not a valid transfer: multiplication by `m<N` magnifies
the snapping error, and the corollary does not state stability under that operation.

Precise gap: a fixed-set version for `K_pi`, with no assumed positive-power
finite-scale cardinality, and an improvement from polynomial depth to logarithmic
depth.

Verdict for BLMV09 Corollary 1.6: **DOES NOT APPLY**.

## 6. Entropy and dimension results

### 6.1 Projection dimension

Source HS12, Theorem 1.3, printed page 1005/PDF page 5, takes probability measures
`mu,nu` invariant under `T_m,T_n`, respectively, where `m,n` are not powers of a
common integer. Every non-coordinate projection of `mu x nu` has the expected lower
Hausdorff dimension; for exact-dimensional measures the exact dimension statement
holds.

This is a dimension theorem for two measures. It neither constructs an appropriate
measure on `K_pi`, nor studies the increasing union `U_R`, nor converts dimension into
an `eps`-net at a specified scale. Hausdorff dimension alone has no uniform covering
constant or first-scale threshold. The exact missing hypotheses are a measure supported
on `K_pi` with quantitative finite-scale entropy bounds uniform at all small scales,
together with a theorem converting those bounds into `U_R` density with controlled
times-16 depth.

Verdict for HS12 Theorem 1.3: **DOES NOT APPLY**.

### 6.2 Positive entropy implies pointwise times-16 normality

Source HS15, Theorem 1.10, printed/PDF page 8, states that if `beta` is Pisot,
`beta` and `gamma` are multiplicatively independent, and `mu` is an ergodic
positive-entropy `T_gamma`-invariant measure, then `mu` is pointwise
`beta`-normal. Taking `beta=16` and `gamma=10` fits the arithmetic hypotheses.

If one additionally had such a measure supported on `K_pi`, then almost every point
of that measure would have a qualitative equidistributed times-16 orbit. Neither the
existence of that measure nor positive entropy is supplied by C6's structural facts.
For this program, positive entropy of the decimal orbit closure is an additional open
premise of the same type as the target phenomenon, so assuming it does not provide an
independent route to C6. The theorem also gives no effective discrepancy or
first-hitting-time bound, hence no `R(eps)`.

Precise gap: remove the positive-entropy/ergodic-measure assumption, or derive it
independently for `K_pi`, and add a uniform quantitative equidistribution modulus
strong enough to give logarithmic first hitting.

Verdict for HS15 Theorem 1.10: **DOES NOT APPLY**.

### 6.3 Intersection dimension

Source W19, Theorem 1.4, printed page 711/PDF page 5, proves for closed
`T_p`-invariant `A_p` and closed `T_q`-invariant `B_q`, with `p,q`
multiplicatively independent, that every affine intersection has upper box dimension
at most `max(0, dim_H A_p + dim_H B_q - 1)`.

C6 has one times-10 invariant set and asks about its successive times-16 images; it
does not supply a separately times-16 invariant set. An intersection-dimension upper
bound does not imply that a finite union of images is dense, and the theorem has no
scale-effective covering constants.

Precise gap: a finite-scale expansion theorem for the images `T_16^j(K_pi)`, uniform
in scale and with an exponential covering-radius gain per unit `j`.

Verdict for W19 Theorem 1.4: **DOES NOT APPLY**.

## 7. The stronger set-convergence boundary is still open

Source BG24 makes an especially useful logical distinction. On printed/PDF page 2,
Conjecture 1.2 says that for every infinite closed `T_p`-invariant set `F`, the
individual images `T_q^n(F)` converge to the circle in Hausdorff distance. This is a
conjecture, not a result, and the source states that it is largely open on printed/PDF
page 3. Even this conjecture contains no rate, so it would not by itself prove C6's
`O(log(1/eps))` bound.

BG24 Theorem 1.5, printed/PDF page 5, proves that a residual set of continuous
`T_p`-invariant measures has a nonzero limsup of Fourier coefficients along `q^n`;
in particular, their pushforwards do not converge weak-star to Lebesgue measure.
This disproves the measure Conjecture 1.4 in that source, not the closed-set
Conjecture 1.2. It neither disproves nor proves C6.

Precise gap: the theorem concerns generic measures and weak-star nonconvergence,
whereas C6 concerns the support set `K_pi`, Hausdorff covering, every small scale,
and a uniform logarithmic bound.

Verdict for BG24 Theorem 1.5: **DOES NOT APPLY**.

## 8. Exclusions and final finding

This audit intentionally does not revisit discrepancy estimates, exponential-sum
arguments, BBP formulas, irrationality measures, or additive-combinatorial inverse
theorems. BLMV is included because its stated quantitative Furstenberg theorems are
the direct comparison objects; its proof machinery is not audited here. The six
primary PDFs, retrieval URLs, hashes, and exact locators are recorded in
`SOURCE_MANIFEST.md` and checked by `verify.sh`. The verifier also checks the packaged
canonical statement against its fixed hash and requires no workspace-relative input.

Final finding: the checked literature gives

1. qualitative density and hence an ineffective finite transversal;
2. an effective point-orbit modulus whose stated inversion is vastly larger than
   logarithmic;
3. a polynomial finite-grid modulus under hypotheses not available for `K_pi`;
4. dimension and positive-entropy conclusions without a uniform covering modulus;
5. no theorem establishing C6's all-small-`eps`, fixed-constant,
   `R=O(log(1/eps))` conclusion.

Accordingly, this audit makes no unconditional claim about C6, C1, or pi.
