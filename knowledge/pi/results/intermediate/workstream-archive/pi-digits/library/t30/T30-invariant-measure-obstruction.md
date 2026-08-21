# T30: invariant-measure form of fixed-frequency resonance

Status: `proof sketch` (rigorous written proof, not machine-checked)

## Scope and exact target

The immutable canonical question V1 asks whether every finite decimal digit
string, including strings with leading zeroes, occurs contiguously in the
decimal expansion of pi. This note proves the following conditional statement
only.

> **Theorem (necessary invariant-measure obstruction).** If canonical V1 is
> false, then there are integers `k >= 1` and `h != 0`, with
> `|h| <= T29.H(k)`, a strictly increasing sequence of positive integers
> `(N_r)`, and a Borel probability measure `mu` on the circle
> `T = R/Z` such that, for
> `x_j = [fract(10^j pi)]` and
> `mu_N = (1/N) sum_{j=0}^{N-1} delta_(x_j)`, some subsequence of
> `(mu_(N_r))` converges weak-* to `mu`, the measure is invariant under
> `S([x]) = [10x]`, and
> `|hat(mu)(h)| >= T29.epsilon(k) > 0`.

Here the Fourier convention is

```text
hat(mu)(h) = integral_T exp(2 pi i h x) dmu([x]).
```

The notation is well-defined because adding an integer to `x` does not change
the exponential.

This is a necessary consequence of the hypothesis `not V1`. It is not a
converse. It does not prove V1, `not V1`, V3, or `not V3`.

## Normalization and ambiguities

1. The hypothesis is the literal negation of canonical V1, not failure of
   normality and not either sibling variant V2 or V3.
2. "Empirical measures of the fractional parts" means Borel probability
   measures on `T = R/Z`, with each real fractional part sent to its residue
   class. This ambient space is essential: the representative-valued function
   `x |-> fract(10x)` has jumps on `[0,1)`, whereas `S([x]) = [10x]` is
   continuous on `T`.
3. "Subsequential limit" means weak-* convergence against every continuous
   complex-valued function on `T`.
4. The frequency `h` is chosen once, before the lengths `N_r`; it is not
   allowed to vary with `r`.
5. No assertion is made that every weak-* limit of the orbit empiricals has a
   nonzero Fourier coefficient. The construction extracts one such limit from
   the resonant lengths supplied by T29.

## Pinned inputs

All mathlib links below use commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

| Input | Exact statement used | SHA-256 |
|---|---|---|
| `knowledge/pi/statements/pi-digits.txt` | Lines 3-10 give canonical V1; lines 21-37 separate V1/V2/V3. | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| `knowledge_library/t20/BaseTenOrbitDensity.lean` | `Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense`, lines 283-290. | `202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126` |
| `knowledge_library/t29/FixedFrequencyResonance.lean` | `epsilon_pos`, lines 46-47; `phase_fract_eq_phase`, lines 49-63; `piFractional_exponentialSum_eq`, lines 65-75; and `not_canonicalV1_implies_fixed_frequency_resonance`, lines 224-253. | `36bccfb678a9e3452bb4321a518541d2d0c9af79b995e1305ae47bc35d11c171` |
| [`Mathlib/Topology/Instances/AddCircle/Real.lean`, lines 32-35](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/Instances/AddCircle/Real.lean#L32-L35) | `AddCircle.compactSpace`: `R/Z` is compact. | `21dbd379dae0d06d14882ad19e0c89ba90df2f3f9c7b811fee218ba5ae442e8e` |
| [`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`, lines 324-385](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean#L324-L385) | The map `[x] |-> exp(2 pi i x)` and `AddCircle.homeomorphCircle`; thus `R/Z` is homeomorphic to the metric unit circle. | `dd7908047f0391a4bb23306218948e2b52596965eb59b11e7fda9a693d9c85db` |
| [`Mathlib/Analysis/Complex/Circle.lean`, lines 49-61 and 103-105](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Analysis/Complex/Circle.lean#L49-L105) | The unit circle is a metric space and a compact space. | `41d345b90fc131abcf0560b4c0f1df475b7770314b6e1f9b06cf70ea7cb78235` |
| [`Mathlib/MeasureTheory/Measure/Prokhorov.lean`, lines 159-163](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/Prokhorov.lean#L159-L163) | Exact compactness theorem: `[CompactSpace E] : CompactSpace (ProbabilityMeasure E)`. | `c801011b50b53785597d1b94550ec8ee42ba43f9bdd7621141438dd8de6e71dc` |
| [`Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean`, lines 667-700](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean#L667-L700) | On a separable metrizable Borel space, the weak topology on probability measures is metrizable. | `51e47176a2084cabf70fc6e6587bbe4839c0ceac183a7e5d9a168225d81bf4dc` |
| [`Mathlib/Topology/Sequences.lean`, lines 277-304](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/Sequences.lean#L277-L304) | A sequence in a sequentially compact space has a strictly monotone convergent subsequence; compact plus first countable gives sequential compactness. | `a20e0b26d5b642601a1056170605ee7d66f36b6e33a8f3ff85dc9f0c97f050fc` |
| [`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`, lines 286-290 and 343-360](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean#L286-L360) | Defines the weak topology and characterizes its convergence by integrals of bounded continuous real or complex functions. | `e4957676ea41f80a67601e35f392fad974eb40b9d2297c8a7c6273068518b8c2` |
| [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, lines 1018-1039](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L1018-L1039) | `integral_map`: integration against a pushforward equals integration after composition. | `e86e447e872e259495203bdd12e7aaf105ab9d73a3c7156647dc87a90cee7759` |
| [`Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`, lines 378-389](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean#L378-L389) | Finite Borel measures agreeing on all bounded continuous real test functions are equal. | `5afdd4bc3c8d5535e8de710b29912670d05c419a54cec0071645dd0e387db7eb` |

The compactness result invoked below is therefore pinned exactly, including
the theorem implementation, repository revision, and file digest. The unit
circle is separable: the images of rational angles form a countable dense
set. Consequently the cited Levy-Prokhorov metrizability result applies.

## Imported conclusions of T20 and T29

T20 proves the exact equivalence

```text
V1 <-> the sequence fract(10^j pi) is metrically dense in [0,1].       (T20)
```

Thus the present hypothesis also implies failure of that density statement.
This observation identifies the canonical dynamical system; compactness or
resonance is not inferred from non-density alone.

Applying T29's
`not_canonicalV1_implies_fixed_frequency_resonance` to `not V1` gives

```text
k : N,                 0 < k,
s : List (Fin 10),     length(s) = k and T29.WordMissing(s),
h : Z,                 h != 0 and |h| <= T29.H(k),              (1)
forall B : N, exists N : N,
  B <= N and T29.epsilon(k) * N <= norm(T29.piExponentialSum(N,h)). (2)
```

T29 also proves

```text
T29.epsilon(k) > 0.                                          (3)
```

The order of quantifiers in (1)-(2) fixes `h` before `B` and `N`.

## Proof

### 1. Extract resonant lengths tending to infinity

Put `eps = T29.epsilon(k)`. Apply (2) with `B_0 = 1` and choose `N_0`
such that

```text
1 <= N_0,       eps * N_0 <= norm(piExponentialSum(N_0,h)).    (4)
```

After `N_r` has been chosen, apply (2) with `B_(r+1) = N_r + 1` and
choose `N_(r+1)` such that

```text
N_r + 1 <= N_(r+1),
eps * N_(r+1) <= norm(piExponentialSum(N_(r+1),h)).            (5)
```

Dependent choice produces the sequence. Equation (5) makes it strictly
increasing. Induction gives `N_r >= r+1`, so `N_r -> infinity`. Every `N_r`
is positive, which will justify division by `N_r`.

### 2. Define the compact dynamical system and empirical measures

Let `T = R/Z`, write `[y]` for the residue class of `y`, and set

```text
y_j = fract(10^j pi),       x_j = [y_j],
S([y]) = [10y].                                                (6)
```

The definition of `S` is independent of the representative: if `y-y'` is an
integer, then `10y-10y'` is an integer. It is continuous because it is the
quotient map induced by the continuous linear map `y |-> 10y`.

Fractional part differs from its argument by an integer, so

```text
x_j = [10^j pi].                                               (7)
```

It follows directly that

```text
S(x_j) = [10 * 10^j pi] = [10^(j+1) pi] = x_(j+1).            (8)
```

For each positive integer `N`, define

```text
mu_N = (1/N) * sum_{j=0}^{N-1} delta_(x_j).                    (9)
```

It has total mass `(1/N) * N = 1`, hence is a Borel probability
measure on `T`. These are exactly the empirical measures of the stated
fractional parts, interpreted in the compact quotient as specified above.

### 3. Extract a weak-* subsequential limit

The cited AddCircle and Circle sources show that `T` is compact metrizable.
The cited Prokhorov theorem says that the full space `P(T)` of Borel
probability measures is compact in its weak topology. Rational angles give
separability of `T`, so the cited Levy-Prokhorov theorem says this weak
topology is metrizable. It is therefore first countable, and the cited
sequential compactness theorem applies.

Apply it to the sequence `(mu_(N_r))`. There are a Borel probability measure
`mu`, a strictly increasing map `q : N -> N`, and

```text
mu_(N_(q(l))) -> mu weak-* as l -> infinity.                  (10)
```

For brevity put `M_l = N_(q(l))`. Since `N_r >= r+1` and a strictly
increasing map `q : N -> N` satisfies `q(l) >= l`,

```text
M_l >= q(l)+1 >= l+1,       hence M_l -> infinity.            (11)
```

The composition of the two strictly increasing maps is strictly increasing,
so `(mu_(M_l))` is genuinely a subsequence of the full empirical sequence
`(mu_N)`, not merely a subnet.

Each `M_l` is one of the recursively selected lengths, so (4)-(5) retain the
T29 resonance inequality at every `M_l`.

### 4. Finite telescoping identity

Let `f : T -> C` be continuous. From (9) and then (8),

```text
integral f(Sx) dmu_N(x)
  = (1/N) * sum_{j=0}^{N-1} f(S(x_j))
  = (1/N) * sum_{j=0}^{N-1} f(x_(j+1)),                        (12)

integral f(x) dmu_N(x)
  = (1/N) * sum_{j=0}^{N-1} f(x_j).                            (13)
```

Subtract (13) from (12). Terms `f(x_1),...,f(x_(N-1))` cancel
pairwise, giving the exact finite identity

```text
integral f(Sx) dmu_N(x) - integral f(x) dmu_N(x)
  = (f(x_N) - f(x_0))/N.                                     (14)
```

Compactness of `T` makes `f` bounded. If
`C_f = sup_{x in T} |f(x)|`, the triangle inequality gives

```text
norm((f(x_N)-f(x_0))/N) <= 2 C_f/N.                           (15)
```

This proves the finite telescoping step without an asymptotic or measure
theorem.

### 5. Pass telescoping to the weak-* limit

Use (14) with `N=M_l`. Both `f` and `f o S` are continuous. By (10) and the
pinned weak-convergence characterization,

```text
integral f dmu_(M_l)       -> integral f dmu,
integral (f o S) dmu_(M_l) -> integral (f o S) dmu.           (16)
```

By (11) and (15), the right side of (14) tends to zero. Taking the limit in
(14) therefore gives

```text
integral (f o S) dmu = integral f dmu                         (17)
```

for every continuous complex-valued `f`.

Let `S_*mu` denote the pushforward. The pinned `integral_map` identity
turns (17), restricted to real-valued `f`, into

```text
integral f d(S_*mu) = integral f dmu
```

for every bounded continuous real `f`. The pinned finite-measure extensionality
theorem now gives

```text
S_*mu = mu.                                                    (18)
```

Thus `mu` is invariant under `[x] |-> [10x]`, equivalently under
`x |-> fract(10x)` when points are represented in `[0,1)`.

### 6. Retain T29's fixed Fourier lower bound

Define the continuous character

```text
chi_h([x]) = exp(2 pi i h x).                                 (19)
```

For every positive `N`, equations (9) and (19) give

```text
integral chi_h dmu_N
  = (1/N) * sum_{j=0}^{N-1} exp(2 pi i h fract(10^j pi)).      (20)
```

T29's `phase_fract_eq_phase` removes each fractional part without changing
the phase. Equivalently, T29's
`piFractional_exponentialSum_eq` identifies the sum in (20) with its exact
`piExponentialSum(N,h)`. Therefore

```text
hat(mu_N)(h) = (1/N) * piExponentialSum(N,h).                  (21)
```

At every retained length `M_l`, the T29 inequality and positivity of `M_l`
allow division by `M_l` in (21):

```text
eps <= norm(hat(mu_(M_l))(h)).                                (22)
```

The character `chi_h` is continuous, so weak-* convergence (10) gives

```text
hat(mu_(M_l))(h) -> hat(mu)(h).                               (23)
```

The complex norm is continuous. Taking norms in (23), then passing to the
limit in the closed inequality (22), yields

```text
eps <= norm(hat(mu)(h)).                                      (24)
```

By (3), `eps > 0`; hence

```text
hat(mu)(h) != 0.                                              (25)
```

The same `h != 0` fixed in (1) appears in (20)-(25), and its T29 bound
`|h| <= H(k)` is unchanged.

## Conclusion and logical strength

Starting from `not V1`, T29 supplies one fixed bounded nonzero frequency and
unboundedly many resonant empirical lengths. Compactness supplies a weak-*
subsequence; the exact identity (14) forces invariance of its limit; and
weak-* continuity of the fixed Fourier character preserves the positive
lower bound (24).

Only the forward implication

```text
not V1  ->  existence of the invariant resonant limit described above
```

has been proved. No converse is asserted. In particular, the mere existence
of an invariant measure with a nonzero Fourier coefficient is not claimed to
force failure of V1. Nothing here proves or disproves canonical V1 or sibling
V3.
