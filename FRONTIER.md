# π decimal disjunctivity: current frontier

Status: `conjecture`

Last audited: 2026-08-24 UTC

No theorem in this repository proves that every finite decimal word occurs in
the decimal expansion of π. The proof authority is [`TheoryLib/`](TheoryLib/)
and the explicit [`audit/AxiomAudit.lean`](audit/AxiomAudit.lean); reports and
experiments do not replace them.

## Canonical target

[`Theory.PiDigits.V1`](TheoryLib/PiDigits/T7Statements.lean) states

```text
∀ s : List (Fin 10), ∃ n : ℕ,
  ∀ i : ℕ, i < s.length → piDigit (n + i) = s[i].
```

Leading-zero words and overlaps are included. The empty word is vacuous.

The machine-checked theorem
[`Theory.PiDigits.T20.v1_iff_pi_baseTenOrbitDense`](TheoryLib/PiDigits/T20BaseTenOrbitDensity.lean)
identifies the target with density of the exact decimal orbit:

```text
V1  ↔  { fract (10^n * π) : n ∈ ℕ } is dense in [0,1].
```

## Direct machine-checked Fourier frontier

Let

```text
S_h(N) = ∑_{n < N} exp(2π i h fract(10^n π)).
```

[`T120T120WeightedNaturalScaleFrontier.lean`](TheoryLib/PiQuantitativeBlockHitting/T120T120WeightedNaturalScaleFrontier.lean)
and [`T121T121WeightedNaturalScaleCriterion.lean`](TheoryLib/PiQuantitativeBlockHitting/T121T121WeightedNaturalScaleCriterion.lean)
expose the exact Jackson-coefficient load that precedes the worst-mode step in
T19. A missing length-`k` decimal cylinder before time `N` forces

```text
sum_{nonzero Jackson modes i} |c_i| |S_{h_i}(N)| / N
  ≥ 1 / (3 * 10^k) + 2 / (3 * 10^(3k)).
```

Consequently, V1 follows if for every `k ≥ 1` there is one `N > 0` where this
weighted load is strictly below the displayed threshold. T19's simultaneous
pointwise premise implies this weighted premise. A machine-checked finite
two-point-grid separator proves that the converse implication fails for the
generic finite predicates; it is not a claim that either fixed-π premise is
known.

For comparison, T19 asks simultaneously for every nonzero
`|h| ≤ 2 * 10^k` that

```text
|S_h(N)| / N < 1 / (24 * 10^k) + 1 / (12 * 10^(3k)).
```

The π-specific weighted moving-frequency estimate is open. It is the cleanest
direct checked Fourier frontier in the trusted core.

## Entropy-deficit frontier

The
[`entropy-deficit hierarchy`](knowledge/pi/results/intermediate/20260824-entropy-deficit-haar-hierarchy.md)
has status `proof sketch`. On a selected nonempty block of the exact decimal π
orbit, let `p_k(a)` be the empirical distribution of the canonical `10^k`
cells and put

```text
H_k = -∑_a p_k(a) log p_k(a)
D_k = k * log 10 - H_k.
```

If there are `k_j -> infinity` and selected blocks with

```text
D_(k_j) / k_j -> 0,
```

then V1 follows. The support of `p_k` is bounded by the number `p_π(k)` of
distinct length-`k` decimal factors. Hence sublinear entropy deficit forces the
machine-checked factor-entropy limit to equal its maximum, and
[`T1CanonicalEntropy.lean`](TheoryLib/PiPositiveDecimalFactorEntropy/T1CanonicalEntropy.lean)
then gives V1.

This criterion does not require every cell to be occupied at any displayed
scale and gives no first-occurrence rate. No such entropy estimate is proved
for π.

### Bounded entropy gives Haar limits

For a general approximate times-ten orbit, uniformly bounded cell entropy
deficit together with vanishing averaged pseudo-orbit error forces the selected
block measures to converge to Haar. Bounded entropy deficit gives uniform
integrability of the cell-smoothed densities; absolute continuity plus
invariance then gives Haar by the Riemann--Lebesgue Fourier-ray argument.

The older
[`moving-mesh collision-to-Haar consumer`](knowledge/pi/results/intermediate/20260823-moving-mesh-collision-haar-consumer.md)
assumes

```text
∑_{a < q_j} n_j(a)^2 ≤ C * (L_j^2 / q_j + L_j)
```

and bounded `q_j/L_j`. Jensen's inequality implies uniformly bounded entropy
deficit, so the entropy consumer strictly weakens the quadratic collision
premise.

The same note gives exact-times-ten decimal de Bruijn separators proving both
strict implications:

```text
quadratic collision
        => bounded entropy deficit
        => sublinear entropy deficit
        => V1 for the exact decimal π orbit.
```

A retained finite experiment checks the separator combinatorics and numerical
diagnostics through word length five. The proof-sketch implications, not the
finite table, are the research claim.

## What is known unconditionally for fixed π

[`T11PiDigitFactorComplexity.lean`](TheoryLib/PiDigits/T11PiDigitFactorComplexity.lean)
proves that the decimal digit stream of π is not eventually periodic and hence
its length-`k` factor complexity satisfies

```text
p_π(k) ≥ k + 1.
```

V1 would require `p_π(k) = 10^k`.

[`T22T22AllFixedFrequencyGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T22T22AllFixedFrequencyGap.lean)
proves that for each fixed nonzero integer `h`, the additive gap

```text
N - |S_h(N)|
```

eventually exceeds every fixed real threshold.

This is nontrivial but quantitatively insufficient. A divergent additive gap
is compatible with `|S_h(N)| / N → 1`, while the checked Fourier frontier needs
moving-frequency normalized control and the entropy frontier needs almost
maximal block entropy at unbounded word lengths.

## BBP claim boundary

The classical BBP series identity is `machine-checked` in
[`T104T104BBPSeriesIdentity.lean`](TheoryLib/PiQuantitativeBlockHitting/T104T104BBPSeriesIdentity.lean).
The sampled BBP orbit is asymptotic to the canonical decimal π orbit, and
[`T108T108BBPCircleDensityTransfer.lean`](TheoryLib/PiQuantitativeBlockHitting/T108T108BBPCircleDensityTransfer.lean)
proves

```text
V1  ↔  the sampled BBP orbit is arbitrarily-late dense on the circle.
```

Thus BBP identities and recurrences transfer the problem; they do not supply
density, mixing, cancellation, entropy, or word occurrence. Any successful BBP
route must produce a genuinely new fixed-π quantitative estimate.

## Missing theorem

A resolution still requires a new fixed-π input. The retained targets are:

1. **Entropy:** selected `10^k`-cell laws with
   `k * log 10 - H_k = o(k)` along unbounded `k`;
2. **Fourier:** Jackson-weighted natural-scale cancellation strong enough for
   T120/T121;
3. **Bounded entropy / collision:** a uniformly bounded cell entropy deficit,
   or the stronger moving-mesh collision bound, giving Haar block limits.

Among the collision-derived premises, sublinear entropy deficit is the weakest
current sufficient condition with an explicit strict separator. It remains a
`proof sketch` and is unproved for π.

Equivalences, exact rational normal forms, recurrence packaging, finite digit
experiments, and representation-only lemmas are infrastructure, not frontier
progress, unless they produce one of these estimates, strictly weaken a
sufficient premise with a checked separator, or decisively falsify a live route.

```text
fixed-π sublinear entropy deficit  ───────────────→ V1

fixed-π bounded entropy / collision + dynamics ─→ Haar ─→ V1

fixed-π weighted Fourier cancellation ──────────→ finite hits ─→ V1
```

Every fixed-π premise displayed above remains open.
