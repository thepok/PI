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

[`T19T19ExactNaturalScaleResonance.lean`](TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean)
proves that a missing length-`k` decimal cylinder before time `N` forces some
nonzero integer frequency `h` with `|h| ≤ 2 * 10^k` to satisfy

```text
|S_h(N)| / N ≥ 1 / (24 * 10^k) + 1 / (12 * 10^(3k)).
```

Consequently, the machine-checked predicate
`PiNaturalScaleCancellationExact` implies V1. It asks that for every `k ≥ 1`
there exist one `N > 0` such that, simultaneously for every nonzero
`|h| ≤ 2 * 10^k`,

```text
|S_h(N)| / N < 1 / (24 * 10^k) + 1 / (12 * 10^(3k)).
```

This π-specific simultaneous moving-frequency estimate is open. It is the
cleanest direct checked frontier currently encoded in the trusted core.

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
is compatible with `|S_h(N)| / N → 1`, while T19 needs normalized
`O(10^-k)` cancellation simultaneously over an exponentially growing
frequency window.

## Alternative collision frontier

The reviewed [`moving-mesh collision-to-Haar consumer`](knowledge/pi/results/intermediate/20260823-moving-mesh-collision-haar-consumer.md)
has status `proof sketch`. For selected blocks of length `L_j`, partitioned
into `q_j` equal cells with occupancies `n_j(a)`, it assumes

```text
∑_{a < q_j} n_j(a)^2 ≤ C * (L_j^2 / q_j + L_j),
```

bounded `q_j / L_j`, and vanishing averaged error in the approximate dynamics
`x_{n+1} = 10 x_n mod 1`. These hypotheses force the block empirical measures
to converge to Haar measure and hence force every fixed decimal cylinder to be
hit eventually.

The consumer does not prove its collision premise for the decimal π orbit or
the sampled BBP orbit. Establishing that fixed-π estimate is open and expands
back into the long-lag/Fejér self-return frontier.

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
density, mixing, cancellation, or word occurrence. Any successful BBP route
must produce a genuinely new fixed-π quantitative estimate.

## Missing theorem

A resolution still requires at least one new fixed-π input of the following
kind:

1. **Fourier:** simultaneous natural-scale cancellation strong enough for T19;
   or
2. **Collision:** a moving-mesh occupancy/collision bound strong enough for the
   Haar consumer.

Equivalences, exact rational normal forms, recurrence packaging, finite digit
experiments, and representation-only lemmas are infrastructure, not frontier
progress, unless they produce such an estimate, strictly weaken a sufficient
premise with a checked separator, or decisively falsify a live route.

```text
new fixed-π cancellation or collision estimate
                    ↓
             orbit density
                    ↓
                   V1
```

The first arrow remains open.
