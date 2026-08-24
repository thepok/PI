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

T120/T121 expose the raw Jackson-coefficient load that precedes the worst-mode
step in T19. [`T123`](TheoryLib/PiQuantitativeBlockHitting/T123T123AggregatedJacksonFrontier.lean)
now groups equal frequencies before taking absolute values.
Write `A_q(h)` for the resulting signed coefficient and

```text
L_agg(q,N) = sum_(h != 0) |A_q(h)| |S_h(N)| / N.
```

A missing length-`k` decimal cylinder forces

```text
L_agg(10^k,N) ≥ 1 / (3 * 10^k) + 2 / (3 * 10^(3k)).
```

Consequently V1 follows if the reverse strict inequality holds at one `N>0`
for every `k≥1`. T123 machine-checks `L_agg ≤ L_raw`, so this premise is weaker
than T120/T121. Its actual-Jackson `q=2` grid separator crosses the common
threshold (`7/32 < 1/4 < 11/32`), proving strictness of the generic finite
criteria. The stronger all-decimal-scale coefficient formulas and separator
in the companion report remain `proof sketch`.

[`T124`](TheoryLib/PiQuantitativeBlockHitting/T124T124DirectionalJacksonFrontier.lean)
removes another triangle inequality for a prescribed word. It retains the
centered signed real Jackson defect `D(q,N,a)` and proves

```text
D(q,N,a) ≤ L_agg(q,N).
```

An empty target cylinder forces `D` above the same threshold. Hence the
wordwise premise “for every nonempty word `s`, some `N_s>0` makes its own
directional defect smaller than the threshold” implies V1; unlike T123, its
cutoff may depend on the word rather than only its length. A machine-checked
actual-Jackson `q=1` singleton separates the finite directional and aggregated
criteria. A second machine-checked separator works at the actual decimal scale
`q=10`: its directional value is `-983/500`, while the aggregated criterion
already fails from the `h=10` term `83/1000`. This does not independently
separate the two pi-level quantifier patterns.

An independently audited `proof sketch` improves the minorant itself:

```text
K_q(t) = (cos(2*pi*t) - cos(pi/q)) * F_q(t)^2.
```

It matches the cylinder boundary exactly. T128 machine-checks the finite
Fourier closed form, outside-sign property, coefficientwise domination of the
old Jackson coefficients, positive explicit zero-mode lower bound, and finite
directional hitting consumer. T129 proves exact closed forms for both signed
zero modes and their strict boundary-matching gain for every `q > 1`. T130
checks the piecewise cubic cross-determinant algebra and the actual normalized
improvement at frequency `2q-1`. The general finite-fiber identification needed
to transfer that algebra to every actual interior coefficient is now checked
in T131. T132 checks the signed edge fibers and therefore the full actual
normalized coefficientwise improvement throughout the positive support. The
exact `q=10` directional Boundary-vs-Jackson separator is machine-checked in
T133, and the larger 26-point aggregate separator is machine-checked in T134.
Its wordwise fixed-pi estimate remains open.

For comparison, T19 asks simultaneously for every nonzero
`|h| ≤ 2 * 10^k` that

```text
|S_h(N)| / N < 1 / (24 * 10^k) + 1 / (12 * 10^(3k)).
```

The π-specific directional estimate is the weakest direct machine-checked
Fourier premise currently in the trusted core. It remains open. No fixed-π
cancellation, density, normality, or V1 theorem follows from these reductions.

Two audited transfer calculations, both still `proof sketch`, delimit the next
attack. The
[transfer-compatible family](knowledge/pi/results/intermediate/20260824-transfer-compatible-directional-kernel.md)
classifies the scalar Fejér-square kernels with an exact preimage law and shows
only that parent positivity cannot imply positivity of every prescribed child.
The
[boundary carry-flow reduction](knowledge/pi/results/intermediate/20260824-boundary-kernel-carry-flow.md)
transports a child score to a carry-corrected incoming suffix edge with
`O(Q^-2)` leakage. Its sufficient incoming-edge estimate remains unproved for
π. Its no-gos are deliberately narrow: successor-only scalar reconstruction
and exact coboundary telescoping for the finite boundary polynomial.

An audited
[`primitive-ray coefficient contraction`](knowledge/pi/results/intermediate/20260824-t128-primitive-ray-coefficient-contraction.md)
compresses the actual T128 positive-frequency obstruction to frequencies not
divisible by ten plus exact initial/terminal orbit terms. Generic ray
telescoping was already available. T138 now machine-checks the uniform actual
T128 coefficient-load gap
`sum_u |p_(q,A)(u)| < L_q - 1/3000000` for every `q=10^k`. T139 now also
machine-checks the positive/negative conjugate reconstruction, the exact
actual-π primitive identity with both endpoint blocks, norm and `4E/N` defect
bounds, strict primitive-only T128 hit consumer and decimal-scale wrapper, and
the T138-enhanced uniform primitive-cancellation consumer. A further `proof
sketch` evaluates the exact endpoint budget as
`E=δq(q-1)/18-(k/2)α₀<π²/36`, sharp in the limit, reducing the literal
endpoint defect below `π²/(9N)` for every target; target averaging does not
provide wordwise control because `h=q` survives. The needed
primitive-frequency cancellation estimate remains open for π, so this proves
neither T124 nor V1 and supplies no exact π-orbit logical separator.

A `proof sketch`
[`endpoint-free singleton-ray barrier`](knowledge/pi/results/negative/20260824-endpoint-free-singleton-ray-barrier.md)
shows why decimal-ray compression is only preprocessing: the singleton belt
retains coefficient mass at least `27/160` for T139, `27/200` at mixed order
`4q/5`, and `9/400` for every positive-zero mixed order, while the zero-mode
margin is only `O(1/q)`. Thus controlling colliding rays but leaving singleton
rays at phase-blind coordinatewise caps still requires `O(1/q)` cancellation.
The exact surviving target is a lag-`k`, target-dependent signed correlation
of the actual decimal π orbit; no estimate for it is presently known.

An audited [`mixed-order Fejer boundary construction`](knowledge/pi/results/intermediate/20260824-mixed-order-fejer-boundary-kernels.md),
still only a `proof sketch`, replaces `F_q^2` by `F_q F_(4q/5)`. At decimal
scales it lowers support from `2q-1` to `9q/5-1` and strictly raises the
worst-mode coefficient threshold; an order-adaptive target-centred version is
a strict finite-predicate weakening of the current boundary criterion and
conditionally implies V1 word by word. Exact grid and `q=10` directional
separators certify those finite comparisons. No literature check or actual-π
cancellation estimate is supplied, so T139's primitive-sum gap and V1 remain
open.

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

If there are `k_j -> infinity` and nonempty consecutive selected blocks of the
exact decimal orbit with

```text
D_(k_j) / k_j -> 0,
```

then every fixed-depth cell law on those blocks converges in total variation to
uniform, so the selected empirical measures converge to Haar and V1 follows.
The finite stationarization inequality in the entropy note gives this directly
from exact digit overlap and endpoint control. The older support-size argument
also remains valid: sublinear deficit forces the machine-checked factor-entropy
limit to equal its maximum, and
[`T1CanonicalEntropy.lean`](TheoryLib/PiPositiveDecimalFactorEntropy/T1CanonicalEntropy.lean)
then gives V1.

This criterion does not require every cell to be occupied at any displayed
moving scale and gives no first-occurrence rate. Every fixed word occurs in
every sufficiently large stage `j`, but those stages are arbitrarily late in
the decimal expansion only if their starting indices tend to infinity. The
stationarization statement is restricted to canonical `10^k` meshes,
consecutive blocks, and exact times-ten dynamics; it does not cover arbitrary
meshes or pseudo-orbits. No such entropy estimate is proved for π.

An audited [`sharp forbidden-word entropy gap`](knowledge/pi/results/intermediate/20260824-sharp-forbidden-word-entropy-gap.md),
also only a `proof sketch`, shows uniformly that the constant word `0^r`
maximizes length-`k` avoidance counts. Its recurrence has Perron root `rho_r`,
giving the sharp global scalar threshold `log(rho_r)/log(10)` and an exact
boundary stream attaining it while omitting `0^r`. This strictly lowers T1's
numerical entropy threshold for `r>=2`, but is not a proved strict π-predicate
separator. A finite selected-block inequality retains the endpoint proportion
and binary-mixture slack; its length-free form upgrades `D_(k_j)/k_j -> 0` to
simultaneous coverage through
`r_j=floor(log_10(k_j/(D_j+1)))-1 -> infinity`. Single-word automata and prior
art predate this refinement, and no π entropy estimate or V1 theorem follows.

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

A newer [`uniform-integrability consumer`](knowledge/pi/results/intermediate/20260824-uniform-integrability-haar-frontier.md)
has status `proof sketch`. It replaces bounded entropy by the still weaker
requirement that cells carrying an arbitrarily large multiple of the mean
occupancy contain a uniformly vanishing fraction of visits. The Haar argument
is sound and collision bounds imply this tail condition. The exact decimal
de Bruijn construction from the entropy note has bounded entropy deficit and
hence uniform integrability while its normalized second moment diverges, so it
also certifies strictness inside exact times-ten dynamics. On canonical meshes,
UI implies sublinear entropy deficit, and an exact-global de Bruijn separator
shows that implication is strict: the moving-scale densities fail UI maximally
while all fixed-depth laws stationarize. This comparison does not extend to
arbitrary meshes or pseudo-orbits. No fixed-pi tail or entropy estimate is
known.

The audited sparse-decimal construction
`alpha=sum_j 10^(-j*2^j)` shows that effective irrationality cannot supply this
tail estimate by itself. It satisfies `IrrationalityMeasureBelow alpha B` for
every `B>3` and an explicit exponent-`4` effective bound, yet every moving-mesh
selection fails UI. T126 machine-checks the local zero-window concentration
lemma; the full construction remains `proof sketch`.

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

1. **Uniform integrability:** the two-level moving-mesh occupancy-tail bound;
2. **Entropy:** selected `10^k`-cell laws with
   `k * log 10 - H_k = o(k)` along unbounded `k`;
3. **Fourier:** the boundary-matched wordwise signed estimate, or the stronger
   machine-checked Jackson directional premise;
4. **Bounded entropy / collision:** a uniformly bounded cell entropy deficit,
   or the stronger moving-mesh collision bound, giving Haar block limits.

For arbitrary moving meshes, uniform integrability remains the weakest retained
Haar premise. For exact canonical decimal meshes, sublinear entropy deficit is
strictly weaker and already forces Haar block limits. The boundary kernel is
the weakest currently audited direct Fourier consumer. All pi-specific inputs
remain unproved; this entropy strengthening supplies no T128/T124, BBP, or
carry-flow estimate.

Equivalences, exact rational normal forms, recurrence packaging, finite digit
experiments, and representation-only lemmas are infrastructure, not frontier
progress, unless they produce one of these estimates, strictly weaken a
sufficient premise with a checked separator, or decisively falsify a live route.

```text
fixed-π sublinear canonical entropy deficit ─→ Haar ─→ V1

fixed-π bounded entropy / collision + dynamics ─→ Haar ─→ V1

fixed-π boundary directional cancellation ─────→ finite hits ─→ V1
```

Every fixed-π premise displayed above remains open.
