# π decimal disjunctivity: current frontier

Status: `conjecture`

Last audited: 2026-08-27 UTC

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
provide wordwise control because `h=q` survives. At commit `c917e3d`, T147
machine-checks the exact decimal-layer budget partition and the actual-pi
endpoint theorem
`primitiveBoundaryEndpoint_norm_lt_two_budget_sub`:
`|B|<2E-7/500` for every `k>=3` and all targets and horizons. Thus the literal
endpoint defect contribution improves from `4E/N` to `(4E-7/250)/N`. At commit
`c06952b`, T148 machine-checks the strict transport
`directionalBoundaryDefect_lt_primitive_add_improvedEndpointBudget`, namely
`D<R` for this improved right-hand side, and the hit consumer
`piOrbit_hit_of_improved_primitiveBoundary_smallness_pow_ten`: the non-strict
premise `R<=boundaryZeroCoefficient` implies the target-cylinder hit. This is
still only an endpoint-sector contraction and conditional consumer: the
endpoint-free singleton and primitive/off-diagonal cancellation estimates
remain open. It proves neither T124 nor V1 and supplies no exact π-orbit
logical separator.

A new audited
[`proof sketch`](knowledge/pi/results/intermediate/20260826-papersearch-primitive-martingale-frontier.md)
uses the complete T139 primitive polynomial rather than separate rays. Since
all retained frequencies are nondivisible by ten, its real part is an exact
reverse martingale difference under Lebesgue measure; its variance is at least
`9/(640q)`, and a source-checked functional LIL gives positive excursions for
almost every starting point. T148/T156 also give the clean fixed-pi consumer
that one target-dependent horizon `N>=q` with nonnegative complete primitive
sum forces the target hit. The metric theorem does not select pi, so this
isolates rather than closes the remaining pointwise arithmetic boundary.

### Current signed-bridge research program

The next cycle no longer treats additional BBP, Machin, p-adic,
irrationality, or generic-dynamical structure as the primary route.  Existing
results from those families repeatedly lose the target-signed Archimedean
information of the actual pi orbit.  The provisional summit of the new
pi-specific bridge theory is

```text
forall k >= 3, forall A < 10^k, exists N >= 10^k:
  Re (primitiveBoundaryFourierSum (10^k) A N) >= 0.
```

T148/T156 give its short checked consumer path.  An explicitly stronger or
shorter-to-V1 theorem is welcome.  The immediate research objective is the
first rigorous new lemma that genuinely *produces* target-signed Archimedean
information for pi: a signed invariant, recurrence, drift/energy structure,
or a special pi-arithmetic estimate controlling one. PaperSearch is used early
for ingredients. Averages, almost-everywhere results, denominator or period
data, local congruences, unsigned energy, and rational shadows do not qualify
without a proved mechanism transferring their information to the required
target sign.

The directed T169 follow-up records a narrow
[`proof sketch`](knowledge/pi/results/negative/20260826-t169-terminal-common-modulus-prime-pulse-no-go.md):
an exact terminal-common-denominator embedding exists, but infinitely many new
prime coordinates are zero throughout the earlier block and nonzero only at
its endpoint. They therefore do not create the hoped-for long
bounded-conductor trace family. Persistent older factors and their full
complementary CRT coupling remain open.

A first finite signed benchmark now survives independent replay:
[`20260827-finite-signed-parent-334-certificate.md`](knowledge/pi/results/intermediate/20260827-finite-signed-parent-334-certificate.md)
records the directed-interval `experiment`

```text
Re (primitiveBoundaryFourierSum 1000 334 10000) > 47539 / 2500.
```

This is actual-pi, prescribed-target Archimedean sign information for one
finite triple `(q,A,N)`, evaluated with the complete endpoint. It does not add
a new digit occurrence—the certified prefix already contains `334`—and it
does not propagate to unbounded scales. T170 machine-checks the first
100-decimal-place fixed-point Machin enclosure. T171 then introduces a compact
integer-row checker, and T173 successfully uses it to machine-check the full
10,015-fractional-place pi cylinder needed by the finite score program (14,341
rows, about 41 seconds and 9.6 GB peak memory in the independent focused
audit). The remaining finite trust step is therefore no longer decimal-prefix
generation but a compact directed trigonometric score certificate.

The complementary scale-transport rung is now machine-checked in T172. For
every `q>=1000`, all coefficient defects are strictly positive, their total
mass is `<21/(10q^2)`, and some left child satisfies the explicit signed lower
bound

```text
score(10q,A+dq,N) >= (score(q,A,N) - N*21/(10q^2))/10.
```

Composed with the finite `(1000,334,10000)` experiment, this yields the
audited [`fixed-horizon signed predecessor ray`](knowledge/pi/results/intermediate/20260827-fixed-horizon-signed-predecessor-ray.md): coherent existential targets have positive complete primitive scores at every decimal scale. This is genuine target-phase preservation, but the horizon remains `N=10000`; only the first child is at natural scale, and the construction neither prescribes the child digit nor supplies an unbounded hit consumer. The live arithmetic gap is therefore horizon-growing signed control or a one-sided estimate for a named nonzero predecessor-digit character sector.

T176 strengthens this to arbitrary finite blocks with a strict max-plus
potential `7/(3q)`. T177 then machine-checks the exact ten-point
[`predecessor-digit DFT`](knowledge/pi/results/intermediate/20260827-predecessor-digit-dft-frontier.md): its zero sector is T172, the nine nonzero sectors reconstruct every specified child, and their real corrections sum to zero over the digits. This precisely names the prescribed-child gap without pretending that mean zero supplies its sign.

T178 machine-checks the conditional infinite recursive selector itself,
including coherent targets and the explicit lower bound at every scale; the
experimental finite root inequality remains an explicit premise. T179 now
machine-checks the next arithmetic normalization: every nonzero digit sector
is exactly an actual-pi lag-one correlation between the predecessor digit
character and a suffix-centered finite kernel with the literal boundary
coefficients. No favorable sign is inferred. The live frontier is a one-sided
estimate for this joint digit/suffix correlation, or horizon-growing signed
control strong enough to bypass it.

T189 makes the horizon-growth alternative exact. Subtracting T177/T179 at
`N <= H` gives, for every child digit `d`,

```text
10 * Re (Z_d(H) - Z_d(N)) = Delta_0(N,H) + Xi_d(N,H),
```

where `Delta_0` is the parent plus left-extension-remainder increment and
`Xi_d` is one literal target-sensitive lag-one correlation over precisely the
fresh indices `N <= n < H`. Its final theorem turns the corresponding
one-sided sector inequality directly into positive T178 surplus at `H`; it
does not assert that inequality. At the first root-to-child experiment
`(q,A,N,H,d)=(1000,334,10000,100000,3)`, the parent/zero sector is negative,
so the coarse transport is falsified, while the digit-3 nonzero sector is
about `43` and easily clears the sufficient threshold (between about `-2.02`
and `-1.64`, depending on the bounded remainder; `Xi_3 > -1.6412` is the
uniform sufficient choice from that bound). This numerical statement is
only an `experiment`. The atomic research target is now a rigorous lower bound
for that exact `Xi_3` fresh-block expression and then a mechanism repeating it
at unbounded scales.

A tight adjacent fixed-point separator now limits the permitted input. On the
decimal orbit `x_n=1/3`, which stays below and never enters the child cylinder
`[0.3334,0.3335)`, the exact digit-3 T189 summand has directed enclosure
`K<-0.034`; 49 fresh steps already give `Xi_3<-1.6749`, below the robust
sufficient threshold. Finite pi-prefix data, the decimal recurrence, and even
bare transcendence are compatible with such a fixed tested block. The next
lemma must use a stronger pi-specific joint transition property, not merely
exclude a target hit or a rational tail.

The earlier finite-cylinder horizon separator also admits a repaired
Roth-optimal upgrade: append a base-ten Thue--Morse `{0,1}` tail to the T173
prefix. The root sign survives only by the recorded Lipschitz margin, while
every sufficiently deep left descendant still ends in `334` and is absent.
The resulting number is transcendental with irrationality exponent exactly
`2`. This remains a `proof sketch` because the T146--T156 endpoint chain is
not yet parameterized away from pi, but it closes finite irrationality measure
as a possible source of the missing signed bootstrap.

Machin remainder positivity is now excluded just as sharply. The complete
T189 nonzero sector is an exact target-centered lacunary polynomial at
`exp(2*i*pi^2)`, and T169 transfers it to the moving Machin carrier with error
below `10^-17963` at the current block. Nevertheless the full-sector response
to a fixed positive phase increment assumes both signs. Thus essentially all
of the observed sign is already in the exact rational carrier arithmetic;
the positive arctangent tail cannot manufacture it.

The finite root certificate remains a bounded checkpoint. T187's ten-point
production shard takes about 10.3 minutes and 9.1 GB; deterministic replay and
a focused one-orbit audit project at least about 134 CPU-hours and roughly
113 GB of `.olean` output for the complete 10,000-point payload. No full
payload will be generated with the present checker. This is a cost boundary,
not mathematical progress and not evidence against the signed bridge.

The independently audited
[`terminal root-grid contraction`](knowledge/pi/results/intermediate/20260825-t139-terminal-root-grid-contraction.md)
is now `machine-checked` through T149--T153 and T156. T149's
`Theory.PiDigits.BoundaryRootGridProjection.rootGridProjection_eq` and
`Theory.PiDigits.BoundaryRootGridProjection.boundaryLayerPolynomial_eq_divisible`
express each terminal divisibility layer as an exact grid average of the T128
kernel. T150's
`Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_193` and
`Theory.PiDigits.BoundaryKernelFloors.boundaryMinorant_re_gt_neg_eight_mul_sq_div`,
followed by T151's
`Theory.PiDigits.BoundaryProjectedLayerFloor.divisibleBoundaryPolynomial_re_gt`,
supply the pointwise projected-layer floor. T152 then proves
`Theory.PiDigits.BoundaryRootGridEndpoint.primitiveBoundaryEndpoint_re_gt_neg_two_budget_add`:
`Re B > -2E + 52909/200000` for every `k>=3`, target, and horizon. At `N=q`,
T153's
`Theory.PiDigits.BoundaryRootGridNaturalConsumer.piOrbit_hit_of_rootGrid_primitiveBoundary_ge`
machine-checks the exact scale-dependent conditional consumer. T156 now
machine-checks the scalar closure: its
`Theory.PiDigits.BoundaryNaturalThresholdClosure.rootGridNaturalThreshold_lt_neg_861`
proves the exact T153 threshold is strictly below `-861/1000`,
`piOrbit_hit_of_primitiveBoundary_ge_neg_861` turns the corresponding
non-strict primitive lower bound into a hit, and
`primitiveBoundary_lt_neg_861_of_piOrbit_misses` records the strict
missed-cylinder contrapositive. The stronger AV endpoint saving and its
`-8669/10000` consequence remain `proof sketch`. No actual-pi estimate proving
such a signed primitive lower bound is known, so the primitive/off-diagonal
frontier and V1 remain open.

The proposed universal natural horizon is now retired. An exact rational
Machin-prefix `experiment` certifies that among π's first 1000 length-three
windows only 634 are distinct and 366 are missing, including `002`; the
initial and terminal two-digit blocks are `14` and `38`. The accompanying
[`de Bruijn no-go`](knowledge/pi/results/negative/20260825-natural-horizon-de-bruijn-no-go.md)
shows at `proof sketch` level that coverage of all `q=10^k` words by exactly
the first `q` windows would force those endpoint blocks to agree. Combining
the unformalized finite prefix certificate for the missed `A=2` cell with the
machine-checked T153--T156 implication gives, only at `proof sketch` status for
this actual instance,
`Re Z_(1000,2)(1000) < R_1000 < -861/1000`. Thus the proposed universal `N=q`
route is mathematically falsified for the actual π orbit, while only the
generic conditional implication and contrapositive are machine-checked. This
does not threaten V1: target-dependent witnesses at later horizons, and
signed π-specific estimates at such horizons, remain live.

The [fixed-degree no-go](knowledge/pi/results/negative/20260824-fixed-degree-transcendence-measures-do-not-force-decimal-dispersion.md)
now also has an exact fixed-target T139 form: affine
digit recoding produces, for every prescribed cylinder, a transcendental
countermodel with simultaneous optimal fixed-degree repulsion whose complete
primitive polynomial fails the T139 threshold at every horizon. Arbitrary
finite full-polynomial van der Corput recurrences stay at nonzero primitive
frequencies, so lower Diophantine repulsion on those phases alone is closed;
actual-π signed/off-diagonal correlation remains the live boundary.
The same note also closes, at every degree and height, the scale-wise uniform
cover of an entire forbidden-word language by polynomial sublevel sets at the
explicit all-degree Nesterenko--Waldschmidt π-measure scale; a π-specific
nonuniform remainder construction is not affected.

A [canonical finite BBP experiment](knowledge/pi/results/negative/20260824-canonical-bbp-singleton-prefix-no-go.md)
retires T139-compatible all-prefix bounds for the singleton core. A subsequent
audited `proof sketch` in the singleton-ray barrier upgrades its termwise part:
at `q=100`, one fixed target has actual-π singleton increments below `-1/50`
arbitrarily late, so deleting any finite transient cannot recover an eventual
T139-compatible termwise bound for every target. Prefix compensation,
compensation by the other primitive rays, T139, and V1 remain open.

A `proof sketch`
[`endpoint-free singleton-ray barrier`](knowledge/pi/results/negative/20260824-endpoint-free-singleton-ray-barrier.md)
shows why decimal-ray compression is only preprocessing: the singleton belt
retains coefficient mass at least `27/160` for T139, `27/200` at mixed order
`4q/5`, and `9/400` for every positive-zero mixed order, while the zero-mode
margin is only `O(1/q)`. Thus controlling colliding rays but leaving singleton
rays at phase-blind coordinatewise caps still requires `O(1/q)` cancellation.
The exact surviving target is a lag-`k`, target-dependent signed correlation
of the actual decimal π orbit; no estimate for it is presently known.  A
frequency-diagonal Gram or weighted large-sieve certificate cannot cross the
T139 threshold: it has an `Ω(q⁻¹/²)` floor at every horizon, above the
`O(q⁻¹)` margin, so any live quadratic route must retain target-specific signed
or off-diagonal actual-π structure.  Exact BBP carry cancellation further
shows that the positive selected tail perturbs the target-labelled rational
core by only `min(O(q), O(log q))`, uniformly in the horizon, so it cannot be
the extensive cancellation source when `N/(qB_(q,k)) → ∞`; the rational core
and the remaining rays stay open.  The
[`sampled-quotient carry corollary`](knowledge/pi/results/negative/20260824-bbp-universal-grid-period-shadow-no-go.md#sampled-quotient-carry-corollary)
also shows that the actual BBP tail exceeds one reduced-denominator cell at
cofinally many even depths, so denominator granularity alone cannot remove
the quotient carry.  Conditional on the existing explicit
`IrrationalityMeasureBelow Real.pi 8` premise, the same note specializes
T35 through T104/T106 to prove eventual equality of the sampled BBP and pi
prefix floors, hence eventual zero carry; cofinal carry compensation is
retired.  This is not distribution or cancellation: the signed T139 quotient
core and V1 remain open.

T141 now proves an additional exact property of the actual reduced sampled
BBP rational: for every `m >= 8`, `10^m * bbpPartial (7*m)` has denominator
prime to five and numerator divisible by `5^ceil(m/2)`. The
[`machine-checked record`](knowledge/pi/results/machine-checked/t141_scaled_bbp_five_adic_numerator_20260825.md)
retains only this audited arithmetic statement. It supplies no control of the
remaining Archimedean phase, primitive cancellation, T139, or V1.

The exact core of the independently audited delayed phase transfer is now
`machine-checked` in T154--T155. Under the exact logarithmic burn-in
hypothesis at every summed index, T154 proves `5^k | P_(n+k)`, removes this
factor from the actual reduced numerator, and identifies the delayed
truncation with denominator `2^k D`. T155 identifies its literal phase and
proves, for
`|h| < 2*10^k`, the pointwise and arbitrary-horizon transfer bounds,
including

```text
e(h * 10^n * B_(n+k)) = e_(2^k D_(n+k))(h U_(n+k)).
```

Replacing an arbitrarily long delayed pi-orbit sum by these actual numerator
phases costs less than
`4*pi*rho^(n+k)/(1-rho)`, independently of the horizon. The denominator
`2^k D_m` is five-free but need not be the reduced phase modulus. The
[`delayed numerator-phase transfer`](knowledge/pi/results/intermediate/20260825-delayed-bbp-numerator-phase-transfer.md)
therefore narrows the live object to target-signed joint/off-diagonal sums in
the varying actual `(U_m,D_m)`; it is not the whole T139 consumer and proves no
cancellation or V1 implication. The explicit formula
`nu_k=min {n : 5^n >= 224k}`, its bound `nu_k<=4k`, the deduction of the Lean
logarithmic hypothesis from `n>=nu_k`, and the predecessor/residue CRT identity
remain `proof sketch`. Its companion
[`unpaired-alias and two-marginal no-go`](knowledge/pi/results/negative/20260825-unpaired-alias-and-two-marginal-blindness.md)
shows that bare digit characters retain a constant natural-window alias
residual and that even perfectly uniform separate `2^k` and `5^k` marginals
can omit a joint target. Those abstract separators do not model BBP joint
dynamics, which remains the live boundary.

T159 now `machine-checks` the exact top-band subset of the
[`reciprocal-prime adaptation`](knowledge/pi/results/intermediate/20260825-delayed-bbp-numerator-phase-transfer.md#exact-t159-top-band-subset).
For every prime `p>5` with `56*m+6<2*p`, the first-family hypotheses
`p=8*i+1` and `p<=56*m+1`, and separately the third-family hypotheses
`p=8*i+5` and `p<=56*m+5`, both give
`PrimeCongruent p (p*scaledBBPRat m) (4*10^m)` and
`padicValRat p (scaledBBPRat m)=-1`. The exact declarations are
`Theory.PiDigits.T159ExactBBPTopPrimeProjection.scaledBBPRat_topPrimeProjection_one`,
`scaledBBPRat_topPrimeProjection_three`,
`scaledBBPRat_topPrime_val_eq_neg_one`, and
`scaledBBPRat_topPrimeThree_val_eq_neg_one`; the corresponding unscaled
prefix projections are `bbpPartial_topPrimeProjection_one` and
`bbpPartial_topPrimeProjection_three`.

Beyond this top-band subset, an independently audited `proof sketch` adapts
the already known general `p^2` localization and high-prime skeleton to the
T154--T155 delayed phases:
two clean quotient profiles `C_+` and `C_-`, with `C_+(infinity)=pi` and the
new-to-this-frontier identity `C_-(infinity)=-pi`, give each eligible local
component of `e_(2^k D_m)(h U_m)` explicitly. That local factor is
target-independent, but only inside an exact product with unresolved
complementary and `q`-primary target factors; no cancellation follows from
either factor alone.
The same audit records the geometrically normalized actual scalar forcing as
a strict Hausdorff moment sequence and its seven slices as TP2, a negative
diagnostic for scalar differencing rather
than a signed/off-diagonal, T139, or V1 estimate. General `C_+`/`C_-` and
middle-band formulas, endpoint corrections, the delayed `U_m` CRT phase, and
the Hausdorff/TP2 statements remain `proof sketch`; T159 proves none of their
cancellation conclusions.

The exact actual-BBP core recorded in the
[`T106--T141 phase-flexibility separator`](knowledge/pi/results/negative/20260825-t106-t141-five-adic-phase-flexibility-no-go.md)
is now `machine-checked` in T157--T158. T157's
`Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_five_val_eq` proves the
exact five-adic valuation at every sampled depth, including `m=0,1`;
`normalized_bbpPartial_five_congruent`,
`scaledBBPFiveUnit_five_congruent`, `scaledBBPFiveUnit_five_val`, and
`scaledBBPFiveUnit_ne_zero` check the normalized residue, explicit leading
unit with `secondaryPoleIndicator`, and its unit corollaries. T158's
`Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_eq_scaledBBPRat_sub`
and `fiveShellLog_succ_eq_or` check the forcing identity and shell dichotomy;
`sampledBBPForcingRat_five_val_eq_of_shell_jump`,
`sampledBBPForcingRat_five_val_eq_of_secondary_activation`, and
`sampledBBPForcingRat_five_val_ge_of_quiet_shell` check the two exact pulse
cases and the quiet-shell gain. T163 separately machine-checks the actual
even-depth dyadic conductor: `scaledBBPRat_two_val_even` gives exact two-adic
order `-27*m`; `scaledBBPRat_even_two_primary` gives reduced denominator
two-primary part `2^(27*m)` and an odd numerator; and
`scaledBBPRat_even_tail_lt_spacing` together with
`scaledBBPRat_even_unique_immediate_lift` places the sampled BBP rational as
the unique point of that lift lattice immediately below `10^m*pi`. The
growing-modulus rational shadow and the negative separator remain `proof
sketch`: positive T106-form forcing, exact coboundary and geometric-tail
control, this now-verified dyadic scale, and actual rational-value congruences
through `5^(m-1)` still admit strictly increasing shadows of a word-omitting
decimal orbit, but those shadows do not preserve a raw numerator or the
actual coupled numerator/odd-denominator and seven-term/four-pole structure.
None of T157--T158 or T163 supplies signed/off-diagonal cancellation, a
later-horizon estimate, T139, or V1.

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

Even optimal polynomial and algebraic repulsion at every fixed degree is
generically insufficient: an audited `proof sketch` constructs a
full-dimensional family inside the decimal \(\{0,1\}\)-Cantor set, whose exact
times-ten orbits have linear entropy deficit and maximally fail moving-mesh UI
([no-go note](knowledge/pi/results/negative/20260824-fixed-degree-transcendence-measures-do-not-force-decimal-dispersion.md)).

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
