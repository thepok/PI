# Shortest verified consumer path

Claim status: the cited Lean implications are `machine-checked`; their
actual-π arithmetic premises are unproved.

```text
actual-π target-signed estimate
  -> T189 positive child surplus at natural horizon Q=10q
  -> elementary positivity of the primitive boundary sum
  -> T156 prescribed child-cylinder hit
```

This is the shortest verified one-step consumer.  T178/T176 form a separate
fixed-horizon recursive-selection package; no current Lean declaration
composes that package to V1 or preserves the natural diagonal.  Iterating
selected children still requires viable branching or a proof that the
selector word contains every finite word.  One coherent ray alone is not V1.

Key Lean modules:

- [`T148`](../../../../TheoryLib/PiQuantitativeBlockHitting/T148T148ImprovedPrimitiveBoundaryConsumer.lean): complete primitive boundary sum to the boundary-kernel hit consumer.
- [`T153`](../../../../TheoryLib/PiQuantitativeBlockHitting/T153T153BoundaryRootGridNaturalConsumer.lean) and [`T156`](../../../../TheoryLib/PiQuantitativeBlockHitting/T156T156BoundaryNaturalThresholdClosure.lean): natural-horizon prescribed-cylinder closure for `q=10^k`, `k≥3`.
- [`T172`](../../../../TheoryLib/PiQuantitativeBlockHitting/T172T172PositiveLeftExtensionTransport.lean) and [`T176`](../../../../TheoryLib/PiQuantitativeBlockHitting/T176T176SignedBlockBellmanTransport.lean): exact parent-to-child transport and signed surplus.
- [`T177`](../../../../TheoryLib/PiQuantitativeBlockHitting/T177T177PredecessorDigitDFT.lean)–[`T179`](../../../../TheoryLib/PiQuantitativeBlockHitting/T179T179PredecessorLagOneCorrelation.lean): digit DFT and literal predecessor-digit/suffix correlation.
- [`T189`](../../../../TheoryLib/PiQuantitativeBlockHitting/T189T189SignedHorizonSectorBridge.lean): exact fresh-horizon sector bridge and one-sided child-surplus theorem.
- [`T190`](../../../../TheoryLib/PiQuantitativeBlockHitting/T190T190ComplementaryRankAlignment.lean): deterministic same-digit alignment from complementary rank information.
- [`T191`](../../../../TheoryLib/PiQuantitativeBlockHitting/T191T191CentralBoundaryKernelFloor.lean): uniform positive central boundary-kernel floor; this is the first machine-checked analytic rung of the adaptive unit-block seed, not a natural-horizon theorem.
- [`T192`](../../../../TheoryLib/PiQuantitativeBlockHitting/T192T192PrimitiveValuationShells.lean): exact one-time primitive atom and decimal-valuation shell decomposition, including the retained central zero-shell margin; positive shells and natural-horizon accumulation remain open.
- [`T193`](../../../../TheoryLib/PiQuantitativeBlockHitting/T193T193PositiveValuationShellAggregate.lean): complete positive-shell aggregate, central primitive-atom floor and native T176 unit-block surplus; actual-pi recurrence and natural-horizon accumulation remain open.
- [`T194`](../../../../TheoryLib/PiQuantitativeBlockHitting/T194T194CentralPiReturnSeed.lean): using only the machine-checked theorem `irrational_pi`, an unprescribed actual-π central return feeds the T193 unit-block surplus at every decimal scale, without a timing bound. Under the additional explicit external premise `IrrationalityMeasureBelow pi 8`, after a premise-dependent onset one can choose `q+1<=n<10q`; the literal predecessor digit then lifts the same centered coordinate to a child-scale unit at time `n-1`, with surplus `>3q/2`, inside the exact T189 fresh block. Discharge of the quantitative premise remains external. This is same-child transport of one atom, not a prescribed target, a sign for the whole fresh block, or a coherent natural-horizon ray.
- [`T198`](../../../../TheoryLib/PiQuantitativeBlockHitting/T198T198MachinBracketPack.lean): exact Machin 3/7 strict brackets, endpoint convergence, the decimal-cylinder bridge, and `machinMC0_iff_piCW0` (`MC0 ↔ CW0`) are machine-checked.
  This is a representation-level equivalence and proves neither side; the Archimedean-lift obstruction remains unchanged.
- [`T199`](../../../../TheoryLib/PiQuantitativeBlockHitting/T199T199BBPShadowPack.lean): exact base-10 BBP defect/shadow bounds, scalar monotonicity and convergence, affine fixed-point conjugation, the two one-sided approach equivalences, and `bbp10_soh0_iff_piCW0` (`SOH⁰_{BBP,10} ↔ CW0`) are machine-checked.
  These are representation-level results and prove neither CW0 nor CW9; the Archimedean-lift obstruction remains unchanged.
- [`T200`](../../../../TheoryLib/PiQuantitativeBlockHitting/T200T200BaileyCrandallCoboundary.lean): the Bailey--Crandall coefficient integral and BBP-term bridge, positive decaying analytic correction, exact coboundary, and `Y n + tau n = 16^(n-1) * pi` for `n≥1` are machine-checked.
  These are representation-level identities and prove no base-16 density or digit occurrence; the moving-modulus Archimedean-lift obstruction remains unchanged.
- [`T202`](../../../../TheoryLib/PiQuantitativeBlockHitting/T202T202RamanujanTwoAdicRamp.lean): the central-binomial and central-cube two-adic valuations, binary digit-sum carry law, exact denominator-exponent increment, strict monotonicity, and prefix ramp are machine-checked.
  These are representation-level denominator facts and supply neither the required positive small tail nor a target hit; the Ramanujan/Erdős carry-killing obstruction remains unchanged.
- [`T204`](../../../../TheoryLib/PiQuantitativeBlockHitting/T204T204ConstantRunBound.lean): the bridge from `IrrationalityMeasureBelow` to the fixed-exponent interface and the eventual nine-run bound are machine-checked. The zero-run eventual bound is still open in Lean; the combined zero-or-nine and published-π consumers are machine-checked only in `HypothesisForms`, with the missing zero-run contract (and, for the numerical specialization, its upstream contract and the published exponent input) left explicit and undischarged.
  These bounds constrain a run if it occurs and prove no zero run, nine run, constant-word target, or nonconstant word occurrence.
- [`T206`](../../../../TheoryLib/PiQuantitativeBlockHitting/T206T206EndpointBridge.lean): the greedy stream evaluates to its representative, any distinct equal-value avoiding expansion is localized to a power-of-ten rational endpoint, and the discharged corollary `CWord_symmDiff_KWordReal_subset_E10` places the full greedy/existential avoidance-set symmetric difference inside that endpoint set.
  This resolves the first endpoint bridge only; the prefix-cylinder analogue is outside T206, and endpoint localization proves no word occurrence or density statement.

T189 is the fixed consumer for the present research cycle. T190 is optional:
use it only if independent π arithmetic naturally provides its rank premises.
Neither theorem estimates the actual-π correlation.  The first genuine input
must independently lower-bound the complete target- and digit-preserving
fresh block in T189; its threshold is an exact rewrite of child surplus, not a
source of π arithmetic.  T179 likewise supplies only the exact correlation
identity, not an estimate.
