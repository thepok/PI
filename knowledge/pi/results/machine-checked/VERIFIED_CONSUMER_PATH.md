# Shortest verified consumer path

Claim status: the cited Lean implications are `machine-checked`; their
actual-π arithmetic premises are unproved.

```text
actual-π target-signed estimate
  -> T189 fresh child surplus at larger horizon
  -> T178/T176 signed predecessor transport
  -> T148/T153/T156 prescribed cylinder hit
  -> viable branching / word coverage
  -> V1
```

Key Lean modules:

- [`T148`](../../../../TheoryLib/PiQuantitativeBlockHitting/T148T148ImprovedPrimitiveBoundaryConsumer.lean): complete primitive boundary sum to the boundary-kernel hit consumer.
- [`T153`](../../../../TheoryLib/PiQuantitativeBlockHitting/T153T153BoundaryRootGridNaturalConsumer.lean) and [`T156`](../../../../TheoryLib/PiQuantitativeBlockHitting/T156T156BoundaryNaturalThresholdClosure.lean): natural-horizon prescribed-cylinder closure for `q=10^k`, `k≥3`.
- [`T172`](../../../../TheoryLib/PiQuantitativeBlockHitting/T172T172PositiveLeftExtensionTransport.lean) and [`T176`](../../../../TheoryLib/PiQuantitativeBlockHitting/T176T176SignedBlockBellmanTransport.lean): exact parent-to-child transport and signed surplus.
- [`T177`](../../../../TheoryLib/PiQuantitativeBlockHitting/T177T177PredecessorDigitDFT.lean)–[`T179`](../../../../TheoryLib/PiQuantitativeBlockHitting/T179T179PredecessorLagOneCorrelation.lean): digit DFT and literal predecessor-digit/suffix correlation.
- [`T189`](../../../../TheoryLib/PiQuantitativeBlockHitting/T189T189SignedHorizonSectorBridge.lean): exact fresh-horizon sector bridge and one-sided child-surplus theorem.
- [`T190`](../../../../TheoryLib/PiQuantitativeBlockHitting/T190T190ComplementaryRankAlignment.lean): deterministic same-digit alignment from complementary rank information.
- [`T191`](../../../../TheoryLib/PiQuantitativeBlockHitting/T191T191CentralBoundaryKernelFloor.lean): uniform positive central boundary-kernel floor; this is the first machine-checked analytic rung of the adaptive unit-block seed, not a natural-horizon theorem.

T189 is the fixed consumer for the present research cycle. T190 is optional:
use it only if independent π arithmetic naturally provides its rank premises.
Neither theorem estimates the actual-π correlation. A single coherent
predecessor ray is not yet V1; it only covers factors of one selector word.
