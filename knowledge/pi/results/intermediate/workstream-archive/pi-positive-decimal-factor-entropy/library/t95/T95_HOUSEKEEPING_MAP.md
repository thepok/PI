# T95 housekeeping map

Status: exact mapping of scheduler-reported gaps to the accumulated accepted
library. This document makes no claim that the canonical positive-entropy
question is resolved.

## Canonical statement and scope

The immutable source is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`, SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
It was formulated locally on 2026-07-22 and has no external source URL.

Its canonical quantifiers require one fixed real `eta > 0` and one fixed
integer `N >= 1` such that every integer `n >= N` satisfies
`p_pi(n) >= 10^(eta*n)`. None of the mappings below proves that open fixed-pi
assertion. In particular, a conditional certificate is not reported as a
pi-specific conclusion, cyclic adjacency is not replaced by equality, and a
proof-sketch provenance artifact is not promoted to a checked theorem.

Each scheduler report below is interpreted independently. Existing public
declarations are imported, not renamed, restated, weakened, or removed.

## Exact gap map

### 1. T61 historical absence of periodic Vaaler infrastructure

Disposition: superseded by a public, kernel-checked implementation. The old
report correctly described an earlier certificate interface, but it does not
describe the current accepted module.

Accepted locator:
`knowledge_library/t61/T61VaalerAnalytic.lean`, SHA-256
`61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993`.

- `DecimalFactorComplexity.T61VaalerAnalytic.VaalerAnalyticCertificate` at
  lines 1873-1884 states the complete analytic certificate.
- `vaalerAnalyticCertificate_proved` at lines 1886-1892 proves it.
- `strictCentralIndicator_le_periodicVaalerMajorant` at lines 1711-1722 is the
  pointwise periodic majorization.
- `strictCentralIndicator_endpoint_pos` and
  `strictCentralIndicator_endpoint_neg` at lines 1838-1870 prove that the
  strict indicator excludes both endpoints.
- `periodicVaalerMajorant_endpoint_pos` and
  `periodicVaalerMajorant_endpoint_neg` at lines 615-663 prove that the
  majorant has value one at both endpoints.
- `exists_vaalerCoefficient_sign_transition` at lines 363-393 proves the
  sampled coefficient sign threshold.

The separate fixed-pi section begins at line 1894. Its sole unproved premise,
`SignedStructuredDenominatorPremise`, is defined at lines 2081-2085; T95 does
not discharge or hide that arithmetic premise.

### 2. T61 direct specialized implementation

Disposition: covered by the same public, kernel-checked T61 module and not
duplicated.

In addition to the declarations listed for report 1:

- `sum_secondDifference`, `sum_weighted_secondDifference`, and
  `cosine_secondDifference` at lines 904-967 provide finite telescoping and
  trigonometric infrastructure.
- `fejerCosineSum_mul_one_sub_cos` at lines 970-1002 is the exact finite Fejer
  cosine identity.
- `periodicVaalerMajorant_decomposition` at lines 1062-1224 gives the finite
  trigonometric decomposition.
- `periodicVaalerMajorant_nonneg` at lines 1682-1708 handles both generic
  points and sine-zero endpoint interpolation.
- `vaalerAnalyticClaims` at lines 1725-1737 packages majorization, endpoints,
  and the sign transition.

### 3. T63 absent original T43 workflow record

Disposition: covered only as exact accepted provenance, not as a mathematical
proof. No Lean theorem is claimed for this report.

The recovered file is
`knowledge_library/notes/t63/T43_AVERAGED_ORBIT_CORRELATION.md`, SHA-256
`7b71b5f9dc7003f0d2d47861ad399db88a0ffaf920d669a97fda092df407afed`.
The accepted T63 crosswalk
`knowledge_library/notes/t63/T63_AOC4_VAALER_CROSSWALK.md`, SHA-256
`9270f11c49df45e3c0716dbf653ccc53a332f553e859007054a35e52a6dc4efc`,
records at lines 13-18 that the exact T43 file was recovered from the
hash-addressed proof-ledger store after the original record disappeared. T43
labels itself a `proof sketch` and its `(AOC_4)` statement a `conjecture`.
Nothing from it is treated as proved here.

### 4. T65 eventual periodicity without SCC terminality

Disposition: covered by public, kernel-checked generic finite-graph theorems;
imported without duplication.

Accepted locator:
`knowledge_library/t65/T65RationalCoreCertificate.lean`, SHA-256
`6ee5b2a7e35405340fc82e4232582c743b820b89b9c5c73a9598e485b48bcba8`.

- `DecimalFactorEntropy.T65RationalCoreCertificate.RelaxedLiveSCCCriterion`
  at lines 38-39 drops exactly T46 terminality while retaining the internal
  simple-cycle condition.
- `infiniteWalk_reaches_source` at lines 72-80 and
  `cyclic_of_infiniteWalk_source_repeat` at lines 82-98 are the supporting
  finite-walk lemmas.
- `infiniteWalk_eq_of_simpleSCC` at lines 118-149 proves uniqueness of hidden
  walks that remain in one simple SCC.
- `infiniteWalk_eventuallyPeriodic_of_relaxedLiveSCCCriterion` at lines
  154-203 is the generic edge-walk theorem.
- `infiniteLabelLanguage_eventuallyPeriodic_of_relaxedLiveSCCCriterion` at
  lines 207-217 is its projected-label form.

### 5. T67 missing equality converse and explicit endpoint cases

Disposition: the absence of an equality converse is retained. The exact
checked conclusion is cyclic adjacency, and the later accepted T69 module
provides the explicit five-case infrastructure.

Checked dependency locator:
`TheoryLib/PiLacunaryNearReturnSparsity/T2NormalOrbitNearReturns.lean`, SHA-256
`1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174`.

- `DecimalFactorComplexity.NormalOrbitNearReturns.CyclicAdjacent` at lines
  177-179 is literally equality, predecessor, successor, wrap-predecessor, or
  wrap-successor.
- `nearReturn_implies_prefixLabels_adjacent` at lines 284-297 proves only this
  relation from a strict circular near return.

Accepted implementation locator:
`knowledge_library/t69/T69FiveCaseCharging.lean`, SHA-256
`43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9`.

- `DecimalFactorComplexity.T69FiveCaseCharging.EndpointCase` and
  `EndpointCase.Holds` at lines 32-47 expose all five cases.
- `classifyFive_holds` at lines 61-65 proves exhaustive classification under
  the exact cyclic-adjacency hypothesis.
- `classifyFive_tie_breaking` at lines 69-79 exposes deterministic priority
  guards, including both wrap cases.
- `collapse_classifyFive_holds` at lines 106-121 collapses the five cases to
  the three cyclic permutation relations without discarding endpoint wraps.

Thus T95 does not assert that a strict near return gives equal decimal blocks.

### 6. T69 arbitrary-sequence permutation-graph charging

Disposition: covered by public, kernel-checked declarations in the same T69
module and hash listed for report 5.

- `labelFiber`, `equalityComponentLoad`, and `finiteCodeGraph` at lines
  142-153 are generic for an arbitrary sequence `x : Fin L -> Fin q`.
- `finiteCodeGraph_card_eq_crossSum` at lines 156-179 proves the exact finite
  cross-sum identity.
- `finiteCodeGraph_card_le_equalityComponentLoad` at lines 183-199 proves the
  finite Cauchy-Schwarz bound for every label permutation.
- `uniformCharging` at lines 272-347 gives the resulting endpoint-safe
  arbitrary-sequence charging theorem.

### 7. T70 common primitive root and least positive period

Disposition: the T70 note remains a `proof sketch`, but its needed content was
subsequently formalized in the public, kernel-checked T72 module. T95 relies
only on T72's checked declarations.

Accepted locator:
`knowledge_library/t72/T72ProjectedPeriodicity.lean`, SHA-256
`d05450c90bfc2aff6567fc4c492575004e2dc96dc6a87fbb2aab4fcb12cd16e7`.

- `DecimalFactorEntropy.T72ProjectedPeriodicity.Graph.StreamPeriod` at lines
  508-509 defines a positive period of an infinite stream.
- `streamPeriod_iterate` and `streamPeriod_mod` at lines 511-528 provide the
  iteration and remainder lemmas.
- `least_streamPeriod_dvd` at lines 530-550 proves that a least positive period
  divides every other positive period.
- `exists_primitive_root_of_streamPeriod` at lines 554-594 constructs the
  least-period finite root, proves it primitive, reconstructs the stream, and
  proves divisibility of all other periods.

The note-level roadmap is
`knowledge_library/notes/t70/T70_PROJECTED_PHASE_EQUIVALENCE.md`, SHA-256
`ff9645d4effdd5a5b5dab38de782502b0dd0c47e0767d8b679d60532b71e8e86`;
it is not used as a proved premise.

### 8. T72 rotation-based primitive words and circular phases

Disposition: covered by public, kernel-checked declarations in the same T72
module and hash listed for report 7.

- `PrimitiveWord` at lines 44-46 is the finite rotation-based predicate: each
  nonzero phase shift has a position witnessing unequal symbols.
- `PrimitivePhaseCertificate` at lines 51-61 combines a positive primitive
  root with vertex phases, exact edge outputs, and one-step phase advancement.
- `primitivePhaseCertificate_iff_everyInternalProjectionEventuallyPeriodic`
  at lines 742-751 proves the exact SCC-local semantic equivalence.
- `PrimitivePhaseCertificate.period_le_card_state` at lines 802-864 supplies
  the finite search bound.
- `exists_boundedPhaseData_iff_everyInternalProjectionEventuallyPeriodic` at
  lines 911-924 packages the bounded certificate equivalence.

## Public import surface

`T95Housekeeping.lean` imports T61, T65, T69, and T72 and checks the public
declarations listed above. It introduces no aliases or replacement
declarations, so existing signatures remain unchanged and become available
transitively through one additive module. It also prints the axioms of the
checked theorem surface selected for T95 review.

## Scope

This delivery is housekeeping only. It proves neither C1 nor its negation,
does not upgrade T43 or T70 prose to evidence, does not create an equality
converse for strict near returns, and does not discharge T61's fixed-pi signed
structured-denominator premise.
