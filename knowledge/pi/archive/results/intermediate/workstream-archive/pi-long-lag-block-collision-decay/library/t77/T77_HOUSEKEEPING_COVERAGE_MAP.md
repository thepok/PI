# T77 housekeeping coverage map

Status: `machine-checked` applies only to the accepted Lean declarations named
below. This map adds no mathematical theorem. It records why duplicating any of
the eight telemetry items would be incorrect. The T25, T27, T30, and T33 prose
notes remain `proof sketch`; no claim unique to those notes is used as a proved
premise.

## Scope and canonical statement

The canonical source is the locally formulated problem
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`; it has no original
external source URL. Its checked SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question asks whether, for every real `s` with `0 < s < 1`, one
constant `C_s >= 1` works for all positive integers `m,N` in the ordered
long-lag estimate

```text
R_pi(m,N) <= C_s * (N + N^2 * 10^(-s*m)).
```

The weak cutoff is `|i-j| >= m`, pairs are ordered, and `C_s` may depend on
`s` but not on `m` or `N`. The question remains open. The sparse-Fourier
objects below concern the residual sibling A12 and do not replace the
canonical collision count.

## Checked module pins

The mappings below refer to these accepted modules and checked source hashes:

| Item | Module | SHA-256 |
|---|---|---|
| T16 | `TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD` | `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec` |
| T29 | `TheoryLib.PiLongLagBlockCollisionDecay.T29T29WidthWeightedSquareFunction` | `2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358` |
| T31 | `TheoryLib.PiLongLagBlockCollisionDecay.T31T31CrossBlockAlmostEverywhere` | `535a43fc06ac84d9b61760300c642fc05dbd797dc7cedb25f0ed30156bf10380` |
| T32 | `TheoryLib.PiLongLagBlockCollisionDecay.T32T32AllBlockFixedPiRange` | `3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc` |
| T34 | `TheoryLib.PiLongLagBlockCollisionDecay.T34T34CancellingRepunitIncidence` | `720e5ee33f63226c560aee19751421fa383448e0aef45602c5eaf9a10f52778c` |
| T49 | `TheoryLib.PiLongLagBlockCollisionDecay.T49T49PrimitiveIncidenceAssembly` | `65776873b77b51df5639e7546db7319f14ce4b76259d3faa19732744e6e13cdb` |

All declaration names below have prefix
`Theory.PiDigits.LongLagBlockCollisionDecay`.

## Gap dispositions

### 1. T16: sparse-decimal rational neighbors and component separation

Disposition: already machine-checked in T16. The public implementation is:

- `T16.decimal_upper_sum_eq_zero`, including the explicit `q < J` branch.
- `T16.proximity_component_sum_eq_zero`, separating every proximity-graph
  component of a bounded-coefficient zero decimal sum.
- `T16.sparseDecimal_rationalNeighbor`, giving the signed sparse-decimal
  reduced-ratio neighbor estimate.
- `T16.longDifferenceMultiplicityWeightedGCD_eq_witness` and
  `T16.longDifferenceMultiplicityWeightedGCD_le`, connecting the finite
  witnesses to the final ordinary-GCD bound.

These are finite arithmetic theorems. They contain no assertion about
Dirichlet kernels at `Real.pi`.

### 2. T25: arithmetic control to a fixed-phase Dirichlet-kernel bound

Disposition: the missing interface was later implemented in T34 and T49 with
the necessary orbit-specific premise retained explicitly. The checked public
chain is:

- `T34.abs_inclusiveRealKernel_le_height_mul_shellWeight`, converting one
  fixed-phase kernel into its exact nearest-integer shell weight.
- `T34.cancellingSector_norm_le_weightedShellIncidence`, converting the full
  cancelling sector at `Real.pi` into the literal weighted shell incidence.
- `T34.cancellingSector_bound_of_literal_incidence`, exposing the fixed-scale
  implication with all constants.
- `T34.ARI_cancel_implies_cancellingSectorBound`, preserving the quantifier
  order `forall s, exists C_s, forall positive m,N`.
- `T49.primitiveSector_abs_le_weightedShellIncidence`, supplying the analogous
  primitive-sector bridge.

This mapping does not claim that T16's ordinary-GCD bound implies the required
orbit incidence. The latter remains an explicit hypothesis, so no fixed-`pi`
estimate is made unconditional.

### 3. T27: width-sensitive `N^2 log(2N)` cross-block estimate

Disposition: already machine-checked in T31. The exact acceptance-facing
theorem is `T31.crossBlockWeightedGCD_le_explicit`. It retains:

- T24's canonical half-open blocks;
- the literal weights `sqrt(b^2-a^2) sqrt(d^2-c^2)`;
- both positive-difference domains and all multiplicities;
- the inclusive frequency valuation split, including `h = 10^m`; and
- the bound `470226400 * N^2 * log(2N)`.

The shorter packaged form is `T31.crossBlockWeightedGCD_le`. Supporting public
lemmas include `T31.primitive_weighted_card_sum_le`,
`T31.cancelling_weighted_card_sum_le`, and
`T31.cancelling_sqWeighted_card_sum_le`. Thus the historical `N^4` loss is not
a current library gap.

### 4. T29: list-indexed weighted Cauchy-Schwarz

Disposition: already machine-checked in T29, without adding a duplicate
general list theorem. `T29.translatedCanonicalBlocks_nodup` justifies passing
the canonical block list to a finite set, and
`T29.cutoff_L1_sq_le_width_product` applies
`Finset.sum_mul_sq_le_sq_mul_sq` on the block-frequency product. The subsequent
constant transfer is `T29.widthWeightedSquareFunctionAt_implies_cutoff`, using
`T29.canonical_widthWeight_sum_le_sharp`.

The implementation is reusable at the square-function level and retains the
literal canonical widths and inclusive frequency range.

### 5. T30: ordinary-GCD resonance versus fixed-phase evaluation

Disposition: the honest boundary and both available alternatives are now
machine-checked.

- `T32.blockSquaredEnergy_eq_diagonal_add_offDiagonal` and
  `T32.widthWeightedSquareFunction_eq_diagonal_add_offDiagonal` expose the
  exact fixed-phase Dirichlet-kernel expressions.
- `T32.widthWeightedSquareFunction_le_width_count` gives the unconditional
  phase-uniform counting bound.
- `T32.phaseUniform_partialRange` and `T32.fixedPi_partialRange` give the
  checked restricted range without pretending to obtain cancellation from
  ordinary GCD data.
- For orbit-specific cancellation, the T34 and T49 shell-incidence bridges
  listed in disposition 2 are the checked replacement interface.

No accepted theorem asserts an invalid implication from
`gcd(d,e)/max(d,e)` to the size of `C_H(d*pi)`.

### 6. T32: sharp triangular record count by endpoint width

Disposition: already machine-checked in T32. The exact public chain is:

- `T32.endpointEnvelopeCode_mem` maps every ordered record into the endpoint
  envelope.
- `T32.endpointEnvelopeCode_injOn` proves injectivity.
- `T32.endpointEnvelope_card` proves the exact cardinality
  `(N-m)(N-m+1)`, including both Bool orientations.
- `T32.orderedLongPairDomain_card_le_width` transfers that count to the exact
  filtered record domain.
- `T32.canonicalBlockRecord_card_sum` is the T24 endpoint-cardinality
  telescope across canonical blocks.

### 7. T31: width-sensitive canonical-block witness counts

Disposition: already machine-checked in T31. The relevant public declarations
are:

- `T31.blockOrderedDomain_card_lt_width_sq`, the local record count in terms
  of the literal block width.
- `T31.blockPositiveDifferenceDomain_card_two_le_sq`, retaining the strict
  positive orientation convention.
- `T31.cancellingBlockDifferenceDomain_card_le`, retaining the hidden
  exponent and both cancellation choices.
- `T31.primitive_weighted_card_sum_le`,
  `T31.cancelling_weighted_card_sum_le`, and
  `T31.cancelling_sqWeighted_card_sum_le`, the normalized sector sums used by
  `T31.crossBlockWeightedGCD_le`.

These declarations are the checked implementation of the sharp cancelling
count and normalized canonical-sector bookkeeping that the earlier imported
interfaces lacked.

### 8. T33: six cancelling domains and repunit regrouping

Disposition: already machine-checked in T34 and T49.

- T34 publicly defines `T34.cancellingRowDomain` and
  `T34.blockRepunitMultiplicity`.
- `T34.cancellingRow_witness_unique` proves uniqueness of row, valuation,
  repunit length, and hidden exponent for an active witness.
- `T49.mem_cancellingBlockDifferenceDomain_iff_six_rows` proves the six rows
  exhaustive for the exact T31 cancelling positive-difference domain.
- `T49.cancellingWitness_image_eq_domain` upgrades that classification to an
  exact finite image equality.
- `T49.blockCancellingPositiveSum_eq_rows` proves the exact repunit
  multiplicity regrouping.
- `T34.cancellingSectorContribution_eq_regrouped` proves the corresponding
  signed kernel identity.
- `T49.centeredWidthWeightedSquareFunction_eq_sectors` assembles the primitive
  and cancelling sectors into the exact centered square function.

The T33 prose is therefore provenance only; the coverage above comes from the
later Lean modules, not from treating that proof sketch as established.

## Additivity and claim audit

T77 changes no existing source file and introduces no Lean declaration. The
companion `T77HousekeepingCoverageAudit.lean` is declaration-free: it imports
the six pinned modules, checks every mapped public name, and prints the axioms
of representative endpoints. Every reported gap maps to a public declaration
in an accepted module, so adding aliases would duplicate library content
rather than improve reuse. No theorem is renamed, weakened, removed, or
redeclared.

The map does not assert T29's all-scale premise at `Real.pi`, ARI_cancel,
PrimitiveIncidence, C1, C2, or C3. In particular, the orbit-specific shell
incidences remain hypotheses in every bridge that uses them. The canonical
collision question remains open.

## Replay

From the workspace root, after installing the pinned package-cache link, run:

```text
timeout 900 lake build TheoryLib
lake env lean removed-workflow-record://todo-theory-pi-long-lag-block-collision-decay-t77-1785782223-r0/theory_artifacts/T77HousekeepingCoverageAudit.lean
```

The T77 build ran both commands successfully. The representative axiom output
contained only `propext`, `Classical.choice`, and `Quot.sound`; some endpoints
use a strict subset. Existing linter warnings in imported modules are not
errors.
