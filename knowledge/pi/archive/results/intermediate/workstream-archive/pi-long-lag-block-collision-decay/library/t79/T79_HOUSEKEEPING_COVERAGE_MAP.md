# T79 housekeeping coverage map

## Status and scope

The canonical source is the locally formulated problem
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`; it has no external
source URL. Its verified SHA-256 is
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
It asks for one constant for every `0 < s < 1`, uniform over all positive
`m,N`, for the ordered collision count with weak lag cutoff `|i-j| >= m` and
the additive `N` term. That question remains open. The sparse-Fourier and
incidence objects below concern conditional or residual sibling reductions;
none is substituted for the canonical statement.

`machine-checked` below applies only to the named Lean declarations. The T44
and T50 prose notes are unverified `proof sketch` artifacts and are not used as
premises.

## Source pins

| Item | Accepted source path | SHA-256 |
|---|---|---|
| T25 | `TheoryLib/PiPositiveLowerBlockDensity/T25T25ResidualPairReduction.lean` | `86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c` |
| T16 | `TheoryLib/PiLongLagBlockCollisionDecay/T16T16FiniteWeightedGCD.lean` | `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec` |
| T31 | `TheoryLib/PiLongLagBlockCollisionDecay/T31T31CrossBlockAlmostEverywhere.lean` | `535a43fc06ac84d9b61760300c642fc05dbd797dc7cedb25f0ed30156bf10380` |
| T32 | `TheoryLib/PiLongLagBlockCollisionDecay/T32T32AllBlockFixedPiRange.lean` | `3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc` |
| T34 | `TheoryLib/PiLongLagBlockCollisionDecay/T34T34CancellingRepunitIncidence.lean` | `720e5ee33f63226c560aee19751421fa383448e0aef45602c5eaf9a10f52778c` |
| T36 | `TheoryLib/PiLongLagBlockCollisionDecay/T36T36SubcriticalCancellationSaving.lean` | `3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24` |
| T49 | `TheoryLib/PiLongLagBlockCollisionDecay/T49T49PrimitiveIncidenceAssembly.lean` | `65776873b77b51df5639e7546db7319f14ce4b76259d3faa19732744e6e13cdb` |
| T51 | `TheoryLib/PiLongLagBlockCollisionDecay/T51T51FiniteSparsePeriodicSelection.lean` | `520e27acd8a8866158a8fe01ec83cf0aca1edf8938374f933f474142f1564789` |
| T53 | `TheoryLib/PiLongLagBlockCollisionDecay/T53T53PrefixFaithfulFiniteWords.lean` | `eab6befd80efbe529575876994c3ba7d1e3bab6f2ab0c226e733ae8180aa5f10` |

## Telemetry dispositions

### 1. T44 transitive arithmetic exclusion

T36 reaches
`Theory.PiDigits.PositiveLowerBlockDensity.T25.ArithmeticExcluded` through its
imports. The declaration is at lines 51-56 of the pinned T25 source above and
uses
`structuredDenominator n r = 10^n * (10^r - 1)`. T79 now exposes the complete
expansion as the public machine-checked theorem
`T79.arithmeticExcluded_iff_explicit`. At `(mu,c)=(8,1)` this is exactly the
formula recorded by the unverified T44 note, but the checked T79 theorem, not
that note, is the evidence.

### 2. T45 all-scale noncancelling remainder

No unconditional fixed-`pi`, all-positive-`m,N` estimate is claimed. The
accepted public replacement interface is T49's `PrimitiveIncidenceAt` together
with `primitiveSector_abs_le_weightedShellIncidence`. The exact assembly theorem
`widthWeightedSquareFunction_le_of_three_obstructions` retains
`PrimitiveIncidenceAt 8 1 Q0 s Cprim` as an explicit hypothesis. Thus the
missing estimate is isolated in a checked bridge rather than assumed.

### 3. T45 averaged and partial-range machinery

T16's `longDifferenceMultiplicityWeightedGCD_le` and T31's
`crossBlockWeightedGCD_le_explicit` do not imply pointwise cancellation at
`Real.pi`. T32's `fixedPi_partialRange` is explicitly restricted by
`((N-m)(N-m+1))^2 <= N`. The all-scale boundary is represented by the same T49
primitive-incidence premise named in disposition 2. This is a precise mapping,
not a discharge of that premise.

### 4. T48 four-row shrinking-shell incidence

T34's `cancellingSector_norm_le_weightedShellIncidence` converts the exact
cancelling sector to shell incidence. T36 then defines `ARI_superAt` and
`ARI_super`; `ARI_super_iff_quantifiers` displays every positive `m,N` range,
while `ARI_superAt_implies_ARI_cancelAt` is conditional on both the published
source premise and `ARI_superAt`. These accepted declarations isolate the
aggregate four-row fixed-`pi` input. T79 does not assert it.

### 5. T48 absence of a fixed-pi shrinking-target theorem

The accepted endpoint remains T49's
`widthWeightedSquareFunction_le_of_three_obstructions`, which requires both
`ARI_superAt` and `PrimitiveIncidenceAt`. T32 contributes only
`fixedPi_partialRange`. Therefore no listed accepted artifact supplies the
required all-scale fixed-`pi` shrinking-target or pair-correlation estimate;
the checked library records it as a premise. The canonical conjectures remain
open.

### 6. T49 six-row exhaustion and block-domain equality

This report is already machine-checked in accepted T49:

- `mem_cancellingBlockDifferenceDomain_iff_six_rows` proves that the six T34
  rows exhaust T31's exact cancelling positive-difference domain.
- `cancellingWitness_image_eq_domain` gives the canonical finite image equality.
- `blockCancellingPositiveSum_eq_rows` gives the resulting exact sum regrouping.

T79 imports and checks these names instead of adding duplicate aliases.

### 7. T50 reconstruction provenance

The rejected T46 artifact is absent and is not a dependency. The T50 note is
an unverified `proof sketch`; none of its square-variation conclusions is
claimed here. Its kernel-checked inputs map directly to accepted T36, including
`canonical_blockLength_weight_budget`,
`restrictedWeightedShellIncidence_eq_direct`, and
`ARI_super_iff_quantifiers`. This disposition certifies dependency provenance
only; it does not upgrade T50's argument to `machine-checked`.

### 8. T53 external finite-instance bridge

Accepted T53 proved `intervalWordEvent_card_le_three` using local `letI`
instances. A repository search found no public `Finite` instance for T51's
`IntervalWordEvent`, so external applications could not synthesize the target
instance. T79 adds public instances `t51IntervalWordEventFinite`, constructed
through T51's `finiteWordCode_injective`, and
`t53IntervalWordEventFinite`, inherited through T53's checked injection. The
public theorem `t53_intervalWordEvent_card_le_t51` now performs the formerly
failing external `Nat.card_le_card_of_injective` application.

## Additivity and replay

T79 changes no existing declaration. All new declarations are in the fresh
namespace `Theory.PiDigits.LongLagBlockCollisionDecay.T79`; no accepted name is
renamed, weakened, removed, or redeclared.

From the workspace root, after the prescribed package-cache setup, replay:

```text
timeout 900 lake build TheoryLib
lake env lean removed-workflow-record://todo-theory-pi-long-lag-block-collision-decay-t79-1786020580-r2/theory_artifacts/T79HousekeepingBridges.lean
```

The Lean file prints the axioms of every new declaration used as evidence.
