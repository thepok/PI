# BBP Weyl, circle-density, and symbolic-transfer milestone (2026-08-21 UTC)

Claim label: `machine-checked`.

The canonical T107--T109 modules consolidate the seven-step BBP forced orbit
into three exact transfer interfaces.

## Verified statements

- **T107, Weyl transfer.** The scaled BBP error tends to zero. The positive
  forcing is bounded by ten times that error, is summable, and tends to zero.
  At each integer frequency, the phase discrepancy between the sampled BBP
  orbit and the unwrapped decimal pi orbit is absolutely summable. A generic
  summable-perturbation theorem therefore proves
  `RealWeylCancellation sampledBBPOrbit ↔ RealWeylCancellation (fun N =>
  10^N * Real.pi)`. Consequently, sampled-orbit Weyl cancellation implies
  canonical V1, but only when that cancellation is supplied as an explicit
  premise.
- **T108, endpoint-safe circle transfer.** In `UnitAddCircle`, the distance
  between the sampled BBP point and the matching canonical base-ten pi point
  is bounded by the scaled BBP error and tends to zero. A generic tail-
  stability theorem transfers the exact arbitrarily-late density predicate in
  both directions. Canonical V1 implies arbitrarily-late circle density of the
  pi orbit, and sampled-orbit arbitrarily-late circle density implies V1.
  Hence the module proves the equivalence
  `V1 ↔ SampledBBPOrbitCircleDenseArbitrarilyLate`; this equivalence asserts
  neither side.
- **T109, symbolic packaging.** Under the explicit external hypothesis
  `IrrationalityMeasureBelow Real.pi 8`, the seven-oversampled BBP finite block
  code is eventually equal to `piCylinderCode`, and its integer floor code is
  eventually equal to the value of the same-position
  `DecimalFactorComplexity.blockAt Theory.PiDigits.piDigit` word. These are
  eventual identifications, not occurrence statements.

## Verification record

`pwsh workflows/verification/check.ps1` passed after canonical integration,
including the Lean build, forbidden-construct checks, and exact-allowlist
axiom audit. Every public T107--T109 declaration is registered in
`audit/AxiomAudit.lean`; the permitted dependencies remain only `propext`,
`Classical.choice`, and `Quot.sound`.

Pinned canonical source hashes at the passing state:

- T107 `TheoryLib/PiQuantitativeBlockHitting/T107T107BBPWeylTransfer.lean`:
  `72bc7980c3ae8105b5dc1457fddb6cc8b8281df85b5ceed131866c8db3add8e7`
- T108 `TheoryLib/PiQuantitativeBlockHitting/T108T108BBPCircleDensityTransfer.lean`:
  `62847285b36b59cb39ae26c33ceebe5c1043c5ec2004a23d40f3e7a6d0085973`
- T109 `TheoryLib/PiQuantitativeBlockHitting/T109T109BBPSymbolicPackaging.lean`:
  `745dab8683d11b85409162ca04504da435f8e69cb1b3398abfc01802f30d1318`

The reverse T108 implication was independently corroborated before
integration by three isolated-gate candidates: OpenRouter artifact
`e906928109f3fad6d129a27216521644544e7915983f9af35f1a3ea13ab0e2a7`
and native artifacts
`82dd807ed6c6ea78009c7001a91e58ff6e0629574b039453adb621b314eb1819`
and `b66dabb5d4acdc00237b79bc1a3ada2bb2a331fb15c267e305c16c4440c242fe`.
Their proof shapes separately checked the arbitrary lower time bound and
endpoint-safe quotient-circle geometry. The canonical source uses the short
proof through T21's arbitrarily-late word occurrence and T72's prefix-match
bound.

## Claim firewall

- This is not a solution of the pi decimal-disjunctivity problem and not a
  `candidate resolution` or `verified resolution`.
- No theorem proves Weyl cancellation for the sampled BBP orbit or the pi
  orbit. T107 only transfers cancellation and derives V1 conditionally.
- No theorem proves circle density unconditionally. T108 identifies the
  sampled density proposition with canonical V1 but proves neither one.
- T109 proves no prescribed word occurs. Both results retain
  `IrrationalityMeasureBelow Real.pi 8` as an explicit external hypothesis.
- No novelty or literature-check claim is made for T107--T109 by this report.
