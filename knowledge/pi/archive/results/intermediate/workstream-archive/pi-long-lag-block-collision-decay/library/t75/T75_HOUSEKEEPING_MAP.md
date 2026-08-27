# T75 housekeeping coverage map

Status: `machine-checked` only for the Lean declarations identified below and
for the two new T75 bridges after compilation. Source pins are provenance
records, not Lean proofs. T11, T13, and T15 prose notes remain `proof sketch`
and are never used as proved premises.

## Scope

The canonical source is
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`, a problem formulated
locally on 2026-07-23 with no external source URL. Its checked SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question retains ordered pairs, the weak cutoff `|i-j| >= m`,
the additive `N` term, and the order
`forall 0<s<1, exists C_s>=1, forall positive m,N`. It remains open. T75 is
strictly additive housekeeping and makes no fixed-`pi` estimate unconditional.

## Gap dispositions

### 1. T5: absent prior T3/T24 prose audits

Disposition: mapped to the accepted T5 source-pinned literature artifact; no
Lean declaration was missing. The exact record is
`knowledge_library/t5/SOURCE_MANIFEST.md`, lines 35-41, which states that the
requested prose audits were absent and identifies the freshly pinned primary
sources. `knowledge_library/t5/SOURCE_SHA256SUMS` records the expected bytes.
The mapping-file hashes are:

- `SOURCE_MANIFEST.md`:
  `ace2233019ea2a24e8b83fb49b03c968ca4f5a1f6d87e04327f12a784c70fc65`
- `SOURCE_SHA256SUMS`:
  `c0bf2c2db3c26b7a1e549d1541a473d4a2dc8552c1ce06b80a6554aa2f5cf309`
- `APPLICABILITY_MATRIX.md`:
  `ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406`

An adversarial replay of `knowledge_library/t5/verify_sources.sh` checked the
canonical statement and all six retained PDFs, but the script exited nonzero
because its local directory omits the listed comparator snapshot
`T2UniformLongLagResidual.lean`. The accepted comparator is instead staged at
`knowledge_library/t2/T2UniformLongLagResidual.lean`; its independently checked
SHA-256 is the manifest's expected
`ffe231e2750445a8f2c0a342cb60e1259a2427e5bb0f8067bf1350ab62bdeba3`.
Thus the source pins below replay, while the T5 directory by itself is not a
self-contained replay bundle. The pinned PDF hashes include Bailey--Crandall
`8c482ef709857877ea22e4bdf9ff3fa3673dd8c20ba9f9026e3a1bded1a6704d`,
Philipp
`4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a`,
Fukuyama
`cc825c90055c5661d4ab1923c37e320b2af7846fedc0717cb27284c52eb7a94c`,
and Rudnick--Zaharescu
`d16de4bd2990cf6d022c9e49fff5ae59493a651db2690c74ec8aacbfc36a293f`.
The applicability conclusions are literature comparisons, not proofs of C1.

### 2. T5: absent inherited T3/T24 audits

Disposition: this is duplicate telemetry for item 1. It maps to the same T5
`SOURCE_MANIFEST.md`, `SOURCE_SHA256SUMS`, retained PDFs, and
`APPLICABILITY_MATRIX.md`, with the separate T2 comparator location and replay
limitation stated above. No second source bundle or duplicate theorem is
introduced.

### 3. T7: counting assignments under disjoint coordinate equalities

Disposition: already machine-checked in module
`TheoryLib.PiLongLagBlockCollisionDecay.T7T7FiniteBernoulliCollisions`, source
SHA-256
`f48c72dc7030f13f014da7f1b33817425de7fb3b7e0a06409e5e5f0fbc91f4bf`.
The public coverage is exact:

- `Theory.PiDigits.LongLagBlockCollisionDecay.T7.pairEqEquiv` deletes the
  constrained right-hand coordinates.
- `Theory.PiDigits.LongLagBlockCollisionDecay.T7.card_pairEq` gives the exact
  assignment cardinality.
- `Theory.PiDigits.LongLagBlockCollisionDecay.T7.uniformProbability_pairEq`
  gives the uniform probability.
- `Theory.PiDigits.LongLagBlockCollisionDecay.T7.collision_probability`
  specializes the result to disjoint decimal blocks.

T75 imports this module and does not duplicate those declarations.

### 4. T8: Fejer expansion on a restricted finite pair domain

Disposition: already machine-checked in module
`TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction`, source
SHA-256
`f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9`.
The public restricted-domain expansion is
`Theory.PiDigits.LongLagBlockCollisionDecay.T8.sum_fejerKernel_eq_doubleSignedRe`.
The comparison chain is
`sum_fejerKernel_le_zero_add_positive`,
`longResidualPairCount_le_majorant`, and
`positiveFrequencyNormSum_le_of_energy`. The domain itself is exposed by
`orderedLongPairDomain` and `mem_orderedLongPairDomain_iff`. These are exactly
restricted finite sums; no unrestricted mathlib theorem is claimed.

### 5. T8: omitted T4 source-pin files during an earlier replay

Disposition: mapped to the retained accepted provenance files now present at
`knowledge_library/notes/t4/SOURCE_PIN.md` and
`knowledge_library/notes/t4/zeilberger-zudilin-moscow-2020-9-407.pdf`.
Their checked SHA-256 values are respectively
`9c2b2a2448db5bd490deedd8e82a15a8d6a7600f40a879442f6e48e9ee3c6e26`
and
`3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
The source pin gives DOI `10.2140/moscow.2020.9.407` and exact PDF locators.
This repairs hash replay only. The publication's mathematical claim remains
external evidence, and the T4 Lean module keeps it as an explicit hypothesis.

### 6. T11: scale-dependent premise lacked a direct final bridge

Disposition: implemented as public checked additions in
`theory_artifacts/T75HousekeepingBridges.lean`:

- `Theory.PiDigits.LongLagBlockCollisionDecay.T75.scaleMatchedSquaredEnergyBound_implies_T2`
- `Theory.PiDigits.LongLagBlockCollisionDecay.T75.scaleMatchedSquaredEnergyBound_implies_C1`

They compose the existing machine-checked T12 declarations
`scaleMatchedSquaredEnergyBound_implies_L1` and
`scaleMatchedL1Bound_implies_T2` with T2's
`piUniformLongLagResidualPairDecay_implies_C1`. T12's source SHA-256 is
`a4108ff862c13ee0f9fa3fc877723856eb34497430cde36d85f7943ce0347bcf`.
The effective-irrationality and scale-dependent energy estimates remain
explicit hypotheses; no result is specialized unconditionally to `pi`.

### 7. T13: no pinned three-distance theorem

Disposition: mapped only as a provenance/non-use report to the unverified T13
note `knowledge_library/notes/t13/T13_MANY_ANCHOR_INCIDENCE.md`, Section 8.4,
lines 557-572, SHA-256
`7c2298029c4f66b613d03405caefa60567e9b1a34632336e67e6cf3bfff12f1e`.
That section explicitly says no three-distance theorem was
imported. T75 does not claim that the note proves the broader methodological
assertion that bare three-gap data can never help. No T75 theorem depends on
that assertion, so there is no missing formal premise to discharge and no
literature theorem to invent or silently import.

### 8. T15: weighted ordinary-GCD interaction

Disposition: later implemented and machine-checked in module
`TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD`, source
SHA-256
`4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec`.
The exact public endpoint is
`Theory.PiDigits.LongLagBlockCollisionDecay.T16.longDifferenceMultiplicityWeightedGCD_le`:
for every `m,N`, the exact positive long-difference multiplicity sum with the
ordinary gcd kernel is at most `574913232 * N^4`. Its supporting public
infrastructure includes `sparseDecimal_rationalNeighbor`,
`allPositiveFourTokenWeightedGCD_le`, and
`longDifferenceMultiplicityWeightedGCD_eq_witness`. This is finite arithmetic
only and asserts no analytic estimate at `pi`.

## Additivity audit

No existing source file or declaration is changed, renamed, weakened, or
removed. The Lean artifact uses the fresh namespace
`Theory.PiDigits.LongLagBlockCollisionDecay.T75`. Existing coverage is imported
and mapped rather than redeclared.
