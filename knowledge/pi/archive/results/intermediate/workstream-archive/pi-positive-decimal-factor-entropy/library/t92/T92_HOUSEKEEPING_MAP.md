# T92 housekeeping map

Status: exact mapping of scheduler-reported implementation and provenance gaps
to the staged accepted library. This document makes no claim that the canonical
positive-entropy question is resolved.

## Canonical statement

The immutable source is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`, SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
Its canonical quantifiers require one fixed real `eta > 0` and one fixed
integer `N >= 1` such that every integer `n >= N` satisfies
`p_pi(n) >= 10^(eta*n)`. None of the mappings below supplies that open fixed-pi
estimate. In particular, bounded experiments, positive measure entropy, and
full entropy are not substituted for the canonical statement.

For this housekeeping item, each of the eight scheduler reports is interpreted
independently. A report is covered either by an existing public checked Lean
declaration or by an exact accepted experimental/provenance locator. Existing
declarations are imported, not renamed, restated, weakened, or removed.

## Exact gap map

### 1. T20 one-sided factor-two orbit-closure comparison

Disposition: covered by public, kernel-checked declarations; imported without
duplication.

Accepted locator:
`knowledge_library/t20/T20TransversalEntropy.lean`, SHA-256
`ac5ed1c3c9c74fae5ae5d2191e92a8895ad991c34e0d2e950dfc10b036a09a64`.

- `DecimalFactorEntropy.TransversalEntropy.decimalCellSuccessor_eq_zero_of_eq`
  at lines 782-785 handles the wraparound successor.
- `DecimalFactorEntropy.TransversalEntropy.decimalCylinder_inter_closedDecimalCell`
  at lines 789-874 proves the one-sided alternative `a = b` or
  `a = decimalCellSuccessor n b`, including the endpoint `0 = 1`.
- `DecimalFactorEntropy.TransversalEntropy.occupiedLabels_subset_factorLabels_union_successors`
  at lines 901-917 transfers that intersection statement to occupied labels.
- `DecimalFactorEntropy.TransversalEntropy.pi_factorComplexity_le_occupiedCount_le_two_mul`
  at lines 921-952 gives the required one-sided factor-two comparison.

### 2. T23 generated-subgroup finite representation

Disposition: covered by public, kernel-checked declarations; imported without
inventing an `AddSubgroup.toFinset` API.

Accepted locator:
`knowledge_library/t23/T23AbstractSubgroupSeparation.lean`, SHA-256
`8bbf203c8b317a96b4aec9a2af5d780caa9b6e6e44de26ebc7533d0343a326c4`.

- `DecimalFactorComplexity.AbstractSubgroupSeparation.labelSubgroupFinset` at
  lines 73-76 is the explicit ambient `Finset.univ.filter` representation.
- `DecimalFactorComplexity.AbstractSubgroupSeparation.labelSubgroup_card` at
  lines 175-184 computes the cardinality using `Nat.card_zmultiples`.
- `DecimalFactorComplexity.AbstractSubgroupSeparation.subgroupSupport_eq_labelSubgroup_toFinset`
  at lines 186-205 identifies the explicit support with the filtered subgroup
  representation.

### 3. T26 rounding-aware eventual growth

Disposition: covered by a public, kernel-checked declaration; imported without
duplication.

Accepted locator:
`knowledge_library/t26/T26SparseLongBandFejer.lean`, SHA-256
`8f61cdce1f5cab84c58777274f019c124c872e42180c7a13123900883fe710f0`.

`DecimalFactorComplexity.SparseLongBandFejer.eventually_constant_le_sparseSampleLength_mul_quarter_decay`
at lines 225-296 states the fixed-constant absorption with
`sparseSampleLength n = 10^(n/2)` using natural-number division. Lines 272-295
perform the explicit odd/even rounding comparison needed for the exponent.

### 4. T35 finite-partition Hellinger affinity

Disposition: covered by public, kernel-checked declarations; imported without
asserting a stronger packaged theorem than was proved.

Accepted locator:
`knowledge_library/t35/T35CylinderAffinity.lean`, SHA-256
`0d62aa6ca27c5965b3e5733d9fcef68989a472c667a249f160125f4359d492e3`.

- `DecimalFactorEntropy.CylinderAffinity.affinity_antitone` at lines 210-240
  proves monotonicity under nested finite-cylinder refinement using finite
  Cauchy-Schwarz.
- `DecimalFactorEntropy.CylinderAffinity.commonSubmeasure_mass_le_affinity` at
  lines 316-333 supplies the lattice-common-submeasure lower bound.
- `DecimalFactorEntropy.CylinderAffinity.not_mutuallySingular_implies_affinityLimit_pos`
  at lines 335-361 uses `mu inf nu` to obtain strict positivity.
- `DecimalFactorEntropy.CylinderAffinity.positive_affinityLimit_iff_not_mutuallySingular`
  at lines 363-373 gives the exact criterion under the explicit
  `GeneratesInMeasure` premise.

### 5. T37 omitted replay and tau layers

Disposition: covered at `experiment` level by the later accepted T38 bundle,
not by Lean and not as evidence for a universal statement. No T37 directory is
present in the staged knowledge library, so T92 maps only to the reconstructed,
self-contained accepted bundle that is actually available.

Accepted locators:

- `knowledge_library/t38/README.md`, SHA-256
  `4d8917bb62a4f2d179419cd929fbb70e0deca088ae9a34090411da6bcc913de1`.
  Lines 9-19 specify artifact-only replay; lines 45-74 specify the Perron and
  tau checks; lines 76-85 enumerate the replay implementation and outputs; and
  lines 117-123 enumerate the reconstruction checks.
- `knowledge_library/t38/t38_experiment.py`, SHA-256
  `7598c198969b40fdfa3fcfe0b8320730c337764ac12b932775d676f33fe8c8cb`,
  is the deterministic generator and exact verifier.
- `knowledge_library/t38/entropy_certificates.json.gz`, SHA-256
  `bdf20ce54a4198e61af6fcf100aaffd5d0cfc050e93dd0d99b19c4d8a939e4da`,
  contains the replayed Perron certificates.
- `knowledge_library/t38/tau_probes.json`, SHA-256
  `a2f984f292e309c44fda8e52a01406c033dd12a8c15ffaab5b25bc6e70c6d7df`,
  contains the exact bounded tau probes.
- `knowledge_library/t38/verify.sh`, SHA-256
  `051a41d64bed6f773a9d519af3250b2cc36b8f7749ec6aa78391044dfcb021a4`,
  is the one-command artifact-only replay entry point.

The accepted status is only `experiment`. Finite replay does not prove C1, C6,
or an asymptotic tau bound.

### 6. T38 unavailable T37 MDD, QBF, and primitive-gap sources

Disposition: confirmed as a provenance limitation, not converted into a new
certificate. The staged accepted T38 artifact is stricter than the scheduler's
historical wording: it does not deliver or claim MDD, QBF, primitive-gap, or
inherited non-replayed frontier figures at all. T92 therefore neither repeats
those figures nor treats them as evidence.

The exact accepted scope locator is `knowledge_library/t38/README.md` with the
hash above. It labels the bundle `experiment` at line 3, enumerates every
delivered output at lines 76-85, enumerates the actual replay checks at lines
117-123, and states at lines 125-129 that no asymptotic tau or pi claim is made.
The artifact-only replay described at lines 9-19 was rerun during T92 review and
regenerated the delivered T38 outputs byte-for-byte.

No staged accepted artifact preserves the historical MDD, QBF, primitive-gap,
or inherited-frontier figures named by the scheduler telemetry. That part of
the telemetry is therefore mapped as unavailable rather than discharged. The
accepted T38 artifact covers only its explicitly replayed, narrower claims; no
missing formal bridge is silently asserted.

### 7. T39 common-map ergodic dichotomy

Disposition: covered by a public, kernel-checked declaration built from the
invariant singular-part and absolute-continuity APIs.

Accepted locator:
`knowledge_library/t39/T39ErgodicAffinityRigidity.lean`, SHA-256
`f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09`.

`DecimalFactorEntropy.T39ErgodicAffinityRigidity.ergodic_eq_or_mutuallySingular`
at lines 107-132 states that two probability measures ergodic for one map are
equal or mutually singular. The proof exposes the singular part, its
invariance, and both absolute-continuity steps.

### 8. T39 abstract metric-entropy and rigidity interface

Disposition: covered by a public definition and a public, kernel-checked
conditional bridge. No Kolmogorov-Sinai entropy implementation is claimed.

Accepted locator: the same T39 file and hash as report 7.

- `DecimalFactorEntropy.T39ErgodicAffinityRigidity.RudolphJohnsonRigidityPremise`
  at lines 164-178 quantifies over one explicit abstract functional
  `metricEntropy : Measure UnitAddCircle -> Real` and retains probability,
  both invariances, times-ten ergodicity, and strict entropy positivity.
- `DecimalFactorEntropy.T39ErgodicAffinityRigidity.affinity_and_source_rigidity_imply_lebesgue`
  at lines 180-201 uses that source premise explicitly; it does not package or
  prove the external Rudolph-Johnson theorem.

## Public import surface

`T92Housekeeping.lean` imports the accepted T20, T23, T26, T35, and T39 modules
and checks the declarations listed above. It introduces no aliases or
replacement declarations, so all existing public signatures remain unchanged
and available transitively. T37/T38 remain provenance and experiment mappings,
not Lean theorems.

## Scope

This delivery is housekeeping only. It proves neither C1 nor its negation,
does not upgrade an experiment to a formal or asymptotic result, and does not
replace the explicit hypotheses of T35 or T39 with unconditional fixed-pi
claims.
