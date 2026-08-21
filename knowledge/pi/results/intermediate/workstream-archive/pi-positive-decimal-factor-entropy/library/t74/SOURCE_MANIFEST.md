# T74 source manifest

Audit date: 2026-08-02 UTC.

## Canonical statement

- Packaged file: `pi-positive-decimal-factor-entropy.txt`
- Workspace origin: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`
- SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
- Source URL: none; this is a locally formulated canonical question.

## Furstenberg 1967

- Packaged file: `furstenberg-1967.pdf`
- SHA-256: `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358`
- Citation: H. Furstenberg, "Disjointness in ergodic theory, minimal sets, and
  a problem in Diophantine approximation," *Mathematical Systems Theory* 1
  (1967), 1-49.
- DOI: <https://doi.org/10.1007/BF01692494>
- Retrieved PDF: <https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf>
- Retrieval history: inherited from T21's 2026-07-24 literature audit. The
  mirror required disabled TLS certificate checking there; the bytes are
  pinned by the hash above.
- Locator 1: Definition IV.1 and Lemma IV.2, printed/PDF page 47, with the
  lemma's proof continuing on page 48. Search anchors: `Definition IV.1`,
  `LEMMA IV.2`, `non-lacunary`, and `non-isolated`.
- Locator 2: Theorem IV.1, printed/PDF page 48. Search anchors:
  `THEOREM IV. 1`, `non-lacunary`, and `irrational`.
- Used content: Lemma IV.2 classifies a closed forward semigroup-invariant set
  having zero as a non-isolated point; Theorem IV.1 gives density of every
  irrational orbit under a nonlacunary integer semigroup.

## Kernel-checked dependency modules

These modules are reused from the accumulated knowledge library and are not
duplicated in this delivery.

| Module artifact | SHA-256 | Used declarations |
|---|---|---|
| `T44EndpointSafeInvariantCore.lean` | `0157022e5125d130a8e12d1e40e97ee9e3df10fb3aa179c8a1cacbdaace59083` | `KWord_isCompact`, `core_isClosed`, `core_forward_timesTen_invariant`, `core_eq_finiteAvoidanceIntersection`, `core_antitone_radius` |
| `T46T46LiveSCC.lean` | `9e35511d20b9997e7fd98eaf54bfb3eb3b2e53f42b720d962b671b128bf61ec8` | `infiniteLabelLanguage_finite_iff_liveSCCCriterion` |
| `T48EndpointCarryKMP.lean` | `cbe1652c833fb21ae2618aedbc3040a2f29a7db5b310a9f3873536c888c4b211` | `graphEvaluation_image_eq_core`, `graphLanguage_finite_iff_core_finite` |
| `T72ProjectedPeriodicity.lean` | `d05450c90bfc2aff6567fc4c492575004e2dc96dc6a87fbb2aab4fcb12cd16e7` | `globalPrimitivePhaseCriterion_iff_globalEveryInternalProjectionEventuallyPeriodic`, `endpointComplete_global_primitivePhase_iff_coordinateZeroEventuallyPeriodic` |

The hashes above were recomputed from the exact files supplied to this T74
session. Their prior knowledge entries record kernel verification. T74 itself
is a prose note and makes no new machine-checked theorem claim.
