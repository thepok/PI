# T77 source manifest

Audit date: 2026-08-02 UTC.

## Scope

T77 formalizes a sibling fixed-word finite-core certificate. It does not prove
the canonical positive decimal factor-entropy question, a uniform depth rate,
C6, or C1.

The final theorem has the quantifier order

```text
FurstenbergSourcePremise ->
  forall w : List (Fin 10), w != [] ->
    exists R, T72 GlobalPrimitivePhaseCriterion at (w, R).
```

`FurstenbergSourcePremise` is an explicit parameter. The Lean file does not
construct it or present the cited source theorem as unconditionally formalized.

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
- Retrieval history: inherited from T21's 2026-07-24 literature audit; bytes
  are pinned by the hash above.
- Locator 1: Definition IV.1 and Lemma IV.2, printed/PDF page 47, with proof
  continuing on page 48. Anchors: `IV.2`, `non-lacunary`, `non-isolated`.
- Locator 2: Theorem IV.1, printed/PDF page 48. Anchors: `IV. 1`,
  `non-lacunary`, `irrational`.
- Formal use: the two conclusions are fields of
  `FurstenbergSourcePremise`; every theorem depending on them takes that
  premise explicitly.

## Kernel-checked dependencies

| Module | SHA-256 | Main reused interface |
|---|---|---|
| `TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore` | `0157022e5125d130a8e12d1e40e97ee9e3df10fb3aa179c8a1cacbdaace59083` | Endpoint-safe `KWord`, inclusive `Core`, closedness, antitonicity, times-ten invariance |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T46T46T46LiveSCC` | `9e35511d20b9997e7fd98eaf54bfb3eb3b2e53f42b720d962b671b128bf61ec8` | Exact reachable/live/cyclic SCC criterion |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T48T48EndpointCarryKMP` | `cbe1652c833fb21ae2618aedbc3040a2f29a7db5b310a9f3873536c888c4b211` | Endpoint-complete carry/KMP graph and core-finiteness equivalence |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T72T72ProjectedPeriodicity` | `d05450c90bfc2aff6567fc4c492575004e2dc96dc6a87fbb2aab4fcb12cd16e7` | Exact global primitive-phase certificate equivalence |

## Named theorem audit

- `timesSixteen_core_succ_mapsTo`: inclusive-depth core convention.
- `circleValue_eq_center_implies_occursAt_zero`, `KWord_ne_univ`:
  endpoint-safe properness.
- `limitingCore_timesTen_mapsTo`, `limitingCore_timesSixteen_mapsTo`:
  compact limiting-core invariance.
- `limitingCore_finite`: conditional source-dependent finiteness.
- `finite_intersection_stabilizes_of_positivelyExpansive`: empty,
  subsingleton, and finite preperiodic stabilization.
- `timesTen_positivelyExpansive`: explicit strict constant `1/100`.
- `exists_fixedWord_core_stabilization_depth`: word-dependent depth.
- `liveSCCCriterion_implies_globalEveryInternalProjectionEventuallyPeriodic`:
  T46 semantic bridge retaining internal hidden walks.
- `core_finite_implies_exact_T72_certificate`: exact T72 certificate.
- `exists_wordDependent_exact_T72_certificate`: final conditional theorem.

The Lean file prints the axioms of these declarations. The observed allowlist
is exactly `propext`, `Classical.choice`, and `Quot.sound`.
