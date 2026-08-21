# T107–T109 integration handoff — 2026-08-21

Status: **canonical integration complete**. The independently reviewed candidate artifacts below were consolidated into T107--T109, imported by `TheoryLib.lean`, registered in `audit/AxiomAudit.lean`, and accepted by `pwsh workflows/verification/check.ps1` on 2026-08-21. The exact allowlist remains `propext`, `Classical.choice`, and `Quot.sound`.

Canonical source hashes at the passing state:

- T107: `72bc7980c3ae8105b5dc1457fddb6cc8b8281df85b5ceed131866c8db3add8e7`
- T108: `62847285b36b59cb39ae26c33ceebe5c1043c5ec2004a23d40f3e7a6d0085973`
- T109: `745dab8683d11b85409162ca04504da435f8e69cb1b3398abfc01802f30d1318`

## Accepted candidates

| Target | Candidate contribution | Artifact SHA-256 | Gate-log SHA-256 | Integration disposition |
|---|---|---|---|---|
| T107 error decay | `oxzen-pi-t107-error-convergence-a` | `971ff3eae81b1c898aa1bb2c472b0f21f6cc6292fbe9168e8526fcdd3b9c498d` | `d2896be9683b649f41cc5c999c9889eddde133fb628babe9461ce00f2a6059d0` | Retain `sampledBBPError -> 0` as a small T106-derived interface lemma. |
| T107 forcing asymptotics | `ox-pi-t107-forcing-asymptotics-a` | `3d7bafbeb6f74eeb929cc27b0e1e48808f7bb2d7f6a0e1907016959c12cf76a0` | `625d1ddf12860df318ff16d0e296ccfbcfdba641c40fcb4963951e98af12d37a` | Retain the forcing bound, summability, and decay only as ancillary asymptotic infrastructure. |
| T107 phase discrepancy | `oxzen-pi-t107-phase-discrepancy-a` | `c9893ffaead1c0ee590a235ca5bffebf843b12d716f710ed4b777a7109425db0` | `5d3a588047a32504b51935cb50dd3c72dfc2ef4a267cdc98bbb3e25f22e01192` | Retain the pointwise phase bound and absolute summability of the phase discrepancy. |
| T107 generic Weyl transfer | `oxzen-pi-t107-generic-weyl-transfer-a` | `4704f49d23693fa1e531d652a182ca7c33d908c41a7d285d42c72619d3d6a8a5` | `b17e3ad3155e83f9f3f2209ea85379479994ce32df80708cca75eca8ab70748c` | Use as the canonical logical engine: summable phase discrepancy implies an iff of real Weyl cancellation. |
| T107 specialized endpoint | `oxzen-pi-t107-bbp-weyl-endpoint-a` | `c22fb4d464ceea50eeffdc90e030855be9ee60e8e3aa9b2ea4790bc824bdbbf7` | `f6ef7ae00f752247667d8708b331914197647f1b93bbac5919d0d80521d5212b` | Retain the sampled-BBP/pi cancellation equivalence and the explicit-premise implication to canonical V1; implement them through the generic transfer rather than duplicating its proof. |
| T108 endpoint-safe circle transfer | `oxzen-pi-t108-bbp-circle-transfer-a` | `f260d2203ea342eca650a92c2619ce3258bd3cdae0a4c4727040bf45f1a4d29e` | `6ac63f261b52aa4393ac7a14a37ae1259cd118ffcc7eb96316dce254510252f2` | Retain the UnitAddCircle distance bound/convergence, the arbitrarily-late density iff, and only the conditional implication to V1. |
| T109 corrected symbolic packaging | `oxzen-pi-t109-symbolic-packaging-a` from `pi-t109-corrected-contract-20260821` | `971d72bbaec70f5ac6bac07f18ff651e13f2687e2c7a3108cdf3f566069f7107` | `299c887a5dc098def8def13d724f8f04027cc706d446bf8593d6d37fae4a1e31` | Retain the two eventual-identification theorems. They use `DecimalFactorComplexity.blockAt` directly and keep `IrrationalityMeasureBelow Real.pi 8` explicit. |

## Canonical consolidation outcome

- T107 uses the generic summable-discrepancy theorem and the BBP phase-
  summability lemma for the specialized cancellation iff. Proof-only helpers
  are private; task suffixes and duplicated endpoint machinery were removed.
- T108 retains endpoint-safe `UnitAddCircle` control, uses the generic tail-
  stability theorem for the sampled/pi density iff, and adds the independently
  corroborated reverse implication from V1. It proves
  `V1 ↔ SampledBBPOrbitCircleDenseArbitrarilyLate` without asserting either
  proposition.
- T109 contains only the corrected two-theorem packaging, uses
  `DecimalFactorComplexity.blockAt` directly, and introduces no compatibility
  alias outside its namespace.
- All retained public declarations are centrally audited, and the full
  repository verification command passed.

## Rejected T109 contract lineage

Reject artifacts produced under old task-contract SHA `0645e1c2cf9841ad223f82b5a4942eda72f85bec8a7c07757868ce131596ccea`. Its expected type misspelled the canonical selector as nonexistent `Theory.PiDigits.blockAt`. Passing artifacts worked around that typo by introducing a compatibility alias outside the contracted T109 namespace, so they are not integration sources:

- initial run: artifact `e6b97bf6f861aa5893c8095d24d6a61acdab4e5d95fb8ca6b84509643cf258b0`, gate log `39b887538efdba6674a822e29f6bbe3ae001bc52c347e07a0758675abb941be0`;
- refill run: artifact `bc8bfe91f560c1daa4479d06955903b66929698b20c7b1a8de92db8e3e428f68`, gate log `2aa5dfa730633b0ec286c7a491570de7048c3d3a34724ca108b61fcec3240dea`.

The corrected contract SHA is `31e73c57a7728ff0b4003e436ed524534d8da4b672d75ea63ef84cee8101cad1`.

## Claim firewall

- No result here proves a decimal occurrence statement for pi, solves the pi problem, or proves normality.
- T107 proves no cancellation unconditionally. Its V1 endpoint requires `RealWeylCancellation sampledBBPOrbit` as an explicit premise.
- T108 proves no density unconditionally. Its V1 endpoint requires arbitrarily-late circle density of the sampled BBP orbit as an explicit premise.
- T109 proves only eventual equality of corresponding finite block codes. It does not prove that any prescribed word occurs, and every statement retains the external hypothesis `IrrationalityMeasureBelow Real.pi 8`.
- The isolated candidates are retained above as provenance; the consolidated
  theorems are now canonical `machine-checked` results. This is still not
  novelty, literature validation, a `candidate resolution`, or a
  `verified resolution`.
