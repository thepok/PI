# Locked evidence imported by T24

T24 does not repeat T5's six-source applicability audit. It imports a
hash-identical copy of the accepted T5 package from
`EVIDENCE.tar::evidence/knowledge_library/t5/` and uses only its established
negative separation: known uniform-distribution, discrepancy, and earlier
irrationality-measure rows do not prove fixed-pi decimal distribution.

## T5 package pins

| File | SHA-256 |
|---|---|
| `T5_APPLICABILITY_AUDIT.md` | `5c910ab9ae1ae5704d27a6efaf1573750c4a68a98b1e746836426b56c89c3663` |
| `CORPUS.json` | `0b46e2138d6ea87a1a76bd795dcafa46b92641118a2378a0413eccea1bac0f12` |
| `LOCKED_EVIDENCE.md` | `75865a43aa02ffb8e8935b984a7264bbba5cb164d9de478692da4e53db05e1ad` |
| `SEARCH_LOG.md` | `9b8a376677d4d1c2ca9d7dac9c06fb9109c8d8df66efb07ac70ecd5a59262dc6` |
| `HASHES.sha256` | `5802114d4108effef018df29f6526b00f45e851cf607baddb5b7e2242ca4def4` |
| `reproduce.sh` | `fd623aa88228d6d4eafeae3c4a1eeef1e660829408b17dc08492a5fec909479d` |

T5's own hash manifest also pins its six primary PDFs and three retained
Crossref responses. All are stored at their original `sources/` and
`searches/` paths inside the bundled T5 directory. T24's `reproduce.sh verify`
checks them without rerunning T5's search.

## Accepted irrationality evidence reused, not retranscribed

T5 imports the accepted pi-quantitative-block-hitting T9 audit:

| Role | Content-addressed path and hash |
|---|---|
| Audit | `evidence/.research/proof-ledger-artifacts/sha256/97/9734cd424f252b6f166a601c1d6f6bd1297645b6d39d6a276d2ba2b90118c350` |
| Source manifest | `evidence/.research/proof-ledger-artifacts/sha256/27/27ecb1ef8221d1e5bb5903d004b192caa86288415b518eaa993e7d05eb38e870` |
| Acceptance evidence | `evidence/.research/proof-ledger-artifacts/sha256/c1/c139f6f8ce2cd95f44936fde22131e922871c8b693c93197a5163119daa52128` |
| Salikhov PDF | `evidence/.research/proof-ledger-artifacts/sha256/a8/a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d` |
| Salikhov text | `evidence/.research/proof-ledger-artifacts/sha256/e0/e05fcf2c6941386ab51d0bb2705110f4e67660d7669d9f2a92d9c3e9a9466699` |

T5 also imports the accepted fixed-pi Fourier audit that pins the current
Zeilberger--Zudilin exponent:

| Role | Content-addressed path and hash |
|---|---|
| Audit | `evidence/.research/proof-ledger-artifacts/sha256/19/19842fdad9fae9ea19abadeaf21121946558b181ab8eb49c57668e8823107016` |
| Source manifest | `evidence/.research/proof-ledger-artifacts/sha256/bb/bb2b0c4ed44a6e77b800ca6aef3fc1a635828890e080dce9ccd60d82c7a4d328` |
| Acceptance evidence | `evidence/.research/proof-ledger-artifacts/sha256/da/dafd9dadcac2279f02d3d2d2930405e59955f2379da13f84f2a30cc6abb2af58` |
| Zeilberger--Zudilin text | `evidence/.research/proof-ledger-artifacts/sha256/49/49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68` |

T24 adds only the new T23 near-return translation and the bounded historical
source comparison. Reusing a source pin does not upgrade T5, T9, or T11 into
evidence for T23 or C1.

## Formal bridge pins

| Role | Path | SHA-256 | Locator |
|---|---|---|---|
| Exact T23 hypothesis and energy identification | `evidence/knowledge_library/t23/T23FiniteCylinderEnergyCriterion.lean` | `8e8f560806f13a8e56bd4432aef2b689309837c8a1adb2bab72cf7c9349e6aa6` | lines 32-55 and 467-475 |
| Energy/near-return comparison and diagonal lower bound | `evidence/TheoryLib/PiLacunaryNearReturnSparsity/T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | lines 173-197 and 292-345 |
| Exact lag decomposition | `evidence/TheoryLib/PiLacunaryNearReturnSparsity/T1LagDecomposition.lean` | `932faf3f1515b5073e07ba81f70aae3cdea9d168bb7ea280bd57e2300e643a68` | lines 43-48 and 218-230 |

These are accepted machine-checked interfaces. T24 claims no new Lean
theorem and does not alter them.

## Replay closure

`EVIDENCE_HASHES.sha256` enumerates every file inside `EVIDENCE.tar`, including
T5's accepted T3 formal source, all twelve content-addressed objects named by
T5's own `LOCKED_EVIDENCE.md`, and the three additional
Salikhov/Zeilberger--Zudilin source objects used directly by T24. The replay
also regenerates T5's six PDF extraction hashes. Thus every retained hash is
replayable from the delivered directory; no `../knowledge_library`, project
checkout, or host object store is assumed.
