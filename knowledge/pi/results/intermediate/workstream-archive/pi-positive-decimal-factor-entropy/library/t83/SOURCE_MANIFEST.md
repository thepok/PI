# T83 source manifest

Accessed and checked: 2026-08-03 UTC.

The canonical problem is locally formulated and has no original external
source URL.  T83 performs no new literature search and reuses T60's pinned
irrationality estimate without reopening that audit.

| ID | File or source | SHA-256 | Verification and exact use |
|---|---|---|---|
| Canonical | `pi-positive-decimal-factor-entropy.txt`; no external URL | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` | Exact fixed-pi positive decimal factor-entropy question and recorded sibling variants. |
| T56 | `DecimalFactorComplexity.T56LagSectorAudit` | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` | `machine-checked`; `L_n`, strict short-sector ranges, sector partition, and the retained abstract budget. |
| T58 | `DecimalFactorComplexity.T58TriangularFejerAudit` | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` | `machine-checked`; `H_n`, strict positive frequencies, structured frequency, and ten reduction. |
| T61 | `DecimalFactorComplexity.T61VaalerAnalytic` | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` | `machine-checked`; residual mask, signed Vaaler weight, strict endpoints, exact finite expression, and conditional incidence bridge. |
| T1 | `DecimalFactorEntropy.entropyRatio_tendsto` | `8f424db10d98a42ab0e547b2abdef0db9c5b45443c05a4e01033502a2934dbdf` | `machine-checked`; used only in the explicitly conditional good-subsequence calibration. |
| T2 | `DecimalFactorComplexity.ExponentialCollisionCriterion.factorComplexity_ge_rpow_of_Q_pi_le` | `608e959dcbb2114c7102ca7d06ae0b16c8c6309c7f994e25c372c495b00f0fac` | `machine-checked`; used only in the explicitly conditional good-scale calibration. |
| T60 note | `T60_VAALER_IRRATIONALITY_FRONTIER.md` | `2a9aa7628b0611279e4b9d74659e744e8386da5308b196507e3fe47cd164b4ef` | Inspection copy.  The note is a `proof sketch`; T83 reuses only its separately source-pinned irrationality statement. |
| T60 manifest | `T60_SOURCE_MANIFEST.md` | checked by `SHA256SUMS` | Existing DOI, PDF hashes, dates, and printed-page locators. |
| ZZ20 | D. Zeilberger and W. Zudilin, *The irrationality measure of pi is at most 7.103205334137...*, DOI <https://doi.org/10.2140/moscow.2020.9.407> | PDF pin `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` | `literature-checked` by T60; definition p. 407, Propositions 7-8 and equation (18) pp. 417-418, final exponent p. 418. T83 uses `mu=888/125`, `lambda=763/125`, and the unknown eventual onset `Q0`. |
| T82 | `T82_METRIC_SIGNED_RESIDUAL.md` | `f630bbfb5ff410699e52b201947cdbe34e66329dad6c11efee5f174752684322` | `proof sketch`; motivation only. No T82 assertion is used as a discharged premise. |

`T83_CROSS_SCALE_FIXED_PI_AUDIT.md` rederives the finite cross-scale formulas.
`t83_cross_scale_replay.py` is a dependency-free `experiment`; its output is
not proof of a universal or fixed-pi estimate.
