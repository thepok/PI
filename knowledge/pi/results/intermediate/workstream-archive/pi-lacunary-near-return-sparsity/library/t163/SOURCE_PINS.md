# T163 source pins

Search and retrieval date: 2026-08-12 UTC. These five primary PDFs were
retrieved from the displayed versioned arXiv URLs and inspected through the
delivered `pdftotext -layout` extracts. PDF bytes, not extracts, are the source
pins. The search stopped at five sources, below the cap of ten.

| ID | domain | primary source and URL | delivered files and SHA-256 | exact inspected locator | use |
|---|---|---|---|---|---|
| S1 | Mahler/functional equations | Dzmitry Badziahin, *On spectrum of irrationality exponents of Mahler numbers*, arXiv:1806.02946v1, <https://arxiv.org/abs/1806.02946v1>, <https://arxiv.org/pdf/1806.02946v1> | `badziahin-1806.02946v1.pdf` `87992e4a5f78c9c1d7b38e55477eb1d1fef3dfd2698fff9916e18395459d0c66` | Theorems 1-2, printed pp. 2-3 (PDF pp. 2-3); Theorem 3, printed p. 3; Proposition 1, printed pp. 3-4 | screened duplicate/closed |
| S2 | restricted-denominator approximation | Lucas Tapia, *Multiplicative Diophantine Approximation on Planar Lines with Restricted Denominators*, arXiv:2602.22512v1, <https://arxiv.org/abs/2602.22512v1>, <https://arxiv.org/pdf/2602.22512v1> | `tapia-2602.22512v1.pdf` `613ef7bb0c80e0ed5e3a609a509be585391dabca43d05cdb6565808c25f6fd57`; extract `dda21767b0d4af4855f426812c3f649dd9952472465bac73557e25a6405bbbdf` | Definition (6) and Theorem 1, printed pp. 2-3 (PDF pp. 2-3), extract lines 112-139; Corollary 3, printed p. 3, lines 157-169 | retained C-GCD |
| S3 | arithmetic/fractal Fourier decay and restricted denominators | Kyle Hambrook, *Explicit Salem sets and applications to metrical Diophantine approximation*, arXiv:1604.00411v1, <https://arxiv.org/abs/1604.00411v1>, <https://arxiv.org/pdf/1604.00411v1> | `hambrook-1604.00411v1.pdf` `74ef6d8595be80a1dd139837f6f0a91ec3f43c4277a805ffe38966e9c7e0673c`; extract `4c884d213a29de16b16372017e8ebc4e54099715d60871760bc2c3ea1e9bca33` | Theorem 1.1, printed pp. 1-2 (PDF pp. 1-2), extract lines 30-54; exact gap (8.5), printed p. 18, lines 975-983; Lemma 9.1, printed pp. 18-19, lines 988-1053 | retained with S4 as C-SHELL |
| S4 | arithmetic/fractal Fourier decay | Thomas Cai and Kyle Hambrook, *On the Exact Fourier Dimension of Sets of Well-Approximable Matrices*, arXiv:2403.19410v1, <https://arxiv.org/abs/2403.19410v1>, <https://arxiv.org/pdf/2403.19410v1> | `cai-hambrook-2403.19410v1.pdf` `c340647222371d95274a053ac2cb4ed4a974ad5da962efa17d2ef558e6f8a57f`; extract `7050e30c25b7a67be2247196c8ab1198723cc7500557566095640ccee4546cbb` | Theorem 1.4.1 and Propositions 1.4.3-1.4.4, printed pp. 3-4 (PDF pp. 3-4), extract lines 137-168; Lemma 4.3.2, printed pp. 16-17, lines 845-909 | retained with S3 as C-SHELL |
| S5 | symbolic collision theory | Vanessa Barros, Lingmin Liao, Jerome Rousseau, *On the shortest distance between orbits and the longest common substring problem*, arXiv:1808.00078v2, <https://arxiv.org/abs/1808.00078v2>, <https://arxiv.org/pdf/1808.00078v2> | `barros-liao-rousseau-1808.00078v2.pdf` `86cdfce61d7b1a88e81c46354871750eb7f84e49aaf5d0ed11d4dae18bafea8e`; extract `dc5ac4f6ee24ddb85cb2e9c107107c0efa91e0bf7374d6cd461913f96fcdd7b2` | longest common substring and Renyi definitions, printed pp. 5-6 (PDF pp. 5-6), extract lines 242-264; Theorem 7 and hypotheses, printed p. 6, lines 265-290 | retained C-XMATCH |

The immutable non-literature control input is `canonical_statement.txt`,
SHA-256 `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

## Duplication screen

The prior theorem/source ledger supplied with the accepted T155 artifact had
no exact arXiv tuple for S1-S5. Exact tuple absence is not a novelty claim.
S1 was nevertheless rejected because its continued-fraction degree-gap output
is a renamed Mahler-lifting/irrationality-measure branch adjacent to T89, T114,
T127, and T136. In the refreshed snapshot, accepted T160 pins six source tuples:
Dębowski `1609.04683v4`, Kosolobov `2410.00209v1`, Pirsic--Stockinger
`1710.09313v2`, He--Liao `2302.05149v2`, Fouvry--Kowalski--Michel
`1307.0135v2`, and Fouvry--Kowalski--Michel--Raju--Rivat--Soundararajan
`1508.00512v3`. Accepted T162 pins Dvorakova--Medkova--Pelantova
`2003.06916v3`, Klouda--Medkova--Pelantova--Starosta `1801.09203v3`, and
Drappeau--Mullner `1710.01091v1`. T163 reserves those complete source/theorem
tuples, imports no proof-sketch deduction from either artifact, and did not
count them among its five inspected sources.
