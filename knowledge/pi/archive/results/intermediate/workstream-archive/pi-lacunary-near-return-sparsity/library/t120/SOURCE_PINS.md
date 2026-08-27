# T120 source pins

Audit date: 2026-08-10 UTC. Exactly four primary papers were opened and
retained. A PDF and its text derivative count as one source.

## S1: Gouezel

- Sebastien Gouezel, *Sharp polynomial estimates for the decay of
  correlations*.
- arXiv: `math/0202147v1`, 15 February 2002.
- URL: <https://arxiv.org/pdf/math/0202147>
- DOI: <https://doi.org/10.1007/BF02787541>
- PDF: `gouezel-math0202147.pdf`
- PDF SHA-256:
  `c17395927edc5f02a5edbdf9975bd13fcd5b0d28ae339addb442b046d07b6343`
- Text: `gouezel-math0202147.txt`
- Text SHA-256:
  `18f88fcdaf54253738526534a244bcc818f2ece21c6aeac792a7d7fa79c6b100`
- Exact locators: preprint p. 4, Corollary 1.5, derivative lines 161--178,
  for the LSV map and correlation ranges; preprint p. 31, Section 7.1 and
  Corollary 7.1, derivative lines 1757--1779, for the map, countable Markov
  partition, and induced map; preprint p. 31, equations (9)--(10) and the
  following paragraph, derivative lines 1780--1799, for the integrated return
  tail and exact constant.
- Role: R-LSV only.

## S2: Kessebohmer--Slassi

- Marc Kessebohmer and Mehdi Slassi, *Critical waiting time processes in
  infinite ergodic theory*.
- arXiv: `math/0607681v1`, 26 July 2006.
- URL: <https://arxiv.org/pdf/math/0607681>
- DOI: <https://doi.org/10.1142/S0219493707001962>
- PDF: `kessebohmer-slassi-math0607681.pdf`
- PDF SHA-256:
  `ec9b2b54a6e0ca0bfade2564d15a9ac66213679a00bf6072c4cf103b0a968114`
- Text: `kessebohmer-slassi-math0607681.txt`
- Text SHA-256:
  `8404284f280f61436bd4c82e10ee08a2699ad66f51cb59f44a96b7fd55e2e0d7`
- Exact locators: preprint pp. 19--20, derivative lines 1170--1215, for Gauss
  digits, the process, and Theorem 4.1; pp. 20--21, derivative lines
  1225--1286, for the Farey map, invariant density, intervals `K_n`, entry
  time, and induced Gauss map; pp. 21--22, derivative lines 1288--1346, for
  return times, Lemma 4.2, and the asymptotic tail integral in the proof of
  Theorem 4.1. REPORT records the printed `A_1` label/index inconsistency and
  does not use it as an exact finite-`n` identity. The `K_1` conditional tail
  in REPORT (4.4) is an explicitly labeled deduction from the source's map,
  digit, and return-time formulas.
- Role: R-FAR only.

## S3: Isola

- Stefano Isola, *On the rate of convergence to equilibrium for countable
  ergodic Markov chains*.
- arXiv: `math/0308018v1`, 4 August 2003.
- URL: <https://arxiv.org/pdf/math/0308018>
- PDF: `isola-math0308018.pdf`
- PDF SHA-256:
  `24cef1306ff28a06330e4bfa3dba144dee85c733ed3c3b8bd6bee62ffa54b5f3`
- Text: `isola-math0308018.txt`
- Text SHA-256:
  `fad73cbf17f501a2f04f44fe1e2f755452a653fbbde8d7bed2d99ef0f7e1d8a6`
- Exact locators: preprint pp. 6--7, Theorem 1 and Corollary 1, derivative
  lines 269--332, for ergodic degree, `O_epsilon`, convergence, stationary
  path measure, and correlations; p. 13, derivative lines 699--730, for the
  explicit failure of uniformity in departing state; pp. 14--15, derivative
  lines 780--830, for the chain, return law, stationary distribution, and
  renewal interpretation; pp. 16--17, Theorem 2, derivative lines 833--876,
  for the fixed-observable asymptotic and hypotheses; p. 18, equation (3.4),
  derivative lines 889--917, for the renewal generating function.
- Role: R-ISO only.

## S4: Jordan--Sahlsten

- Thomas Jordan and Tuomas Sahlsten, *Fourier transforms of Gibbs measures for
  the Gauss map*.
- arXiv: `1312.3619v3`, 2 February 2015; published in *Mathematische
  Annalen* 364 (2016), 983--1023.
- URL: <https://arxiv.org/pdf/1312.3619v3>
- DOI: <https://doi.org/10.1007/s00208-015-1241-9>
- PDF: `jordan-sahlsten-1312.3619v3.pdf`
- PDF SHA-256:
  `21e65b4456ea71e2113a3f2a5191b6d9a1061c6732dfa0618d0e4891ba70cb75`
- Text: `jordan-sahlsten-1312.3619v3.txt`
- Text SHA-256:
  `2b8c086b1f45b13e463bade618ec521525a24510eb9700fc3efdb3ff4cef6483`
- Exact locators: preprint pp. 3--4, equations (1.2)--(1.3) and Theorem
  1.3, derivative lines 160--201, for polynomial digit tail and Fourier decay;
  p. 5, derivative lines 256--276, for the Minkowski weights, exact exponential
  tail, and almost-everywhere Corollary 1.6; pp. 6--8, derivative lines
  307--418, for the full countable Gauss coding and inverse branches; pp.
  13--14, Proposition 4.4, derivative lines 708--769, for the exact tail and
  pressure ranges; p. 18, equations (6.1)--(6.3), derivative lines 950--973,
  for the displayed Fourier exponent.
- Role: R-JS only.

## Immutable and local interface pins

- `canonical_statement.txt` SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- T7 machine-checked interface:
  `knowledge_library/t7/FiniteCylinderEnergy.lean`; the exact ordered
  collision identity is lines 126--171 and the factor-three metric comparison
  is lines 247--344. No T7 premise is asserted here.
- T107 machine-checked interface:
  `knowledge_library/t107/T107AveragedTriangularFejer.lean`, SHA-256
  `45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`;
  literal boundary/Fourier definitions are lines 31--69 and the triangular
  defect is lines 150--173. No T107 premise is asserted here.

## Required prior fingerprints

These are comparison pins, not theorem premises.

| Item | Readable report pin | Level used |
|---|---|---|
| T39 | SHA `ff5ae4e484dfa42957064ab63302729162e5fcc164c4842bbf96c9fbaac93b5d` | source audit `literature-checked` |
| T90 | SHA `730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0` | sources `literature-checked`; transfers `proof sketch` |
| T103 | SHA `ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0` | sources `literature-checked`; deductions `proof sketch` |
| rejected T109 | report SHA `6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf`; skeptic SHA `987966c0c2074ab1b058bd16024806165f3e63357c51c5d46524faafc25fc558` | sources `literature-checked`; transports `proof sketch`; skeptic verdict `escalate` |
| T112 | SHA `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa` | sources `literature-checked`; transfers `proof sketch` |
| T115 | SHA `29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36` | sources `literature-checked`; deductions `proof sketch` |
| T117 | SHA `ee6974209f7e6064f30ec3ae83240cb1e7994e66566e920417dbf361da0ff30b` | sources `literature-checked`; deductions `proof sketch` |
| active T118 | vendored `prior-t118-REPORT.md`, SHA `f7f2491e5d11a11268d7e75de452950073fba75e1682ea883b52b608a520bf4b` | sources `literature-checked`; deductions `proof sketch`; rerun pending |
| active T119 | no readable artifact at cutoff; agenda-level collision-to-Hankel-rank exclusion only | unavailable; no unpublished content inferred |

The orchestration snapshot that showed the active T118/T119 leases had SHA-256
`6d42a3ca0e9432ac04e2372f7d9f2f5e59e4750c19a49dea30e03880b604ad87`.
It is not a delivered dependency and is cited only to timestamp the
availability boundary.
