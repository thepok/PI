# T116 source pins

Audit and retrieval date: 2026-08-10 UTC.

Exactly four primary sources were inspected, one per searched lane. PDF bytes
are authoritative. Text files are `pdftotext -layout` derivatives used for
line-addressable locators. No OCR was used.

## S1: algorithmic/computable avoidance

Matthieu Rosenfeld and Alexander Shen, *Local obstructions in sequences
revisited*.

- Primary URL/version: <https://arxiv.org/abs/2503.20529v1>
- PDF URL: <https://arxiv.org/pdf/2503.20529v1>
- Version/date: arXiv:2503.20529v1, 2025-03-26.
- Delivered PDF: `rosenfeld-shen-2503.20529v1.pdf`
- PDF SHA-256: `35e39cbf5006aa1dd459a51df5225f3fdbde214ddd4fb03d9bb4f81660e43f1c`
- Text derivative: `rosenfeld-shen-2503.20529v1.txt`
- Text SHA-256: `f9ad4a894679bbd3a7db5787a5bdef87fcab74265a3bb251438f111086b076a3`

Exact locators:

- Theorem 1 and proof, printed pp. 2-3, derivative lines 87-117: weighted
  `q`-ary tree game and condition `beta(1+omega)<=q`.
- Theorem 2 and proof, printed pp. 3-4, derivative lines 119-149: computable
  strategy, membership program, convergence modulus, and finite-list special
  case.
- Theorem 8 statement, printed pp. 9-10, derivative lines 430-448: advertised
  constant-shell denominator theorem.
- Theorem 8 proof and Lemma 1, printed pp. 10-11, derivative lines 450-524:
  dyadic schedule, at most three descendants per denominator, and the actual
  weighted-game inequality used by the proof.

Source-status boundary: this is a 2025 arXiv preprint. T116 checks its source
statements but does not represent them as independently refereed or
machine-checked. The mismatch between Theorem 8's display and its proof is
reported explicitly; T116 uses only Theorems 1-2.

## S2: symbolic entropy/collision coding

Lior Fishman, Keith Merrill, and David Simmons, *Uniformly de Bruijn
Sequences and Symbolic Diophantine Approximation on Fractals*, Annals of
Combinatorics 22 (2018), 271-293.

- Repository URL: <https://eprints.whiterose.ac.uk/id/eprint/126995/>
- PDF URL: <https://eprints.whiterose.ac.uk/id/eprint/126995/8/10.1007_2Fs00026_018_0384_2.pdf>
- DOI: <https://doi.org/10.1007/s00026-018-0384-2>
- Version/date: published version, 2018.
- Delivered PDF: `fishman-merrill-simmons-2018.pdf`
- PDF SHA-256: `a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4`
- Text derivative: `fishman-merrill-simmons-2018.txt`
- Text SHA-256: `34621967d63c119b5b1f0d25fda15804cdfbb2dafaae17e0008ec9b9eaa9eff8`

Exact locators:

- Section 2 immediately preceding and including definition (2.1), printed
  pp. 3-4, derivative lines 137-155: finite non-cyclic de Bruijn words followed
  by infinite, totally, and uniformly de Bruijn variants.
- Remark 3.3, printed p. 5, derivative lines 267-279: Hamiltonian-cycle
  correction.
- Proposition 4.2, printed p. 9, derivative lines 503-540: selected Eulerian
  path family and exact cardinality.
- Corollary 4.3 and proof, printed pp. 10-11, derivative lines 550-617:
  order-by-order extension family and positive dimension for `k>=4`.

Role: effective symbolic survivor and exact comparison with T111. The odd
decimal specialization, lexicographic selector, interval recurrence, parity
argument, and `Q_x=N` identity are T116 proof-sketch deductions, not source
claims.

## S3: restricted-denominator approximation

Nikolay G. Moshchevitin, *Density modulo 1 of sublacunary sequences:
application of Peres-Schlag's arguments*.

- Primary URL/version: <https://arxiv.org/abs/0709.3419v2>
- PDF URL: <https://arxiv.org/pdf/0709.3419v2>
- Version/date: arXiv:0709.3419v2, 2007-10-20.
- Journal DOI: <https://doi.org/10.1007/s10958-012-0660-3>
- Delivered PDF: `moshchevitin-0709.3419v2.pdf`
- PDF SHA-256: `d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5`
- Text derivative: `moshchevitin-0709.3419v2.txt`
- Text SHA-256: `117fc4dee8a4d5bbeef0d1d36af90599146d228f0af6529068bdd437b2ae5278`

Exact locators:

- Definition (1), printed p. 2, derivative lines 66-71: variable growth
  function `H(n,tau)`.
- Theorem 1, printed pp. 2-3, derivative lines 73-105: finite nested closed
  avoidance sets and quantitative measure lower bound.
- Theorem 2, printed pp. 2-3, derivative lines 107-129: infinite nonempty
  avoidance set under conditions (i), (ii'), and (iii').
- Lemmas 1-2 and Theorem 1 proof, printed pp. 3-6, derivative lines 144-362:
  dyadic covers and measure induction.

Role: variable-threshold comparator. The source conclusion is nonemptiness;
it does not state a computable member or safe-child algorithm.

## S4: fixed-point/lacunary game dynamics

Ryan Broderick, Lior Fishman, and Dmitry Kleinbock, *Schmidt's game,
fractals, and orbits of toral endomorphisms*, Ergodic Theory and Dynamical
Systems 31 (2011), 1095-1107.

- Primary URL/version: <https://arxiv.org/abs/1001.0318v3>
- PDF URL: <https://arxiv.org/pdf/1001.0318v3>
- DOI: <https://doi.org/10.1017/S0143385710000374>
- Version/date: arXiv:1001.0318v3, 2018-09-21; journal publication 2011.
- Delivered PDF: `broderick-fishman-kleinbock-1001.0318v3.pdf`
- PDF SHA-256: `af22faa5bd33c9bf719c0c6fbfdf3c173d35ea7bee71368cffd0da0c0f0c9b36`
- Text derivative: `broderick-fishman-kleinbock-1001.0318v3.txt`
- Text SHA-256: `c7fffee401ed7249ca6d9641b30b88738bd861a7b57c597ad7a3f4f97724e259`

Exact locators:

- Theorem 1.3, printed p. 3, derivative lines 112-155: winning avoidance for
  lacunary matrix sequences and uniformly discrete targets.
- Schmidt-game definition, printed pp. 4-5, derivative lines 190-229.
- Absolute decay definition and Lemma 3.2, printed pp. 5 and 7-8, derivative
  lines 246-265 and 347-388: constants and measure-based center choice.
- Theorem 4.1 and proof, printed pp. 8-9, derivative lines 390-480: explicit
  lacunarity ratio, game parameters, and avoidance constant.

Role: fixed-dynamics/game comparator. The ordered decimal-difference sequence
fails its uniform lacunarity hypothesis, and the source does not state an
effective rational-center selector.

## Retrieval boundary

S1 and S4 were retrieved from their exact arXiv version URLs during this run.
S2 and S3 were reused byte-for-byte from the supplied pinned library and
hash-checked after copying. Every retrieval succeeded. No image-only source,
OCR, secondary survey, or silently failed source is used.
