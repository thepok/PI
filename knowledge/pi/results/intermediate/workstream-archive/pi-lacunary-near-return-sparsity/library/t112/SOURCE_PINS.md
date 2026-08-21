# T112 source pins

Search date: 2026-08-10 UTC. All five files are primary author/preprint copies.
Text derivatives were produced locally with `pdftotext -layout` for the four
retained source cards and are separately hashed. The screened S5 source is
delivered as its pinned PDF only. Printed-page locators refer to the PDF page
labels when present; derivative line locators are stable within delivered text
files.

## S1: Spiegelhofer--Wallner

- Lukas Spiegelhofer and Michael Wallner, *The binary digits of n+t*.
- arXiv: <https://arxiv.org/abs/2005.07167v3>
- PDF: <https://arxiv.org/pdf/2005.07167v3>
- DOI: <https://doi.org/10.2422/2036-2145.202105_069>
- Delivered PDF: `spiegelhofer-wallner-2005.07167v3.pdf`
- PDF SHA-256: `4e7ed13cab1b9cd23a8886db4fda3919ac8924873770695fb243f5c0b5116130`
- Text derivative: `spiegelhofer-wallner-2005.07167v3.txt`
- Text SHA-256: `4a8c93a160a492b463dd3f5d589d8db29392c330081a2296d0d03f44bec79b81`
- Inspected locators: equations (1.3)--(1.6), preprint p. 3, derivative lines
  130--167; Theorem 1.2 and effectiveness discussion, pp. 3--4, derivative
  lines 168--203; characteristic-function recurrence in Section 2.1; proof of
  Theorem 1.2 in Section 3.
- Claim used: exact carry recurrence and uniform local-limit formula in the
  number `M` of maximal binary one-blocks.

## S2: Hosten--Janvresse--de la Rue

- Yohan Hosten, Elise Janvresse, Thierry de la Rue, *A central limit theorem
  for the variation of the sum of digits*.
- arXiv: <https://arxiv.org/abs/2111.05030v2>
- PDF: <https://arxiv.org/pdf/2111.05030v2>
- DOI: <https://doi.org/10.1214/22-AIHP1346>
- Delivered PDF: `hosten-janvresse-delarue-2111.05030v2.pdf`
- PDF SHA-256: `cd910d2cb105c2887ff9ae6c25672973f0093c8ebd718349d829e0c79eccafa3`
- Text derivative: `hosten-janvresse-delarue-2111.05030v2.txt`
- Text SHA-256: `08f3a4f82e0719a748a37982dc1fb870b834a257ea51e77882ae81391bcbd0ec`
- Inspected locators: block definition and Theorems 1.2--1.4, preprint
  pp. 2--4, derivative lines 90--174; Proposition 3.1 and equation (19), p. 12,
  derivative lines 704--751; Lemma 4.3, p. 22, derivative lines 1347--1404.
- Claim used: variance range, CLT/Kolmogorov rate, exact digit recurrence, and
  geometric phi-mixing estimate.

## S3: Diaconis--Fulman

- Persi Diaconis and Jason Fulman, *Carries, Shuffling, and an Amazing Matrix*.
- arXiv: <https://arxiv.org/abs/0806.3583v1>
- PDF: <https://arxiv.org/pdf/0806.3583v1>
- DOI: <https://doi.org/10.4169/000298909X474864>
- Delivered PDF: `diaconis-fulman-0806.3583v1.pdf`
- PDF SHA-256: `348abf1bc7b06a1527d285dc5274bd72b670b4cf2e19eec391118a659c44312e`
- Text derivative: `diaconis-fulman-0806.3583v1.txt`
- Text SHA-256: `ad61f1515402522501ccc47b0a5d41134f370090dcf6dc69d4738d1be91c0580`
- Inspected locators: formulas (H1), (H4), and (H5), printed pp. 1--2,
  derivative lines 20--104; Theorem 4.1, p. 9, derivative lines 453--485;
  Theorem 4.3, p. 10, derivative lines 535--555.
- Claim used: exact carries transition matrix, stationary Eulerian law,
  complete spectrum, Gaussian column law, and asymptotic separation profile
  on the cutoff window.

## S4: Balister

- Paul Balister, *Bounds on Rudin--Shapiro polynomials of arbitrary degree*.
- arXiv: <https://arxiv.org/abs/1909.08777v1>
- PDF: <https://arxiv.org/pdf/1909.08777v1>
- Delivered PDF: `balister-1909.08777v1.pdf`
- PDF SHA-256: `53cb919f9e23c2edddd0141bb4d51a6c570f5ae4f5734bc1030d729878e42cc3`
- Text derivative: `balister-1909.08777v1.txt`
- Text SHA-256: `2ea1eb9f92b97ec3775b7f360053ecd16829fd7846292abaa1e5a9319afd8b4a`
- Inspected locators: polynomial recurrence, preprint p. 1, derivative lines
  23--32; coefficient recurrence (1), p. 1, derivative lines 33--46; Theorems
  1 and 3, p. 2, derivative lines 55--108; Proposition 4 and Lemma 6, p. 3,
  derivative lines 111--157.
- Claim used: exact Hadamard cocycle, dyadic energy identity, and uniform
  arbitrary-prefix/interval square-root bounds.

## S5: Heuberger--Kropf--Wagner

- Clemens Heuberger, Sara Kropf, Stephan Wagner, *Variances and covariances in
  the Central Limit Theorem for the output of a transducer*.
- arXiv: <https://arxiv.org/abs/1404.3680v2>
- PDF: <https://arxiv.org/pdf/1404.3680v2>
- DOI: <https://doi.org/10.1016/j.ejc.2015.03.004>
- Delivered PDF: `heuberger-kropf-wagner-1404.3680v2.pdf`
- PDF SHA-256: `20944e0a9cc1de10285ecfb0e664454cf6b3719dd23b27c805761bc9f993a1e9`
- Inspected locators: Definition 3.8 and Theorem 3.9, preprint pp. 8--9;
  Example 4.1, p. 13; proof of Theorem 3.9 and resolvent formula,
  pp. 18--19.
- Claim used: exact finite-transducer transition matrices, determinant
  operator, random-word covariance/CLT, and width-w NAF example.

## Local checked-interface pins

These are not counted as primary literature sources.

- `knowledge_library/t64/AggregateFejerCriterion.lean`:
  `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16`.
- `knowledge_library/t107/T107AveragedTriangularFejer.lean`:
  `45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`.
- Canonical statement:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
