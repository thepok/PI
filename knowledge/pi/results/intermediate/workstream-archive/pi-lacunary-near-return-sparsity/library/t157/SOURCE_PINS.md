# T157 source pins

Audit date: 2026-08-12 UTC. `pdftotext -layout` generated each delivered text
derivative. Physical PDF pages and printed pages coincide for S1--S4 in the
cited ranges. Source statements are `literature-checked`; local substitutions
remain `proof sketch`.

## S1: Nguyen--Vu

- Authors: Hoi Nguyen and Van Vu.
- Title: *Optimal Inverse Littlewood-Offord theorems*.
- Version: arXiv:1004.3967v2, revised 2011-01-16.
- URL: https://arxiv.org/pdf/1004.3967
- Landing page: https://arxiv.org/abs/1004.3967
- PDF SHA-256: `2f2c66acd3e8d80602d0c98841d5ec0bef8ab2aa04a6472a587aa34e8694f83e`.
- Text SHA-256: `57bd3b9e33d6b5941f88b96a8b502774bdd0dfe393c340ed2a5199042afe25f8`.
- Exact locator: printed/physical pp. 6--7, Theorem 2.1 from the heading through
  the displayed bound for `|Q|`; Theorem 2.5 from its heading through the
  displayed bound for `|Q|`.
- Source range used: fixed positive `C`, `epsilon<1`; integer multiset for
  Theorem 2.1; `n^epsilon<=n'<=n` in Theorem 2.5; proper symmetric GAP,
  bounded rank, and stated exceptional-coordinate/volume bounds.

## S2: Rudelson--Vershynin

- Authors: Mark Rudelson and Roman Vershynin.
- Title: *The Littlewood-Offord Problem and invertibility of random matrices*.
- Version: arXiv:math/0703503v2; journal reference Adv. Math. 218 (2008),
  600--633.
- URL: https://arxiv.org/pdf/math/0703503
- Landing page: https://arxiv.org/abs/math/0703503
- PDF SHA-256: `e0a00846c9d66057e670809052e0a7a10d04846243169d5b04ff595b0f6c4471`.
- Text SHA-256: `9c71a75cdd3d6261261673dac66968ba0d8adab44e94eec9e2981eed98235bfe`.
- Exact locator 1: printed/physical pp. 6--7, Definition 1.4 and Corollary 1.6,
  from each heading through its final displayed parameter condition.
- Exact locator 2: printed/physical pp. 20--21, Theorem 4.1 from the heading
  through the complete inequality and Remarks 1--2.
- Source range used: equal-order nonzero coefficients `1<=|a_k|<=K`,
  `0<alpha<1/(6K)`, `0<kappa<n`, and the displayed essential-LCD small-ball
  bound; approximate arithmetic progression only under Corollary 1.6's stated
  scale condition.

## S3: Ferber--Jain--Luh--Samotij

- Authors: Asaf Ferber, Vishesh Jain, Kyle Luh, and Wojciech Samotij.
- Title: *On the counting problem in inverse Littlewood--Offord theory*.
- Version: arXiv:1904.10425v1, 2019-04-23.
- URL: https://arxiv.org/pdf/1904.10425
- Landing page: https://arxiv.org/abs/1904.10425
- PDF SHA-256: `6f4e7593b3024ccf2d2db70c302cec27cc41642b76c3a372133498e62193f687`.
- Text SHA-256: `985579e6e44c8ba720ad10961f60d5ce8b5a43d7dccaf190179f553956c7b860`.
- Context locator: printed/physical pp. 1--2, Theorem 1.1, from the heading
  through the displayed Halasz inequality and the statement that `k` may grow.
  This is inspected as the authors' restatement, not retained as an original S3
  theorem.
- Retained exact locator: printed/physical pp. 4--5, Theorem 1.4, Definition 1.5,
  Lemma 1.6, and Theorem 1.7, including support/parameter conditions and the
  complete counting bound.
- Source range used: odd prime, nonzero finite-field vector,
  `30M<=|supp(a)|`, and `80kM<=n` for Theorem
  1.4; the exact hereditary relation-count set in Theorem 1.7.

## S4: Tao--Vu

- Authors: Terence Tao and Van Vu.
- Title: *A sharp inverse Littlewood-Offord theorem*.
- Version: arXiv:0902.2357v2, revised 2009-10-20.
- URL: https://arxiv.org/pdf/0902.2357
- Landing page: https://arxiv.org/abs/0902.2357
- PDF SHA-256: `9c7e700ef85543fc665380e7a64b81ace174d9d7ffbd297246e547ad9b7d6018`.
- Text SHA-256: `d37050f992a31ffaa1f4e30df98a38051f1f07a2c8ca798a6e5fa4b127089aed`.
- Exact locator: printed/physical pp. 4--5, Theorems 1.9 and 1.10 from each
  heading through all displayed hypotheses and conclusions.
- Disposition: inspected inverse-concentration comparator, not retained.
  S1 gives the later optimal theorem used for the literal substitution.

## S5: Guibas--Odlyzko retrieval blocker

- Authors: L. J. Guibas and A. M. Odlyzko.
- Title: *String overlaps, pattern matching, and nontransitive games*.
- Journal: J. Combin. Theory Ser. A 30(2) (1981), 183--208.
- DOI: https://doi.org/10.1016/0097-3165(81)90005-4
- Exact bibliographic range inspected: Crossref primary record for DOI,
  journal pp. 183--208.
- Retrieval result: the publisher text-mining endpoint returned HTTP 406 and
  no PDF was available for exact theorem inspection. No source theorem or quote
  from S5 is used in REPORT.md.

## S6: Arratia--Waterman retrieval blocker

- Authors: Richard Arratia and Michael S. Waterman.
- Title: *Critical Phenomena in Sequence Matching*.
- Journal: Ann. Probab. 13(4) (1985).
- DOI: https://doi.org/10.1214/aop/1176992808
- Exact bibliographic range inspected: Crossref/Project Euclid primary record,
  volume 13, issue 4.
- Retrieval result: the advertised PDF request returned an HTML publisher
  challenge rather than a PDF. No source theorem or quote from S6 is used in
  REPORT.md.

## Cap and uniqueness ledger

Bounded query/disposition order:

1. `optimal inverse Littlewood Offord theorem GAP exceptional coordinates`:
   opened S1 and retained C-GAP.
2. `sharp inverse Littlewood Offord Tao Vu`: opened S4 and screened it in favor
   of the later optimal S1 theorem.
3. `Littlewood Offord essential LCD small ball probability`: opened S2 and
   retained C-LCD.
4. `counting problem inverse Littlewood Offord Halasz relations`: opened S3 and
   retained its original finite-field results as C-HAL.
5. `String overlaps pattern matching nontransitive games Guibas Odlyzko`:
   opened S5's DOI record; retrieval blocker.
6. `Critical Phenomena in Sequence Matching Arratia Waterman`: opened S6's
   DOI record; retrieval blocker.

The search stopped because the candidate cap was reached and all retained
encodings met the same zero-vector/support gate.

```text
INSPECTED_PRIMARY_SOURCES: S1,S2,S3,S4,S5,S6
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
RETAINED_SOURCE_THEOREM_TUPLES: C-GAP,C-LCD,C-HAL
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
```

Tuple keys use the complete PDF SHA and full locator set. S5--S6 have no tuple
keys because retrieval failed and no mathematical claim was retained.
