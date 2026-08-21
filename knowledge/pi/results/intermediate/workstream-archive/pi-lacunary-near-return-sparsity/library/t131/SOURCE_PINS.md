# T131 primary-source pins

Search date: 2026-08-10 UTC. Exactly seven primary sources were opened. PDF
page numbers below are the page labels visible in the pinned arXiv or author
PDF, not search-result snippets.

## S1. Doerr: integral discrepancy

- Benjamin Doerr, *Linear Discrepancy of Totally Unimodular Matrices*.
- Combinatorica 24 (2004), 117--125.
- DOI: <https://doi.org/10.1007/s00493-004-0007-x>
- Archived author PDF: <https://web.archive.org/web/20050412235215id_/http://www.numerik.uni-kiel.de:80/~bed/papers/lindturev.pdf>
- Delivered file: `doerr-tu-discrepancy.pdf`.
- SHA-256: `5478f98548430d1da62f0472ef107804f20cc82567fa2d79c1c149ca798b04ae`.
- Exact locators: linear-discrepancy definitions, visible PDF p. 1;
  integer-rounding remark and directed-incidence total unimodularity, p. 2;
  Theorem 1, p. 6; proof, pp. 8--10.
- Exact hypotheses/range: every totally unimodular real `r x n` matrix; every
  target `p in [0,1]^n`; conclusion `lindisc(A)<=1-1/(n+1)`, and
  `<=1-1/r` when `r>=2`.
- T131 role: C-TU floor/ceiling circulation rounding.

## S2. Holroyd--Levine--Meszaros--Peres--Propp--Wilson: Euler tours

- Alexander E. Holroyd, Lionel Levine, Karola Meszaros, Yuval Peres, James
  Propp, and David B. Wilson, *Chip-Firing and Rotor-Routing on Directed
  Graphs*.
- Exact version: arXiv:0801.3306v4, 20 June 2013.
- Primary URL: <https://arxiv.org/abs/0801.3306v4>
- PDF URL: <https://arxiv.org/pdf/0801.3306v4>
- Chapter DOI: <https://doi.org/10.1007/978-3-7643-8786-0_17>
- Delivered file: `holroyd-et-al-0801.3306v4.pdf`.
- SHA-256: `17f1a472024a680eebc7ed884d04ebd8180908c8571a14ee704a9a809b02f48d`.
- Exact locators: rotor rule, preprint p. 2; Eulerian definition and Euler-tour
  criterion, p. 21; Lemma 4.9 and proof, pp. 25--26.
- Exact hypotheses/range: finite strongly connected directed multigraph with
  equal in/out degree at every vertex; a unicycle initial state; arbitrary
  cyclic orders of outgoing edge copies. After exactly the number of edge
  copies many steps, every copy is traversed once and the state returns.
- T131 role: exact one-tour ordering and support-connectivity boundary.

## S3. Holroyd--Propp: rotor prefix constants

- Alexander E. Holroyd and James Propp, *Rotor Walks and Markov Chains*.
- Exact version: arXiv:0904.4507v3, 6 April 2010.
- Primary URL: <https://arxiv.org/abs/0904.4507v3>
- PDF URL: <https://arxiv.org/pdf/0904.4507v3>
- DOI: <https://doi.org/10.1090/conm/520/10256>
- Delivered file: `holroyd-propp-0904.4507v3.pdf`.
- SHA-256: `50b7bf9d576939add4e94208037289254ff22520af5a05250f23cd2c361660fb`.
- Exact locators: rational rotor mechanism, preprint p. 2; visit counts, p. 3;
  Theorem 4 and the definition of `K4`, p. 6; Proposition 13, p. 16, with
  proof on pp. 17--18; proof of Theorem 4, pp. 18--19.
- Exact hypotheses/range: finite irreducible positive recurrent Markov chain,
  rational finite rotor mechanism, arbitrary initial rotor configuration;
  occupation bound for every time `t`, with the explicit hitting-time constant
  `K4` stated in the theorem.
- T131 role: C-EULER partial-prefix ordering test.

## S4. Angel--Holroyd--Martin--Propp: local low-discrepancy stacks

- Omer Angel, Alexander E. Holroyd, James B. Martin, and James Propp,
  *Discrete Low-Discrepancy Sequences*.
- Exact version: arXiv:0910.1077v3, 14 July 2010.
- Primary URL: <https://arxiv.org/abs/0910.1077v3>
- PDF URL: <https://arxiv.org/pdf/0910.1077v3>
- arXiv DOI: <https://doi.org/10.48550/arXiv.0910.1077>
- Delivered file: `angel-et-al-0910.1077v3.pdf`.
- SHA-256: `dcd300ad04d9b79c1a9ad86fcd4d3c8a818e8e0312133682022cdfa9caa0c454`.
- Exact locators: Theorems 1 and 2, preprint p. 2; constructive earliest-deadline
  proof, pp. 2--4; sharpness and interval error less than two, pp. 4--5;
  rational periodic specialization, pp. 5--6.
- Exact hypotheses/range: Theorem 2 allows any sequence of discrete
  probability distributions on a countable set and controls every symbol at
  every prefix by strictly less than one.
- T131 role: local outgoing-edge stack balance in C-EULER.

## S5. Fishman--Merrill--Simmons: literal nested de Bruijn prefixes

- Lior Fishman, Keith Merrill, and David Simmons, *Uniformly de Bruijn
  Sequences and Symbolic Diophantine Approximation on Fractals*.
- Exact version: arXiv:1605.07953v3, 17 October 2016.
- Primary URL: <https://arxiv.org/abs/1605.07953v3>
- PDF URL: <https://arxiv.org/pdf/1605.07953v3>
- Journal DOI: <https://doi.org/10.1007/s00026-018-0384-2>
- Delivered file: `fishman-merrill-simmons-1605.07953v3.pdf`.
- SHA-256: `e190cb7781e2994e65169993dab3b404c9d744678c6df7abd47f00e534a05c7e`.
- Exact locators: de Bruijn word and totally/uniformly de Bruijn definitions,
  preprint p. 2 and equation (2.1); de Bruijn graph and Euler correspondence,
  pp. 3--4, especially Observation 3.2 and Remark 3.3; Corollary 4.3 and its
  extension construction, pp. 7--8.
- Exact hypotheses/range: finite alphabet size `k>=4` for Corollary 4.3's
  positive-dimensional set of totally de Bruijn expansions. Decimal `k=10`
  is within range.
- T131 role: literal cross-depth nesting in C-NEST.

## S6. Nellore--Ward: arbitrary-length balanced necklaces

- Abhinav Nellore and Rachel Ward, *Arbitrary-Length Analogs to de Bruijn
  Sequences*.
- Exact version: arXiv:2108.07759v2, 30 August 2021.
- Primary URL: <https://arxiv.org/abs/2108.07759v2>
- PDF URL: <https://arxiv.org/pdf/2108.07759v2>
- Published DOI: <https://doi.org/10.4230/LIPIcs.CPM.2022.9>
- Delivered file: `nellore-ward-2108.07759v2.pdf`.
- SHA-256: `277dcd82f88cd88092375b4023458480593bfdd26aaba0d921287fac4453492b`.
- Exact locators: Definition 1.1 and Proposition 1.1, preprint p. 2;
  lift counting Lemmas 2.1--2.2, pp. 7--8; LIFTANDJOIN and Theorem 2.4,
  p. 9, with proof continuing through p. 10; Theorems 2.5 and 2.6,
  pp. 11--13.
- Exact hypotheses/range: every alphabet size `K>=2` and every length `L>=1`;
  every word length `m<=L` has floor/ceiling `L/K^m` cyclic occurrences;
  construction takes `O(L)` time and `O(L log K)` space.
- T131 role: finite multidepth incidence balance and cycle joining in C-NEST.

## S7. Becher--Carton: nested-perfect-necklace comparator

- Veronica Becher and Olivier Carton, *Normal Numbers and Nested Perfect
  Necklaces*.
- Exact version: arXiv:1805.03713v1, 9 May 2018.
- Primary URL: <https://arxiv.org/abs/1805.03713v1>
- PDF URL: <https://arxiv.org/pdf/1805.03713v1>
- Journal DOI: <https://doi.org/10.1016/j.jco.2019.03.003>
- Delivered file: `becher-carton-1805.03713v1.pdf`.
- SHA-256: `3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448`.
- Exact locators: discrepancy definition, preprint p. 1; perfect and nested
  perfect definitions, p. 2; Theorem 1, p. 2; affine construction and Theorem
  2, pp. 3--4.
- Exact hypotheses/range: every integer base `b>=2`; concatenate arbitrary
  `(s,s)`-nested perfect necklaces for `s=2^d`; all-prefix orbit discrepancy is
  `O((log N)^2/N)`.
- T131 role: exact T122 C-NPN duplication boundary.

## Non-primary pins

- `canonical_statement.txt`, SHA-256
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- `prior-t121-REPORT.md`, SHA-256
  `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2`.
- `prior-t122-REJECTED-REPORT.md`, SHA-256
  `6ea3b7798ff4b211c0f6c3b514d062fbce8e518208c570231a1f2c32417845b7`.
