# T155 primary-source pins

Audit date: 2026-08-12 UTC. Exactly three original research PDFs were opened,
one in each searched domain. Their exact PDF hashes, stable identifiers, and
normalized theorem tuples were absent from the supplied prior hash/pin ledger
before retention. No OCR was used.

## S1: Stringology and maximal repetitions

- Hideo Bannai, Tomohiro I, Shunsuke Inenaga, Yuto Nakashima, Masayuki
  Takeda, and Kazuya Tsuruta, *The "Runs" Theorem*.
- Primary URLs: <https://arxiv.org/abs/1406.0263v7> and
  <https://arxiv.org/pdf/1406.0263v7>.
- DOI: <https://doi.org/10.1137/15M1011032>.
- File: `bannai-et-al-1406.0263v7.pdf`.
- SHA-256: `9bbe130b1a864a4932c09c32a7dad27b97b4910f05ce410cfb0a9535a74b6ce7`.
- Stable tuple: `arXiv:1406.0263v7|Definition1;Lemma8;Theorem9;Theorem10`.
- Locator and range: Definition 1, PDF p. 3, defines a run and exponent;
  Lemma 8, PDF pp. 3--4, gives disjoint beginning-position sets; Theorems
  9--10, PDF p. 4, give `rho(n)<n` and `sigma(n)<=3n-3`. Full inspected range:
  PDF pp. 3--4.
- Scope: deterministic finite words. It is screened, not retained, because its
  positional charging normalizes to the T95/T100 charging branch.

## S2: Extremal graph theory

- Tao Jiang and Sean Longbrake, *Tree-degenerate graphs and nested dependent
  random choice*.
- Primary URLs: <https://arxiv.org/abs/2201.10699v1> and
  <https://arxiv.org/pdf/2201.10699v1>.
- File: `jiang-longbrake-2201.10699v1.pdf`.
- SHA-256: `724204236a460893fc01128bdb7231de39531d57c7c4ea8e412b4cb4de83deeb`.
- Stable tuple: `arXiv:2201.10699v1|Definition3.1;Theorem3.2;Theorem3.3`.
- Locator: Definition 3.1 and Theorems 3.2--3.3, PDF p. 6.
  Definition 3.1 recursively defines `i`-good sequences by common-neighborhood
  richness; Theorem 3.2 gives the weighted nested-goodness sum and existence
  bound; Theorem 3.3 gives its `r=1` specialization. Full inspected range: PDF
  pp. 5--6.
- Scope: deterministic dense graphs. It is screened, not retained, because it
  strengthens common-neighborhood heavy fibers, the direction prohibited by
  active T153 locality-to-occupancy.

## S3: Probability and locally dependent point processes

- Louis H. Y. Chen and Aihua Xia, *Stein's method, Palm theory and Poisson
  process approximation*, Annals of Probability 32 (2004), 2545--2569.
- Primary URLs: <https://arxiv.org/abs/math/0410169> and
  <https://arxiv.org/pdf/math/0410169>.
- DOI: <https://doi.org/10.1214/009117904000000027>.
- File: `chen-xia-math0410169.pdf`.
- SHA-256: `3640caf66dd78cc1fa3e4ad69cd5b250123c9896e86c17962912cc3fbc82f87e`.
- Stable tuple: `arXiv:math/0410169|Theorem4.1`.
- Locator and range: Theorem 4.1 and Remarks 4.2--4.3, printed pp. 2555--2556,
  PDF pp. 11--12. The theorem bounds second-Wasserstein distance for a marked
  Bernoulli point process using neighborhoods, outside-neighborhood dependence,
  and conditional couplings. Full inspected range: PDF pp. 11--12.
- Scope: random marked Bernoulli processes on a probability space. It supplies
  no deterministic theorem for the prescribed decimal orbit.

## Retrieval record

All PDFs were fetched from the displayed primary arXiv URLs on 2026-08-12.
`pdftotext -layout` produced nonempty text. An initial Project Euclid request
for Arratia--Goldstein--Gordon was blocked by Incapsula. The earlier draft used
survey restatements for S2/S3; hostile review correctly rejected that choice,
so the delivered S2/S3 are original research papers instead.
