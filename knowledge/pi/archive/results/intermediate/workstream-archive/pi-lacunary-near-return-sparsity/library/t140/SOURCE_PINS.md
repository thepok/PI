# T140 source pins

Audit date: 2026-08-12 UTC. Two primary sources were inspected, below the cap
of six. Exactly two theorems were retained, at the cap of two. Page numbers
below are both physical PDF pages and printed pages; they coincide in these
two arXiv PDFs.

## S1: Saxton--Thomason

- David Saxton and Andrew Thomason, "Hypergraph containers."
- arXiv version: `1204.6595v3`, submitted 2012-04-30, revised 2014-11-28.
- Journal DOI: <https://doi.org/10.1007/s00222-014-0562-8>.
- Version URL: <https://arxiv.org/pdf/1204.6595v3>.
- Local file: `saxton-thomason-1204.6595v3.pdf`.
- SHA-256: `23dd1542e20d1513b7021828cb4e4153a5091774117616727791272357622437`.
- Definitions 3.1--3.3: physical/printed pp. 11--12. These define `d(sigma)`,
  `d^(j)(v)`, `delta_j`, `delta(G,tau)`, and degree measure `mu`.
- Retained Theorem 3.4: physical/printed pp. 13--14. Hypothesis:
  `delta(G,tau)<=zeta`. Conclusions include independent-set containment,
  fingerprint bounds, degree-measure bound, and the two explicitly stated
  extensions to degenerate or edge-sparse induced subgraphs.
- Corollary 3.6, physical/printed pp. 14--15, was inspected to confirm the
  iterated edge-sparse direction but is not counted as a retained theorem.
- Exact page replay:
  `pdftotext -f 11 -l 14 -layout saxton-thomason-1204.6595v3.pdf -`.

## S2: Balogh--Morris--Samotij

- Jozsef Balogh, Robert Morris, and Wojciech Samotij, "Independent sets in
  hypergraphs."
- arXiv version: `1204.6530v2`, submitted 2012-04-29, revised 2014-03-21.
- Journal DOI: <https://doi.org/10.1090/S0894-0347-2014-00816-X>.
- Version URL: <https://arxiv.org/pdf/1204.6530v2>.
- Local file: `balogh-morris-samotij-1204.6530v2.pdf`.
- SHA-256: `2e2a7973b172bdb6e539d1cd541c0d8640fcb72f07f58b7816e94854dceb47fe`.
- Definition 2.1: physical/printed p. 11. This defines `(F,epsilon)`-density.
- Codegree definitions `deg_H(T)` and `Delta_l(H)`: physical/printed pp.
  11--12.
- Retained Theorem 2.2: physical/printed p. 12. It fixes uniformity and
  positive constants, assumes `p in (0,1)`, `|A|>=epsilon*v(H)` for every
  `A in F`, `(F,epsilon)`-density, and the displayed `Delta_l` inequalities.
  It labels every independent set by a small fingerprint whose remainder lies
  in a member outside `F`.
- Exact page replay:
  `pdftotext -f 11 -l 12 -layout balogh-morris-samotij-1204.6530v2.pdf -`.

## Retrieval log

Both versioned arXiv PDFs were retrieved successfully on 2026-08-12 UTC.
`pdftotext -layout` produced searchable text; no OCR was used. No retrieval
failure is hidden. DOI metadata was checked, but theorem wording is pinned to
the byte-hashed arXiv versions above.
