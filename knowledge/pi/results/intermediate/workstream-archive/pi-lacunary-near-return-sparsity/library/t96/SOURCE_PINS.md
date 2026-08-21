# T96 source pins

Audit date: 2026-08-09 UTC.

## Audit scope

The bounded query class was `Stoneham` plus `Poissonian pair correlation`.
The two primary sources below were inspected directly. They cover the family
definition and the known `(2,3)` non-PPC theorem, respectively. This is an
exact coverage audit of the two-source corpus, not an exhaustive literature
search and not a novelty claim for T96.

The unverified T93 note was used only to locate this corpus. Its calculations
are not cited as established; the family arithmetic is independently proved in
`REPORT.md`.

## S1. Stoneham family definition

R. G. Stoneham, "On the uniform epsilon-distribution of residues within the
periods of rational fractions with applications to normal numbers,"
*Acta Arithmetica* 22 (1973), 371--389.

- DOI: https://doi.org/10.4064/aa-22-4-371-389
- Publisher page: https://www.impan.pl/get/doi/10.4064/aa-22-4-371-389
- Retrieval URL:
  https://www.impan.pl/shop/publication/transaction/download/product/98674?download.pdf
- Local PDF: `stoneham-1973.pdf`
- PDF SHA-256: `62d1718944b11b61543a20eebc2df9adbe94b94f825befa1774063897d2586d3`
- Exact locator: journal p. 372, PDF page 2, left panel, equation (1.0) and
  the sentence immediately following it.
- Exact scope: for odd prime `p` and primitive root `g modulo p^2`, equation
  (1.0) defines `w(g,p)=sum_(q>=1) 1/(p^q*g^(p^q))`; the following sentence
  states its transcendental, non-Liouville, and normal properties.
- T96 use: family identification and scope only. Stoneham's normality theorem
  is not used in the pair-correlation proof.

### Scan handling

The PDF is an image-only scan. `pdftotext -layout` yields only form-feed
characters. The locator above was checked visually against PDF page 2; no OCR
quotation is treated as authoritative.

## S2. Pair-correlation definition and the (2,3) theorem

Gerhard Larcher and Wolfgang Stockinger, "Some negative results related to
Poissonian pair correlation problems," *Discrete Mathematics* 343(2) (2020),
article 111656.

- DOI: https://doi.org/10.1016/j.disc.2019.111656
- Stable preprint: https://arxiv.org/abs/1803.05236v2
- Retrieval URL: https://arxiv.org/pdf/1803.05236v2
- Local PDF: `larcher-stockinger-1803.05236v2.pdf`
- PDF SHA-256: `a9ea7099fb191b68cd7a322bf6b50a1d009820c69c5fa16fc3d2746a1c4baeae`
- Text derivative: `larcher-stockinger-1803.05236v2.txt`
- Text SHA-256: `82d585a371bc8a5c88ff0a4b79f3fe5448356835fa74a1464ac4f1aba2301639`
- PPC locator: preprint pp. 1--2, equation (1); derivative lines 57--63.
- Stoneham theorem locator: definition of `alpha_(2,3)` and Theorem 3,
  preprint p. 4; derivative lines 162--172.
- Proof locator: preprint pp. 14--16; derivative lines 723--840.
- Exact scope: Theorem 3 states non-PPC only for
  `({2^n*alpha_(2,3)})_(n in N)`. It does not state the T96 `p>=5` family
  theorem.

## Canonical statement

- Local file: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Role: immutable fixed-pi scope and A13 sibling boundary.
