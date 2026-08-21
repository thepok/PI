# T93 source pins

Audit date: 2026-08-09 UTC.

T90 was used only as a source map. The files below are byte-identical copies
of its pinned primary sources. PDF bytes are authoritative. The Larcher--
Stockinger text derivative was produced from the pinned PDF with
`pdftotext -layout` and is included only for line-addressable replay.

## Bounded audit method

The search universe was deliberately limited to T90's dated fixed-point
source map. Within that map, the query class was `Stoneham` plus `Poissonian
pair correlation`; Larcher--Stockinger was the only mapped pair-correlation
source, and Stoneham was retained as the primary definition of the family.
The audit checked the exact theorem, definition, and proof locators below.
This is a reproducible source audit, not an exhaustive literature search or a
novelty claim for the new proof sketch.

## S1. Exact non-Poissonian theorem

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
- Exact locators: PPC definition and quantifiers, preprint pp. 1--2,
  equation (1), derivative lines 57--63; definition of `alpha_(2,3)` and
  Theorem 3, preprint p. 4, derivative lines 162--172; proof of Theorem 3,
  preprint pp. 14--16, derivative lines 723--840.
- Exact role: source map and comparison theorem for `(2,3)`. It does not state
  a theorem about `alpha_(10,7)`.

## S2. Stoneham family

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
- Exact role: identifies `alpha_(10,7)` as the family member `w(10,7)` once
  primitivity modulo 49 is checked. Its normality assertion is not used in the
  pair-correlation proof.

### Scan limitation

The Stoneham PDF is an image-only scan. Its equation (1.0) locator was checked
visually in the pinned PDF; no OCR quotation is treated as authoritative.

## Literature boundary

No delivered primary source states non-PPC for `alpha_(10,7)`. The result in
`REPORT.md` is an independent `proof sketch` obtained by replaying and
repairing the arithmetic mechanism, not by broadening Theorem 3's statement.
