# T99 source pins and bounded search log

Audit date: 2026-08-09 UTC.

Result label: `literature-checked` two-source coverage audit with a dated
supplementary database search, within the queries and retrieval limits listed
below. This is not an exhaustive literature or novelty claim.

The T93 and T96 notes were unverified locator maps only. Their two primary
sources were copied byte-for-byte into this self-contained artifact set and
inspected directly.

## S1. Stoneham family definition

R. G. Stoneham, "On the uniform epsilon-distribution of residues within the
periods of rational fractions with applications to normal numbers,"
*Acta Arithmetica* 22 (1973), 371--389.

- DOI: https://doi.org/10.4064/aa-22-4-371-389
- Publisher: https://www.impan.pl/get/doi/10.4064/aa-22-4-371-389
- Retrieval URL:
  https://www.impan.pl/shop/publication/transaction/download/product/98674?download.pdf
- Local PDF: `stoneham-1973.pdf`
- PDF SHA-256: `62d1718944b11b61543a20eebc2df9adbe94b94f825befa1774063897d2586d3`
- Exact locator: journal p. 372, local PDF page 2, left panel, equation (1.0)
  and the immediately following sentence.
- Exact scope: for an odd prime `p` and primitive root `g modulo p^2`, (1.0)
  defines `w(g,p)=sum_(q>=1) 1/(p^q*g^(p^q))`; the following sentence states
  transcendental, non-Liouville, and normal properties.
- T99 use: taking `p=3` and `g=b` identifies every base satisfying
  `ord_9(b)=6` with the Stoneham family. Normality is not used.
- Exclusion: this source contains no pair-correlation theorem.

The PDF is an image-only scan. `pdftotext -layout` produces no usable text.
The locator was checked visually against local PDF page 2; no OCR quotation is
treated as authoritative.

## S2. Pair correlation and the single (2,3) theorem

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
- Theorem locator: preprint p. 4, Theorem 3; derivative lines 162--172.
- Proof locator: preprint pp. 14--16; derivative lines 723--840.
- Exact scope: Theorem 3 states non-PPC only for
  `({2^n*alpha_(2,3)})_(n in N)`. It does not state a theorem for every
  primitive root modulo 9.
- General-theorem boundary: Theorem 1 is a gap criterion. This paper gives no
  displayed verification of that criterion for all `alpha_(b,3)`.

The text derivative was produced from the pinned PDF with `pdftotext -layout`.
The PDF bytes, not the derivative, are authoritative.

## Canonical statement

- Local file: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Exact role: immutable fixed-pi scope and A13 sibling boundary.

## Coverage map

| Claim | Stoneham 1973 | Larcher--Stockinger 2020 | Located status |
|---|---|---|---|
| Definition of every admissible `alpha_(b,3)` | Yes | Only `(2,3)` | Covered |
| Normality of every admissible family member | Yes | Recalls `(2,3)` | Covered, unused |
| Non-PPC for `(b,p)=(2,3)` | No | Theorem 3 | Covered |
| Non-PPC for every `b` with `ord_9(b)=6` | No | No | No direct theorem located |

## Dated search log

| Date | Database or query | Finding |
|---|---|---|
| 2026-08-09 | Direct inspection of the vendored Stoneham and Larcher--Stockinger bytes | Verified the definition, PPC normalization, Theorem 3, proof scope, and hashes |
| 2026-08-09 | arXiv: `"Stoneham number"`, `"Stoneham-numbers"`, and pair correlation | Located Larcher--Stockinger and Stoneham-structure literature, but no broader primitive-root-modulo-9 PPC theorem |
| 2026-08-09 | Crossref exact DOI and bibliographic phrase searches | Confirmed source metadata; no additional Stoneham PPC theorem identified |
| 2026-08-09 | Semantic Scholar citation records for the Larcher--Stockinger paper | Title and abstract inspection found no broader Stoneham family theorem |
| 2026-08-09 | OpenCitations DOI citation records | No citing title identified a broader family theorem |
| 2026-08-09 | HAL query `"Stoneham number"` | No records returned |
| 2026-08-09 | Google phrase queries combining Stoneham, primitive root modulo 9, and pair correlation | Search shell returned no inspectable additional source |

The broader search also located normality and digit-structure papers. They were
not used as premises because Sections 4--9 of `REPORT.md` independently derive
all order, skeleton, tail, and pair-count facts needed for T99.

## Retrieval blockers

- Elsevier's version of record returned HTTP 403. The source text inspected was
  arXiv v2, linked to the journal DOI by bibliographic databases.
- Semantic Scholar general search and later OpenAlex/arXiv requests were
  rate-limited, although direct records and citation data were available.
- zbMATH returned a terms gate or request error.
- BASE presented an anti-bot challenge.
- Internet Archive Scholar rate-limited phrase searches.
- Google returned only a search shell rather than inspectable result records.

## Exact bounded verdict

The two pinned primary sources cover Stoneham's definition and normality for
all admissible bases and non-PPC for the single pair `(2,3)`. The dated
supplementary search found no direct coverage of the every-base T99 theorem.
This negative coverage statement is limited to that search and is not a
novelty claim.
