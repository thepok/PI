# T102 source pins and bounded audit

Audit date: 2026-08-09 UTC.

Result label: `literature-checked` for the exact two-source coverage statements
below. The audit directly inspected the vendored primary-source bytes. It is
not an exhaustive literature search and makes no novelty claim for T102.

## S1. Stoneham's primitive-root family

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
- Exact source scope: odd prime `p` and primitive root `g modulo p^2`; equation
  (1.0) defines `w(g,p)=sum_(q>=1)1/(p^q*g^(p^q))`, and the following sentence
  states transcendental, non-Liouville, and normal properties.
- T102 boundary: in the parameters `d=ord_p(b)` and
  `lambda=v_p(b^d-1)`, Stoneham's cited scope is `d=p-1, lambda=1`.
  Arbitrary coprime cases in T102 are called generalized Stoneham-type series.
  Stoneham's normality statement is not used or extended.
- Exclusion: this source states no pair-correlation theorem.

The PDF is an image-only scan. `pdftotext -layout` yields no usable text. The
locator was checked visually against local PDF page 2; no OCR quotation is
treated as authoritative.

## S2. PPC normalization and the single (2,3) theorem

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
- Theorem locator: definition of `alpha_(2,3)` and Theorem 3, preprint p. 4;
  derivative lines 162--172.
- Proof locator: preprint pp. 14--16; derivative lines 723--840. The choices
  `s=1` and `N=2^w` occur at derivative lines 742--743.
- Exact scope: Theorem 3 states non-PPC only for
  `({2^n*alpha_(2,3)})_(n in N)`. It does not state a theorem for every base,
  every coprime pair, or every primitive root modulo 9.
- General-theorem boundary: Theorem 1 is a gap criterion, but the paper gives
  no displayed verification of it for the generalized T102 family.

The text derivative was produced with `pdftotext -layout`. The pinned PDF
bytes, not the derivative, are authoritative.

## Canonical statement

- Local file: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Exact role: immutable fixed-pi quantifiers, verification rules, and A13
  sibling boundary.

## Coverage map

| Claim | Stoneham 1973 | Larcher--Stockinger 2020 | T102 status |
|---|---|---|---|
| Formula in the primitive-root-mod-`p^2` case | Equation (1.0) | Recalls `(2,3)` | Source-pinned |
| Formula for arbitrary coprime `b` | Not stated as its family | Not stated | Definition adopted explicitly |
| Normality in primitive-root scope | Sentence after (1.0) | Recalls `(2,3)` | Covered but unused |
| Non-PPC for `(b,p)=(2,3)` | No | Theorem 3 | Source-pinned comparison |
| Non-PPC for every coprime profile | No | No | Independent T102 `proof sketch` |

## Bounded search log and blockers

| Date | Corpus or query | Finding |
|---|---|---|
| 2026-08-09 | Direct inspection of vendored Stoneham scan | Verified equation (1.0), primitive-root hypothesis, and scope boundary |
| 2026-08-09 | Direct inspection of vendored Larcher--Stockinger preprint and derivative | Verified PPC normalization, Theorem 3's `(2,3)` scope, and proof locators |
| 2026-08-09 | T93/T96/T99 notes, used only as unverified locator maps | Located the two primary sources; no note claim was used as a premise |

The Stoneham scan is image-only. No broader live database search was attempted
in T102 because the item extends an already pinned two-source mechanism audit.
Accordingly, this file supports exact attribution and source scope, not an
exhaustive negative literature verdict or novelty claim.
