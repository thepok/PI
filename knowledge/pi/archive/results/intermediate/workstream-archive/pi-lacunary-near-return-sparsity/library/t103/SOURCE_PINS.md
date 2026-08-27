# T103 source pins

Audit date: 2026-08-09 UTC.

Exactly two primary sources are retained.  Both PDFs were fetched directly
from the displayed arXiv version URLs, converted with `pdftotext -layout`, and
are delivered with their text derivatives.

## S1. El Abdalaoui--Kasjan--Lemanczyk

- Authors: El Houcein El Abdalaoui, Stanislaw Kasjan, Mariusz Lemanczyk.
- Title: *0-1 sequences of the Thue-Morse type and Sarnak's conjecture*.
- Publication: Proceedings of the American Mathematical Society 144 (2016),
  161--176.
- DOI: `10.1090/proc/12683`.
- DOI URL: <https://doi.org/10.1090/proc/12683>.
- Retrieved primary version: arXiv:1304.3587v2.
- Retrieval URL: <https://arxiv.org/pdf/1304.3587v2>.
- PDF: `akl-1304.3587v2.pdf`.
- PDF SHA-256:
  `6d65ce118a10b38450fd0d38716a3624ec3a2dea56bb08c32771a88165b88ce3`.
- Text derivative: `akl-1304.3587v2.txt`.
- Text SHA-256:
  `cba463bd9a3522b3ece79f760aa8d08f65e058c0088a36b07fb5f7b6037ab97a`.

Exact locators:

| Claim used | Printed locator | Delivered derivative locator |
|---|---|---|
| Toeplitz definition and stage-word convention | Section 6, printed p. 12 | lines 721--737 |
| Divisible scale, `rho<=1/4`, and allowed example `a_n=5^n` | equation (24), printed pp. 12--13 | lines 749--760 |
| Recursive disjoint progressions and initials | printed p. 13, immediately before Proposition 5 | lines 761--787 |
| Point is Toeplitz by progression property 3 | printed p. 13 | lines 768--787 |
| Correlation proposition, used only to identify the same construction | Proposition 5, printed pp. 13--14 | lines 788--831 |
| Positive entropy announced but not proved in S1 | Remark 3, printed p. 14 | lines 834--836 |

No entropy lower bound is attributed to S1; that proof is supplied by S2.

## S2. Downarowicz--Kasjan

- Authors: Tomasz Downarowicz, Stanislaw Kasjan.
- Title: *Odometers and Toeplitz systems revisited in the context of Sarnak's
  conjecture*.
- Publication: Studia Mathematica 229 (2015), 45--72.
- DOI: `10.4064/sm8314-12-2015`.
- DOI URL: <https://doi.org/10.4064/sm8314-12-2015>.
- Retrieved primary version: arXiv:1502.02307v1.
- Retrieval URL: <https://arxiv.org/pdf/1502.02307>.
- PDF: `downarowicz-kasjan-1502.02307.pdf`.
- PDF SHA-256:
  `11f3315b34ec2d84a59c849860c2a2a90903348160e7a4316788840f2713e540`.
- Text derivative: `downarowicz-kasjan-1502.02307.txt`.
- Text SHA-256:
  `a8f7432f3e2a85641b39020a98b129816f3d9fd9187747e6fa2dd2e78fb7003d`.

Exact locators:

| Claim used | Printed locator | Delivered derivative locator |
|---|---|---|
| Scale means `p_k | p_(k+1)` | Section 2, printed p. 2 | lines 70--79 |
| S1 construction restated as first available placement with period `p_k` | Example 6.3, printed pp. 13--14 | lines 682--769 |
| Period-block marker geometry and density | Lemma 7.1(1)--(4), printed pp. 14--15 | lines 771--829 |
| Positive entropy proof begins | Section 8, printed p. 18 | lines 948--963 |
| Complexity comparison and threshold `rho<6/pi^2` | Section 8, printed p. 18 | lines 964--977 |
| Word-dependent translated interval construction | Section 8, printed pp. 18--22 | lines 978--1157 |

The text extraction writes mathematical symbols imperfectly in a few places,
but the cited formulas and prose are readable in the PDFs.  No OCR was needed.

## Canonical source

- File: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Original URL: none; local system formulation dated 2026-07-22.
