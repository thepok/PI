# T117 primary-source pins

Audit date: 2026-08-10 UTC.

`PRIMARY_SOURCE_COUNT: 2` (cap: 6).

## S1: Mauduit--Sarkozy

- Christian Mauduit and Andras Sarkozy, *On finite pseudorandom binary
  sequences I: Measure of pseudorandomness, the Legendre symbol*, Acta
  Arithmetica 82 (1997), 365--377.
- DOI: <https://doi.org/10.4064/aa-82-4-365-377>
- Publisher landing page:
  <https://www.impan.pl/pl/wydawnictwa/czasopisma-i-serie-wydawnicze/acta-arithmetica/all/82/4/109629/on-finite-pseudorandom-binary-sequences-i-measure-of-pseudorandomness-the-legendre-symbol>
- Primary PDF URL:
  <https://www.impan.pl/shop/publication/transaction/download/product/109629?download.pdf>
- Delivered PDF: `mauduit-sarkozy-1997.pdf`
- PDF SHA-256:
  `d95bbd2b7cbecfb0cee08f82a41f7879579277f865b8f0d0dc53c5e79e2a39fa`
- `pdftotext -layout` derivative: `mauduit-sarkozy-1997.txt`
- Text SHA-256:
  `e3aa1279155d19d144057cf518b4597d61aff4d4070f86b9806fa1ff35a05fd4`

Exact inspected locators:

| Claim | Printed locator | Text lines |
|---|---|---|
| word count `T(E,M,X)` and normality main term | p. 368, equations (2.1), (2.4) | 131--159 |
| finite normality measure and logarithmic word range | pp. 368--370, Definition 1 and normality measure | 165--215 |
| pattern indicator expansion and `N_k<=max C_t` | pp. 370--371, Proposition 1, equation (2.9), proof | 227--282 |
| Legendre sequence and `Q_k<=9k sqrt(p) log p` | p. 373, Theorem 1, equations (3.1)--(3.3) | 369--415 |
| nonsquare polynomial criterion | pp. 373--374, Theorem 2 and Corollary 1 | 399--430 |
| complete hybrid and complete character bounds | p. 374, Lemmas 1--3, equations (4.1)--(4.2) | 433--468 |
| shifted-product polynomial and distinct-root check | pp. 375--376, equations (6.1)--(6.3) | 520--560 |

Claims used: the literature-checked source statements are exactly those listed
above. T117's cyclic zero convention, error `E(p,m)`, collision bound, and
growing-range calculation are separately labeled `proof sketch`.

## S2: Weil

- Andre Weil, *On Some Exponential Sums*, Proceedings of the National Academy
  of Sciences 34 (1948), 204--207.
- DOI: <https://doi.org/10.1073/pnas.34.5.204>
- PubMed: <https://pubmed.ncbi.nlm.nih.gov/16578290/>
- Primary scan URL:
  <https://europepmc.org/articles/PMC1079093?pdf=render>
- Delivered PDF: `weil-1948-pnas.pdf`
- PDF SHA-256:
  `c19b498bacb4878f2067e679f92306f3f2a3fa54f53937f12c5d6650a5f5abef`
- `pdftotext -layout` derivative: `weil-1948-pnas.txt`
- Text SHA-256:
  `c3d84b507fc00d3bf5beb17e760102984d72fd77c0dfa0bae4fe1991a8abc6a6`

Exact inspected locators:

| Claim | Printed locator | Approximate text lines |
|---|---|---|
| finite-field multiplicative character and root-divisor hypotheses | p. 205 | 59--83 |
| conductor degree, equations (4)--(5), square-root root bounds | p. 206 | 84--120 |
| order-two character and polynomial hybrid specialization | p. 207 | 131--149 |

The PDF is an image scan with imperfect embedded OCR. The line-addressable text
is approximate and is supplied only for search. Exact symbols and quotations
were checked against the rendered PDF pages. The load-bearing specialized
constant used by T117 is taken from S1 Lemma 3, not reconstructed from damaged
OCR in S2.

## Prior-item comparison evidence

The exceptional and newly staged novelty-table records are vendored
byte-exactly. They are comparison history, not primary sources for T117's
mathematical deductions:

- `prior-t109-REPORT.md`, SHA-256
  `6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf`.
- `prior-t109-SKEPTIC.json`, SHA-256
  `987966c0c2074ab1b058bd16024806165f3e63357c51c5d46524faafc25fc558`.
  Its `notes` field records the rejection: sufficient certificate failures were
  overstated as necessary refutations.
- `prior-t114-REPORT.md`, SHA-256
  `db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca`.
  Its source statements are `literature-checked`; determinant
  specializations and exponent comparisons are `proof sketch` deductions.
- `prior-t116-REPORT.md`, SHA-256
  `573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1`.
  Its source statements are `literature-checked`; selector and collision
  deductions are `proof sketch`, and its bounded replay is an `experiment`.

## Canonical statement

- Delivered file: `canonical_statement.txt`
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Original source URL: none; local formulation dated 2026-07-22.
