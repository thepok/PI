# T89 source and local-library pins

Search date: 2026-08-09 UTC.

## Scope

`PRIMARY_SOURCE_COUNT: 3`

`RETAINED_CANDIDATE_COUNT: 2`

The independent search queried Crossref by title and DOI, checked DOI landing
records, searched the web for primary PDFs, and searched the supplied accepted
local library by name and normalized mechanism. The search is bounded, not
exhaustive. Crossref and OpenAlex rate-limited some requests with HTTP 429;
successful DOI records and the primary files below were checked directly.

## Immutable statement

- Local URL: `local:pi-lacunary-near-return-sparsity`.
- File: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Canonical question: line 2.
- Ambiguities A1--A16: lines 7--23.
- Verification rule for artificial constants: line 26.

## S1: Kempner/Fredholm number

Aubrey J. Kempner, "On Transcendental Numbers," *Transactions of the
American Mathematical Society* 17 (1916), no. 4, 476--482.

- DOI: <https://doi.org/10.1090/S0002-9947-1916-1501054-4>.
- Publisher PDF URL:
  <https://www.ams.org/journals/tran/1916-017-04/S0002-9947-1916-1501054-4/S0002-9947-1916-1501054-4.pdf>.
- File: `kempner-1916.pdf`.
- SHA-256:
  `99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014`.
- Printed p. 477, PDF p. 2: the displayed theorem treats
  `sum alpha_n/a^(2^n) * (p/q)^n` for bounded nonzero integral
  coefficients and gives transcendence under its stated hypotheses.
- Printed p. 482, PDF p. 7: setting `p/q=1` is stated explicitly, followed
  by the Fredholm function `sum x^(2^n)` and its transcendental values.
- The PDF is a scan with an embedded approximate OCR layer. Formula locators
  were checked against the rendered page; the report uses only the displayed
  specialization `a=10`, `alpha_n=1`, `p/q=1`.

## S2: Thue--Morse recurrence and Mahler product

Dmitry Badziahin and Evgeniy Zorin, "On the Irrationality Measure of the
Thue--Morse Constant," *Mathematical Proceedings of the Cambridge
Philosophical Society* 168 (2020), 455--472.

- DOI: <https://doi.org/10.1017/S0305004118000117>.
- arXiv identifier: <https://arxiv.org/abs/1707.06677v1>.
- Primary preprint PDF URL: <https://arxiv.org/pdf/1707.06677v1>.
- File: `badziahin-zorin-1707.06677v1.pdf`.
- SHA-256:
  `f8de296ba104cca97f4f6c3d45647e21c3db3d2207274facaf2c16b445483d15`.
- PDF pp. 3--4, equations (3)--(5): recurrence
  `t_(2n)=t_n`, `t_(2n+1)=1-t_n`, the binary constant, the product
  `f_TM(z)=product_(k>=0)(1-z^(-2^k))`, and
  `f_TM(z^2)=z/(z-1) f_TM(z)`.
- PDF pp. 7--8, Theorem 2: the stated restricted approximation theorem for
  the product family at integer arguments. T89 records it only to distinguish
  scalar approximation from the symbolic collision calculation; it is not a
  premise of that calculation.

## S3: exact Thue--Morse factor-complexity formula

Hsien-Kuei Hwang, Svante Janson, and Tsung-Hsi Tsai, "Exact and Asymptotic
Solutions of a Divide-and-Conquer Recurrence Dividing at Half," *ACM
Transactions on Algorithms* 13 (2017), no. 4, Article 47.

- DOI: <https://doi.org/10.1145/3127585>.
- Author PDF URL: <https://www2.math.uu.se/~svantejs/papers/sj315.pdf>.
- File: `hwang-janson-tsai-2017.pdf`.
- SHA-256:
  `d47477fa8b92a4f213b6bfe4febd1075bacb77ec706f2823efaedfeda48c9481`.
- PDF p. 2, equations (1.1)--(1.2): the balanced divide-and-conquer
  recurrence.
- PDF pp. 15--16, Example 3.2, equation (3.4), and Table 3: the exact
  solution for constant toll 2 and the identity
  `A005942(n+1)=2(f(n)+2)`, explicitly labeled as the complexity of the
  Thue--Morse sequence. These displayed formulas yield the `p_TM` formula in
  `REPORT.md` by substitution.
- Direct TLS validation of the author host failed because the sandbox lacked
  the issuer chain. The byte was retrieved from that HTTPS URL with certificate
  checking disabled, then pinned by SHA-256 and checked as a 49-page PDF. This
  is a retrieval limitation, not a mathematical premise.

## Accepted local interfaces

These are byte-exact copies from the supplied accepted library. The Lean
declarations are machine-checked interfaces; no conditional premise in them is
asserted for pi here.

| item | file | SHA-256 | locator and use |
|---|---|---|---|
| T7 | `T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | lines 292--318: `E_pi <= Q_pi <= 3 E_pi`; lines 346--386: exact canonical energy frontier |
| T10 | `T10LongLagResonance.lean` | `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947` | lines 623--636: explicit resonance threshold; lines 829--894: literal failure quantifiers and adaptive `N,r,h` |
| T61 | `T61DirectLabelAdjacentPhaseVariance.lean` | `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb` | lines 293--338: mass-minus-half-variance identity; lines 340--418: exact strict variance premise and implication |

## Prior comparison inventory

| file | SHA-256 | verification and exact use |
|---|---|---|
| `prior-t63-REPORT.md` | `28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59` | literature-checked applicability audit; lines 260--297 already cover Bailey--Crandall constructed constants, so Stoneham is screened out; lines 765--807 give the rational-phase obstruction and conditional transfer target |
| `SEMANTIC_OBSTRUCTION_MEMORY.md` | `aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f` | unverified dependency/obstruction note written during T82 and later vendored by T87; lines 9--17 identify checked interfaces, lines 22--32 record source/verification levels, and lines 35--55 summarize the earlier T18--T82 comparison cards (including T63/T68/T78/T79, but not T85--T87) |
| `prior-t86-REPORT.md` | `16cff30f045a0b5bf56aa80c98c63add19d55c6a5a5b126602d8c785e48e11fa` | literature-checked bounded audit; lines 570--604 give the T63/T68/T78--T85 fingerprint table and candidate-complete negative map |
| `prior-t87-REPORT.md` | `a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078` | unverified survey note with literature-checked pins and machine-checked quoted types; lines 469--484 give its cross-frontier closure, with its mixed status stated at lines 5--10 |

The semantic memory and T87 survey are consultation history, not discharged
premises. Every arithmetic conclusion in T89 is derived independently in
`REPORT.md` and checked at bounded scales by `verify_note.py`.

## Extraction

The replay uses `pdftotext -layout` in a temporary directory and checks source
anchors. PDF hashes, not extracted text bytes, are the source pins.
