# T82 source pins

Access date for the external sources: 2026-08-09 UTC.

## Canonical statement

- Local source: `local:pi-lacunary-near-return-sparsity`.
- Vendored file: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- The local formulation has no external original-source URL. It remains an
  open fixed-pi question with the quantifiers reproduced in `REPORT.md`.

## Inspectable proof source for the Chudnovsky identity

Lorenz Milla, *A detailed proof of the Chudnovsky formula with means of basic
complex analysis*, arXiv:1809.00533v6 (2021),
<https://arxiv.org/abs/1809.00533>, PDF
<https://arxiv.org/pdf/1809.00533v6>.

- Vendored PDF: `milla-1809.00533v6.pdf`.
- PDF SHA-256:
  `69e9513d3c03c7c5c5dce12b24187b2522e0f1b08d54266a15eef93a3421cd20`.
- Vendored `pdftotext -layout` extraction: `milla-1809.00533v6.txt`.
- Text SHA-256:
  `edf60a42b2e1c7dc56f3f5fd5175f381860d944d38a5ee131d0815e838ce5a83`.
- Exact locator: Theorem 10.12, printed/PDF page 44; the text extraction
  begins the theorem at line 2862 and displays `640320`, `13591409`, and
  `545140134` at lines 2864-2867.
- General analytic hypothesis: Theorem 0.1/Main Theorem 9.7, printed/PDF
  page 3, assumes `Im(tau)>1.25`. The specialization uses
  `tau=(1+i*sqrt(163))/2`, whose imaginary part is greater than `5/4`.
- The theorem and the exact identity
  `640320^3=(12*426880)^2*10005` give
  `pi=426880*sqrt(10005)/S`, with the positive square root and the series
  `S` written in `REPORT.md`.

Milla supplies the published identity and proof. Milla does not state the
binary-splitting leaf and merge code used below; that implementation is pinned
separately.

## Original attribution

D. V. Chudnovsky and G. V. Chudnovsky, *Approximations and complex
multiplication according to Ramanujan*, in *Ramanujan Revisited*, Academic
Press (1988), pp. 375-472; reprinted in *Pi: A Source Book*, pp. 596-622,
DOI <https://doi.org/10.1007/978-1-4757-2736-4_63>.

- Vendored Crossref response: `chudnovsky-crossref.json`, SHA-256
  `67f5af4ad7c4c5377c72762947d3e13a276605715b18c34a9ee3493a9ab089c2`.
- Original printed page 389, reprint page 610, equations (1.4)-(1.5).
- Vendored normalized Google Books excerpts:
  `chudnovsky-primary-formula.json`, SHA-256
  `65b756cdb5019e09a6b2ade96668a03c9655553e52c123995e95e9e0ceac937b`,
  and `chudnovsky-primary-derivation.json`, SHA-256
  `11c5349c04a1dd142d81505631a334eec90b6dbf3dbe5d831228c2bed5a84729`.
- The excerpts are approximate OCR-derived search records, not a substitute
  for a page image and not the proof source. The full original scan was
  access-restricted. Milla Theorem 10.12 is the retained inspectable proof.

## Exact certification implementation

- Vendored T17 implementation: `t17_certify_pi.py`, SHA-256
  `5ef0ca84488829bcdcc89c2f49dc283bba4867bce38f813af09de80dd18c5f2a`.
- Leaf and merge recurrence: lines 30-44.
- Exact conversion, adjacent partial sums, square-root bracket, and scaled
  endpoints: lines 60-104.
- Vendored endpoint integers: `t17_interval_endpoints.hex`, SHA-256
  `30e7186d43de56ceba645ef7170fed40ddc22bd50f6eb2bf6a39b1fcb170a0f9`.

`verify_note.py` reruns all 74,919 root terms and the adjacent term through the
vendored implementation, regenerates the square-root bracket and endpoints,
and byte-compares the resulting endpoint file with the vendored pin.

The implementation is exact computation based on the published identity. Its
docstring at line 31 is literally correct for the root interval `[0,N)`; for a
general subinterval `[a,b)` with `a>0`, `T/Q` is the locally normalized tail
specified in `REPORT.md`, not the unweighted sum of the global Chudnovsky
terms. T82 uses the proved merge identity rather than overreading that
docstring.

## Checked local interfaces

- `T14CoherentSuccessorSplitting.lean`, SHA-256
  `bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833`.
- `T64AggregateFejerCriterion.lean`, SHA-256
  `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16`.

These are byte-exact copies of the accepted kernel-track artifacts. T82 does
not add a Lean theorem and does not claim that either conditional T64 premise
holds for pi.
