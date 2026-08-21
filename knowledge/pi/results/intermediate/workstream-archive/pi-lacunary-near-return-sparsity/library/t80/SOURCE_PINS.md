# T80 source pins

Access date: 2026-08-09 UTC.

## Primary article

Srinivasa Ramanujan, "Modular equations and approximations to pi,"
*Quarterly Journal of Pure and Applied Mathematics* 45 (1914), 350-372.

- Original-volume record: <https://books.google.com/books?id=7pBoGLtYYeAC>
- Original journal page 350: <https://books.google.com/books?id=7pBoGLtYYeAC&pg=PA350>
- Original journal equation (44), printed p. 370:
  <https://books.google.com/books?id=7pBoGLtYYeAC&pg=PA370>
- Original journal discussion, printed p. 371:
  <https://books.google.com/books?id=7pBoGLtYYeAC&pg=PA371>

Equation (44), printed p. 370, is the bibliographic original-journal locator.
The Google Books page is corroboration; its page bytes are not claimed as a
delivered hash pin. The controlling hashed primary-text witness for replay is
the 1927 collected-paper scan below, which reproduces Ramanujan's article and
equation (44). The equation gives the
specialized series in expanded product notation, with coefficients
`1103, 27493, 53883, ...`. The following sentence says that the first factors
form arithmetic progressions, and the paragraph immediately below calls (44)
"extremely rapidly convergent." The modern factorial summation is derived
term by term in `REPORT.md`; it is not falsely quoted as Ramanujan's original
typography.

## Delivered primary-text witnesses

### Searchable transcription

- Retrieval URL:
  <https://ramanujan.sirinudi.org/Volumes/published/ram06.pdf>
- Delivered PDF: `ramanujan-1914-modular-equations.pdf`
- PDF SHA-256:
  `478e2643fd7ca8a2dbbba23b60ae35608845c21d29019bb9d8dd9b0af27710a1`
- Delivered `pdftotext -layout` extraction:
  `ramanujan-1914-modular-equations.txt`
- Text SHA-256:
  `f80754fa22cd1dadfd58a36a686224a392a7dd9ec9fdb0ee6ca1d43bf25fa73b`
- Exact locator: PDF p. 22, article p. 47, equation (44).
- Delivered visual locator: `ramanujan-1914-page-22.png`, SHA-256
  `b5bf023ac9d868ffc412c3a707fb1db0326c3373ddd04e598d3f70fcf261ecfe`.

This PDF is a 2013 searchable typesetting of the primary article, not a scan
of the 1914 journal issue. Its text extraction is useful for anchors but
garbles stacked fractions. The delivered page image was visually checked:
equation (44), its arithmetic-progression explanation, and the convergence
sentence are legible and agree with the formula transcribed in `REPORT.md`.

### Collected-papers scan (controlling hashed primary-text witness)

- Retrieval URL:
  <https://archive.org/download/pli.kerala.rare.28155/pli.kerala.rare.28155.pdf>
- Archive item: <https://archive.org/details/pli.kerala.rare.28155>
- Bibliographic container: G. H. Hardy, P. V. Seshu Aiyar, and B. M. Wilson,
  editors, *Collected Papers of Srinivasa Ramanujan*, Cambridge University
  Press, 1927.
- Delivered scan: `ramanujan-collected-papers-1927-scan.pdf`
- PDF SHA-256:
  `858af6247df93916a2ef7cedfe774782e95acbb9c06fe40a876c06ff0add41a7`
- Delivered `pdftotext -layout` extraction:
  `ramanujan-collected-papers-1927-scan.txt`
- Text SHA-256:
  `7fc153f0f5dd44fbd91b583fe3d5ad9e15e6df37987b2b3ed75156eadad4e4a0`
- Exact locator: PDF p. 74, collected-paper p. 38, equation (44).
- Delivered visual locator: `ramanujan-collected-1927-page-074.png`, SHA-256
  `3d13aa1026384fa56c5ec2fe8e216359f23adb78f732cc9cbb6d64a582517e20`.

The scan reproduces the primary article but not the original journal
pagination. Its OCR is approximate and omits mathematical structure; the page
image, not the OCR transcription, controls the equation check.

## Canonical statement

- Project URL: `local:pi-lacunary-near-return-sparsity`
- Delivered byte-exact copy: `canonical_statement.txt`
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`

The delivered byte-exact predecessor copies `prior-t63-REPORT.md`,
`prior-t68-CorrectedZudilinTransient.lean`, `prior-t78-REPORT.md`, and
`prior-t79-REPORT.md` make every status and non-overlap entry locally
inspectable. The replay command `python3 verify_note.py` verifies every
delivered file against `SHA256SUMS`, including both rendered page images and
the predecessor copies.
