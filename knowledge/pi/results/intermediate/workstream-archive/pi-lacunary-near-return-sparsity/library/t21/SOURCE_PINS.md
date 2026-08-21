# T21 dependency and literature pins

Access date: 2026-07-23 UTC.

## Immutable canonical statement

- File: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Canonical ordered, diagonal-inclusive A1: line 2.
- Recorded ambiguities and sibling readings A1--A16: lines 7--23.
- The local statement has no original external source URL; its provenance is
  preserved at line 5.

## Kernel-checked T13 dependency

- Knowledge-library file: `knowledge_library/t13/IteratedLagResonance.lean`
- SHA-256:
  `14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13`
- Density and recursive threshold definitions: lines 28--51.
- Resonance sum: lines 64--69.
- Arbitrary-depth theorem: lines 629--702.
- Literal negation of A1: lines 630--632.
- Quantifiers and witness bounds: lines 633--647.

## Accepted T18 citation dependency

T21 reuses, rather than re-retrieves, T18's accepted source pin:
`knowledge_library/notes/t18/SOURCE_PINS.md`, SHA-256
`10ef6a070051bec743d3e59d84aab0e842c8ae4dc0a84c8626e122031563bce5`.

Doron Zeilberger and Wadim Zudilin, *The irrationality measure of pi is at
most 7.103205334137...*, Moscow Journal of Combinatorics and Number Theory 9
(2020), no. 4, 407--419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher page: <https://msp.org/moscow/2020/9-4/p06.xhtml>
- Retained publisher PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Accepted retained file:
  `knowledge_library/notes/t18/zeilberger-zudilin-2020.pdf`
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Accepted layout extract:
  `knowledge_library/notes/t18/zeilberger-zudilin-2020.txt`
- Extract SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`
- Extract command used by T18:
  `pdftotext -layout zeilberger-zudilin-2020.pdf zeilberger-zudilin-2020.txt`

Exact locators in the accepted extract:

- Printed p. 407, PDF page 2, lines 27--34: definition and quantifiers of
  irrationality measure.
- Printed p. 407, PDF page 2, lines 22--23 and 40--42: stated
  `7.103205334137...` result.
- Proposition 7, printed p. 417, PDF page 12, lines 630--633.
- Proposition 8 and equation (18), printed p. 417, PDF page 12, lines
  635--646.
- `World record`, printed p. 418, PDF page 13, lines 676--691: final bound
  `mu(pi) <= 7.10320533413700172750577342281...`.

The source gives an existential sufficiently-large-denominator threshold, not
a numerical value. T21 uses only the consequent exponent-8 statement with an
existential threshold `Q8`.

## Accepted T19 note dependency

- Report: `knowledge_library/notes/t19/REPORT.md`
- SHA-256:
  `fb299c0120ecb9fb0e3f9e6ad5e61786540a6bbd99c37f91fbcc8fa48d54cf48`
- Exact checker: `knowledge_library/notes/t19/verify_examples.py`
- SHA-256:
  `76063b7da130d8eef5fe4380b9afd3d7d179d24fd80f0914199c3f7108652de1`
- T21 re-proves T19's concentration argument for every `0<tau<delta` and
  retains T19's exact examples. T19 remains a `proof sketch`, not a Lean
  module.
