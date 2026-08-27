# T18 source pins and exact locators

Access date: 2026-07-23 UTC.

## Irrationality-measure source

Doron Zeilberger and Wadim Zudilin, *The irrationality measure of pi is at
most 7.103205334137...*, Moscow Journal of Combinatorics and Number Theory 9
(2020), no. 4, 407--419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher page: <https://msp.org/moscow/2020/9-4/p06.xhtml>
- Retained publisher PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Retained file: `zeilberger-zudilin-2020.pdf`
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Layout extract command:
  `pdftotext -layout zeilberger-zudilin-2020.pdf zeilberger-zudilin-2020.txt`
- Retained extract: `zeilberger-zudilin-2020.txt`
- Extract SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`

Exact locators:

- Printed p. 407, PDF page 2, retained extract lines 27--34: definition of
  irrationality measure, including `epsilon>0`, all integer numerators and
  denominators, and the sufficiently-large-denominator quantifier.
- Printed p. 407, PDF page 2, extract lines 22--23 and 40--42: statement of
  the `7.103205334137...` result.
- Proposition 7, printed p. 417, PDF page 12, extract lines 630--633:
  integrality of the linear forms.
- Proposition 8 and equation (18), printed p. 417, PDF page 12, extract lines
  635--646: asymptotics and the exact cubic
  `108*N^3-2359989*N^2+138304*N-2048`.
- `World record`, printed p. 418, PDF page 13, extract lines 676--691: final
  calculation
  `mu(pi) <= 7.10320533413700172750577342281...`.

The source gives an asymptotic threshold, not a numerical denominator cutoff.
The specialization at exponent 8 is therefore

```text
exists Q8, forall integer q>=Q8, forall p in Z,
  |pi-p/q| > q^(-8),
```

with `Q8` existential and dependent on the exponent choice.

## Accepted T13 source

- Knowledge-library file: `knowledge_library/t13/IteratedLagResonance.lean`
- SHA-256:
  `14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13`
- Density and threshold definitions: lines 28--51.
- Resonance-sum definition: lines 64--69.
- Arbitrary-depth theorem statement and proof: lines 629--702.
- The literal A1 negation is in the theorem premise at lines 630--632.
- The quantifier conclusion and all witness bounds are at lines 633--647.

## Canonical statement

- File: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Canonical ordered, diagonal-inclusive A1: line 2.
- Recorded sibling readings and ambiguities A1--A16: lines 7--23.
- The local statement records no original external source URL; its provenance
  is stated at line 5.
