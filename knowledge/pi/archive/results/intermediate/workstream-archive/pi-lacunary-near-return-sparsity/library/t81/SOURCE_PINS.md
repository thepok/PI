# T81 source pins

Access date: 2026-08-09 UTC.

## Canonical statement

- Local source URL: `local:pi-lacunary-near-return-sparsity`.
- Original project path: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Delivered byte-exact file: `canonical_statement.txt`.
- SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Exact canonical statement: line 2.
- System provenance: line 5. The source records no external original URL.
- Ambiguities A1--A16: lines 7--23.

## Irrationality-measure source

Doron Zeilberger and Wadim Zudilin, *The irrationality measure of pi is at
most 7.103205334137...*, Moscow Journal of Combinatorics and Number Theory 9
(2020), no. 4, 407--419.

- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher page: <https://msp.org/moscow/2020/9-4/p06.xhtml>
- Retained publisher PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Delivered PDF: `zeilberger-zudilin-2020.pdf`.
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
- Extract command originally used:
  `pdftotext -layout zeilberger-zudilin-2020.pdf zeilberger-zudilin-2020.txt`.
- Delivered extract: `zeilberger-zudilin-2020.txt`.
- Extract SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`.

Exact locators:

- Printed p. 407, PDF page 2, extract lines 27--34: definition of the
  irrationality measure, including every positive epsilon, all integer
  numerators, and sufficiently large integer denominators.
- Printed p. 407, PDF page 2, extract lines 22--23 and 39--42: announced
  `7.103205334137...` upper bound.
- Proposition 7, printed p. 417, PDF page 12, extract lines 630--633:
  integrality of the linear forms used in the final estimate.
- Proposition 8, printed p. 417, PDF page 12, extract lines 635--646:
  asymptotic input.
- `World record`, printed p. 418, PDF page 13, extract lines 676--691: final
  value `7.10320533413700172750577342281...`.

The source gives an eventual denominator threshold, not a numerical one. T81
therefore retains `Q8` existentially.

## Kernel-checked library inputs

### T73

- Delivered byte-exact file: `T73ManyChildResonance.lean`.
- SHA-256:
  `34ec4af51b95e7e1e1a0a350357fedf4fb7c0427daaf8a53331c3767992727de`.
- Accepted module:
  `TheoryLib.PiLacunaryNearReturnSparsity.T73ManyChildResonance`.
- Good-shift definition and exact interval: lines 29--35.
- Membership theorem: lines 39--46.
- Complete cardinality theorem and losses: lines 63--72.
- Geometric child coefficient identity: lines 267--292.
- Length threshold: lines 294--297.
- Literal not-canonical-C1 theorem: lines 305--344.
- The accepted knowledge entry records kernel verification. T81's adversarial
  pass also recompiled this byte-exact copy directly on 2026-08-09; all six
  printed theorem axiom sets contained exactly `propext`, `Classical.choice`,
  and `Quot.sound`. T81 does not relabel it as a new theorem.

### T28

- Delivered byte-exact file: `T28AdjacentNodeCompatibility.lean`.
- SHA-256:
  `f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd`.
- Accepted module:
  `TheoryLib.PiLacunaryNearReturnSparsity.T28AdjacentNodeCompatibility`.
- `AdjacentPairCompatible`: lines 88--107.
- `ExponentEightClosingBounds`: lines 109--122.
- Exact cancellation theorem: lines 274--326.
- Pi-error transport: lines 328--388.
- Exponent-eight contradiction: lines 390--451.
- Conditional canonical bridge: lines 453--492.
- The accepted knowledge entry records kernel verification. Its compatibility
  and closing predicates remain hypotheses, not established properties of pi.
  T81's adversarial pass also recompiled this byte-exact copy directly on
  2026-08-09. It produced only three `unnecessarySimpa` style warnings, and all
  seven printed theorem axiom sets contained exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
