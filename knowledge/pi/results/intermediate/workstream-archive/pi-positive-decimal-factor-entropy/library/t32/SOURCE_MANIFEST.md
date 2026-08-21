# T32 source manifest

Retrieval and audit date: 2026-07-24 UTC

Run `bash verify.sh` from this directory.  It requires `sha256sum`, `pdftotext`,
and `grep`, uses only delivered files, and performs no network access.

## Canonical statement

File: `pi-positive-decimal-factor-entropy.txt`

SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`

Origin: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.  This is a locally
formulated problem and has no external source URL.  The delivered copy is byte-exact.

## R90: Rudolph 1990

File: `sources/rudolph-1990.pdf`

SHA-256: `9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85`

Citation: Daniel J. Rudolph, "x2 and x3 invariant measures and entropy,"
*Ergodic Theory and Dynamical Systems* 10 (1990), 395-406.

DOI: <https://doi.org/10.1017/S0143385700005629>

Retrieved PDF: <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/64243AD8323B37089540F911F8CC77EB/S0143385700005629a.pdf/div-class-title-2-and-3-invariant-measures-and-entropy-div.pdf>

Exact locators:

- Abstract, printed page 395/PDF page 1: relatively prime `p,q`; invariance under
  both maps; ergodicity for the generated semigroup; non-Lebesgue implies both
  entropies zero.
- Definitions of `M` and `M_0`, printed page 399/PDF page 5: simultaneously
  invariant Borel probabilities and their ergodic extreme points.
- Lemma 2.2, printed pages 397-398/PDF pages 3-4: the natural almost one-to-one
  coding between the one-sided symbolic system and the multiplication maps on the
  circle.  This is not asserted for the later doubly-infinite inverse limit.
- Lemma 3.1 and Corollary 3.2, printed page 399/PDF page 5: control of exceptional
  coding points and the unique invariant inverse-limit lift of a circle measure with
  no mass at zero.  The introduction, printed pages 395-396/PDF pages 1-2,
  explicitly states that an invariant ergodic circle probability lifts invariantly
  and ergodically.  The audit uses factor entropy monotonicity, not an incorrect
  assertion that the inverse-limit map is almost one-to-one.
- Lemma 3.5, printed page 400/PDF page 6: the lift's measure-theoretic entropy is
  the coordinate-partition entropy `h(T,P)` used in Theorem 4.9 (and symmetrically
  for `S`).
- Theorem 4.9, printed page 405/PDF page 11: under `gcd(p,q)=1`, a non-Lebesgue
  ergodic invariant measure has zero entropy for both maps.
- Corollary 4.10, printed page 405/PDF page 11: the corresponding circle maps are
  almost surely invertible in the zero-entropy conclusion.
- Corollary 4.11, printed page 406/PDF page 12: Theorem 4.9 extends to
  `p=u^n1 v^m1`, `q=u^n2 v^m2` when `gcd(u,v)=1`, `u,v != 1`, and
  `n1*m2-m1*n2 != 0`.

Search anchors checked by `verify.sh`: `THEOREM 4.9`, `COROLLARY 4.11`,
`LEMMA 2.2`, `COROLLARY 3.2`, `LEMMA 3.5`, `COROLLARY 4.10`, `GCD(u, v)`, and
`m 2 - m 1 n 2` after `pdftotext -layout` extraction.

Applicability arithmetic: use `u=2`, `v=5`, `(n1,m1)=(1,1)`, and
`(n2,m2)=(4,0)`.  Then `p=10`, `q=16`, and the exponent determinant is `-4`.

## J92: Johnson 1992 publisher statement

File: `sources/johnson-1992-publisher.html`

SHA-256: `5b28eb0b738a6e331749bc6550c5ac4f2346b71368a86fa84fd66a2e36d59df9`

Citation: Aimee S. A. Johnson, "Measures on the circle invariant under
multiplication by a nonlacunary subsemigroup of the integers," *Israel Journal of
Mathematics* 77 (1992), 211-240.

DOI and retrieved publisher page: <https://doi.org/10.1007/BF02808018>

Exact locator: publisher HTML Abstract, element IDs `Abs1-section`, `Abs1`, and
`Abs1-content`.  It states that for a nonlacunary subsemigroup `S`, an `S`-invariant
and ergodic measure is Lebesgue if any element of `S` has positive entropy.  The
publisher metadata identifies the article's topic as Borel probability measures.

Retrieval blocker: the advertised PDF URL
<https://link.springer.com/content/pdf/10.1007/BF02808018.pdf> returned the
subscription/paywall HTML page rather than PDF bytes in this sandbox.  OpenAlex and
Semantic Scholar reported no open repository copy.  The inaccessible response was
not retained or mislabeled as a PDF.  No internal theorem number or page claim is
made from unavailable text.  The exact publisher abstract is pinned, while the
fully inspectable application uses R90 Corollary 4.11.

## F67: Furstenberg 1967

File: `sources/furstenberg-1967.pdf`

SHA-256: `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358`

Citation: H. Furstenberg, "Disjointness in ergodic theory, minimal sets, and a
problem in Diophantine approximation," *Mathematical Systems Theory* 1 (1967),
1-49.

DOI: <https://doi.org/10.1007/BF01692494>

Retrieved PDF: <https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf>

Retrieval provenance: this byte-exact PDF is reused from the source-pinned T21
knowledge artifact.  Its recorded mirror retrieval required bypassing a broken TLS
certificate chain; the DOI independently confirms the citation.

Exact locator: Definition IV.1, printed page 47/PDF page 47.  A multiplicative
integer semigroup is lacunary if all positive members are powers of one integer,
and nonlacunary otherwise.  The adjacent example lists the semigroup generated by
2 and 3 as nonlacunary.
