# T70 source manifest

Audit date: 2026-08-03 UTC

The files listed here are the authoritative bytes. ASCII formulas in
`T70_SOURCE_PINNED_APPLICABILITY_AUDIT.md` are transcriptions for comparison.

## Formal and canonical comparators

### Canonical statement

- File: `CANONICAL_STATEMENT.txt`
- Original source URL: none; the local problem was formulated by this system.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Locators: lines 1-10 for the canonical question; lines 17-36 for recorded
  ambiguities; lines 38-39 for verification rules.

### T69 kernel-checked interface

- File: `T69_KERNEL_INTERFACE.lean`
- SHA-256:
  `09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301`
- Source status: copied byte-exact from the accepted kernel-checked T69 entry.
- Locators: lines 30-59, 63-128, 130-159, 243-275, 330-424, 446-492,
  494-610, and 612-880.
- Scope: conditional residual-A12, `m=1`, dyadic primitive-sector interface;
  no analytic premise at `pi` is asserted.

## D3: Aistleitner--Fukuyama

- Authors: Christoph Aistleitner and Katusi Fukuyama
- Title: *Extremal discrepancy behavior of lacunary sequences*
- arXiv record: <https://arxiv.org/abs/1403.1630v2>
- Retrieved PDF URL: <https://arxiv.org/pdf/1403.1630v2>
- arXiv DOI: <https://doi.org/10.48550/arXiv.1403.1630>
- File: `aistleitner-fukuyama-1403.1630v2.pdf`
- SHA-256:
  `4c2990ec21a5962bfee2f7d603074d71b987e1dddaa1a885b3c55934f1749eea`
- PDF properties: 15 pages, text extraction available, no OCR used.
- Exact locators: physical PDF page 5 for the centered periodized indicator;
  physical PDF page 7, Theorem 4, for the double-average identity; physical
  PDF page 14 for its proof.

## D4: Technau--Zafeiropoulos

- Authors: Niclas Technau and Agamemnon Zafeiropoulos
- Title: *The discrepancy of (n_k x) with respect to certain probability
  measures*
- Publication: *Quarterly Journal of Mathematics* 71 (2020), 573-597
- DOI: <https://doi.org/10.1093/qmathj/haz058>
- arXiv record: <https://arxiv.org/abs/1812.06293v2>
- Retrieved PDF URL: <https://arxiv.org/pdf/1812.06293v2>
- File: `technau-zafeiropoulos-1812.06293v2.pdf`
- SHA-256:
  `33a5d518ce974021dd672af2d5d5b8c1e830a1af4328a2f7148e509513cb955e`
- PDF properties: 26 pages, text extraction available, no OCR used.
- Exact locators: physical PDF pages 2-3 for Fourier-decay hypothesis (4) and
  Theorem 1; physical PDF pages 4-5 for Corollary 3 and its interpretation.

## B1: Bombieri--Iwaniec

- Authors: Enrico Bombieri and Henryk Iwaniec
- Title: *On the order of zeta(1/2+it)*
- Publication: *Annali della Scuola Normale Superiore di Pisa*, Series 4,
  13.3 (1986), 449-472
- Primary record: <https://www.numdam.org/item/ASNSP_1986_4_13_3_449_0/>
- Retrieved PDF URL:
  <https://www.numdam.org/item/ASNSP_1986_4_13_3_449_0.pdf>
- File: `bombieri-iwaniec-1986.pdf`
- SHA-256:
  `90f99ac228726c6ebe7944929c718a1af80162dffd7aaff2bc58769f6e3904cc`
- PDF properties: 25-page scan, partial text extraction; displayed formulas
  in Lemma 2.4 are absent from extracted text.
- Exact locators: physical PDF page 5, journal page 452, Lemma 2.4 and its
  displayed bilinear inequality; physical PDF pages 6-7, journal pages
  453-454, proof and integer-coordinate/circle-distance modification.
- Scan handling: pages were rendered at 220 dpi and inspected visually.
  `tesseract` was unavailable, so no OCR transcription is claimed. The PDF
  pages are authoritative.

## B2: Garaev

- Author: M. Z. Garaev
- Title: *Double exponential sums and congruences with intervals and
  exponential functions modulo a prime*
- Publication: *Journal of Number Theory* 199 (2019), 377-388
- DOI: <https://doi.org/10.1016/j.jnt.2018.11.019>
- arXiv record: <https://arxiv.org/abs/1810.06341v1>
- Retrieved PDF URL: <https://arxiv.org/pdf/1810.06341v1>
- File: `garaev-1810.06341v1.pdf`
- SHA-256:
  `60053bb3ce7ddc002e24367b00fa43fee3b554f7fce6287b75aa7a61e0459c1c`
- PDF properties: 12 pages, text extraction available, no OCR used.
- Exact locators: physical PDF pages 1-3 for interval and notation
  hypotheses; physical PDF pages 3-4, Section 2, Theorem 1, for all four
  terms in `Delta` and the `M < p^(2/3)` range.

## B3: Kerr

- Author: Bryce Kerr
- Title: *Incomplete exponential sums over exponential functions*
- Publication: *Quarterly Journal of Mathematics* 66 (2015), 213-224
- DOI: <https://doi.org/10.1093/qmath/hau015>
- arXiv record: <https://arxiv.org/abs/1302.4170v1>
- Retrieved PDF URL: <https://arxiv.org/pdf/1302.4170v1>
- File: `kerr-1302.4170v1.pdf`
- SHA-256:
  `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd`
- PDF properties: 13 pages, text extraction available, no OCR used.
- Exact locators: physical PDF page 1, equation (1), for `S_(g,p)`;
  physical PDF page 2, Section 2, Theorem 2, for the three cases.

## L1: Baker--Munsch--Shparlinski

- Authors: Roger C. Baker, Marc Munsch, and Igor E. Shparlinski
- Title: *Additive energy and a large sieve inequality for sparse sequences*
- Publication: *Mathematika* 68 (2022), 362-399
- DOI: <https://doi.org/10.1112/mtk.12140>
- arXiv record: <https://arxiv.org/abs/2103.12659v2>
- Retrieved PDF URL: <https://arxiv.org/pdf/2103.12659v2>
- File: `baker-munsch-shparlinski-2103.12659v2.pdf`
- SHA-256:
  `16a64bb33679c0236533ac30a4037e954a3b4529b53cf07b03c386807f336db2`
- PDF properties: 38 pages, text extraction available, no OCR used.
- Exact locators: physical PDF pages 3-4 for the averaged sum; physical PDF
  pages 6-7, equations (1.11)-(1.13) and Theorem 1.1, for energies, growth,
  range, and bound.

## Referenced but not duplicated

- `knowledge_library/t5/APPLICABILITY_MATRIX.md`, SHA-256
  `ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406`
- `knowledge_library/t5/SOURCE_MANIFEST.md`, SHA-256
  `ace2233019ea2a24e8b83fb49b03c968ca4f5a1f6d87e04327f12a784c70fc65`
- `knowledge_library/t21/T21_APPLICABILITY_AUDIT.md`, SHA-256
  `b468e509c4aa3b8bad7d833458578f94b4a5f0d95c53567a69a69e1598c525ae`
- `knowledge_library/t21/SOURCE_MANIFEST.md`, SHA-256
  `b1efc07b51c3904aa8aae3ef148e58fb5bd62a727651b7498c7e3ce43c88bcf8`

Those files and their PDFs are intentionally absent from the T70 artifact
set.

## Search log and blockers

| Date | Search branch | Result |
|---|---|---|
| 2026-08-03 | fixed-point bilinear lacunary and incomplete geometric sums | Retained Bombieri--Iwaniec, Garaev, and Kerr. No real fixed-`pi` cancellation theorem was located. |
| 2026-08-03 | structured multiplier discrepancy and half-arc averages | Retained Aistleitner--Fukuyama and Technau--Zafeiropoulos. The former matches the finite average scale; neither evaluates at `pi`. |
| 2026-08-03 | averaged multiplier, sparse-modulus, and digital large sieve | Retained Baker--Munsch--Shparlinski. T21's Chang--Kerr--Shparlinski row was not repeated. |
| 2026-08-03 | Bombieri--Iwaniec extraction | `pdftotext` omitted displayed formulas and `tesseract` was not installed. Pages 452-454 were rendered and checked visually instead. |

## Replay

Run from the artifact directory:

```sh
sh verify_sources.sh
```

For the scanned source, manually inspect physical PDF pages 5-7.
