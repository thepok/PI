# T21 source manifest

Audit date: 2026-08-01 UTC

The authoritative source bytes are the files named below. ASCII formulas in
`T21_APPLICABILITY_AUDIT.md` are transcriptions for comparison; the retained
PDFs and Lean snapshots control.

## Canonical and formal comparators

### Canonical statement

- File: `CANONICAL_STATEMENT.txt`
- Original source URL: none; local problem formulated by this system, with
  provenance in lines 12-15.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Locators: lines 1-10 for the canonical question; lines 17-36 for recorded
  ambiguities; lines 38-39 for verification rules.

### T8 exact domain and spectral sum

- File: `T8_SPECTRAL_SOURCE.lean`
- SHA-256:
  `f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9`
- Knowledge-library status: `machine-checked` in the accepted T8 record. T21
  uses the established interface and does not reprove it.
- Locators: lines 37-42, 44-68, 71-94, 96-123, and 154-159.

### T12 scale-matched interface

- File: `T12_SCALE_MATCHED_SOURCE.lean`
- SHA-256:
  `a4108ff862c13ee0f9fa3fc877723856eb34497430cde36d85f7943ce0347bcf`
- Knowledge-library status: restored `machine-checked` T12 module. T21 quotes
  only its existing definitions and conditional implications.
- Locators: lines 29-41, 53-62, 151-161, and 230-244.

## V1: Demeter--Silva

- Authors: Ciprian Demeter and Prabath Silva
- Title: *Some new light on a few classical results*
- Publication: *Colloquium Mathematicum* 140.1 (2015), 129-147
- DOI: <https://doi.org/10.4064/cm140-1-11>
- arXiv record: <https://arxiv.org/abs/1311.4092>
- Retrieved PDF URL: <https://arxiv.org/pdf/1311.4092v1>
- File: `demeter-silva-1311.4092v1.pdf`
- SHA-256:
  `eaf4081ebc9796efa80ddb6c81349846263b9900b56a7e78d881f39117ad7348`
- PDF properties: 17 pages, text extraction available, no OCR used.
- Exact locators: physical/article PDF page 3, equation (7), for the Carleson operator and
  arbitrary measurable cutoff; PDF page 15, Section 7, Theorem 7.1, for the
  vector-valued inequality.

## V2: Aistleitner--Berkes--Seip

- Authors: Christoph Aistleitner, Istvan Berkes, and Kristian Seip
- Title: *GCD sums from Poisson integrals and systems of dilated functions*
- Publication: *Journal of the European Mathematical Society* 17.6 (2015),
  1517-1546
- DOI: <https://doi.org/10.4171/JEMS/537>
- arXiv record: <https://arxiv.org/abs/1210.0741>
- Retrieved PDF URL: <https://arxiv.org/pdf/1210.0741v5>
- File: `aistleitner-berkes-seip-1210.0741v5.pdf`
- SHA-256:
  `b89868f1563d382525608059b45a338feb4e18a52ac6470c99baf077e122375b`
- PDF properties: 30 pages, text extraction available, no OCR used.
- Exact locator: PDF/article page 17, Section 5, Lemma 4 and equation (30),
  continuing on page 18; constant dependence is stated immediately below.

## D1-D2: Chang--Kerr--Shparlinski

- Authors: Mei-Chu Chang, Bryce Kerr, and Igor E. Shparlinski
- Title: *On the exponential large sieve inequality for sparse sequences
  modulo primes*
- Publication: *Journal of Mathematical Analysis and Applications* 459.1
  (2018), 53-81
- DOI: <https://doi.org/10.1016/j.jmaa.2017.10.070>
- arXiv record: <https://arxiv.org/abs/1706.04776>
- Retrieved PDF URL: <https://arxiv.org/pdf/1706.04776v2>
- File: `chang-kerr-shparlinski-1706.04776v2.pdf`
- SHA-256:
  `561ffe68b4a1730d7cbd460f83f815c88b06e55579880fd440934ffe2c42634d`
- PDF properties: 30 pages, text extraction available, no OCR used.
- Exact locators: PDF page 2 for `V_lambda`; PDF pages 4-5, Theorems
  2.1-2.2; physical/article PDF page 6, Lemma 3.1.

## Referenced but not duplicated: T5

- Record-root-relative external library path:
  `knowledge_library/t5/APPLICABILITY_MATRIX.md` (from the artifact directory:
  `../knowledge_library/t5/APPLICABILITY_MATRIX.md`)
- SHA-256:
  `ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406`
- Record-root-relative external manifest path:
  `knowledge_library/t5/SOURCE_MANIFEST.md` (from the artifact directory:
  `../knowledge_library/t5/SOURCE_MANIFEST.md`)
- SHA-256:
  `ace2233019ea2a24e8b83fb49b03c968ca4f5a1f6d87e04327f12a784c70fc65`
- T5 rows M1-M7 and their source PDFs are intentionally not copied into T21.

## Retrieval blockers and negative searches

### Montgomery 1978 maximal large sieve

- Author: Hugh L. Montgomery
- Title: *The analytic principle of the large sieve*
- Publication: *Bulletin of the American Mathematical Society* 84 (1978),
  547-567
- DOI: <https://doi.org/10.1090/S0002-9904-1978-14497-8>
- Attempted official PDF URL:
  <https://www.ams.org/journals/bull/1978-84-04/S0002-9904-1978-14497-8/S0002-9904-1978-14497-8.pdf>
- Attempted Project Euclid article route:
  <https://projecteuclid.org/journals/bulletin-of-the-american-mathematical-society/volume-84/issue-4/The-analytic-principle-of-the-large-sieve/bams/1183540928.full>
- Result on 2026-08-01: AMS returned HTTP 403; the Project Euclid PDF route
  returned an HTML denial. No PDF is retained, no hash is claimed, and no
  theorem from this source is used in the applicability matrix.

### Search log

| Date | Query or database | Result |
|---|---|---|
| 2026-08-01 | arXiv API, exact phrase `digital large sieve` | Zero results. |
| 2026-08-01 | arXiv API, `large sieve` AND `lacunary` | Zero results. |
| 2026-08-01 | arXiv API, `large sieve` AND `digital` | Two results; Chang--Kerr--Shparlinski was the relevant sparse-power primary source. |
| 2026-08-01 | Crossref title/metadata searches | Confirmed DOI and publication metadata for all three retained papers. |
| 2026-08-01 | Local T9-T19 staged notes | Found ordinary large-sieve and discrepancy leads, but no pinned fixed-`pi` maximal/vector theorem and no real-orbit digital large sieve. |

## Replay

Run from the artifact directory:

```sh
sh verify_sources.sh
```

For manual extraction:

```sh
pdftotext -layout demeter-silva-1311.4092v1.pdf ds.txt
pdftotext -layout aistleitner-berkes-seip-1210.0741v5.pdf abs.txt
pdftotext -layout chang-kerr-shparlinski-1706.04776v2.pdf cks.txt
```

Search respectively for `Theorem 7.1`, `Lemma 4`, `Theorem 2.2`, and
`Lemma 3.1` at the page locators above.
