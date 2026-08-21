# T99 source manifest

Audit date: 2026-08-09 UTC.

Claim label: `literature-checked` applies only to the pinned source statements,
locators, and applicability comparisons in `T99_DIRECTION_DISCOVERY_AUDIT.md`.
No source below proves T29 at `alpha=pi`, C1, C2, or C3.

## Local comparators

### Canonical statement

- File: `CANONICAL_STATEMENT.txt`
- Original source URL: none; the statement says it was formulated locally.
- SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Locators: lines 1-10 for the canonical question, 17-36 for recorded
  ambiguities, and 38-39 for verification rules.

### T29 machine-checked interface

- File: `T29_KERNEL_INTERFACE.lean`
- SHA-256: `2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358`
- Source: byte-exact copy of the machine-checked T29 library entry.
- Locators: lines 28-83 for endpoints, frequencies, blocks, widths, energy,
  target, and quantifiers; 100-151 for literal expansions; 687-772 for the
  conditional transfer and explicit absence of a fixed-pi proof.

### T87 and T90 machine-checked specialization interfaces

- Files: `T87_KERNEL_SPECIALIZATION.lean` and
  `T90_KERNEL_SPECIALIZATION.lean`.
- SHA-256: `88b17a0be03261d3b53fe64d09452491920ca3550194d4bd2efa22f0ca2519e4`
  and `0481de1cbdb9c8466efa6bff5ceb4ceb684536484ecdf6429f062ab2adc2ab90`.
- Source: byte-exact copies of the machine-checked T87 and T90 library
  entries.
- Locators: T87 lines 68-125 for elimination of every `(8,1)` arithmetic
  exclusion; T90 lines 31-113 for the core domain and two orientations,
  115-217 for the fixed-pi cosine and full square-function identity, and
  340-467 for the explicitly unproved `CORR_pi` critical-band premise and
  conditional consequence.

## Primary sources

### P1: Zeilberger and Zudilin

- Authors: Doron Zeilberger and Wadim Zudilin
- Title: *The Irrationality Measure of Pi is at most 7.103205334137...*
- Publication: Moscow Journal of Combinatorics and Number Theory 9 (2020),
  407-419
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Retrieved PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- File: `zeilberger-zudilin-2020.pdf`
- SHA-256: `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- PDF: 16 pages, 804062 bytes, text extraction available, no OCR.
- Locators: physical PDF page 2 (journal page 407), Introduction, definition
  of irrationality measure; physical PDF page 13 (journal page 418), `World
  record`, final displayed bound.

### P2: Matveev

- Author: E. M. Matveev
- Title: *An explicit lower bound for a homogeneous rational linear form in
  the logarithms of algebraic numbers. II*
- Publication: Izvestiya: Mathematics 64:6 (2000), 1217-1269
- DOI: <https://doi.org/10.1070/IM2000v064n06ABEH000314>
- Primary record: <https://www.mathnet.ru/eng/im314>
- Retrieved PDF URL:
  <https://www.mathnet.ru/php/getFT.phtml?jrnid=im&paperid=314&what=fullteng&option_lang=eng>
- File: `matveev-2000.pdf`
- SHA-256: `e395e4698837950b683362558441e1e75298ad28cb0cc8cf260a556c93093574`
- PDF: 53 pages, 526302 bytes, text extraction available, no OCR.
- Locators: physical PDF page 1, equation (1.1); physical PDF page 3,
  equations (2.1)-(2.3) and Theorem 2.1.
- Extraction warning: `pdftotext` drops the `not equal` glyph in the clauses
  `b_n != 0` and `Lambda != 0`. Those glyphs were checked visually on physical
  page 3; the PDF is authoritative.
- Retrieval note: the first unadorned HTTP request returned 403. Repeating the
  same primary URL with a browser user-agent and MathNet referrer succeeded.

### P3: Evertse, Schlickewei, and Schmidt

- Authors: J.-H. Evertse, H. P. Schlickewei, and W. M. Schmidt
- Title: *Linear equations in variables which lie in a multiplicative group*
- Publication: Annals of Mathematics 155 (2002), 807-836
- DOI: <https://doi.org/10.2307/3062133>
- Publisher record: <https://annals.math.princeton.edu/2002/155-3/p04>
- Retrieved author/journal-form manuscript:
  <https://arxiv.org/pdf/math/0409604>
- File: `evertse-schlickewei-schmidt-math0409604.pdf`
- SHA-256: `3c809fcadaddbc08f57045e4f55562c8a379b5fa33d7e83046b63a9c14766e8f`
- Version: arXiv `math/0409604v1`, 30 pages, text extraction available.
- Locators: physical PDF pages 1-2, equation (1.1), definition of
  nondegenerate, Theorem 1.1, and equation (1.2).

### P4: Garaev

- Author: M. Z. Garaev
- Title: *Double exponential sums and congruences with intervals and
  exponential functions modulo a prime*
- Publication: Journal of Number Theory 199 (2019), 377-388
- DOI: <https://doi.org/10.1016/j.jnt.2018.11.019>
- Retrieved PDF URL: <https://arxiv.org/pdf/1810.06341v1>
- File: `garaev-1810.06341v1.pdf`
- SHA-256: `60053bb3ce7ddc002e24367b00fa43fee3b554f7fce6287b75aa7a61e0459c1c`
- PDF: 12 pages, text extraction available, no OCR.
- Locators: physical PDF pages 1-3 for interval, order, and character
  notation; physical PDF pages 3-4, Section 2, Theorem 1, for the four terms
  in `Delta` and `M < p^(2/3)`.

### P5: Aistleitner and Fukuyama

- Authors: Christoph Aistleitner and Katusi Fukuyama
- Title: *Extremal discrepancy behavior of lacunary sequences*
- Publication: Monatshefte fuer Mathematik 177 (2015), 167-184
- DOI: <https://doi.org/10.1007/s00605-014-0693-4>
- Retrieved PDF URL: <https://arxiv.org/pdf/1403.1630v2>
- File: `aistleitner-fukuyama-1403.1630v2.pdf`
- SHA-256: `4c2990ec21a5962bfee2f7d603074d71b987e1dddaa1a885b3c55934f1749eea`
- PDF: 15 pages, text extraction available, no OCR.
- Locators: physical PDF page 5 for the centered periodized indicator and
  physical PDF page 7, Theorem 4, for the exact double-average identity.

### P6: Chernov and Kleinbock

- Authors: Nikolai Chernov and Dmitry Kleinbock
- Title: *Dynamical Borel-Cantelli lemmas for Gibbs measures*
- Publication: Israel Journal of Mathematics 122 (2001), 1-27
- DOI: <https://doi.org/10.1007/BF02809888>
- Retrieved PDF URL: <https://arxiv.org/pdf/math/9912178v1>
- File: `chernov-kleinbock-math9912178v1.pdf`
- SHA-256: `b779dfb61606b3991a86fe6dc3a4d1c7d1c45a81c9b746c9d799178bb00195d7`
- PDF: 23 pages, text extraction available, no OCR.
- Locators: physical PDF page 3, Theorem 1.4 and formula (1.1); page 4,
  Theorem 1.7; page 6, cylinder definition (2.1) and Theorem 2.1.

### P7: Technau and Zafeiropoulos

- Authors: Niclas Technau and Agamemnon Zafeiropoulos
- Title: *The discrepancy of (n_k x) with respect to certain probability
  measures*
- Publication: Quarterly Journal of Mathematics 71 (2020), 573-597
- DOI: <https://doi.org/10.1093/qmathj/haz058>
- Retrieved PDF URL: <https://arxiv.org/pdf/1812.06293v2>
- File: `technau-zafeiropoulos-1812.06293v2.pdf`
- SHA-256: `33a5d518ce974021dd672af2d5d5b8c1e830a1af4328a2f7148e509513cb955e`
- PDF: 26 pages, text extraction available, no OCR.
- Locators: physical PDF pages 2-3, Fourier-decay hypothesis (4) and
  Theorem 1.

### P8: Bailey and Crandall

- Authors: David H. Bailey and Richard E. Crandall
- Title: *On the Random Character of Fundamental Constant Expansions*
- Publication: Experimental Mathematics 10 (2001), 175-190
- DOI: <https://doi.org/10.1080/10586458.2001.10504441>
- Retrieved author-copy URL:
  <https://www.davidhbailey.com/dhbpapers/baicran.pdf>
- File: `bailey-crandall-2001.pdf`
- SHA-256: `8c482ef709857877ea22e4bdf9ff3fa3673dd8c20ba9f9026e3a1bded1a6704d`
- PDF: 25 pages, text extraction available, no OCR.
- Locators: PDF/article page 2, Hypothesis A; page 3, Theorem 1.1.

## Bounded search and retrieval record

The retained corpus has eight primary papers. It was chosen to represent:
quantitative transcendence at pi; Archimedean logarithmic forms; sparse exact
relations; finite-field/modular exponential sums; averaged lacunary identities;
expanding-map and Gibbs-shift dynamics; Fourier-decaying-measure discrepancy;
and a conditional fixed-pi pseudorandom-digit mechanism.

The p-adic search branch located algebraic-number/S-unit and p-adic logarithm
theorems, but no source was retained as a separate candidate because their
first gate is again algebraicity/S-unit input and their conclusions concern
valuations or exact equations, not the real additive character at pi. Garaev
P4 is the retained modular representative. The transfer-operator branch is
represented at the theorem-output level by the expanding-map/Gibbs results P6;
no claim is made that P6 is itself phrased as a spectral theorem for a transfer
operator.

This is not a claim that the literature outside these eight sources has been
exhausted.

## Prior-art replay bundle

- File: `PRIOR_PINNED_CORPUS.tar`
- SHA-256: `68ed33e72b941db6c25664dcfdcf4d969d197ceee46e90120f898354df748b61`
- Contents: the exact T5, T21, T63, T68, T70, T79-T82, T85, T13, T35,
  T47, T92, T95, and T97 files cited by the duplication matrix, plus the
  escalation record used only to establish absence/pipeline status for T78 and
  T93.
- Replay: `verify_sources.sh` extracts the archive into a temporary directory
  and checks every member against the hashes printed in the matrix and script.

## Replay

Run from the artifact directory:

```sh
sh verify_sources.sh
```

The script checks byte identity and text-extractable locator markers. For
Matveev, inspect the two dropped `not equal` glyphs visually on physical PDF
page 3 as recorded above.
