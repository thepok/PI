# T88 Source Pins

## Canonical statement

- File: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Original URL: local program statement
  `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.

## Cuny--Eisner--Farkas

- Christophe Cuny, Tanja Eisner, Balint Farkas, "Wiener's lemma along primes
  and other subsequences," *Advances in Mathematics* 347 (2019), 340--383.
- DOI: <https://doi.org/10.1016/j.aim.2019.02.005>
- Stable author-version record: <https://arxiv.org/abs/1701.00101v6>
- Retrieved PDF URL: <https://arxiv.org/pdf/1701.00101v6>
- PDF: `cuny-eisner-farkas-1701.00101v6.pdf`
- PDF SHA-256:
  `fdcc0b42f7f1472acfd9d8a984a1f061ab5f1eaf2db6abebe6705137d6d4e237`
- `pdftotext -layout` output:
  `cuny-eisner-farkas-1701.00101v6.txt`
- Text SHA-256:
  `ee8aafd40cdb6b08c4c63833fba96b15806d27ba7b32742d8dd9f9d722233d6a`
- Exact locator: Theorem 1.1, published page 340; author-version printed page
  1; extracted text lines 41--52. It gives
  `lim_N N^(-1) sum_(n=1)^N |mu_hat(n)|^2`
  equal to the sum of squared atom masses. The parenthetical immediately after
  the formula gives the symmetric normalization.
- Version caveat: v6 is dated 2023 and reports a gap in a page-13 return-times
  example. Theorem 1.1 used here is present at the stated locator and is not
  that example.
- Retrieval caveat: the ScienceDirect published-PDF endpoint returned HTTP 403
  in the sandbox, so the exact author-version PDF is pinned rather than silently
  claiming it is the publisher PDF.

## Birkhoff

- George D. Birkhoff, "Proof of the Ergodic Theorem," *Proceedings of the
  National Academy of Sciences* 17(12) (1931), 656--660.
- DOI metadata: <https://doi.org/10.1073/pnas.17.2.656>. PMC and Crossref list
  issue 12 and also expose `10.1073/pnas.17.12.656` as an alias.
- Stable record: <https://pmc.ncbi.nlm.nih.gov/articles/PMC1076138/>
- Exact locators: page 656 formula (1), pages 659--660 construction of the
  time spent in a measurable region, and page 660 statement of the resulting
  almost-everywhere time-probability and extension to function space.
- The PMC article is an image-only scan. The five exact official page-image
  URLs and hashes are:

| Page | File | Official PMC image URL | SHA-256 |
|---|---|---|---|
| 656 | `birkhoff-1931-p656.png` | <https://cdn.ncbi.nlm.nih.gov/pmc/blobs/8890/1076138/241315addf79/pnas01728-0036.png> | `f210435ec22628da76e7e90060c2ef66c7cd1816079fd63f4640ea2c2b569d57` |
| 657 | `birkhoff-1931-p657.png` | <https://cdn.ncbi.nlm.nih.gov/pmc/blobs/8890/1076138/a73ea4f2a691/pnas01728-0037.png> | `ae8a4d9876372fa894825f68e9a1670d8bf54edb2d347fefebdf89291c62754d` |
| 658 | `birkhoff-1931-p658.png` | <https://cdn.ncbi.nlm.nih.gov/pmc/blobs/8890/1076138/b0710c132512/pnas01728-0038.png> | `caa684d81e50aa85198c2ca99104c4a05172d2b869bc026a7fc1edeaf8899fe4` |
| 659 | `birkhoff-1931-p659.png` | <https://cdn.ncbi.nlm.nih.gov/pmc/blobs/8890/1076138/ac474993ab5e/pnas01728-0039.png> | `992675f218240fa1746da28d5f1d894f62678d8202b2e75304667ac55071b33f` |
| 660 | `birkhoff-1931-p660.png` | <https://cdn.ncbi.nlm.nih.gov/pmc/blobs/8890/1076138/e3137e6e35dd/pnas01728-0040.png> | `1f8d14bcee2880570ffee8a34c6184fecbd531bcd633116fc9ea8bc7e0dffefb` |

- Visual verification: the page numbers, title, formulas, and quoted passages
  were checked directly against these rendered scans. No OCR quotation is
  represented as exact.
- Retrieval blocker: PNAS returned HTTP 403 and the PMC PDF endpoint returned
  a 1,817-byte anti-bot HTML page. That response was deleted. The official
  page scans above are the pinned source.
- Substitution caveat: REPORT.md states separately the modern pointwise
  Birkhoff formulation used on an invertible two-sided Bernoulli extension and
  derives simultaneous character genericity by a countable intersection. It
  does not pretend that the 1931 notation is the modern theorem statement.

## Modern pointwise formulation used in the substitution

- Paul Hagelstein, Daniel Herden, Alexander Stokolos, "A theorem of Besicovitch
  and a generalization of the Birkhoff Ergodic Theorem," arXiv:1910.09054v1
  (2019).
- Stable record: <https://arxiv.org/abs/1910.09054v1>
- Retrieved PDF: <https://arxiv.org/pdf/1910.09054v1>
- File: `hagelstein-herden-stokolos-1910.09054v1.pdf`
- SHA-256:
  `cbae98a5eed652c00907d8f302a62daef2b8cdede915bc0f0029ba3e04d93d30`
- Exact locator: Theorem 2, printed page 3. It assumes an invertible
  measure-preserving transformation of a standard probability space and
  states almost-everywhere existence of the ergodic-average limit when the
  displayed ergodic maximal function is finite. The sentence immediately
  following says that integrable `f` has this convergence by Birkhoff.
- Application map: REPORT.md uses the invertible two-sided iid shift, applies
  the theorem to bounded real and imaginary parts of pulled-back characters,
  identifies the limit using ergodicity and bounded convergence, and only then
  projects to the one-sided decimal factor.

## Checked local interfaces

- `T55SignedMultiplierTenPairing.lean`
  SHA-256 `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd`.
  Relevant lines: 187--188 (`triangularWeight`), 229--230 (`terminalShell`).
- `T61DirectLabelAdjacentPhaseVariance.lean`
  SHA-256 `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb`.
  Relevant lines: 35--36 (`directFrequency`), 57--58
  (`directTerminalMass`), 344--367 (exact-remainder premise and threshold).
- `T67TerminalRayStrength.lean`
  SHA-256 `e9fc18166d2b31c52adbfe73bfcbb10ccd8d93c785fb39144b88db75ed493dff`.
  Relevant lines: 53--61 (empirical coefficient and defect), 90--132
  (endpoint telescope), 138--160 (primitive rays and shell), 167--192
  (margin and exact quantifier order), 227--284 (strict implication),
  497--509 (two means), 522--525 (total weight), and 581--645 (abstract
  separator theorem clauses).

These three files are byte-exact copies from the accumulated checked library;
T88 does not claim to recompile or extend them.
