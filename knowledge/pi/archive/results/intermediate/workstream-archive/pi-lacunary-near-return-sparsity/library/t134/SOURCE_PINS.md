# T134 source and comparator pins

Audit date: 2026-08-10 UTC. Exactly six primary papers were inspected. A PDF
and a temporary `pdftotext -layout` derivative count as one source. PDF bytes
are authoritative; no OCR was used.

## S1: Zeilberger--Zudilin

- Doron Zeilberger and Wadim Zudilin, *The irrationality measure of pi is at
  most 7.103205334137...*, Moscow Journal of Combinatorics and Number Theory 9
  (2020), 407--419.
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher URL: <https://msp.org/moscow/2020/9-4/p01.xhtml>
- File: `zeilberger-zudilin-2020.pdf`
- SHA-256: `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Exact locators: irrationality-measure definition, printed p.407, physical
  PDF p.2; final upper bound, printed p.418, physical PDF p.13.
- Role: C-RD load-bearing fixed-pi approximation theorem.

## S2: Bugeaud--Kim

- Yann Bugeaud and Dong Han Kim, *On the b-ary expansions of log(1+1/a) and
  e*, Annali della Scuola Normale Superiore di Pisa (2017), 931--947.
- DOI: <https://doi.org/10.2422/2036-2145.201603_002>
- Publisher record:
  <https://journals.sns.it/index.php/annaliscienze/article/view/519>
- Retrieved PDF URL:
  <https://journals.sns.it/index.php/annaliscienze/article/download/519/509>
- File: `bugeaud-kim-2017.pdf`
- SHA-256: `4a4a2d949b342c9360b78dcb8073e1fb367b910b30bba9d1be19b5f29e3f6c9d`
- Exact locator: Lemma 3.6 and proof, printed pp.944--945, PDF pp.14--15;
  denominator `b^|W|*(b^|UV|-1)` in the displayed proof.
- Role: C-RD repetition/restricted-denominator theorem and maximum-repetition
  rejection.

## S3: Moshchevitin

- Nikolay G. Moshchevitin, *Density modulo 1 of sublacunary sequences:
  application of Peres-Schlag's arguments*.
- Primary version: <https://arxiv.org/abs/0709.3419v2>
- PDF URL: <https://arxiv.org/pdf/0709.3419v2>
- DOI: <https://doi.org/10.1007/s10958-012-0660-3>
- File: `moshchevitin-0709.3419v2.pdf`
- SHA-256: `d6b435d06149f5b5030be9a0e31175a8b8676d64e612acee282be74fd9f874a5`
- Exact locators: definition (1), printed p.2, PDF p.2; Theorem 2 and
  hypotheses, printed pp.2--3, PDF pp.2--3; conclusion that the infinite
  avoidance set is nonempty, printed p.3.
- Role: restricted-denominator avoidance source screened before candidate
  admission because it supplies no named point or fixed-pi specialization.

## S4: Fischler--Rivoal

- Stephane Fischler and Tanguy Rivoal, *Rational approximation to values of
  G-functions, and their expansions in integer bases*, Manuscripta
  Mathematica 155 (2018), 579--595; delivered arXiv revision 2021-09-16.
- Versioned PDF URL: <https://arxiv.org/pdf/1512.06534>
- DOI: <https://doi.org/10.1007/s00229-017-0933-8>
- File: `fischler-rivoal-1512.06534.pdf`
- SHA-256: `2cc01bb677d29ac3b2aa79b54eff131928d747489335ff90e4bf4a48778736b8`
- Exact locators: definition of `N_b` and Theorem 3, PDF p.5; explicit
  `Li_2` condition `s>=10^7/epsilon`, PDF p.5; proof denominator
  `b^(n-1)*(b^t-1)`, Section 4, PDF p.15.
- Role: C-GRUN load-bearing maximum-run theorem.

## S5: Fishman--Merrill--Simmons

- Lior Fishman, Keith Merrill, and David Simmons, *Uniformly de Bruijn
  Sequences and Symbolic Diophantine Approximation on Fractals*, Annals of
  Combinatorics 22 (2018), 271--293.
- Repository URL: <https://eprints.whiterose.ac.uk/id/eprint/126995/>
- PDF URL:
  <https://eprints.whiterose.ac.uk/id/eprint/126995/8/10.1007_2Fs00026_018_0384_2.pdf>
- DOI: <https://doi.org/10.1007/s00026-018-0384-2>
- File: `fishman-merrill-simmons-2018.pdf`
- SHA-256: `a1aa39f1783491077c55513c737895253bb7a7323fa7eb823afac672e48924d4`
- Exact locators: definition (2.1), printed pp.3--4, physical PDF pp.4--5;
  Remark 3.3, printed p.5, physical PDF p.6; Corollary 4.3 and its extension
  proof, printed pp.10--11, physical PDF pp.11--12.
- Role: C-DB load-bearing totally de Bruijn existence theorem.

## S6: Becher--Carton

- Veronica Becher and Olivier Carton, *Normal numbers and nested perfect
  necklaces*, Journal of Complexity 54 (2019), article 101403.
- Versioned PDF URL: <https://arxiv.org/pdf/1805.03713v1>
- DOI: <https://doi.org/10.1016/j.jco.2019.03.003>
- File: `becher-carton-1805.03713v1.pdf`
- SHA-256: `3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448`
- Exact locators: perfect and nested-perfect necklace definitions, preprint
  pp.1--2; Theorem 1, preprint p.2, for Levin's concatenation and
  `O((log N)^2/N)` discrepancy.
- Role: symbolic exact-incidence comparator screened as the already-audited
  global discrepancy route.

## Local interfaces

| File | SHA-256 | Status used |
|---|---|---|
| `canonical_statement.txt` | `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8` | immutable local statement |
| `T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | machine-checked definition, ordered-pair identity, and factor-three interface; no decay theorem |

## Comparator archive

`prior_evidence.tar` has SHA-256
`37a4c7c59d0a5704273f053d5fd3b4ead84c020891b7f66a3e6f3103d42a0285`
and contains exactly these readable reports:

| Item | Archive member | SHA-256 | Level used |
|---|---|---|---|
| T87 | `notes/t87/REPORT.md` | `a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078` | unverified note; source statements literature-checked, deductions proof sketch |
| T111 | `t111/REPORT.md` | `89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8` | source statements literature-checked, deductions proof sketch |
| T113 | `notes/t113/REPORT.md` | `30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445` | unverified note; source statements literature-checked, deductions proof sketch |
| T116 | `t116/REPORT.md` | `573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1` | source statements literature-checked, deductions proof sketch |
| T119 | `t130/prior-t119-REPORT.md` | `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a` | recovered incomplete package; comparison memory only |
| T121 | `t121/REPORT.md` | `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2` | source statements literature-checked, deductions proof sketch |
| T128 | `t128/REPORT.md` | `7e9520d7a0191df6f988d7f4f4920cfb954ac5162efa7fae43c1851de5863ffc` | source statements literature-checked, deductions proof sketch |
| T130 | `t130/REPORT.md` | `c130b2c8790dce80080367201e56efb3847f8262189af57f2ce756aacb6a893c` | source statements literature-checked, deductions proof sketch |
| T131 | `t131/REPORT.md` | `ed2229ceedcff357f80121fbdc31ffbb8e3582717f487a3a85368eabe64790db` | source statements literature-checked, deductions proof sketch |

No T132 or T133 artifact was readable in the supplied knowledge library,
workspace records, or orchestration input. Their identifiers occur only in
T134's mandatory comparison sentence. No source, theorem, status, or
mathematical fingerprint is inferred from that observation.

## Retrieval boundary

All six PDFs were reused byte-for-byte from the supplied pinned knowledge
library and hash-checked after copying. Every PDF produced nonempty text under
`pdftotext -layout`; no OCR or network retrieval was required.
