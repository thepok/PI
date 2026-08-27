# T130 source pins and bounded search log

Search date: 2026-08-10 UTC.

Exactly five primary papers were inspected. Five prior reports and the T7 Lean
module are comparator/interface evidence, not additional primary literature.
No unnamed source is used for a mathematical claim.

## S1: Beukers-Schlickewei

- F. Beukers and H. P. Schlickewei, *The equation x+y=1 in finitely generated
  groups*, Acta Arithmetica 78.2 (1996), 189-199.
- Primary PDF URL:
  `https://matwbn.icm.edu.pl/ksiazki/aa/aa78/aa7826.pdf`
- DOI: `https://doi.org/10.4064/aa-78-2-189-199`
- Delivered file: `beukers-schlickewei-1996.pdf`
- SHA-256:
  `f1b115cd8c5f190a0bce8628e229e019191c83b6562a891d8d84f2ed82832a0e`
- Exact locator: printed p.189, PDF p.1, introduction equation (1) and Theorem
  1.1. Fresh `pdftotext -layout` anchors: `Q-closure`, `Theorem 1.1`,
  `x + y = 1`, and the displayed exponent `8r+8`.
- Statement used: the Q-closure of a finitely generated rank-`r` subgroup of
  `(C^*)^2` has at most `2^(8r+8)` solutions of `x+y=1`.

## S2: Amoroso-Viada

- Francesco Amoroso and Evelina Viada, *Small points on subvarieties of a
  torus*, Duke Mathematical Journal 150.3 (2009), 407-442.
- Primary PDF URL: `https://hal.science/hal-00424769/document`
- DOI: `https://doi.org/10.1215/00127094-2009-056`
- Delivered file: `amoroso-viada-2009.pdf`
- SHA-256:
  `eca4350c7787b8caa26fba8d8c950214fc048a11c3259903f83fd4590a740a67`
- Exact locator: Theorem 6.2 and equation (6.24), printed p.26, PDF p.27;
  nondegeneracy definition in footnote 2 near the introductory statement,
  PDF p.6. Fresh text anchors: `Theorem 6.2`, `algebraically closed field of
  characteristic 0`, `(6.24)`, and `non-degenerate solutions`.
- Statement used: for nonzero fixed coefficients and a rank-`r` subgroup of
  `(K^*)^d`, the number of nondegenerate solutions is at most
  `(8d)^(4*d^4*(d+r+1))`.

## S3: Bugeaud-Evertse

- Yann Bugeaud and Jan-Hendrik Evertse, *On two notions of complexity of
  algebraic numbers*, Acta Arithmetica 133.3 (2008), 221-250.
- Versioned primary PDF URL: `https://arxiv.org/pdf/0709.1560`
- DOI: `https://doi.org/10.4064/aa133-3-3`
- Delivered file: `bugeaud-evertse-0709.1560.pdf`
- SHA-256:
  `81d7e7d57867dbfcd08e6c17e8d48a3ecc23f562701be1e68c5acf3bb0ef35db`
- Exact locators: global block-complexity definition, printed pp.221-222,
  PDF pp.1-2; Theorem 2.1 and equation (2.2), printed p.223, PDF p.3.
  Fresh text anchors: `Theorem 2.1`, `algebraic irrational`, `1/11`, and
  `p(n, xi, b)` after normalized extraction.
- Statement used: for algebraic irrational `0<xi<1`, integer base `b>=2`, and
  every real `eta<1/11`, the limsup of
  `p(d,xi,b)/(d*(log d)^eta)` is infinite.

## S4: Fischler-Rivoal

- S. Fischler and T. Rivoal, *Rational approximation to values of G-functions,
  and their expansions in integer bases*, Manuscripta Mathematica 155 (2018),
  579-595; delivered arXiv revision dated 2021-09-16.
- Versioned primary PDF URL: `https://arxiv.org/pdf/1512.06534`
- DOI: `https://doi.org/10.1007/s00229-017-0933-8`
- Delivered file: `fischler-rivoal-1512.06534.pdf`
- SHA-256:
  `2cc01bb677d29ac3b2aa79b54eff131928d747489335ff90e4bf4a48778736b8`
- Exact locators: definition of `N_b` and Theorem 3, PDF p.5; explicit
  `Li_2` calibration in the same theorem; proof denominator
  `q_n=b^(n-1)(b^t-1)`, Section 4, PDF p.15.
- Fresh text anchors: `Theorem 3`, `G-function with rational Taylor
  coefficients`, `Li2`, `107 /epsilon` as extracted from `10^7/epsilon`, and
  `q_n` after normalized extraction.
- Statement used only as a screened application: for source-valid fixed
  G-value data and every fixed `t>=1`, the consecutive repetition ratio has
  limsup at most `epsilon/t`; for `Li_2(1/b^s)`, `s>=10^7/epsilon` is displayed.

## S5: Evertse-Schlickewei-Schmidt

- J.-H. Evertse, H. P. Schlickewei, and W. M. Schmidt, *Linear equations in
  variables which lie in a multiplicative group*, Annals of Mathematics 155
  (2002), 807-836.
- Versioned primary PDF URL: `https://arxiv.org/pdf/math/0409604`
- Official article: `https://annals.math.princeton.edu/2002/155-3/p04`
- Delivered file: `evertse-schlickewei-schmidt-math0409604.pdf`
- SHA-256:
  `3c809fcadaddbc08f57045e4f55562c8a379b5fa33d7e83046b63a9c14766e8f`
- Exact locator: rank and nondegeneracy conventions, printed p.807, PDF p.1;
  Theorem 1.1 and equation (1.2), printed p.808, PDF p.2.
- Statement screened: for arity `d` and group rank `r`, the number of
  nondegenerate solutions is at most `exp((6d)^(3d)*(r+1))`. S2 is sharper
  for the retained three-term card, so S5 is not a fourth candidate.

## Bounded search log

| Date | Domain/query | Disposition |
|---|---|---|
| 2026-08-10 | quantitative `x+y=1` finite-rank multiplicative group | retained S1 as C1; best two-term rank dependence found in the bounded search |
| 2026-08-10 | quantitative nondegenerate linear equations in multiplicative groups | retained S2 as C2; fixed-arity polynomial-in-base explicit count |
| 2026-08-10 | Evertse-Schlickewei-Schmidt general bound `exp((6d)^(3d)(r+1))` | counted as S5 and screened because S2 is quantitatively sharper for the retained three-term card |
| 2026-08-10 | quantitative Subspace theorem plus digit block complexity | retained S3 as C3, then rejected support-to-frequency transfer |
| 2026-08-10 | explicit repeated blocks and restricted denominators for G-values | inspected S4 as a source-shaped boundary; not retained as a fourth card |

The search stopped at five counted primary sources and three retained cards,
below the binding caps of eight and three. The ESS paper was consulted only to
confirm the standard rank/nondegeneracy convention and the older general
constant; no retained card depends on its weaker bound.

## Interface and comparator pins

| File | SHA-256 | Status used |
|---|---|---|
| `canonical_statement.txt` | `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8` | immutable local statement |
| `T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | accepted machine-checked interface, no T130 theorem claimed |
| `prior-t81-REPORT.md` | `73b4198003d637e5b7277dbdfe05e4f2606613f8e906860243331a293dd3b77f` | unverified proof-sketch report with checked imported interfaces |
| `prior-t87-REPORT.md` | `a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078` | mixed literature-checked/machine-checked/proof-sketch report |
| `prior-t114-REPORT.md` | `db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca` | source claims literature-checked; deductions proof sketch |
| `prior-t119-REPORT.md` | `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a` | recovered revised report; incomplete source package, comparison memory only |
| `prior-t125-REPORT.md` | `1ce372d3a99323eae9460a4dbc25b329b93b66e0a356aa3284f1fc9c543f461a` | accepted pinned literature artifact; deductions proof sketch |

T127 boundary: the supplied orchestration snapshot records only an active
generation-1 lease for node
`todo:theory-pi-lacunary-near-return-sparsity:t127`. No report or mathematical
agenda text was available, so no source hash or fingerprint is invented.
