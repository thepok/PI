# T79 source manifest

Accessed and checked: 2026-08-03 UTC.

All retained PDFs were converted with `pdftotext -layout`; none is image-only.
The PDFs are authoritative. `verify.sh` recomputes all hashes and checks the
listed text anchors from a directory containing only the delivered artifacts.

## Canonical statement and program inputs

| ID | File | SHA-256 | Status and exact use |
|---|---|---|---|
| Canonical | `pi-positive-decimal-factor-entropy.txt` | `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6` | Locally formulated; no original external URL. Exact canonical question and recorded ambiguities. |
| T56 | `T56LagSectorAudit.lean` | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` | `machine-checked`; short-sector endpoints and `SparseShortRepunitIncidenceBound`, lines 68-72 and 116-133. |
| T58 | `T58TriangularFejerAudit.lean` | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` | `machine-checked`; `1<=h<H_n`, triangle, and `h*10^j*(10^r-1)`, lines 29-71. |
| T60 | `T60_VAALER_IRRATIONALITY_FRONTIER.md` | `2a9aa7628b0611279e4b9d74659e744e8386da5308b196507e3fe47cd164b4ef` | `proof sketch`; audited specification `(SI_pi)`, lines 484-516. No claim from this note is promoted to machine-checked. |
| T61 | `T61VaalerAnalytic.lean` | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` | `machine-checked`; analytic certificate, exact ranges, strict endpoints, complete signed expression, and eventual quantifiers, lines 1724-1737, 1759-1768, 1837-1892, 1894-1920, and 2022-2122. |

## Primary literature

### IY23

- File: `iyer-2312.01076.pdf`
- SHA-256: `a312fd3c401f46360939dfa7ffff92a3d3f293693a9637fad2f2574e181821d8`
- Citation: S. Iyer, "Rational Approximation with Digit-Restricted
  Denominators," arXiv:2312.01076v1 (2023).
- Versioned record: <https://arxiv.org/abs/2312.01076v1>
- Retrieved PDF: <https://arxiv.org/pdf/2312.01076v1>
- Persistent identifier: <https://doi.org/10.48550/arXiv.2312.01076>
- Locators: Theorem 1.1, PDF p. 3; elementary construction, PDF p. 4;
  Lemmas 3.3-3.4, PDF p. 6.
- Search anchors: `Theorem 1.1. For any`, `Some elementary observations`,
  `Lemma 3.3. For all`, and `Lemma 3.4.`
- Checked use: effective `C_b/(log N)^2` approximation using arbitrary base-`b`
  zero-one digit denominators; exact elementary block-difference construction
  at `1/(t(b,N)+1)` scale.

### AB07

- File: `adamczewski-bugeaud-2007.pdf`
- SHA-256: `55da32c4712b193ffee370af434a98d08ae5922e4731af1cb46a1a44212a83ec`
- Citation: B. Adamczewski and Y. Bugeaud, "On the complexity of algebraic
  numbers I. Expansions in integer bases," *Annals of Mathematics* 165 (2007),
  547-565.
- DOI: <https://doi.org/10.4007/annals.2007.165.547>
- Retrieved PDF:
  <https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf>
- Locators: Condition `(*)_w` and Theorem 5, printed pp. 553-554, PDF p. 7;
  equation (2) and Lemma 1, printed p. 556, PDF p. 10.
- Search anchors: `Theorem 5. Let`, `The key fact is the observation`, and
  `Lemma 1. For any integer n`.
- Checked use: the periodic completion has exact denominator
  `beta^r_n*(beta^s_n-1)` and the theorem concludes membership in `Q(beta)` or
  transcendence.

### PVZZ19

- File: `pollington-velani-zafeiropoulos-zorin-1906.01151.pdf`
- SHA-256: `a392ea606ae8df3ff03c08f5e27e41187373f65dae0bf5b4d22f6cc744ce5269`
- Citation: A. D. Pollington, S. Velani, A. Zafeiropoulos, and E. Zorin,
  "Inhomogeneous Diophantine Approximation on M0-sets with Restricted
  Denominators," arXiv:1906.01151v2 (2019), subsequently *International
  Mathematics Research Notices* (2022), 8571-8643.
- Versioned record: <https://arxiv.org/abs/1906.01151v2>
- Retrieved PDF: <https://arxiv.org/pdf/1906.01151v2>
- DOI: <https://doi.org/10.1093/imrn/rnaa307>
- Locators: counting function (7), Theorem 1 and equations (8)-(10), PDF pp.
  2-3; finite-prime semigroup (29)-(30), Theorem 3 and equation (31), PDF
  pp. 10-11 (Theorem 3 is on PDF p. 11).
- Search anchors: `Theorem 1. Let`, `Theorem 3. Let`, and `smooth numbers`.
- Checked use: quantitative shrinking-target counts for almost every target,
  first for lacunary sequences and then sequences supported on one fixed finite
  prime set.

### BLMV09

- File: `blmv-2009.pdf`
- SHA-256: `372d251b5c7c4936ab4e6b9cc6fb3af2ded2c8fe81020ad3e467843c20878e3b`
- Citation: J. Bourgain, E. Lindenstrauss, P. Michel, and A. Venkatesh, "Some
  effective results for times a times b," *Ergodic Theory and Dynamical
  Systems* 29 (2009), 1705-1722.
- DOI: <https://doi.org/10.1017/S0143385708000898>
- Retrieved PDF:
  <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/01225FAD40EEBC38F3AE1A5C119D0267/S0143385708000898a.pdf/some-effective-results-for-ab.pdf>
- Locator: Theorem 1.8, printed p. 1707, PDF p. 3.
- Search anchors: `Diophantine-generic: there exists k so that` and
  `(log log N )`.
- Checked use: effective density of the two-generator multiplicative-semigroup
  orbit of a Diophantine-generic fixed point.

### CZ04

- File: `corvaja-zannier-math0403522.pdf`
- SHA-256: `90dc898925b01539afe05fcbb4cd2728c921bdb268719bf2cf02304ab252192f`
- Citation: P. Corvaja and U. Zannier, "On the rational approximations to the
  powers of an algebraic number: Solution of two problems of Mahler and Mendes
  France," *Acta Mathematica* 193 (2004), 175-191.
- Versioned record: <https://arxiv.org/abs/math/0403522v1>
- Retrieved PDF: <https://arxiv.org/pdf/math/0403522v1>
- DOI: <https://doi.org/10.1007/BF02392563>
- Locator: definition of pseudo-Pisot and Main Theorem (1.1), preprint p. 2.
- Search anchors: `Main Theorem. Let` and `finitely generated multiplicative`.
- Checked use: finite-exception lower bound for algebraic moving targets in a
  fixed finitely generated multiplicative group.

### HA93

- File: `hata-1993.pdf`
- SHA-256: `c3294d1987dfd013ec4d13f93737233177817d50c9c102ea95033e986cd9e3df`
- Citation: M. Hata, "Rational approximations to pi and some other numbers,"
  *Acta Arithmetica* 63 (1993), 335-349.
- DOI: <https://doi.org/10.4064/aa-63-4-335-349>
- Retrieved PDF:
  <https://www.impan.pl/shop/publication/transaction/download/product/107787?download.pdf>
- Locators: integral construction (1.3)-(1.4) and Theorem 1.1, printed p. 336,
  PDF p. 2;
  Lemma 2.2 and products defining `Delta_i(n)` and `D_n`, printed pp. 339-341;
  `q_n=D_n*v_n`, printed p. 344, PDF p. 10.
- Search anchors: `Theorem 1.1. For any`, `Lemma 2.2. There exists`, and
  `qn = Dn vn` after text extraction.
- Checked use: the denominator-clearing mechanism of the Pade/linear-form
  construction. Its ordinary irrationality-measure conclusion is not reused.

### BBP97

- File: `bailey-borwein-plouffe-1997.pdf`
- SHA-256: `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`
- Citation: D. H. Bailey, P. B. Borwein, and S. Plouffe, "On the Rapid
  Computation of Various Polylogarithmic Constants," *Mathematics of
  Computation* 66 (1997), 903-913. The retained PDF is NASA Technical Report
  NAS-96-016 (1996), the source version of the paper.
- DOI: <https://doi.org/10.1090/S0025-5718-97-00856-9>
- Retrieved PDF:
  <https://ntrs.nasa.gov/api/citations/19970009337/downloads/19970009337.pdf>
- Locator: Theorem 1 and equations (1.2)-(1.4), report Section 1, PDF p. 3.
- Search anchors: a whitespace-tolerant `Theorem 1.` and `(1.2)`.
- Checked use: the base-16 identity for pi and the exact linear denominator
  factors in its truncations.

## Retrieval and scope notes

- All seven retained primary PDFs downloaded successfully and produced
  nonempty text extractions.
- Some additional publisher endpoints encountered HTTP 403 or rate limiting
  during triage. No theorem statement from an unretrieved source is used.
- Search results are mutable. The dated search log in the audit defines the
  bounded corpus; the negative verdict is only about that corpus.
- The final all-denominator irrationality bounds in Hata and later work are the
  ordinary irrationality-measure route excluded by T79 and already audited by
  T60. Only Hata's construction-denominator mechanism is assessed here.
