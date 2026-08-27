# T125 source pins and bounded search log

Inspection date: 2026-08-10 UTC.

Exactly five primary papers were opened. A PDF and its temporary `pdftotext
-layout` derivative count as one source. The six vendored comparator reports
are prior-program evidence, not primary literature and are not included in the
primary-source count.

```text
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 12
RETAINED_CANDIDATE_COUNT: 4
RETAINED_CANDIDATE_CAP: 4
```

## S1: averaged correlations and short Fourier sums

- Authors: Kaisa Matomaki, Maksym Radziwill, and Terence Tao.
- Title: *An averaged form of Chowla's conjecture*.
- Version inspected: arXiv:1503.05121v3, dated 1 March 2022.
- Abstract page: <https://arxiv.org/abs/1503.05121>.
- Versioned PDF: <https://arxiv.org/pdf/1503.05121v3>.
- DOI: <https://doi.org/10.2140/ant.2015.9.2167>.
- Delivered file: `mrt-1503.05121v3.pdf`.
- SHA-256: `8a2633b1594615fe0c340bbca01ad059be5bd66d3495bd028e7e9d2264f1e688`.
- Exact locators: PDF p. 2, Theorem 1.1 and equations (1.2)-(1.3),
  including the ranges `10 <= H <= X`, every natural `k`, the ordered
  shift-tuple sums, and the factor
  `k*(log log H/log H + 1/log^(1/3000) X)`; PDF p. 3, Theorem 1.3,
  including `sup_alpha` outside `integral_0^X`, the interval-location
  average, and exponent `1/700`; PDF pp. 7-8, Section 1.3, for the
  absolute-implied-constant and fixed-parameter little-o conventions.
- Use: C-AVG and C-SHORT.

## S2: logarithmic two-point correlation

- Author: Terence Tao.
- Title: *The logarithmically averaged Chowla and Elliott conjectures for
  two-point correlations*.
- Version inspected: arXiv:1509.05422v4, dated 29 July 2016.
- Abstract page: <https://arxiv.org/abs/1509.05422>.
- Versioned PDF: <https://arxiv.org/pdf/1509.05422v4>.
- DOI: <https://doi.org/10.1017/fmp.2016.6>.
- Delivered file: `tao-1509.05422v4.pdf`.
- SHA-256: `467329ae414b669808555fddf131be3bc07025777ae3af8ccdea6e98db6722e9`.
- Exact locator: PDF p. 2, Theorem 1.2 and equation (1.3), including fixed
  natural `a_1,a_2`, integer `b_1,b_2`, determinant condition
  `a_1*b_2-a_2*b_1 != 0`, arbitrary `1 <= omega(x) <= x` tending to
  infinity, logarithmic weight `1/n`, moving interval
  `x/omega(x) < n <= x`, and qualitative `o(log omega(x))`.
- Use: C-LOG.

## S3: logarithmic odd-order correlations

- Authors: Terence Tao and Joni Teravainen.
- Title: *Odd order cases of the logarithmically averaged Chowla conjecture*.
- Version inspected: arXiv:1710.02112v1, dated 5 October 2017.
- Abstract page: <https://arxiv.org/abs/1710.02112>.
- Versioned PDF: <https://arxiv.org/pdf/1710.02112v1>.
- DOI: <https://doi.org/10.5802/jtnb.1062>.
- Delivered file: `tao-teravainen-1710.02112v1.pdf`.
- SHA-256: `232dc29917cf20f223695e3a680830e5db3b4a221049cd22f040b31144369748`.
- Exact locators: PDF p. 2, Theorem 1.1 and footnote 1; PDF p. 3,
  Remark 1.2. The order `k` is any fixed odd natural number; all affine
  coefficients are fixed before `x -> infinity`; the average is `1/log x`
  times a `1/n` weighted sum; no nondegeneracy condition is needed at odd
  order; and the moving-window normalization by `log omega(x)` is explicitly
  noted.
- Use: C-LOG.

## S4: first-order short intervals and fixed-shift two-point separation

- Authors: Kaisa Matomaki and Maksym Radziwill.
- Title: *Multiplicative functions in short intervals*.
- Version inspected: arXiv:1501.04585v4, dated 15 October 2017.
- Abstract page: <https://arxiv.org/abs/1501.04585>.
- Versioned PDF: <https://arxiv.org/pdf/1501.04585v4>.
- DOI: <https://doi.org/10.4007/annals.2016.183.3.6>.
- Delivered file: `mr-1501.04585v4.pdf`.
- SHA-256: `ec546fdf256b3b3b26b161886c5bab5efb372978ab430c0032e55919f5329277`.
- Exact locators: PDF pp. 1-2, Theorem 1, for multiplicative
  `f:N->[-1,1]`, absolute constants `C,C'>1`, uniform
  `2 <= h <= X`, `delta>0`, the explicit exceptional-set bound, and
  `C'=20000`; PDF p. 3, Corollary 2, for every fixed integer `h>=1`, an
  unspecified `delta(h)>0`, and the one-sided eventual bound
  `X^(-1) sum_(n<=X) lambda(n)lambda(n+h) <= 1-delta(h)`. Corollary 2 has no
  absolute value and supplies no lower bound.
- Use: C-SHORT.

## S5: nonpretentious higher uniformity and pattern support

- Authors: Kaisa Matomaki, Maksym Radziwill, Terence Tao, Joni Teravainen,
  and Tamar Ziegler.
- Title: *Higher uniformity of bounded multiplicative functions in short
  intervals on average*.
- Version inspected: arXiv:2007.15644v3, dated 9 June 2022.
- Abstract page: <https://arxiv.org/abs/2007.15644>.
- Versioned PDF: <https://arxiv.org/pdf/2007.15644v3>.
- DOI: <https://doi.org/10.4007/annals.2023.197.2.3>.
- Delivered file: `mrttz-2007.15644v3.pdf`.
- SHA-256: `fef1a239e616f40c57aa45e7df3397aebe880cde8ce5763acb815a24a171f6aa`.
- Exact locators: PDF p. 6, Corollary 1.6, for fixed integer `k>=0`, fixed
  `0<theta<=1`, `H>=X^theta`, interval-location averaging, and qualitative
  `o(X)` of the normalized `U^(k+1)` norm; PDF p. 9, Theorem 1.9, for
  `s(k) >>_A k^A` for every fixed `A>=1`; PDF p. 11, Corollary 1.11, for
  fixed correlation order, fixed distinct coefficients, fixed `epsilon>0`,
  an ordinary `n<=X` average followed by a uniform dilation average
  `h<=X^epsilon`, and the explicit observation that bounded `h` would amount
  to Chowla; PDF pp. 7-8, Proposition 1.7, for the unsolved polylogarithmic
  interval regime relevant to logarithmically averaged Chowla.
- Use: C-HIGH.

## Prior comparator pins

These byte-exact prior reports are supplied only to verify fingerprint
comparisons. Their source statements retain the labels used in the reports;
their new deductions are not silently promoted to theorems.

| Item | Delivered file | SHA-256 | Status used |
|---|---|---|---|
| T110 | `prior-t110-REPORT.md` | `4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668` | sources literature-checked; deductions proof sketch |
| T117 | `prior-t117-REPORT.md` | `ee6974209f7e6064f30ec3ae83240cb1e7994e66566e920417dbf361da0ff30b` | sources literature-checked; deductions proof sketch |
| T121 | `prior-t121-REPORT.md` | `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2` | sources literature-checked; deductions proof sketch |
| T122 | `prior-t122-REJECTED-REPORT.md` | `6ea3b7798ff4b211c0f6c3b514d062fbce8e518208c570231a1f2c32417845b7` | report deductions proof sketch; final workflow status rejected for duplication |
| T123 r0 | `prior-t123-R0-REPORT.md` | `3eed848437e5ade5cfc0ac5c8f8fabf5968ff156262b74ea2d947413b74fecb2` | revision requested; not an accepted artifact |
| T124 | `prior-t124-REPORT.md` | `461df40595e9d59852b7d86f8df8800b0e5fafaf6803843cb2ea1e29d737dd86` | source quotations literature-checked; deductions and comparisons unverified proof sketch |

The T124 report is a byte-exact copy from the refreshed knowledge library's
`notes/t124` directory. It is used only as an unverified mechanism comparator;
none of its proof-sketch deductions is a discharged premise of T125.

## Search log

The bounded search used the following lanes and then stopped at five papers.

| Date | Lane and queries | Outcome |
|---|---|---|
| 2026-08-10 | arithmetic pretentiousness and Fourier decay: `Liouville averaged Chowla shifts quantitative`, `Liouville short interval exponential sums uniform alpha` | S1 and S4 retained; direct prescribed-shift decay remains unavailable |
| 2026-08-10 | higher correlation and entropy: `logarithmically averaged Chowla odd order Liouville`, `Liouville entropy sign patterns higher Gowers short intervals` | S2, S3, and S5 retained; averaging and growing-order gaps recorded |
| 2026-08-10 | short structured sums: `Liouville polynomial phases short intervals Gowers`, `nonpretentious multiplicative functions short interval nilsequence` | S5 retained; its interval length and fixed-order quantifiers fail the logarithmic-depth test |
| 2026-08-10 | symbolic collision theory: `Liouville block complexity collision entropy Renyi` | S5 Theorem 1.9 is the strongest inspected support theorem; it controls support size, not frequencies or Renyi-2 collision |

Retrieval notes: all five versioned arXiv PDFs downloaded successfully. DOI
landing pages were used only for bibliographic identification. Temporary text
derivatives were produced with `pdftotext -layout`; the delivered PDFs are
authoritative. No image-only scan or OCR was needed. No additional unnamed
primary paper was opened.
