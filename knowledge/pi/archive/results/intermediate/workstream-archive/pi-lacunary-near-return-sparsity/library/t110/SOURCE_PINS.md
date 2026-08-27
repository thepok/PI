# T110 source pins

Search date: 2026-08-10 UTC.

This ledger lists every primary source inspected, including rejected sources.
There are exactly seven. PDF hashes are over the delivered bytes. Text hashes are
listed only for the three candidate-card source derivatives produced by
`pdftotext -layout`; mathematical locators are to printed preprint pages and
the named theorem/equation, not to derivative line numbers alone.

## S1. Direct Gowers decay for Thue--Morse

- Jakub Konieczny, *Gowers norms for the Thue-Morse and Rudin-Shapiro
  sequences*.
- Primary URL: <https://arxiv.org/abs/1611.09985v2>
- PDF URL: <https://arxiv.org/pdf/1611.09985v2>
- Journal DOI: <https://doi.org/10.5802/aif.3285>
- Delivered PDF: `konieczny-1611.09985v2.pdf`
- PDF SHA-256:
  `92cc1e1f37a924d89bb2788d883670eba2604c2d56a029d94c750803e78c2360`
- Delivered derivative: `konieczny-1611.09985v2.txt`
- Derivative SHA-256:
  `ba1c7f0f36212a3b7131c8c8dc82177d21b8dc571a8e03e6b7dd629a14d49f37`
- Exact locators: Definition 1.1 and Theorem A, preprint pp. 2--3;
  polynomial-phase and dynamical consequences (9), p. 3; large
  self-correlation equation (3), pp. 1--2; nilsequence discussion, p. 11.
- Role: retained fingerprint F1.

## S2. q-multiplicative Gelfond bootstrap

- Aihua Fan and Jakub Konieczny, *On uniformity of q-multiplicative
  sequences*.
- Primary URL: <https://arxiv.org/abs/1806.04267v2>
- PDF URL: <https://arxiv.org/pdf/1806.04267v2>
- Journal DOI: <https://doi.org/10.1112/blms.12245>
- Delivered PDF: `fan-konieczny-1806.04267v2.pdf`
- PDF SHA-256:
  `e5fdb01f5f1c717cd5733158edcb97cf70d2f4a18f423c9ab6fd8476fb67f114`
- Delivered derivative: `fan-konieczny-1806.04267v2.txt`
- Derivative SHA-256:
  `32fcce0f37082dc6f4bc90f8a9e6b191f57864a07d04c9a0342c804a04efc51d`
- Exact locators: q-multiplicative definition and equation (3), preprint
  pp. 1--2; Theorems A and B, p. 2; Gelfond type equation (9) and generalized
  Thue--Morse equations (10)--(12), pp. 4--5; fixed-parameter convention,
  p. 9; inverse-theorem/nilsequence discussion, pp. 8--9.
- Role: retained fingerprint F3.

## S3. Higher correlations for lacunary sequences

- Sneha Chaubey and Nadav Yesha, *The distribution of spacings of real-valued
  lacunary sequences modulo one*.
- Primary URL: <https://arxiv.org/abs/2108.00431v1>
- PDF URL: <https://arxiv.org/pdf/2108.00431v1>
- arXiv DOI: <https://doi.org/10.48550/arXiv.2108.00431>
- Delivered PDF: `chaubey-yesha-2108.00431v1.pdf`
- PDF SHA-256:
  `b660b086d52ecaf9d2e7abe13bcc306765dbc1166076ccb9ddbb14d1461e7e54`
- Delivered derivative: `chaubey-yesha-2108.00431v1.txt`
- Derivative SHA-256:
  `97855f7a140140671801c463f10d2d78eb4613a0a70f0407f39f8604013f9043`
- Exact locators: k-level correlation definition and equation (1), preprint
  pp. 2--3; Theorem 1, p. 3; lacunarity condition (2) and Proposition 2,
  pp. 3--4; dependence convention, p. 3.
- Role: candidate card F2 and T104-duplicate comparator; not counted as a
  retained fingerprint.

## S4. Automatic-sequence decomposition

- Jakub Byszewski, Jakub Konieczny, and Clemens Muellner, *Gowers norms for
  automatic sequences*.
- Primary URL: <https://arxiv.org/abs/2002.09509v3>
- PDF URL: <https://arxiv.org/pdf/2002.09509v3>
- Journal DOI: <https://doi.org/10.19086/da.75201>
- Delivered PDF: `bkm-2002.09509v3.pdf`
- PDF SHA-256:
  `6a55a35657c2d3a95d1d11c8de3c472cd3a650312e7248d70c00e6bb5f54553e`
- Exact locators inspected: definition (1) and Theorems A--C, printed pp.
  2--4; fixed-order convention, printed p. 6.
- Screen result: broader structural decomposition but no constants uniform in
  growing order or automaton complexity; redundant with F1 for the named
  Thue--Morse point.

## S5. Automatic weights for ergodic theorems

- Tanja Eisner and Jakub Konieczny, *Automatic sequences as good weights for
  ergodic theorems*.
- Primary URL: <https://arxiv.org/abs/1710.08643v3>
- PDF URL: <https://arxiv.org/pdf/1710.08643v3>
- Journal DOI: <https://doi.org/10.3934/dcds.2018178>
- Delivered PDF: `eisner-konieczny-1710.08643v3.pdf`
- PDF SHA-256:
  `00627afdff0baef233976eaa09fc367c705f57357eac82740b40b5e033daa4a3`
- Exact locators inspected: Theorems A--C, preprint pp. 3--4; Corollary 5.2,
  p. 12; Proposition 8.1, pp. 17--18.
- Screen result: polynomial correlation is qualitative except for the uniform
  linear estimate; no new higher-order triangular mechanism beyond S1/S2.

## S6. Erroneous identifier returned during search

- Doron Zeilberger, *What is Mathematics and What Should it Be?*
- Primary URL: <https://arxiv.org/abs/1704.05560v1>
- PDF URL: <https://arxiv.org/pdf/1704.05560v1>
- arXiv DOI: <https://doi.org/10.48550/arXiv.1704.05560>
- Delivered PDF: `zeilberger-1704.05560v1.pdf`
- PDF SHA-256:
  `fc31fd7558c5191f13b00a4e0c8688d5f7b6098a95310471331ebfb6054f3f8b`
- Locator inspected: title and opening page/preamble, p. 1.
- Screen result: no Thue--Morse, Gowers, nilsequence, digital, or lacunary
  theorem; rejected immediately and counted against the source cap.

## S7. Explicit fixed base-10 expanding-map point

- Veronica Becher and Olivier Carton, *Normal numbers and nested perfect
  necklaces*.
- Primary URL: <https://arxiv.org/abs/1805.03713v1>
- PDF URL: <https://arxiv.org/pdf/1805.03713v1>
- arXiv DOI: <https://doi.org/10.48550/arXiv.1805.03713>
- Delivered PDF: `becher-carton-1805.03713v1.pdf`
- PDF SHA-256:
  `3197ae6ff0aecb4cfc80bb89688bdc3250d09f9c11b168c9f401fdb835602448`
- Exact locator inspected: Theorem 1, preprint p. 2. For every integer base
  `b>=2`, Levin's explicitly constructed point is the stated concatenation of
  nested perfect necklaces; conversely every point with that construction has
  discrepancy `O((log N)^2/N)` for `({b^n x})_(n>=1)`.
- Screen result: this makes the fixed-point lacunary-dynamics search literal at
  `b=10`, but supplies discrepancy only, no U3, nilsequence, higher-order
  correlation, or T107 anti-boundary theorem. The mechanism was already
  audited in T90 and is not retained.

## Count audit

```text
INSPECTED_PRIMARY_SOURCE_IDS: S1,S2,S3,S4,S5,S6,S7
PRIMARY_SOURCE_COUNT: 7
PRIMARY_SOURCE_CAP: 10
CARD_SOURCE_IDS: S1,S2,S3
RETAINED_FINGERPRINT_SOURCE_IDS: S1,S2
RETAINED_FINGERPRINT_COUNT: 2
CANDIDATE_CAP: 3
```

No retrieval failure occurred. The S3 PDF is byte-identical to the copy already
present in the accepted T104 source package; reusing those pinned bytes avoids
an unnecessary second network representation. S7 is byte-identical to the copy
already present in T90. S1, S2, S4, S5, and S6 were retrieved from the exact
arXiv PDF URLs above.
