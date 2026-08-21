# T11 source and dependency manifest

Retrieval date: 2026-07-22 UTC.

PDFs were retrieved from the listed primary or author repositories and
converted with `pdftotext -layout`. Hashes identify the exact retained bytes.

## New primary-source pins

### S1: Salem--Zygmund (1947)

- R. Salem and A. Zygmund, "On Lacunary Trigonometric Series," *Proceedings
  of the National Academy of Sciences* 33 (1947), 333-338.
- DOI: <https://doi.org/10.1073/pnas.33.11.333>
- Repository record: <https://europepmc.org/article/MED/16588755>
- PDF endpoint: <https://europepmc.org/articles/PMC1079068?pdf=render>
- Local PDF: `sources/salem-zygmund-1947.pdf`
- PDF SHA-256:
  `5c9a042807dab935ab49179bfbfd765dc5f2416873cabf60d2886a7fc2cee604`
- Text: `source_text/salem-zygmund-1947.txt`
- Text SHA-256:
  `ec68043708099acadfe044d351b216d632c9fe4b390deb2b3b22899131df8390`
- Exact pointers: setup and results (i)-(iii), printed pp. 333-334; complex
  coefficient result (vi), printed p. 337.
- Pin note: this is a scan and its extracted text has OCR errors in formulas.
  The matrix uses only statements visually legible in the retained PDF; in
  particular the small-coefficient condition in (vi) is `c_N=o(C_N)`.

### S2: Rudnick--Zaharescu (1999/2002)

- Zeev Rudnick and Alexandru Zaharescu, "The distribution of spacings between
  fractional parts of lacunary sequences," *Forum Mathematicum* 14 (2002),
  691-712.
- Journal DOI: <https://doi.org/10.1515/form.2002.030>
- Version-pinned primary preprint record:
  <https://arxiv.org/abs/math/9912103v1>
- PDF: <https://arxiv.org/pdf/math/9912103v1>
- Local PDF: `sources/rudnick-zaharescu-1999.pdf`
- PDF SHA-256:
  `4e05292f2d3541e93dd1085cb0ebbf9aded0a53358bf1410feecd0535bdb64cb`
- Text: `source_text/rudnick-zaharescu-1999.txt`
- Text SHA-256:
  `93dcad0aebc5900578437a0edcd6cdc3f1776881108dfd7ae15e2a37ddc27fbc`
- Exact pointers: lacunarity definition and Theorems 1.1-1.2, preprint
  pp. 1-3; mean Lemma 3.1, pp. 10-11; variance Proposition 4.1, p. 11.
- Version note: the retained PDF is the authors' arXiv v1 dated 1999-12-13;
  the bibliographic citation records the subsequent journal publication.

### S3: Zeilberger--Zudilin (2020)

- Doron Zeilberger and Wadim Zudilin, "The irrationality measure of pi is at
  most 7.103205334137...," *Moscow Journal of Combinatorics and Number
  Theory* 9(4) (2020), 407-419.
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher record: <https://msp.org/moscow/2020/9-4/p06.xhtml>
- Publisher PDF:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Local PDF: `sources/zeilberger-zudilin-2020.pdf`
- PDF SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Text: `source_text/zeilberger-zudilin-2020.txt`
- Text SHA-256:
  `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`
- Exact pointers: definition and claimed bound, printed p. 407; Propositions
  7-8 and final numerical exponent, printed pp. 417-418.

## Reused accepted dependencies

D1-D3 are cited from the immutable statement and accepted knowledge library.
D4 is staged in this T11 artifact directory to close the prior review gap.

### D1: canonical statement

- Path: `knowledge/pi/statements/pi-decimal-factor-complexity.txt`
- SHA-256:
  `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`

### D2: accepted T10 formal HFE definition

- Knowledge-library path: `knowledge_library/t10/PiWeightedFourierReduction.lean`
- SHA-256:
  `45003707a7b30447c9dd9ed5843f8c899a7c7107814c99f9b7a7a9f4ab8bf4ff`
- Exact pointers: `energyWeight`, lines 70-73;
  `weightedFourierEnergy`, lines 75-78; `frequencyCutoff`, lines 1085-1087;
  `HFE_pi`, lines 1089-1097; conditional theorem and scope disclaimer,
  lines 1125-1128 and 1219-1226.

### D3: accepted T2 applicability audit

- Knowledge-library path: `knowledge_library/t2/APPLICABILITY_MATRIX.md`
- SHA-256:
  `54d0dca52b5640c1030714cdf58e3cb5f12ac16a2a3dd90c407e3b41bd96443a`
- Source manifest path: `knowledge_library/t2/SOURCE_MANIFEST.md`
- Source manifest SHA-256:
  `9e24221a6578169d22f85cb9a3245cf0a23ae0cda11304a0435716be6e2fd0fa`
- Reused content: Bailey--Crandall Hypothesis A and Theorem 1.1; the
  base-2/base-16 versus base-10 distinction; decimal normality status; finite
  pi-digit computations. T11 does not repeat T2's primary files.

### D4: staged accepted pi-digits T28 audit

The original workflow record is not present in this checkout. To make this
T11 package independently reviewable, the content-addressed accepted T28
audit, its hash manifest, its gate evidence, and all four cited primary PDFs
are staged under `t28/`:

- Audit path: `t28/T28-lacunary-sum-audit.md`
- Audit SHA-256:
  `4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd`
- Hash-manifest path: `t28/HASHES.sha256`
- Hash-manifest SHA-256:
  `33c0ccc0cba5f8aaa12783e5201da41ffa002d0ea01cdd21621791b8b28e6544`
- Gate-evidence path: `t28/ACCEPTANCE_EVIDENCE.json`
- Gate-evidence SHA-256:
  `5984f0dacb05f4bfc3e612836edc4560a6965c02ccce18ddc9e18b043d4ab401`
The reused primary pins recorded in T28 are:

- Erdos--Gal I: `t28/sources/erdos-gal-1955-part1.pdf`, PDF SHA-256
  `a94e2560d886e4de674f678363c596276c73e0e06a492a866239543dee746931`,
  DOI <https://doi.org/10.1016/S1385-7258(55)50010-2>.
- Erdos--Gal II: `t28/sources/erdos-gal-1955-part2.pdf`, PDF SHA-256
  `c638ec58e455da94a2406b858e0a5b9ce3271954e77c38eec10581abf0ed7ff6`,
  DOI <https://doi.org/10.1016/S1385-7258(55)50011-4>.
- Philipp: `t28/sources/philipp-1975-lacunary.pdf`, PDF SHA-256
  `4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a`,
  DOI <https://doi.org/10.4064/aa-26-3-241-251>.
- Fukuyama: `t28/sources/fukuyama-2008-geometric-discrepancy.pdf`, retained
  PDF SHA-256
  `59b263e7d74aa627606181646c75c02803c41d42af4d1780f7ff8de28f917266`,
  stable extracted-text SHA-256
  `f0f50d8450f05bbe5bcf78d76a5448232631c3c974369103048f6e4a0064c808`,
  DOI <https://doi.org/10.1007/s10474-007-6201-8>.

T28 exact pointers and qualifications are retained in its Sections 3-6. T11
does not repeat its T27 parameter derivation; it adds the different HFE
frequency-weight and quantifier audit.

## Retrieval and search limitations

- The bounded candidate search covered direct lacunary sums, geometric
  discrepancy, parameter mean square, pair correlation, and the current
  pinned pointwise irrationality-measure bound for pi. It is not an exhaustive
  proof that no fixed-pi theorem exists.
- One Crossref request returned HTTP 429 and one EuDML search endpoint returned
  HTTP 500. Exact DOI, arXiv, publisher, and repository pages for retained
  sources were checked directly instead.
- The first attempted Europe PMC PDF endpoint for Salem--Zygmund failed with
  an HTTP/2 stream error. Retrying its documented rendered-PDF endpoint over
  HTTP/1.1 succeeded; the retained bytes are hashed above.
- T28's original workflow directory was absent. Its content-addressed audit,
  hash manifest, and acceptance evidence were staged verbatim. The three
  locally retained primary PDFs and a fresh download of Erdos--Gal II all
  reproduce T28's accepted PDF hashes exactly; no theorem transcription was
  reconstructed.
