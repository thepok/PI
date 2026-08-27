# Pinned source manifest

Retrieval date: 2026-07-21 UTC.

Every PDF used by the applicability matrix is retained under `sources/` and
has been converted with `pdftotext -layout` under `source_text/`.  Page
extraction from a complete scanned volume changes the file hash, so the hashes
below identify the exact local excerpts, not the complete Internet Archive
volume.

## Primary sources

### S1: Morse--Hedlund (1938)

- Marston Morse and Gustav A. Hedlund, "Symbolic Dynamics," *American
  Journal of Mathematics* 60(4) (1938), 815--866.
- DOI: <https://doi.org/10.2307/2371264>
- Scan source (complete issue):
  <https://archive.org/download/sim_american-journal-of-mathematics_1938-10_60_4/sim_american-journal-of-mathematics_1938-10_60_4.pdf>
- Local PDF: `sources/morse-hedlund-1938.pdf` (journal pages 815--866)
- PDF SHA-256: `4c42a296ccb6588032c40cabd803b9cb4cddf517a34e87cf6b7107bdbb8fe890`
- Text: `source_text/morse-hedlund-1938.txt`
- Text SHA-256: `d28457e31e628dd4a19b8f3ea3ecabe590391fd6674b0e75f407563c38b7393e`
- Exact pointers: Theorem 7.3 and its corollary, pp. 829--830; Theorem
  7.4, p. 830.

### S2: Adamczewski--Bugeaud (2007)

- Boris Adamczewski and Yann Bugeaud, "On the complexity of algebraic
  numbers I. Expansions in integer bases," *Annals of Mathematics* 165(2)
  (2007), 547--565.
- DOI: <https://doi.org/10.4007/annals.2007.165.547>
- Publisher PDF:
  <https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p04.pdf>
- Local PDF: `sources/adamczewski-bugeaud-2007.pdf`
- PDF SHA-256: `55da32c4712b193ffee370af434a98d08ae5922e4731af1cb46a1a44212a83ec`
- Text: `source_text/adamczewski-bugeaud-2007.txt`
- Text SHA-256: `ed0eb771628151f1aca1ea4f405f312fa1d6eab14ba5b624056c5c64b83aee7c`
- Exact pointers: complexity definition and Theorem 1, pp. 549--550;
  Theorems 2--4, pp. 550--551; automatic and Fibonacci examples,
  pp. 552--553.

### S3: Bailey--Crandall (2001)

- David H. Bailey and Richard E. Crandall, "On the Random Character of
  Fundamental Constant Expansions," *Experimental Mathematics* 10(2)
  (2001), 175--190.
- DOI: <https://doi.org/10.1080/10586458.2001.10504441>
- Author-hosted manuscript PDF (dated 2000-10-03, corresponding to the
  published article): <https://www.davidhbailey.com/dhbpapers/bcrandom.pdf>
- Local PDF: `sources/bailey-crandall-2001.pdf`
- PDF SHA-256: `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8`
- Text: `source_text/bailey-crandall-2001.txt`
- Text SHA-256: `d85c9de4771f9f5237409beeada7ebe0ba019c1124b49927c98545bb33b46406`
- Exact pointers in the local manuscript PDF: Hypothesis A, p. 2;
  Theorem 1.1, p. 3; Definitions 2.1--2.2 and Theorems 2.2--2.5,
  pp. 4--7; proof of Theorem 1.1, p. 10; pi base-16 map and
  Conjecture 3.1, p. 11.

### S4: Niven (1947)

- Ivan Niven, "A simple proof that pi is irrational," *Bulletin of the
  American Mathematical Society* 53(6) (1947), 509.
- DOI: <https://doi.org/10.1090/S0002-9904-1947-08821-2>
- Publisher PDF:
  <https://www.ams.org/journals/bull/1947-53-06/S0002-9904-1947-08821-2/S0002-9904-1947-08821-2.pdf>
- Local PDF: `sources/niven-1947-pi-irrational.pdf`
- PDF SHA-256: `fc8e1b80d472cec035bdb7f68963ecf600fba1cb488fd9eeba23def9c7471c77`
- Text: `source_text/niven-1947-pi-irrational.txt`
- Text SHA-256: `74b387ec97fb2c6c9ca89b6534a65a3c85809cbc08a066bffd736016cdd11677`
- Exact pointer: the contradiction to rationality is completed on p. 509.

### S5: Lindemann (1882)

- Ferdinand Lindemann, "Ueber die Zahl pi," *Mathematische Annalen* 20
  (1882), 213--225.
- DOI: <https://doi.org/10.1007/BF01446522>
- Scan source (complete volume):
  <https://archive.org/download/sim_mathematische-annalen_1882_20/sim_mathematische-annalen_1882_20.pdf>
- Local PDF: `sources/lindemann-1882-pi-transcendental.pdf` (journal
  pages 213--225)
- PDF SHA-256: `8ae7cff450c3fd10a46e678f00a7c946a4f9c3ff2188118087025c49f484873e`
- Text: `source_text/lindemann-1882-pi-transcendental.txt`
- Text SHA-256: `27e3390c126f6168a8d6e760a7958a809bcca05a09e7d705bbbcbc246702542e`
- Exact pointer: p. 213 states the goal of proving that pi is not a root
  of an algebraic equation of any degree with rational coefficients; the
  proof occupies Sections 1--3.

### S6: Trueb (2016)

- Peter Trueb, "Digit Statistics of the First pi e Trillion Decimal Digits
  of pi," arXiv:1612.00489v1 (2016).
- Version-pinned record: <https://arxiv.org/abs/1612.00489v1>
- Version-pinned PDF: <https://arxiv.org/pdf/1612.00489v1>
- Local PDF: `sources/trueb-2016-pi-digit-statistics.pdf`
- PDF SHA-256: `d84f17f18ae88ab4b0a197299b00ec675be260a951a5007b4a99b463dd09247b`
- Text: `source_text/trueb-2016-pi-digit-statistics.txt`
- Text SHA-256: `55bb8f756437824d677fe41b3a3c8b279cd856b18a49c9a4caf6ebd1f875126a`
- Exact pointers: abstract and Introduction, p. 1; Table 1 and
  Conclusions, p. 3.
- Reproducibility status: source-reported experiment only.  The PDF and linked
  record page do not provide the full digit dataset, raw block counts,
  frequency-analysis code, or exact analysis command.  See
  `ADVERSARIAL_RECHECK.md`.

## Pinned local statements

- Canonical problem: `knowledge/pi/statements/pi-decimal-factor-complexity.txt`,
  SHA-256
  `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`.
- Accepted T1 formal bridge:
  `knowledge_library/t1/DecimalFactorComplexity.lean`, SHA-256
  `8b61e1319cd9fc753b93723f6f059583741da721252bdb7d3cace8b9c7a80c2e`.
  Relevant declarations are
  `DecimalFactorComplexity.morse_hedlund_canonical` and
  `DecimalFactorComplexity.decimal_disjunctive_iff_canonical_factorComplexity`.

## Retrieval blockers

No cited source was omitted for retrieval failure.  The publisher copies of
S1 and S5 were not directly downloadable in this session; exact article-page
excerpts were therefore made from scans of the complete primary journal
volumes at Internet Archive.  The DOI and scan URL are both retained above.
