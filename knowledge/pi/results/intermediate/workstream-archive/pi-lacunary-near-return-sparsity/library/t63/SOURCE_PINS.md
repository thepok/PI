# T63 primary-source pins

Retrieved and checked: 2026-08-06 UTC.

All PDF hashes below are SHA-256 hashes of the byte-exact files delivered beside
this manifest.  The text files are deterministic `pdftotext -layout` extracts
used only for search and quotation checking.  Page locators in `REPORT.md`
refer to the displayed PDF page and, where useful, the printed manuscript page.

## Zudilin version pair

1. Wadim Zudilin, *A BBP-style computation for pi in base 10*, arXiv:2409.10097v1,
   submitted 16 September 2024.
   - Versioned record: <https://arxiv.org/abs/2409.10097v1>
   - Versioned PDF: <https://arxiv.org/pdf/2409.10097v1>
   - DOI family: <https://doi.org/10.48550/arXiv.2409.10097>
   - Delivered PDF: `zudilin-2409.10097v1.pdf`
   - PDF SHA-256: `67e8946c37b9e91da0dcdcc9f9886ef7278b69ca68200c7acac03197c9c59743`
   - Text SHA-256: `bc82ae9f327ef2533062d07216d94c092efec8128c733f526bccc3341ab41d79`
   - Exact locators retained: equation (1), PDF p. 2; condition (2), PDF p. 3;
     unnumbered base-5 modular equality, PDF p. 3; decimal paragraph and
     unnumbered decimal modular equality, PDF p. 3.

2. Wadim Zudilin, *A BBP-style computation for pi in base 5*, arXiv:2409.10097v2,
   revised 17 September 2024.
   - Versioned record: <https://arxiv.org/abs/2409.10097v2>
   - Versioned PDF: <https://arxiv.org/pdf/2409.10097v2>
   - Delivered PDF: `zudilin-2409.10097v2.pdf`
   - PDF SHA-256: `01ba3b7b1ebd22d0d718b0fa3ed67d20030870a2bfe41a3a6b3ff7a3ce479d25`
   - Text SHA-256: `73f138af3f4871548dcad600f862cf2bc6a84bc77548bbb95c4d0d549afa16c8`
   - Exact locators retained: equation (1), PDF p. 2; condition (2) and
     equation (3), PDF p. 3; Section 3, "An obvious flaw", PDF p. 3.

The version distinction is material.  Version 1 makes the decimal claim.
Version 2 deletes it and states that the same modular step is incorrect.  The
unversioned DOI currently resolves to v2 and must not be used as evidence for
the removed title or claim.

## BBP primary paper actually cited by Zudilin

3. David H. Bailey, Peter B. Borwein, and Simon Plouffe, *On the rapid
   computation of various polylogarithmic constants*, Mathematics of
   Computation 66 (1997), no. 218, 903-913.
   - DOI: <https://doi.org/10.1090/S0025-5718-97-00856-9>
   - Author-hosted PDF used here: <https://www.davidhbailey.com/dhbpapers/digits.pdf>
   - Delivered PDF: `bailey-borwein-plouffe-1997.pdf`
   - PDF SHA-256: `ee6c1f95f17ba7a7b9dcb09005c4f1d2d6a73d142694ac9af695811fa52ac9a2`
   - Text SHA-256: `1c87932b775606577b41256963a32e76643e7a2b61b0157f0689bfb02e05a0d5`
   - Exact locators retained: Theorem 1 and equations (1.2)-(1.3), PDF p. 3
     (printed p. 2); Section 6, PDF p. 12 (printed p. 11); Questions 1-2 in
     Section 7, PDF p. 12 (printed p. 11).

Zudilin v1 and v2 cite this paper as reference [1].  They do not cite either
Bailey-Crandall paper or Lagarias.  Those sources are retained below because
the agenda specifically requests an applicability audit of that machinery,
not because they are dependencies of Zudilin's manuscript.

## Bailey-Crandall and Lagarias machinery audited separately

4. David H. Bailey and Richard E. Crandall, *On the Random Character of
   Fundamental Constant Expansions*, Experimental Mathematics 10 (2001),
   no. 2, 175-190.
   - DOI: <https://doi.org/10.1080/10586458.2001.10504441>
   - Author PDF: <https://www.davidhbailey.com/dhbpapers/bcrandom.pdf>
   - Delivered PDF: `bailey-crandall-2001-bcrandom.pdf`
   - PDF SHA-256: `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8`
   - Text SHA-256: `d85c9de4771f9f5237409beeada7ebe0ba019c1124b49927c98545bb33b46406`
   - Exact locators retained: Hypothesis A and Theorem 1.1, PDF pp. 2-3;
     Theorem 3.1, PDF pp. 9-10; base-10 discussion, PDF pp. 16-17; Weyl-sum
     open question, PDF p. 23 (printed p. 22).

5. David H. Bailey and Richard E. Crandall, *Random Generators and Normal
   Numbers*, Experimental Mathematics 11 (2002), no. 4, 527-546.
   - DOI: <https://doi.org/10.1080/10586458.2002.10504704>
   - Author PDF: <https://www.davidhbailey.com/dhbpapers/bcnormal.pdf>
   - Delivered PDF: `bailey-crandall-2002-bcnormal.pdf`
   - PDF SHA-256: `d6cb4c65494b8447428a480ba9c29139fcedfac47dc3fff029ec4a50a0d8db74`
   - Text SHA-256: `bab7d90671a8c5384d4251b0516c4282554062cc4bd5cdcdc9d12dc02dafec47`
   - Exact locators retained: Theorem 3.1 and Theorem 3.2, printed pp. 6-7;
     Theorem 4.6, printed pp. 12-13; Theorem 4.8, printed p. 14.

6. Jeffrey C. Lagarias, *On the Normality of Arithmetical Constants*,
   Experimental Mathematics 10 (2001), no. 3, 355-368, revised arXiv version.
   - DOI: <https://doi.org/10.1080/10586458.2001.10504456>
   - arXiv record: <https://arxiv.org/abs/math/0101055>
   - Versioned PDF: <https://arxiv.org/pdf/math/0101055v2>
   - Delivered PDF: `lagarias-math0101055v2.pdf`
   - PDF SHA-256: `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9`
   - Text SHA-256: `d4dcb5c31735fa51bbe15f7bb5bdcaa7f2cb86582f09b08665c8ec91aa08a346`
   - Exact locators retained: Theorem 2.1, PDF p. 5; Theorem 3.1 and Lemma
     3.2, PDF pp. 7-8; Theorem 3.3, PDF pp. 8-9; Definition 4.1 and Theorem
     4.1, PDF pp. 9-11; no-known-relation statement, PDF p. 17.

## Local checked interfaces

The literature translation uses the machine-checked finite declarations in the
knowledge-library copies of T24, T26, T38, T55, T61, and T62.  Their source
hashes, already registered by the program, are:

- T24 `FiniteInverseDichotomy.lean`:
  `004e8c3e8bef64b172ee4f2dd945bcb2f50dc59f00c7a335b2187d7ffb97c9c4`.
- T26 `SharedResonanceChain.lean`:
  `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2`.
- T38 `FixedStratumFejerSpike.lean`:
  `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014`.
- T55 `SignedMultiplierTenPairing.lean`:
  `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd`.
- T61 `DirectLabelAdjacentPhaseVariance.lean`:
  `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb`.
- T62 `ClosedExpansionPredecessorRegrouping.lean`:
  `cef676197799dc7c3b8d93778ebf94c5a7c4bf1e88e8de17900c75762e47034e`.

No prose claim from an unverified note is used as a discharged premise.  The
`S_N` rewrites in the report are derived directly from the displayed finite
sums; they are not attributed to a sketch-level note.

## Canonical statement pin

- Delivered byte-exact copy: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Original local source URL: `local:pi-lacunary-near-return-sparsity`, represented
  in the project by `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.

## Retrieval note

The AMS PDF endpoint for the 1997 BBP paper returned HTTP 403.  The delivered
copy is the author-hosted PDF linked from Bailey's publication list; the DOI
above pins the journal metadata.  The other retained PDFs downloaded without a
retrieval blocker.  `pdftotext` produced nonempty text for every retained PDF;
no OCR was needed.
