# T114 primary-source pins

Access date for every source: 2026-08-10 UTC. All PDFs are text-based; they
were inspected with `pdftotext -layout`. No OCR was used. Printed-page,
theorem, lemma, and equation locators below refer directly to the delivered
primary PDFs.

`PRIMARY_SOURCE_COUNT: 8` and `PRIMARY_SOURCE_CAP: 12`.

| ID | Lane and source | URL / DOI | Delivered PDF SHA-256 | Exact locator used |
|---|---|---|---|---|
| S1 | Mahler: K. Väänänen and W. Wu, *On linear independence measures of the values of Mahler functions* | https://arxiv.org/abs/1604.01630 | `cf4f08bdef63be4c274c18c09ccf284a998c8e274156e787af837b1b7330e6e7` | preprint pp. 4-8, equations (8)-(25), Lemma 1, Theorem 6 |
| S2 | q-difference: M. Amou, T. Matala-aho, K. Väänänen, *On Siegel-Shidlovskii's theory for q-difference equations* | https://doi.org/10.4064/aa127-4-2 ; open PDF https://www.impan.pl/shop/publication/transaction/download/product/83675?download.pdf | `71b1f76747dcca9a10f334d25416766936c58d1a767690b62d5abf0a7130207a` | printed pp. 318-322, equations (5.1)-(6.8), Theorems 5.1 and 6.1 |
| S3 | Mahler zero estimates: E. Zorin, *Algebraic independence and normality of the values of Mahler's functions* | https://arxiv.org/abs/1309.0105 | `c16eb6ab11a2ab2b71376bc4b5c877a8124b7355a8d28a8b65f45af3eca5b71e` | preprint pp. 1-6 and 23, system (1), definition (3), Theorem 1/equation (8), Theorem 30/equation (43) |
| S4 | scalar determinant exclusion: W. Zudilin, *On the irrationality of generalized q-logarithm* | https://arxiv.org/abs/1601.02688 ; https://doi.org/10.1007/s40993-016-0042-x | `53947bb2fc82e853c12ccfdb293a526229f6fe2ac99d9c991d2170ae6e1266e3` | preprint pp. 3 and 5-8, Theorem 1, equations (6)-(8), Lemma 1 |
| S5 | fixed-point lacunary: P. P. Varjú and H. Yu, *Fourier decay of self-similar measures and self-similar sets of uniqueness* | https://arxiv.org/abs/2004.09358v2 ; https://doi.org/10.2140/apde.2022.15.843 | `4f8fe4bb024df9d7c0c804f93f261f3c4f21cc4d9410f9984804ad60594e7fad` | preprint pp. 4-5 and 8-11, Definition 1.9, Theorem 1.10, Lemmas 3.1-3.2, equations (4)-(7) |
| S6 | structured avoidance exclusion: J. Schleischitz, *Integral Powers of Numbers in Small Intervals Modulo 1: The Cardinality Gap Phenomenon* | https://arxiv.org/abs/1501.07176v6 ; https://doi.org/10.1515/udt-2017-0005 | `d19e88d3478415ee47f4cbdb42089cc255eea0d57f0368a4df933a484103e93a` | printed p. 9, Theorem 3.12 and equation (10) |
| S7 | interpolation determinant: M. Laurent, *Linear forms in two logarithms and interpolation determinants* | https://doi.org/10.4064/aa-66-2-181-199 ; open PDF https://www.impan.pl/shop/publication/transaction/download/product/108147?download.pdf | `9f480dc10057cc639d80a6a5a773a3e35c283170e9d201302921186ca5777dbf` | printed pp. 181-183 and 188-194, Theorem 3, Lemmas 4-8 |
| S8 | short structured sums exclusion: S. V. Konyagin and I. E. Shparlinski, *On the consecutive powers of a primitive root: gaps and exponential sums* | https://doi.org/10.1112/S0025579311002117 ; open PDF https://research-management.mq.edu.au/ws/portalfiles/portal/62037786/Publisher%20version%20(open%20access).pdf | `46f7981327913a4a7adbca724a7b3a214520ed6a946b46baba80ba8af55d97bc` | printed pp. 11-12 and 16-19, Theorem 1, equations (11)-(14), Lemmas 5-9 |

## Local input and prior pins

The canonical statement is delivered byte-for-byte as `canonical_statement.txt`
with SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.

The following prior reports were consulted from the supplied knowledge library
and were not counted as primary sources:

| Item | Verification treatment | Report SHA-256 |
|---|---|---|
| T81 | unverified note / `proof sketch`; never a premise | `73b4198003d637e5b7277dbdfe05e4f2606613f8e906860243331a293dd3b77f` |
| T87 | mixed source audit and unverified synthesis; never a premise | `a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078` |
| T104 | source claims literature-checked; transfers remain proof sketches | `2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5` |
| T105 | source claims literature-checked; transfers remain proof sketches | `ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f` |
| T110 | source claims literature-checked; transfers remain proof sketches | `4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668` |
| T112 | accepted literature artifact; source statements literature-checked, transfers proof sketches | `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa` |
| T113 | staged unverified exploration note; sources reported literature-checked, deductions proof sketches | `30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445` |
| terminal obstruction memory | unverified audit ledger, not a premise | `aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f` |

T112 and T113 were consulted only for normalized fingerprint comparison and
are not counted among T114's eight primary sources. No T113 deduction is
treated as established, and no T112 transfer conjecture is treated as proved.
