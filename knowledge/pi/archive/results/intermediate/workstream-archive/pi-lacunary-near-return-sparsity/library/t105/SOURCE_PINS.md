# T105 source pins

Search date: 2026-08-10 UTC.

`PRIMARY_SOURCE_COUNT: 5`

The search was deliberately capped below the agenda maximum of eight primary
sources. The five retained sources cover energy/BSG, arithmetic or fractal
Fourier decay, and structured exponential sums. PDFs were fetched from the
versioned arXiv records and converted with `pdftotext -layout`. The text files
are retrieval aids; theorem statements were checked against the corresponding
PDFs. No retrieval failed.

## S1: energy decomposition

- Misha Rudnev, Ilya D. Shkredov, and Sophie Stevens, *On the Energy Variant
  of the Sum-Product Conjecture*, `Rev. Mat. Iberoam.` 36 (2020), 207-232.
- Stable records: <https://arxiv.org/abs/1607.05053v5> and
  <https://doi.org/10.4171/RMI/1126>.
- Retrieved PDF: <https://arxiv.org/pdf/1607.05053v5>.
- `rss-energy-1607.05053v5.pdf` SHA-256:
  `007586b8b40da3ac99f22035968e6bb2b6546fed99af686ddf64e2293a6bec03`.
- `rss-energy-1607.05053v5.txt` SHA-256:
  `3df6d0a7e337a29ffb49b6dbdd966d046f48d4bb0a637e5090c4ce45c1c63590`.
- Exact locator: Theorem 5, printed p. 6; layout extract lines 253-266.
  The theorem gives a subset of at least half the original size and an
  additive-or-multiplicative energy alternative. In positive characteristic
  the displayed arbitrary-field exponent has the condition `|A| <= p^(5/8)`.
- Standing conventions: printed p. 3, layout extract lines 105-119, especially
  lines 108-109, state that `0 notin A`, `|A|>1`, and finiteness are implicit in
  every subsequent statement. They therefore apply to Theorem 5.

## S2: quantitative Balog-Szemeredi-Gowers

- Thomas F. Bloom, *Control and its applications in additive combinatorics*,
  2025 preprint.
- Stable record: <https://arxiv.org/abs/2501.09470v1>;
  arXiv DOI <https://doi.org/10.48550/arXiv.2501.09470>.
- Retrieved PDF: <https://arxiv.org/pdf/2501.09470v1>.
- `bloom-control-2501.09470v1.pdf` SHA-256:
  `c7aec98a1dc993a5a52048bf2b5939f3ce474b7019adb9c00d77768db45eaafe`.
- `bloom-control-2501.09470v1.txt` SHA-256:
  `412abbdf098d6ed4c8a3818bdc309724f36297345afd669e22dd31bef840c3fb`.
- Exact locator: Theorem 8, printed p. 6; layout extract lines 284-316.
  This is an arXiv preprint, not represented here as a refereed theorem.

## S3: Fourier-decaying lacunary dynamics

- Bo Tan and Qing-Long Zhou, *Quantitative Matrix-Driven Diophantine
  approximation on M_0-sets*, 2025 preprint.
- Stable record: <https://arxiv.org/abs/2504.21555v1>;
  arXiv DOI <https://doi.org/10.48550/arXiv.2504.21555>.
- Retrieved PDF: <https://arxiv.org/pdf/2504.21555v1>.
- `tan-zhou-2504.21555v1.pdf` SHA-256:
  `f9544bf4a8fa1f40240231fcaedfb0b04df70b965fa70fd033194b55bf319b19`.
- `tan-zhou-2504.21555v1.txt` SHA-256:
  `2cb7ebbfb88ca915ea423acc884193ccb9e4c8b064bb76145a950b72eaf1fce2`.
- Exact locator: Theorem 1.7, printed p. 4, layout extract lines 177-186, and
  its proof, printed pp. 7-8, layout extract lines 367-432. The proof invokes
  `|mu_hat(t)|=O((log |t|)^(-alpha))` and closes the summability argument for
  every `alpha>0` at lines 400-432. Theorem 1.7 assumes expanding integral
  matrices and
  `sigma_min(A_(n+1) A_n^(-1)) >= K>1`, and concludes equidistribution for
  `mu`-almost every point.
- Range distinction: the stronger `s>d+1` condition appears in Theorems 1.8
  and 1.10 and at the start of the proof of Theorem 1.8 (layout lines 434-446).
  Those shrinking-target theorems are not the theorem used in T105.

## S4: incomplete geometric-progression sums

- Bryce Kerr, *Incomplete exponential sums over exponential functions*,
  `Quarterly Journal of Mathematics` 66 (2015), 213-224.
- Stable records: <https://arxiv.org/abs/1302.4170v1> and
  <https://doi.org/10.1093/qmath/hau015>.
- Retrieved PDF: <https://arxiv.org/pdf/1302.4170v1>.
- `kerr-1302.4170v1.pdf` SHA-256:
  `9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd`.
- `kerr-1302.4170v1.txt` SHA-256:
  `2a13bcbb1416ceaf783095661282cf08f9834a71b7a71a97f750d7c314d6ea6b`.
- Exact locator: Theorems 1-3, printed pp. 2-3; layout extract lines 69-101.
  Theorem 2 is the retained incomplete-orbit bound and requires prime `p`,
  `g` of order `t`, and `N<=t`. Its displayed first branch
  `p^(1/8)N^(71/96+o(1))` additionally requires `N<=t^(1/2)`; layout extract
  lines 78-87.
- Date exception: this 2015 paper is outside the preferred 2020-2026 window,
  but it was retained because it is the closest direct theorem for incomplete
  fixed-residue sums `sum_(j<N) e_p(lambda g^j)` found in the bounded search.

## S5: complete small-subgroup sums

- Daniel Di Benedetto, Moubariz Z. Garaev, Victor C. Garcia, Diego
  Gonzalez-Sanchez, Igor E. Shparlinski, and Carlos A. Trujillo,
  *New estimates for exponential sums over multiplicative subgroups and
  intervals in prime fields*, `Journal of Number Theory` 215 (2020), 261-274.
- Stable records: <https://arxiv.org/abs/2003.06165v1> and
  <https://doi.org/10.1016/j.jnt.2020.02.004>.
- Retrieved PDF: <https://arxiv.org/pdf/2003.06165v1>.
- `dibenedetto-et-al-2003.06165v1.pdf` SHA-256:
  `4434b3992292e881139055eb0390ed7a7ff9ce9b243c156ac631c1442c2930d1`.
- `dibenedetto-et-al-2003.06165v1.txt` SHA-256:
  `3529db3774a5b33b0489844e91b507246037aee700ca0e8f7474407e6af75845`.
- Exact locator: Theorem 3.1, printed p. 3; layout extract lines 100-117.
  It assumes a complete multiplicative subgroup of order
  `p^(1/4)<H<p^(1/2)` and gives the displayed bound
  `H^(2689/2880) p^(1/72)` uniformly in the nonzero additive character.

## Search boundary

The complete primary-source search corpus is exactly S1-S5 above: five primary
PDFs were opened and inspected, and all five were retained as pins. No other
primary paper was screened at abstract, theorem, or full-text level. Discovery
queries used arXiv/DOI metadata and the phrases `energy sum-product`,
`Balog-Szemeredi-Gowers`, `polylogarithmic Fourier decay lacunary`, `incomplete
exponential sums powers`, and `multiplicative subgroup exponential sums`, but
unopened search-result titles are not treated as inspected primary sources and
support no claim in this report. T103 and T104 were consulted only as local
prior-fingerprint reports under the separately enumerated pins below. This
exhaustive ledger makes `PRIMARY_SOURCE_COUNT: 5` the searched-source count as
well as the retained-source count. No claim of an exhaustive global literature
review or novelty is made.

## Supplied prior-fingerprint pins

These local files were consulted for the comparison table in `REPORT.md`.
They are not primary sources and do not count toward `PRIMARY_SOURCE_COUNT`.
Paths are relative to the T105 record directory. Note reports remain
unverified sketches unless their row explicitly names a Lean module; the hashes
make the exact consulted versions identifiable in the supplied knowledge
library.

| item | consulted file | SHA-256 |
|---|---|---|
| T10 | `knowledge_library/t10/LongLagResonance.lean` | `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947` |
| T45 | `knowledge_library/t45/REPORT.md` | `1814ec6cf1079b44acbc4bb20b4be9106c9b098e7e49c65617ef4fbc1830434d` |
| T73 | `knowledge_library/t73/ManyChildResonance.lean` | `34ec4af51b95e7e1e1a0a350357fedf4fb7c0427daaf8a53331c3767992727de` |
| T81 | `knowledge_library/notes/t81/REPORT.md` | `73b4198003d637e5b7277dbdfe05e4f2606613f8e906860243331a293dd3b77f` |
| T87 | `knowledge_library/notes/t87/REPORT.md` | `a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078` |
| T90 | `knowledge_library/t90/REPORT.md` | `730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0` |
| T91 | `knowledge_library/notes/t91/REPORT.md` | `a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e` |
| T92 | `knowledge_library/t92/T92ConstantRunDiscriminator.lean` | `d912120e6ebc122d82f889f1731be56eb756b312b66244ff22ee451317e7cd12` |
| T93 | `knowledge_library/notes/t93/REPORT.md` | `2ff685b20920f5a2d71db2b8a300ce8c2762152c3d4b2c59236b160ed812f8ae` |
| T94 | `knowledge_library/notes/t94/REPORT.md` | `f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10` |
| T95 | `knowledge_library/notes/t95/REPORT.md` | `08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb` |
| T96 | `knowledge_library/notes/t96/REPORT.md` | `de8940fd7927a20d88626cec7ae8b411cd2788c1fdecb762496a72c8f18019aa` |
| T97 | `knowledge_library/notes/t97/REPORT.md` | `fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e` |
| T98 | `knowledge_library/notes/t98/REPORT.md` | `b6b8d30499543fadf5be200b85afe3929dcba5b7a7d96061476965060c589f57` |
| T99 | `knowledge_library/notes/t99/REPORT.md` | `9778fd0fdc3151b0e3f8888afdb1d1049347e926d266f2981e7daa3bc44af2b4` |
| T100 | `knowledge_library/t100/T100UniversalCharging.lean` | `8fa767cf17deb3ff7b17f94d2d57679122c7cc46e1d9d7a2286846e12ae51787` |
| T101 | `knowledge_library/notes/t101/REPORT.md` | `ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e` |
| T102 | `knowledge_library/notes/t102/REPORT.md` | `49a63d0003102728766a41e026400f3bc69e9baeb42e66338510bcbecc1d6304` |
| T103 | `knowledge_library/t103/REPORT.md` | `ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0` |
| T104 | `knowledge_library/t104/REPORT.md` | `2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5` |
| terminal memory | `knowledge_library/t89/SEMANTIC_OBSTRUCTION_MEMORY.md` | `aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f` |

The staged T103 and T104 report hashes were verified directly. T103 Sections
4, 6, and 10 give the report's periodic-hole density, collision translation,
and cheap discriminator; those deductions remain a `proof sketch`. T104
Section 6.4, report lines 443-527, gives F4's ambient Fourier-decay card and
pins its primary source as Baker--Banaji, Theorem 1.2, Proposition 2.5, and
Theorem 2.7, PDF SHA-256
`f07b9e579360cff6843fccb526086d27ea454925d6ed46d297fff274ca5689e6`.
These local comparisons do not add primary sources to T105's bounded search
and are not used as discharged mathematical premises.
