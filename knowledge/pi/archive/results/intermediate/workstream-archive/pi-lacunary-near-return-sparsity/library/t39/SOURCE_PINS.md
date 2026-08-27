# T39 source pins and locators

Access date: 2026-07-24 UTC.

All retained PDFs are included beside this file. The text extracts were made
with `pdftotext -layout INPUT.pdf OUTPUT.txt`. Running `sh reproduce.sh`
verifies every retained byte hash and sentinel lines spanning every locator
range used below; the complete retained extracts permit direct inspection of
all intervening lines.

## Canonical statement

- Retained file: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Original project file: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`
- Locator: line 2 is canonical A1; lines 7--23 record A1--A16.
- Source URL: none. The file's own provenance says it was formulated by this
  system on 2026-07-22.

## S1: tree-martingale-family boundary candidate: flows and derived trees

Russell Lyons and Yuval Peres, *Probability on Trees and Networks*, Cambridge
University Press, 2016, corrected online edition dated 2020.

- DOI: <https://doi.org/10.1017/9781316672815>
- Author page: <https://rdlyons.pages.iu.edu/prbtree/>
- Retrieved PDF URL: <https://rdlyons.pages.iu.edu/prbtree/book_corr.pdf>
- Retained PDF: `lyons-peres-2020-corrected.pdf`
- PDF SHA-256: `3ba07bc0fb0397dc256610b328c869983d7ab4f709c78952d86646e25a15d043`
- Retained extract: `lyons-peres-2020-corrected.txt`
- Extract SHA-256: `3f734a0413e5250be19bb227bcae28aec26350eb878101d03ba1496954aaad7a`
- Exact locators: corrected printed p. 526, extract lines 27403--27419 defines
  descendant trees, conditional flows, and `D(T)`; corrected printed p. 528,
  extract lines 27473--27492 states Theorem 15.20; its construction begins at
  extract lines 27493--27506.

The retained theorem assumes a uniformly bounded-degree rooted tree. In the
section's standing setup it is represented as a rooted subtree of a fixed
`r`-ary tree, with no leaves except possibly the root. Theorem 15.20 produces
`T* in D(T)` and a unit flow on `T*` with the displayed boundary-dimension and
flow-exponent properties. The relevant operation is explicitly recentering:
`T^v` identifies `v` with a new root and `theta^v(x)=theta(x)/theta(v)`.

This is the retained candidate for the requested tree-martingale family
because its source-pinned conditional-flow operation is the tree-filtration
conditioning mechanism relevant to moving roots. The theorem itself is a
derived-tree/unit-flow theorem, not a martingale convergence theorem; no claim
that generic martingale convergence creates or anchors a branch is made.

## S2: quasi-Bernoulli Gibbs measure

De-Jun Feng and Ka-Sing Lau, "The Pressure Function for Products of
Non-negative Matrices", *Mathematical Research Letters* 9 (2002), 363--378.

- DOI: <https://doi.org/10.4310/MRL.2002.v9.n3.a10>
- Publisher record: <https://link.intlpress.com/JDetail/1806606366691192834>
- Retrieved PDF URL:
  <https://www.intlpress.com/site/pub/files/_fulltext/journals/mrl/2002/0009/0003/MRL-2002-0009-0003-a010.pdf>
- Retained PDF: `feng-lau-2002.pdf`
- PDF SHA-256: `1ead52b41ef41987ae07067b06fb83d0f5196c40a4e88d7c3c9524ab8c3e7bec`
- Retained extract: `feng-lau-2002.txt`
- Extract SHA-256: `5fe33cd079e2e54b488a7d37e193975d1f769ad5a72d850670461e87b782563e`
- Exact locators: printed p. 363, extract lines 25--43 fixes the primitive
  subshift and cylinder notation; Theorem 1.1 is printed p. 364, extract lines
  80--97; the two-sided quasi-Bernoulli estimate (1.4) is printed p. 365,
  extract lines 103--109; Corollary 2.6 and proof are printed p. 370, extract
  lines 369--380.

The hypotheses are one primitive finite-type shift, a Holder-continuous
strictly positive matrix-valued function, and fixed `q in R`. Theorem 1.1
produces one invariant ergodic Gibbs probability measure. Equation (1.4)
states one word-independent constant comparison

`C^-1 mu([I]) mu([J]) <= mu([IJ]) <= C mu([I]) mu([J])`

for every admissible concatenation. Corollary 2.6's displayed first inequality
at extract line 371 appears reversed relative to (1.4), its proof, and the
standard meaning stated immediately afterward. This audit retains (1.4) as the
unambiguous exact display and records rather than silently repairs the later
typesetting issue.

## S3: tangent distributions

Antti Kaenmaki, Tuomas Sahlsten, and Pablo Shmerkin, "Dynamics of the scenery
flow and geometry of measures", *Proceedings of the London Mathematical
Society* (3) 110 (2015), 1248--1280.

- DOI: <https://doi.org/10.1112/plms/pdv003>
- arXiv record: <https://arxiv.org/abs/1401.0231v3>
- Retrieved PDF URL: <https://arxiv.org/pdf/1401.0231v3>
- Retained PDF: `kaenmaki-sahlsten-shmerkin-2015.pdf`
- PDF SHA-256: `6e17b161355633d4293ad2428550cbc7b919f8ee3fbfa4adb36970d5daa5783f`
- Retained extract: `kaenmaki-sahlsten-shmerkin-2015.txt`
- Extract SHA-256: `b37f8b34299c37e0acb4d7010522becf8e83c64520f9e1f07a27523d3a97f64d`
- Exact locators: arXiv PDF pp. 14--16, extract lines 689--736 gives
  Definitions 3.1, 3.2, and 3.4; Definition 3.7 is extract lines 748--767;
  Theorem 3.10 is arXiv PDF p. 16 (journal p. 1263), extract lines 795--802.

Theorem 3.10 says that for any Radon measure `mu`, at `mu`-almost every point,
all tangent distributions are fractal distributions. These are time-averaged
scenery limits, not individual tangent measures and not paths. The source
normalizes each scenery to a probability measure and proves scale invariance
and quasi-Palm behavior; it does not retain an absolute tree root.

## S4: symbolic languages and subshifts

Jorge Almeida and Alfredo Costa, "A geometric interpretation of the
Schutzenberger group of a minimal subshift", *Arkiv for Matematik* 54 (2016),
243--275.

- DOI: <https://doi.org/10.1007/s11512-016-0233-7>
- arXiv record: <https://arxiv.org/abs/1507.06885>
- Retrieved PDF URL: <https://arxiv.org/pdf/1507.06885>
- Retained PDF: `almeida-costa-2016.pdf`
- PDF SHA-256: `f774b8a9df74809038e95b4925867e99673f2fb055e4568e507a67bb0f2c1ce4`
- Retained extract: `almeida-costa-2016.txt`
- Extract SHA-256: `57b1e48172ea02ab285dfafd9427373e28036720311e86a82cf0f4054deafc24`
- Exact locator: open PDF pp. 7--8, journal pp. 249--250, extract lines
  359--380 defines the finite alphabet, subshift, block language, and states
  that `X -> L(X)` is an isomorphism between subshifts and factorial,
  prolongable languages. The paper attributes this correspondence to Lind and
  Marcus, Proposition 1.3.4.

The theorem concerns one fixed finite alphabet and one fixed factorial,
prolongable language. Its resulting point lies in a shift-coordinate space;
shifting an occurrence to coordinate zero does not retain an external absolute
start depth or any cylinder mass.

## Kernel-checked inputs

`DEPENDENCIES.sha256` records the exact four knowledge-library files inspected.
Their theorem locators are reproduced in `REPORT.md`. They are existing
machine-checked inputs and are not duplicated into this literature artifact.
