# T91 source pins and search log

Search date: 2026-08-09 UTC.  The three systems in `REPORT.md` are sibling
models only.  The canonical statement is vendored byte-for-byte as
`canonical_statement.txt`, SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It has no external source URL; its provenance is preserved in that file.

## Primary literature

### S1: generalized Thue--Morse factor frequencies

- Lubomira Balkova, *Factor frequencies in generalized Thue--Morse words*,
  Kybernetika 48(3) (2012), 371--385.
- Landing page: https://www.kybernetika.cz/content/2012/3/371
- Direct PDF: https://www.kybernetika.cz/content/2012/3/371/paper.pdf
- Vendored file: `balkova-2012.pdf`
- SHA-256: `61a6e5d4a9ad03ff13b7624e8a21f51b00f62074cfd148be3618d2e6e25d40ec`
- Locators: printed pp. 373--374, Proposition 2.2 and Theorem 2.4 (unique
  ancestor/frequency scaling and the general frequency recursion); printed
  p. 376, the displayed morphism defining `t_(b,m)` and properties (a)--(d),
  including synchronization delay `2b`; printed pp. 378--380, the binary
  Thue--Morse specialization.  Only the definition and synchronization context
  are used in T91.  T91 derives its aligned collision identity independently.
- Convention caution: the paper's synchronization-point convention can use an
  endpoint.  T91 does not reinterpret delay four as an interior-cut theorem.

### S2: period-doubling substitution

- Miroslava Polakova, *Complexity and invariant measure of the period-doubling
  subshift*, arXiv:1902.08387v1 (2019); published as *Formulas for complexity,
  invariant measure and RQA characteristics of the period-doubling subshift*,
  Communications in Nonlinear Science and Numerical Simulation 79 (2019),
  104996.
- arXiv record: https://arxiv.org/abs/1902.08387v1
- DOI: https://doi.org/10.1016/j.cnsns.2019.104996
- Direct PDF: https://arxiv.org/pdf/1902.08387v1
- Vendored file: `polakova-1902.08387v1.pdf`
- SHA-256: `219fe5533e352ee92d1774ded36fe4a28fb3ee4f8df891fc61de55ab6a344da1`
- Locators: PDF p. 1 gives `0100 0101 ...`, the fixed point, strict
  ergodicity, and the substitution; PDF pp. 4--5, equations (2.1)--(2.2), give
  `zeta(0)=01`, `zeta(1)=00`, monoid extension, iterates, and supertile
  recursion; Theorem 1.2 gives the invariant cylinder measures.  T91 derives
  the finite letter counts and collision formula from (2.1), rather than
  attributing them to the paper.
- Convention caution: T91 uses zero-based finite words but the source's
  displayed infinite sequence is one-based.  This does not affect substitution
  iterates.  T91 does not use the source's valuation sentence.

### S3: regular paperfolding canonical positions

- Jean-Paul Allouche and Mireille Bousquet-Melou, *Canonical positions for the
  factors in paperfolding sequences*, Theoretical Computer Science 129(2)
  (1994), 263--278.
- DOI: https://doi.org/10.1016/0304-3975(94)90028-0
- Author-hosted source: https://www.labri.fr/perso/bousquet/Articles/Mots/pliage.dvi
- Vendored file: `allouche-bousquet-melou-1994.dvi`
- SHA-256: `9ee4f3884e5029c5dc507736d7c4364c8757bb18996e0535ddf756247108cc72`
- Locators: journal p. 264 (synchronization motivation); p. 265, Section 2 and
  its lemma (recursive/valuation definition); p. 266, Theorem 1 (canonical
  position recursion); p. 268, Theorem 2 (`P_k`, cardinality `4k`, and one
  canonical representative for every length-`k` factor for `k >= 7`).  In the
  author DVI these are pages 2, 3, 4, and 6 respectively.
- Retrieval note: the publisher PDF endpoint returned HTTP 403.  The
  author-hosted primary-source DVI downloaded successfully.  The sandbox lacked
  `dvipdfmx`, so no derivative PDF is presented as a source.  This is a tooling
  limitation, not a missing source pin.

## Accepted local library pins

These files are byte-exact copies from the supplied accepted knowledge library.
The six Lean modules are the checked interfaces.  The obstruction memory is an
unverified note and is used only as a comparison checklist, never as a premise.

| comparator | vendored file | SHA-256 | exact locators used |
|---|---|---|---|
| T14 | `local-T14-CoherentSuccessorSplitting.lean` | `bbc5c0323aaa0213e1d86dd4ec711e5f1a9d5421c7d946c88c56ee0f017bf833` | lines 28--42 (fixed parameters and triangle), 411--501 and 544--590 (equivalence with coherent energy/C2) |
| T37 | `local-T37-ArtificialStreamObstruction.lean` | `aa0979b629131c6e30c2d8a8dc8c70499ff03d98cd35b2f49841f7669585116c` | lines 201--265 (handcrafted stages), 1200--1245 (moving-window leakage), 1688--1763 (failure of stable original-coordinate branch) |
| T49 | `local-T49-ArtificialStreamCoherentSplitting.lean` | `61082f21330c21c22874e31b77af00f365c2995cdcd3909e5399ce89ed28cd93` | lines 70--83 (stream analogue of T14), 791--888 (all shallow levels split and coherent certificate), 921--979 (no original-coordinate branch) |
| T64 | `local-T64-AggregateFejerCriterion.lean` | `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16` | lines 1482--1511 (literal row), 1541--1598 (boundary errors), 1843--1924 (boundary plus Fourier implication) |
| T67 | `local-T67-TerminalRayStrength.lean` | `e9fc18166d2b31c52adbfe73bfcbb10ccd8d93c785fb39144b88db75ed493dff` | lines 286--472 (exact Walsh/cylinder collision identity), 474--646 (abstract-array separators are not orbit witnesses) |
| T83 | `local-T83-LiteralStatisticAudit.lean` | `013170204762b54fd9e8791f6723f189473ccbf03d4a4ec7b63ad657e44ea424` | lines 34--63 (literal near-return statistic), 192--268 (exact versus near-return conditional routes), 270--401 (constant-stream short collisions) |
| obstruction memory | `local-SEMANTIC_OBSTRUCTION_MEMORY.md` | `aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f` | lines 35--52; status declarations in lines 5--7 are retained |

## Search exclusions

This was a bounded opportunity search, not a claim of an exhaustive literature
review.  Three independent clean-context searches were run, one for
Thue--Morse, one for period-doubling, and one for a carry/automatic alternative.
The following log makes the inspected records reproducible.

| date | database or site | query/record inspected | outcome |
|---|---|---|---|
| 2026-08-09 | supplied accepted knowledge library, local full-text search | `automatic|morphic|substitution|Thue-Morse|Rudin-Shapiro|paperfold|carry transducer|Walsh|martingale`, followed by `collision|successor|synchronization` | Located the T14/T37/T49/T64/T67/T83 comparators and the obstruction memory; no prior structured-system T91 survey was present. |
| 2026-08-09 | Kybernetika journal record | https://www.kybernetika.cz/content/2012/3/371 | Retained S1; record and PDF inspected. |
| 2026-08-09 | arXiv record | https://arxiv.org/abs/1902.08387v1 | Retained S2; record and PDF inspected. |
| 2026-08-09 | Crossref/DOI landing record | https://doi.org/10.1016/0304-3975(94)90028-0 | Confirmed S3 bibliographic metadata. |
| 2026-08-09 | author publication archive | https://www.labri.fr/perso/bousquet/Articles/Mots/pliage.dvi | Retained S3; DVI and theorem locators inspected. |
| 2026-08-09 | Crossref REST API | https://api.crossref.org/works?query.title=automatic%20sequence%20exact%20factor%20frequency&rows=5 | Top five results were irrelevant exact-sequence records; no candidate retained. |
| 2026-08-09 | Crossref REST API | https://api.crossref.org/works?query.title=substitution%20synchronization%20block%20collision&rows=5 | Top five results concerned engineering/quantum synchronization rather than symbolic collisions; no candidate retained. |
| 2026-08-09 | Crossref REST API | https://api.crossref.org/works?query.title=paperfolding%20canonical%20positions%20factors&rows=5 | Retrieval returned HTTP 429; the failure is recorded rather than treated as a negative result. |
| 2026-08-09 | three independent runtime clean-context searches; no persistent result-set URL | `automatic sequence exact factor frequency`; `substitution synchronization block collision`; `carry transducer factor collision`; candidate-name searches | Screened Thue--Morse, period-doubling, regular paperfolding, Rudin--Shapiro, Champernowne/de Bruijn constructions, and generic automatic complexity results. Reproducible retained records are the site-specific rows above; the broader result sets were not persisted. |

The retained set was capped at three before drafting.  The exclusion rules were
applied as follows.

- Rudin--Shapiro was excluded: its standard exact polynomial/Walsh cancellation
  identity is not itself a literal block-collision or successor statement and
  would duplicate the T67 warning.
- Champernowne/de Bruijn stage constructions were excluded as artificial
  streams, duplicating rather than improving T37/T49.
- Generic automatic-sequence linear complexity and entropy results were
  excluded because they do not supply an exact collision calculation.
- General substitution recognizability was not retained as a fourth system;
  the system-specific source pins above are enough for the three calculations.
