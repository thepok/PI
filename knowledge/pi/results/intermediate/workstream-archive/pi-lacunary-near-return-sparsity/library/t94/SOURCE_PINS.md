# T94 source and interface pins

Search/check date: 2026-08-09 UTC.

## Immutable program statement

- Vendored file: `canonical_statement.txt`
- SHA-256: `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`
- Original path: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`
- The statement has no external source URL; its provenance is preserved in the
  vendored file.

## Regular paperfolding context

- Jean-Paul Allouche and Mireille Bousquet-Melou, *Canonical positions for the
  factors in paperfolding sequences*, Theoretical Computer Science 129(2)
  (1994), 263--278.
- DOI: https://doi.org/10.1016/0304-3975(94)90028-0
- Author source: https://www.labri.fr/perso/bousquet/Articles/Mots/pliage.dvi
- Vendored file: `allouche-bousquet-melou-1994.dvi`
- SHA-256: `9ee4f3884e5029c5dc507736d7c4364c8757bb18996e0535ddf756247108cc72`
- Context locator: journal pp. 265--266, Section 2 and Theorem 1; author DVI
  pp. 3--4.  T94 does not use the paper's canonical-position theorem as a
  premise.  It takes the agenda's one-based rule
  `p[2^a(2j+1)] = j mod 2` as its definition and derives every recurrence from
  that definition.
- Retrieval limitation inherited from the supplied source pin: the publisher
  PDF endpoint returned HTTP 403; the author-hosted DVI was available.  This
  sandbox has no `dvitype`, so no new text extraction is claimed.

## Checked sibling interfaces

The comparisons in `REPORT.md` were made against these supplied
machine-checked library modules, not against the T91 prose note:

| Interface | Supplied file | SHA-256 | Locators |
|---|---|---|---|
| T64 | `knowledge_library/t64/AggregateFejerCriterion.lean` | `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16` | lines 1485--1511 and 1847--1924 |
| T83 | `knowledge_library/t83/T83LiteralStatisticAudit.lean` | `013170204762b54fd9e8791f6723f189473ccbf03d4a4ec7b63ad657e44ea424` | lines 34--63, 192--268, and 270--401 |

The T91 note is `sketch`-level context only.  T94 independently re-derives its
paperfolding formulas and uses the T91 value `C(7,48)=98` only as a replayed
regression target.  The finite recursion defining `P_7`, its 28 positions, and
their 28 distinct factors are recomputed locally rather than imported as a
discharged T91 premise.
