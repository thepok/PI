# T161 primary-source pins

Audit date: 2026-08-12 UTC. The bounded inspection stopped after two primary
sources. A source and its byte-derived text count once.

```text
PRIMARY_SOURCE_COUNT: 2
PRIMARY_SOURCE_CAP: 4
```

## S1. Marked Poisson process approximation

- Louis H. Y. Chen and Aihua Xia, *Stein's method, Palm theory and Poisson
  process approximation*, Annals of Probability 32 (2004), 2545--2569.
- Primary page: <https://arxiv.org/abs/math/0410169>
- PDF: <https://arxiv.org/pdf/math/0410169>
- DOI: <https://doi.org/10.1214/009117904000000027>
- Delivered PDF: `chen-xia-math0410169.pdf`
- PDF SHA-256:
  `3640caf66dd78cc1fa3e4ad69cd5b250123c9896e86c17962912cc3fbc82f87e`
- Delivered `pdftotext -layout` extraction: `chen-xia-math0410169.txt`
- Extraction SHA-256:
  `8a89a301fda4c86bf2383025840e07d7c0a44466f3466a8d0f37e73c1290381a`
- Inspected range and exact locators:
  - `rho_1,rho_2`, printed p. 2552, PDF p. 8, extraction lines 361--400;
  - marked-trial setup, independent marks, mean measure, `A_i`, and `V_i`,
    printed p. 2555, PDF p. 11, lines 558--583;
  - Theorem 4.1 and equation (4.1), printed pp. 2555--2556, PDF pp. 11--12,
    lines 584--615;
  - Remarks 4.2--4.3, printed p. 2556, PDF p. 12, lines 616--625;
  - lifting proof, printed pp. 2556--2557, PDF pp. 12--13, lines 627--650.
- Exact content used: Theorem 4.1 treats `M=sum_i I_i delta_(U_i)` where the
  marks `U_i` are independent random elements and gives the displayed local
  dependence `d_2` bound. T161 indexes every exact maximal-chain candidate
  separately, uses its deterministic type as the mark, and takes the whole
  candidate set as every neighborhood. At `proof sketch` level, this discharges
  mark independence and gives `(PP-161)`. The first failure in that substitution
  is that its explicit right side exceeds the metric ceiling one, not a failed
  theorem hypothesis.

## S2. Regular-paperfolding separator context

- Jean-Paul Allouche and Mireille Bousquet-Melou, *Canonical positions for the
  factors in paperfolding sequences*, Theoretical Computer Science 129(2)
  (1994), 263--278.
- DOI: <https://doi.org/10.1016/0304-3975(94)90028-0>
- Author source: <https://www.labri.fr/perso/bousquet/Articles/Mots/pliage.dvi>
- Delivered DVI: `allouche-bousquet-melou-1994.dvi`
- DVI SHA-256:
  `9ee4f3884e5029c5dc507736d7c4364c8757bb18996e0535ddf756247108cc72`
- Locator reported by the supplied prior source pin, not independently
  re-inspected here: journal pp. 265--266, Section 2 and Theorem 1; author DVI
  pp. 3--4, for the paperfolding definition/context and canonical positions.
- Retrieval limitation: the publisher endpoint returns HTTP 403 and this
  sandbox has no DVI text extractor. T161 therefore does not quote or use the
  source theorem. The replay defines the one-based regular-paperfolding word
  directly by `p_(2^a(2j+1))=j mod 2` and computes its finite separator from
  that definition. The source is counted because it identifies the named
  standard word, not because it discharges a mathematical step. This S2 entry
  is `bibliographic context`, not a `literature-checked` theorem claim.

No secondary source and no OCR output is used. No separate compound-Poisson
theorem is cited: the S1 Poisson process on deterministic exact-cluster types
maps to the candidate compound-Poisson weighted count. The complete conservative
substitution is a `proof sketch` deduction and gives only the metric ceiling;
no sharper theorem is claimed.
