# T162 primary-source pins

Inspection date: 2026-08-12 UTC. Exactly three previously unaudited primary
papers were opened, one in each mandated lane. PDFs and their `pdftotext
-layout` derivatives are one source each. Every PDF is text-readable; no OCR
was used. Page locators are displayed PDF pages.

## S1: symbolic collision geometry

- Lubomira Dvorakova, Katerina Medkova, and Edita Pelantova,
  *Complementary symmetric Rote sequences: the critical exponent and the
  recurrence function*.
- Version: arXiv:2003.06916v3, 28 May 2020.
- URLs: <https://arxiv.org/abs/2003.06916v3> and
  <https://arxiv.org/pdf/2003.06916v3>.
- DOI: <https://doi.org/10.23638/DMTCS-22-1-20>.
- PDF: `dvorakova-medkova-pelantova-2003.06916v3.pdf`.
- PDF SHA-256: `db42c488a3bb5f661b78a0c1a21d1ceb3ca139933c01c7862f258f0bd12d6239`.
- Text SHA-256: `96b5822f84d56ee069f7ef75c359cd0945df51924f2a548a1cd4eb3d93e1d333`.
- Stable tuple: `arXiv:2003.06916v3|Definition1;Lemma3;Definition39;Observation40;Lemma41;Theorem54`.
- Exact locators: critical exponent, Definition 1, PDF p. 4; reduction to
  return words to bispecial factors, Lemma 3, PDF pp. 5--6; recurrence
  function, Definition 39, PDF p. 24; maximum-return identity, Observation
  40, PDF p. 24; bispecial reduction, Lemma 41, PDF p. 24; exact CS Rote
  recurrence formula, Theorem 54, PDF pp. 30--31.
- Scope: uniformly recurrent symbolic sequences, then CS Rote sequences. The
  recurrence theorem determines the **maximum** return-word length needed to
  see every factor. It does not lower-bound every return word or the minimum
  gap between equal factors.

## S2: named fixed-point dynamics

- Karel Klouda, Katerina Medkova, Edita Pelantova, and Stepan Starosta,
  *Fixed points of Sturmian morphisms and their derivated words*.
- Version: arXiv:1801.09203v3, 7 May 2018.
- URLs: <https://arxiv.org/abs/1801.09203v3> and
  <https://arxiv.org/pdf/1801.09203v3>.
- DOI: <https://doi.org/10.1016/j.tcs.2018.06.037>.
- PDF: `klouda-et-al-1801.09203v3.pdf`.
- PDF SHA-256: `25dec8d82fead16046c4951c1609a0ab7e25b4e1ae68115d64832559598e0211`.
- Text SHA-256: `e76c24bed42876329376b59533eea8b18cd8a8fa44b18498c0c561cf11910a8e`.
- Stable tuple: `arXiv:1801.09203v3|Section2.1;Theorem1;Definition22;Theorem25;Example27;Corollary35`.
- Exact locators: return and derivated words, Section 2.1, PDF pp. 2--3;
  derivated Sturmian theorem, Theorem 1, PDF p. 3; morphism transformation,
  Definition 22, PDF p. 9; exact derivated-fixed-point classification,
  Theorem 25, PDF pp. 9--10; Fibonacci self-derivation, Example 27, PDF p. 10;
  cardinality bound, Corollary 35, PDF p. 13.
- Scope: fixed points of primitive Sturmian morphisms. The result preserves
  the order of return-word types through the derivated word, but gives no
  occurrence-frequency or minimum-return-gap estimate at growing depth.

## S3: short structured exponential sums

- Sary Drappeau and Clemens Mullner, *Exponential sums with automatic
  sequences*.
- Version: arXiv:1710.01091v1, 3 October 2017.
- URLs: <https://arxiv.org/abs/1710.01091v1> and
  <https://arxiv.org/pdf/1710.01091v1>.
- PDF: `drappeau-mullner-1710.01091v1.pdf`.
- PDF SHA-256: `241363dacb03315ef512900d82eadd401583a9b1a76ff77c6a31dd452d411074`.
- Text SHA-256: `d64ad8af80f222f9220df2d9235d35e8e318cdc7318cec689c31bb20c8977d1e`.
- Stable tuple: `arXiv:1710.01091v1|Definition1;Theorem1(1.2)-(1.3);Definition2;Proposition1(4.1)`.
- Exact locators: rational phase and automatic-sequence definitions,
  Definition 1 and preceding text, PDF pp. 1--2; short-interval exponential
  estimates, Theorem 1 equations (1.2)--(1.3), PDF p. 2; carry property,
  Definition 2, PDF p. 7; reduction to two-point phase correlations,
  Proposition 1 and equation (4.1), PDF pp. 7--8.
- Scope: an automatic coefficient sequence against rational periodic phases
  over integer intervals. The theorem is nontrivial in the
  Polya--Vinogradov range and explicitly becomes trivial for linear or
  constant phase. It gives no block-indicator Fourier bound for a prescribed
  decimal orbit and no reconstruction from a short empirical Markov type.

## Search and cap record

The three retained source identities were absent from the supplied accepted
source pins. Searches were bounded to the three mandated lanes. Sources already
audited in T89--T158, especially Durand 0807.4430, the T153 k-Abelian papers,
and T158's Markov sources, were screened but not reopened or counted.

```text
PRIMARY_SOURCE_COUNT: 3
PRIMARY_SOURCE_CAP: 8
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
```
