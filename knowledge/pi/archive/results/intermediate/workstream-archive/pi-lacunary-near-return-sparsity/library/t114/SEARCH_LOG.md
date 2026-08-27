# T114 bounded search log

Search date: 2026-08-10 UTC.

The scout stopped at eight primary sources. Search-result pages, prior T-item
reports, and bibliographies used for navigation are not counted as inspected
primary sources.

| Lane | Queries / navigation terms | Sources inspected | Candidate decision |
|---|---|---|---|
| Mahler and functional equations | `Mahler values linear independence determinant`, `Mahler algebraic independence zero estimate`, `q-difference determinant linear independence` | S1 Väänänen-Wu, S2 Amou-Matala-aho-Väänänen, S3 Zorin, S4 Zudilin | retain S1 and S2; screen S3 for literal rank deficiency and S4 as scalar only |
| Restricted structured approximation | `linear forms two logarithms interpolation determinant`, `integral powers small intervals modulo one countable` | S7 Laurent, S6 Schleischitz | retain S7; screen S6 as eventually-always avoidance without occupancy |
| Fixed-point lacunary dynamics | `algebraic lambda digit changes Vandermonde non-Liouville` | S5 Varjú-Yu | retain S5 as a fixed-lag rank model, then reject its degree-one/consecutive-block specialization |
| Short structured exponential sums | `consecutive powers primitive root short exponential sum` | S8 Konyagin-Shparlinski | screen: moment/small-product-set mechanism, no determinant, polynomial-length threshold |

## Candidate cap

Exactly four candidates were retained for full cards:

```text
C1 Laurent high-dimensional interpolation determinant
C2 Väänänen-Wu fixed three-column Mahler determinant
C3 Amou-Matala-aho-Väänänen scalable q-difference determinant
C4 Varjú-Yu fixed-lag Vandermonde/recurrence rank
```

S3, S4, S6, and S8 remain inspected exclusions, not fifth through eighth
candidates. Every retained card is tested against the same literal `D_N`
occupancy threshold and the regime `N>=A*n`.

## Retrieval notes

- All eight downloads succeeded.
- The correct IMPAN product for S2 is `83675`; an earlier navigation result
  with another product number was not inspected or counted.
- All PDFs produced nonempty text with `pdftotext -layout`; no image-only scan
  or OCR uncertainty occurred.
- The clean-context search initially predated final T112/T113 availability.
  This bounded revision inspected the accepted T112 report and staged T113
  note solely for the mandatory fingerprint comparison. They are prior-work
  comparators, not additional primary sources or new T114 candidates.
