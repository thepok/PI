# T160 source pins and bounded search log

Audit date: 2026-08-12 UTC. Exactly six previously unaudited primary sources
were inspected, two in each of exactly three domains. The six PDF hashes and
retained theorem tuples are absent from the supplied prior source ledger and
readable corpus. Two identifiers, `1710.09313` and `2302.05149`, occur only as
bibliography references in prior text derivatives; no prior audited source
tuple or PDF hash for either was supplied. PDF bytes are authoritative. The verifier
runs `pdftotext -layout` in a temporary directory and checks the listed anchors.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
SEARCHED_DOMAIN_COUNT: 3
RETAINED_TUPLE_COUNT: 3
RETAINED_TUPLE_CAP: 3
```

## DOMAIN 1: symbolic maximal-repeat or collision theory

### SOURCE S1

Lukasz Debowski, "Maximal Repetition and Zero Entropy Rate," *IEEE
Transactions on Information Theory* 64(4) (2018), 2212-2219.

- DOI: https://doi.org/10.1109/TIT.2017.2733535
- Stable record: https://arxiv.org/abs/1609.04683v4
- Retrieval URL: https://arxiv.org/pdf/1609.04683v4
- Local PDF: `debowski-1609.04683v4.pdf`
- PDF SHA-256: `9fe5c1e472f5e78c0cc480fb7a8ae3f7a9b7fa540d8d304a8819ae69386c5af6`
- Inspected range: PDF pp. 1-9.
- Exact locators: maximal repetition equation (1), PDF p. 1; block collision
  entropy `H_2`, equations (9)-(10), PDF p. 3; Theorem 1, PDF pp. 4-5;
  Theorem 8 and equations (41)-(45), physical PDF p. 9 (printed p. 8).
- Disposition: screened. The theorem concerns one longest repeat under a
  stationary law and does not preserve the number of ordered equal-block pairs.

### SOURCE S2

Dmitry Kosolobov, "Closed Repeats," arXiv:2410.00209v1 (2024).

- Stable record: https://arxiv.org/abs/2410.00209v1
- Retrieval URL: https://arxiv.org/pdf/2410.00209v1
- Local PDF: `kosolobov-2410.00209v1.pdf`
- PDF SHA-256: `390cd15bc009eb61e429dccff36f76a8364555f9eeda472dfd30925402285499`
- Inspected range: PDF pp. 1-5.
- Exact locators: Main definition, PDF p. 2; Theorem 1 and its explicit
  `2 n log_2 n` right-repeat charge, PDF p. 4; Lemmas 1-2, PDF p. 5.
- Retained tuple C-CLOSED: `(S2 hash, Main definition + Theorem 1 + Lemmas
  1-2, positional next-occurrence charging)`.

Search query: arXiv `"maximal repetitions"`, `"closed repeats"`, and
`"maximal repetition" Renyi`. S1 was screened because it controls maximum
repeat length; S2 was retained because it ties a repeat to a specific occurrence
and its next occurrence, although its final charge is still linearized.

## DOMAIN 2: named fixed-point expanding dynamics

### SOURCE S3

Isabel Pirsic and Wolfgang Stockinger, "The Champernowne constant is not
Poissonian," *Functiones et Approximatio* 60(2) (2019), 253-262.

- DOI: https://doi.org/10.7169/facm/1749
- Stable record: https://arxiv.org/abs/1710.09313v2
- Retrieval URL: https://arxiv.org/pdf/1710.09313v2
- Local PDF: `pirsic-stockinger-1710.09313v2.pdf`
- PDF SHA-256: `27ba23a17b6762357e263b4425951da309112760dc886b54b9105ce865a20d61`
- Inspected range: PDF pp. 1-8.
- Exact locators: PPC normalization (1), PDF p. 2; Theorem 1, PDF p. 2;
  parameter choice `d=2^e`, `s=1`, `N=2^(d+e)`, PDF pp. 2-3; ordered-pair
  formula and `>> sqrt(d) 2^(d+e)` lower bound, PDF p. 5; Remark 2, PDF p. 6;
  Corollary 1, PDF p. 8.
- Retained tuple C-CHAMP: `(S3 hash, Theorem 1 + proof pp. 3-5, direct
  ordered matching-pattern multiplicity at a named expanding orbit)`.

### SOURCE S4

Yubin He and Lingmin Liao, "Quantitative recurrence properties for piecewise
expanding maps on [0,1]^d," arXiv:2302.05149v2 (2023).

- Stable record: https://arxiv.org/abs/2302.05149v2
- Retrieval URL: https://arxiv.org/pdf/2302.05149v2
- Local PDF: `he-liao-2302.05149v2.pdf`
- PDF SHA-256: `216ba701ee20e4bdb476395c966a57993079b0c069a5f7439de7e322c06e203b`
- Inspected range: PDF pp. 1-7.
- Exact locators: Definitions 1.1-1.2 and equations (1.3)-(1.4), PDF pp. 4-5;
  recurrence limsup sets (1.6), (1.8), PDF p. 5; Theorems 1.3-1.4, PDF p. 6.
- Disposition: screened. These are ambient zero-one laws under an absolutely
  continuous invariant probability and exponential mixing, not a theorem at a
  prescribed point or a finite-prefix ordered-pair bound.

Search query: arXiv `"expanding map" recurrence`, `Champernowne pair
correlation`, and named lacunary points. S3 was retained as a literal named
point with direct pair counting. S4 was charged as the generic ambient boundary
and supplies no premise for S3 or fixed pi.

## DOMAIN 3: short structured exponential sums

### SOURCE S5

Etienne Fouvry, Emmanuel Kowalski, and Philippe Michel, "The sliding-sum
method for short exponential sums," arXiv:1307.0135v2 (2015).

- Stable record: https://arxiv.org/abs/1307.0135v2
- Retrieval URL: https://arxiv.org/pdf/1307.0135v2
- Local PDF: `fouvry-kowalski-michel-1307.0135v2.pdf`
- PDF SHA-256: `ddd6f5dc551523fca670acfcf653f22a76be29445fd5fb44b9dc80ab98f18107`
- Inspected range: PDF pp. 1-5.
- Exact locators: Theorem 1.1, PDF pp. 2-3; definitions (2.1)-(2.2) and
  Theorem 2.1 equation (2.3), PDF pp. 4-5.
- Disposition: screened predecessor. S6 explicitly strengthens this theorem;
  its correlation term also requires the pair statistic one would need to prove.

### SOURCE S6

Etienne Fouvry, Emmanuel Kowalski, Philippe Michel, C. S. Raju, Joel Rivat,
and K. Soundararajan, "On short sums of trace functions,"
arXiv:1508.00512v3 (2016).

- Stable record: https://arxiv.org/abs/1508.00512v3
- Retrieval URL: https://arxiv.org/pdf/1508.00512v3
- Local PDF: `fkmrrs-1508.00512v3.pdf`
- PDF SHA-256: `3591f4c296190089850617665be59ffbc327c827496921e46fee91ded30cb922`
- Inspected range: PDF pp. 1-4.
- Exact locators: normalized Fourier transform (1.2) and completion bound
  (1.3), PDF p. 2; Theorem 1.1 equation (1.5), PDF pp. 2-3; definition
  (1.6) and Theorem 1.2 equations (1.9)-(1.10), PDF pp. 3-4.
- Retained tuple C-SHORT: `(S6 hash, Theorems 1.1-1.2, bounded function and
  bounded Fourier transform on a cyclic interval)`.

Search query: arXiv `"short exponential sums"`, `"sliding sum"`, and
structured trace-function intervals. The search stopped at S6 because it is the
stated strengthening of S5 and exposes the exact circular Fourier hypothesis.

## Nonduplication boundary

The preselection search of the then-supplied readable corpus and T155's
concatenated prior source ledger found none of the six PDF hashes or three
retained tuples. It did find `1710.09313` and `2302.05149` as bibliography
references only; those mentions were excluded from the claim of prior auditing.
This is a bounded corpus check, not a global novelty claim. T156 still has no
readable accepted artifact in the refreshed library, so no nonduplication claim
is made against unknown T156 source tuples.

Retry reconciliation found readable later artifacts for T158 and T159. T158's
four source hashes (`00d7ee6a...`, `7a54a70c...`, `f4a0ccfe...`,
`a4eaf55e...`) are distinct from S1--S6; its graph-gap/census mechanism is
reserved. T159 reuses Chen--Xia (`3640caf6...`) from T155 and specializes the
marked Palm--Stein mechanism; it is a readable unverified note and is reserved.
Neither later artifact changes the six-source inspection count, because neither
was inspected as a T160 source or used as a premise. Their complete report
hashes and levels are recorded in `EXCLUSION_LEDGER.csv`.
