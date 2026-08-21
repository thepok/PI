# T132 bounded search log

Search date: 2026-08-10 UTC.

The search was frozen after exactly three domains, seven opened primary
papers, and two retained theorem cards. Bibliographic/abstract pages used to
locate a paper are not counted as primary papers. No unlisted primary full
text was opened.

| Domain | Queries and routes | Primary papers opened | Decision |
|---|---|---|---|
| restricted-denominator approximation | `weighted larger sieve multiplicity residue classes`, `large sieve arbitrary coefficients exact constant`, `large sieve square moduli arbitrary coefficients` | Gallagher S1; Montgomery--Vaughan S2; Baier--Zhao S3 | retain S2 as C-LS direction test; reject S1 support-only and S3 wrong-direction primitive-frequency bound |
| symbolic collision / Renyi-2 | `minimum Renyi entropy coupling majorization meet`, `collision entropy marginal meet majorization` | Cicalese--Gargano--Vaccaro S4; Yadav--Shkel S5 | retain S4 as C-MEET; S5 confirms the lattice interface but adds no decimal-profile bound |
| short structured exponential sums | reused T121 pins after querying its exact F-AUT sources rather than opening new papers | Konieczny S6; Fan--Konieczny S7 | reject fixed-order/specific-sequence and assumed-Gelfond routes as T121 duplicates |

## Pre-screen order

1. The exact identity `E_q=q^(-1) sum_h |sum_i a_i e(hB_i/q)|^2`
   was derived before source retention.
2. Any proposed theorem whose only conclusion was a single-modulus upper bound
   for this same residue-L2 quantity was discarded as a T121 duplicate.
3. S2 was retained despite that screen only to test the canonical weighted
   large-sieve inequality's direction. It yields a lower, not upper, bound for
   exact collision energy.
4. S4 survived because full Lorenz profiles contain more information than the
   scalar energies and can give a strict deterministic improvement over their
   minimum.

## Retrieval and inspection notes

- S1 downloaded successfully but is image-only. Three pages were rendered at
  300 dpi. Theorem 1 and formula (2) were visually checked. The environment
  lacked `tesseract`, so no OCR derivative was produced or treated as exact.
- S2--S5 downloaded successfully with text layers.
- S6--S7 were copied byte-exactly from the accepted T121 source bundle; their
  hashes match its pins.
- No retrieval failed. The OCR tooling failure is recorded in `REPORT.md` and
  the final problems telemetry.

## Stop boundary

The search stopped at seven of eight allowed sources because both possible
outcomes were already represented: C-MEET gives a genuine profile-level gain,
while the support sieve, analytic large sieve, restricted-denominator bound,
and structured-sum papers expose the required rejection modes. Opening an
eighth paper would not repair the missing fixed-pi profile premise.
