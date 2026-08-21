# T120 bounded search log

Search date: 2026-08-10 UTC.

## Scope and stopping rule

The search covered the three required lanes and stopped after four primary
PDFs were opened because each retained card had exact countable-state data and
a quantitative T7/T107 calculation. No source was added to fill the cap.

```text
PRIMARY_SOURCE_COUNT: 4 <= 12
CANDIDATE_COUNT: 4 <= 4
```

## Queries and decisions

| Lane | Primary-paper query or direct lookup | Opened source | Decision |
|---|---|---|---|
| fixed-point inducing | `LSV map return time tail operator renewal sharp polynomial correlations` | Gouezel `math/0202147` | retain R-LSV: explicit neutral fixed point, countable partition, integrated return tail |
| continued-fraction renewal | `Farey map Gauss induced return time tail critical waiting time` | Kessebohmer--Slassi `math/0607681` | retain R-FAR: exact countable intervals and derived exact `K_1` tail `log((n+2)/(n+1))/log 2` |
| symbolic collisions | `countable ergodic Markov chain renewal p_n convergence equilibrium Isola` | Isola `math/0308018` | retain R-ISO: explicit countdown chain, zeta specialization, fixed-state nonuniformity |
| arithmetic/fractal Fourier | `Fourier transforms Gibbs measures Gauss map countable tail Jordan Sahlsten` | Jordan--Sahlsten `1312.3619v3` | retain R-JS as a rejection: exact countable digit tail but no return-time renewal; quantitative T107 mismatch |

The official corpus consists only of the four delivered PDFs. Search-result
abstracts and later finite-branch papers were not used for mathematical claims
and were not counted as inspected primary sources.

## Exclusion checks

| Excluded fingerprint | Search decision |
|---|---|
| finite-state carry operators | excluded by comparison with T112; Isola is countably infinite and has unbounded excursions |
| Toeplitz towers | excluded by comparison with T103; no periodic skeleton or hole density was retained |
| substitution/Riesz recursions | excluded by comparison with T115; Isola's renewal resolvent is not a finite-alphabet spectral recursion |
| perturbative coupling certificates | excluded under rejected T109; no transfer is inferred from closeness, shadowing, TV, or Wasserstein bounds |
| cyclotomic modular sums | excluded by comparison with active T118 and T117; no modulus or finite character sum occurs |
| collision-to-Hankel-rank inversion | no candidate uses rank, moments, or an inverse low-rank certificate |

## Prior and active artifact search

Readable reports were inspected for T39, T90, T103, rejected T109, T112,
T115, and T117. Their exact hashes are in `SOURCE_PINS.md`.

The original active T118 record was absent, but its report was recovered from
the proof-ledger content-addressed store and vendored byte-exactly as
`prior-t118-REPORT.md`. It remains comparison memory because its review status
requires a rerun.

For active T119, searches covered:

```text
removed-workflow-record://*t119*/**/*
knowledge_library/**/t119/**/*
.research proof-ledger artifact references
the T120 orchestration snapshot
```

Only an active generation-1 lease appeared in the orchestration snapshot. No
source pin, report, artifact hash, or verification status was readable. The
comparison uses only the parent agenda's explicit collision-to-Hankel-rank
exclusion and infers no unpublished T119 content. If T119 becomes readable
before review, its row must be replaced rather than treating absence as
novelty.

## Retrieval log

All four arXiv PDFs were retrieved successfully over HTTPS and converted with
`pdftotext -layout`. No OCR was required. PDF and derivative hashes were taken
immediately after retrieval and are recorded in `SOURCE_PINS.md` and
`SHA256SUMS`.
