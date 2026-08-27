# T134 bounded search log

Search and inspection date: 2026-08-10 UTC.

The search began from the exact zero-cylinder term isolated by T130. It reused
the supplied pinned primary corpus rather than opening a broad mechanism
search. Six sources were sufficient to test all required lanes, so the search
stopped below the cap of eight.

| Order | Lane and query fingerprint | Primary source opened | Decision |
|---:|---|---|---|
| 1 | powers-of-ten rational approximation; fixed-pi zero blocks | Zeilberger--Zudilin | retained in C-RD; direct zero-hit substitution excludes only an initial interval of starts |
| 2 | restricted repetition denominators and run exponents | Bugeaud--Kim | retained in C-RD; theorem controls repetition exponent, not zero-word occupancy |
| 3 | Peres--Schlag variable-threshold avoidance | Moshchevitin | screened; existential avoidance set has no named point or fixed-pi specialization and duplicates T113/T116 boundary |
| 4 | explicit G-function digit runs and denominator `b^(n-1)(b^t-1)` | Fischler--Rivoal | retained as C-GRUN; maximum-run cap fails the all-`A` occupancy substitution for one fixed G-value |
| 5 | exact nested symbolic incidence | Fishman--Merrill--Simmons | retained as C-DB; exact zero occupancy passes but duplicates T111/T128/T131 |
| 6 | nested-perfect-necklace discrepancy | Becher--Carton | screened; stronger all-cylinder balance is an already-audited global-incidence route |

Explicit exclusion decisions:

- No result for almost every point was retained because the agenda requires a
  prescribed-point or named-model applicability calculation.
- No maximum-run theorem was treated as an occupancy theorem. C-GRUN displays
  the missing run-count calculation explicitly.
- No ineffective asymptotic was converted into a finite threshold. C-RD keeps
  the unknown irrationality-measure onset visible.
- Every card was tested at a cutoff satisfying `N>=A*m`; C-RD uses `N=m` at
  `A=1`, C-GRUN uses `N=A*m`, and C-DB proves `10^m>=A*m` on its schedule.
- Search stopped after the exact symbolic survivor was identified as a prior
  fingerprint. More run-length, discrepancy, or normality sources would not
  test a new theorem shape.
