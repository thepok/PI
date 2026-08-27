# T158 bounded search log

Search date: 2026-08-12 UTC.

## Preselection

1. Verified canonical SHA-256
   `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
2. Refreshed the T155 exclusion ledger through T157 before source retention.
3. Replaced stale T153/T154 rows with the current readable levels. Added T155.
4. On retry, replaced stale T156/T157 availability rows. T157 is a readable
   pinned LC/PS/EXP artifact. T156's rejected report is recoverable from the
   supplied proof-ledger snapshot; it is comparison evidence only, and the
   recorded duplicate-source rejection is preserved.
5. Checked candidate author/title, arXiv ID, PDF hash, and theorem tuple against
   supplied `SOURCE_PINS.md` files. None of S1--S4 was previously pinned.

## Search lanes

| Required lane | Query/route | Inspected primary PDF | Outcome |
|---|---|---|---|
| symbolic collision / weighted de Bruijn | weighted de Bruijn process stationary eigenvalues | Ayyer--Strehl, arXiv:1108.5695v1 | retained as exact random-process comparator |
| spectral/conductance concentration | pseudo-spectral gap Markov concentration | Paulin, arXiv:1212.2015v5 | retained as quantitative random-path theorem |
| fixed-point expanding/symbolic dynamics | alpha-mixing fixed target cylinder returns | Abadi--Saussol, arXiv:1003.4856v2 | retained as target-versus-starting-path scope separator |
| short structured exponential sums | short exponential sums Mersenne digits | Kerr--Merai--Shparlinski, arXiv:2001.03380v4 | screened by base and ensemble mismatch |

The search stopped after four successfully opened primary PDFs. Chazottes--
Gouezel was found relevant but excluded before opening because T150 already
pins it. Lawler--Sokal DOI metadata was found, but the primary PDF retrieval
failed with HTTP 403 and no claim uses it.

```text
SEARCHED_DOMAIN_COUNT: 4
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 8
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```
