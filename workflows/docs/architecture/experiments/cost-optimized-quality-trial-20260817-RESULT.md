# Cost-optimized verified-quality trial

Date: 2026-08-17 UTC

## Outcome

The optimized route completed a fresh unresolved workitem, T174, with a final
independent Sol-max verdict of **`accept`, 100/100**.

```text
existing independent Sol review (cached repair contract)
  -> Luna high repair
  -> deterministic verifier and checksum gates
  -> one fresh independent Sol max source audit
```

There was no new Sol planning/guidance call and no repair round was needed.

## Cost estimate

The current local price table is Luna $0.20/M uncached input, $0.02/M cached
input, $1.20/M output/reasoning; Sol $5/M, $0.50/M, and $30/M respectively.
No call crossed the long-context price tier.

| Phase | Uncached input | Output + reasoning | Cache reads | Estimated cost |
|---|---:|---:|---:|---:|
| Luna-high repair | 110,402 | 23,066 | 2,780,160 | $0.105 |
| Sol-max final review | 83,965 | 8,996 | 790,016 | $1.085 |
| Total | | | | **$1.190** |

Pricing the same Luna executor receipts as Sol gives $2.634; with the same
review, the same-token all-Sol route would be $3.719. Observed savings:
**$2.529 (68.0%)**.

This is a price-table estimate from OpenCode traces, not a provider invoice.

## Quality evidence

The reviewer independently extracted the cited pages from all three pinned
PDFs, reran `verify_t174.py`, verified all SHA-256 entries, compared fresh
replay output byte-for-byte, and audited the complete original acceptance
contract. It found no blocking defect.

Acceptance remains scoped to a `literature-checked` source map with
`proof sketch` calculations and `experiment` replay. It is not progress on the
fixed-π claim.

Artifacts:

- repaired packet: `t174/executor/output/`
- final verdict: `t174/review/VERDICT.json`
- detailed review: `t174/review/REVIEW.md`
- raw traces: `t174/executor/run.jsonl`, `t174/review/run.jsonl`

The research orchestrator remained paused and no result was promoted into the
trusted graph or ledger.
