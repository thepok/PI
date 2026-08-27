# UltraPi knowledge-graph migration report

Date: 2026-08-16 UTC

Claim status: this is a data/provenance migration report, not a mathematical
result and not a claim-status upgrade.

## Imported point of truth

The canonical runtime projection is `.research/proof-ledger.sqlite3`. The
reproducible source manifests are:

| Corpus | Manifest SHA-256 | Purpose |
|---|---|---|
| `corpus:local:pi-digits:ultrapi:v1` | `ab388b1dcb63a1287cc2f71ed26448895395f3eb9e1b7cf8c583b3a24bd76916` | Current dossier, T18–T77, linked reports and linked artifact inventory |
| `corpus:local:pi-digits:ultrapi-reconciliation:v1` | `1c1487615747e77f65b660e974bf129183b9763cc2c3876c87d5683a97814a9f` | Existing-node reconciliation, stale memo, and T78 scope boundary |
| `corpus:local:pi-digits:ultrapi-resume-extension:v1` | `fbe659e8eb14b47d79f29701fc787ae6a3b74512f887b548b79df4aed8d8e6bd` | Status-neutral coverage of resume artifacts not linked by the dossier |
| `corpus:local:pi-digits:ultrapi-status-normalization:v1` | `bc062dfe5622d4b917cd5c1295911c00be7847ddfe46c00a997972e990e93f3b` | Explicit V1 and endpoint-gap conjectures plus the bounded endpoint experiment |

All four pin `ultrapi.md` at
`49299073e53c3949ab77f5d9bdb97cd89cd8b24d5c4cbad5f5c97c00121f22fc`.
The dossier bytes are also preserved in the content-addressed ledger artifact
store; the mutable working path is not the only surviving copy.

## Verified migration coverage

`tools/audit_ultrapi_knowledge.py` reports:

- 4 immutable corpora;
- 295 typed knowledge records;
- 546 record/evidence links;
- all 407 existing local files linked by `ultrapi.md` manifest-pinned and
  ledger-evidenced by exact hash;
- all 418 non-cache files under `work/ultrapi-resume/` ledger-evidenced;
- exactly 60 T-items covering T18 through T77;
- 9 active, scoped obstruction/dead-end records;
- all 83 explicit manifest dependency/reconciliation edges present;
- zero proof labels created by corpus import.

The main graph contains additional automatic `documents` edges from each
corpus to its records, so the total number of edges created by import is larger
than the 83 explicitly declared mathematical/reconciliation edges.

## Claim and trust boundary

The T18–T77 records retain `machine-checked` exactly as asserted by the pinned
dossier, but their authority is `source-asserted`. Corpus import did not create
trusted receipts. Unclassified reports and scratch artifacts have null claim
level. The two pre-existing August 13 result nodes retain `proof sketch` and
are connected by `supersedes` edges to their automatically indexed report
duplicates.

The normalized status projection contains 60 `machine-checked`, 11
`proof sketch`, 2 `conjecture`, and 1 `experiment` records, all with
`source-asserted` authority. The remaining 221 inventory/review/mechanism
records intentionally have null claim level.

T78 is explicitly represented as an unintegrated draft: it is absent from the
pinned dossier range and has no imported claim level. The older integration
memo is retained as evidence and marked superseded by the current corpus.

At migration time, the existing core ledger had 539 stale historical Lean
verifier runs and zero current trusted artifacts because its source-manifest
context had changed before this migration. The pre-migration backup already
had the same state, so the knowledge migration neither caused nor concealed
it.

On 2026-08-16, after the migration, the fixed `lean-exact-axiom-gate-v1` was
rerun without LLM calls for all 222 distinct registered theorem/node pairs on
52 nodes. All 222 passed. The current trusted projection therefore contains
222 artifacts bound to source-manifest SHA-256
`8cf338c2563e38e9629d841ce49b226f5c2c83d08c075d7b9489ea4f5ed58635`
and verifier-policy SHA-256
`b889f7439842bed0c03bfae57fe7d528c5e4bcb02880bbf7588458ecf1190397`.
The 539 older runs remain as stale history; they are not counted as trusted.

## Operational safety

The interrupted T188 lease was expired through the ledger's normal transition:
the node returned from stale `active` to `open`, and no result was recorded.
The research service remained `inactive (dead)`. The persistent
`.research/OPERATOR_PAUSED` guard was exercised against the normal start script;
the launcher exited without contacting systemd to start research. No research
worker process or AllMath/OpenCode research pod was present.

A recoverable SQLite backup from immediately before migration is stored at
`.research/backups/proof-ledger-pre-ultrapi-v1-20260816.sqlite3`, SHA-256
`f96548c158d9cd6d21a1ebab779ab8d5b2168cde0aa54d83e4b4f5bcf20cc916`.

## Reproduction and retrieval

```powershell
scripts\knowledge-graph.ps1 audit
scripts\knowledge-graph.ps1 query --root local:pi-digits
scripts\knowledge-graph.ps1 query --root local:pi-digits `
  --active-obstructions --query "logarithmic orbit"
```

```bash
.venv/bin/python tools/audit_ultrapi_knowledge.py
```

The graph is now the unified query surface. Markdown, Lean, checkers, data, and
reviews remain immutable or hash-pinned payloads behind it rather than competing
partial indexes.
