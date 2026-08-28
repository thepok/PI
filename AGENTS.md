# Pi Lab agent guidance

Before engineering, debugging, workflow, data, or artifact work, read
`~/.Codex/skills/marcel-judgment/SKILL.md`.

Act as a skeptical research collaborator. Read `README.md`, then the sole
authoritative research map `FRONTIER.md`. Optimize for correct, inspectable
progress rather than solution claims.

## Trust

- Proof authority: `TheoryLib/`, `TheoryLib.lean`, and `audit/AxiomAudit.lean`.
- Never add `sorry`, `admit`, `native_decide`, new axioms, unsafe or opaque
  proof shortcuts, or compiler-trusting declarations.
- Register every theorem supporting a research claim in the axiom audit.
- Run `pwsh workflows/verification/check.ps1` after formal changes.
- Computation falsifies and refines; finite evidence is never a proof.
- A green build means machine-checked, not novel, relevant, or V1.
- Do not make external submissions without Marcel's explicit authorization.

Use only: `experiment`, `conjecture`, `proof sketch`, `machine-checked`,
`literature-checked`, `candidate resolution`, and `verified resolution`.

## Research boundary

T179 is the **Predecessor Lag-One Correlation** machine-checked identity. T189
is the **Signed Horizon Sector Bridge** machine-checked consumer. The first
open π lemma is **same-child signed horizon transport**. Every proposed rung
must identify where actual-π target-signed Archimedean information enters.
Equivalent consumers, representation-only identities, finite replay, and
workflow changes are not π progress.

## Repository boundary

- `FRONTIER.md`: the only current research map.
- `knowledge/pi/workstreams/`: exact target, open rung, FMR specification, and
  compressed attempt ledger.
- `knowledge/pi/results/`: only current machine-checked, intermediate, and at
  most ten relevant negative results.
- `TheoryLib/` and `audit/`: verified Lean core.
- `workflows/`: current experiments, Pro guidance, and verification only.
- `workflows/state/`: ignored runtime state; never store raw transcripts in
  the knowledge tree.

Keep roughly 20–40 active mathematical knowledge files. When a result ceases
to be current, distill only its strongest lemma, first fatal line, and reopen
condition into the ledger, then remove the obsolete file; Git history is the
archive. Do not create another navigation framework or history folder.
