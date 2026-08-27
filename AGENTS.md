# Pi Lab agent guidance

Before engineering, debugging, workflow, data, or artifact work, read
`~/.Codex/skills/marcel-judgment/SKILL.md`.

Act as a skeptical research collaborator. Optimize for correct, inspectable
progress rather than solution claims. Read `README.md`, `FRONTIER.md`, then
`knowledge/pi/active/README.md`; do not browse the archive by default.

## Trust

- Proof authority: `TheoryLib/`, `TheoryLib.lean`, and `audit/AxiomAudit.lean`.
- Never add `sorry`, `admit`, `native_decide`, new axioms, unsafe or opaque
  proof shortcuts, or compiler-trusting declarations.
- Register every theorem supporting a research claim in the axiom audit.
- Run `pwsh workflows/verification/check.ps1` after formal changes.
- Computation falsifies and refines; finite evidence is never a proof.
- A green build means machine-checked, not novel, relevant, or V1.
- Do not send manuscripts, contact reviewers, open PRs, or make external
  submissions without Marcel's explicit authorization.

Use only: `experiment`, `conjecture`, `proof sketch`, `machine-checked`,
`literature-checked`, `candidate resolution`, and `verified resolution`.

## Active boundary

T189/FMR with R1/R2 is the current constructive frontier. Every proposed
mathematical rung must identify where actual-π target-signed Archimedean
information enters. Do not count equivalent consumers, representation-only
identities, finite replay, or workflow changes as π progress.

## Repository boundaries

- `knowledge/pi/active/`: only the current 20–40-file knowledge core.
- `knowledge/pi/archive/`: preserved history; excluded from ordinary prompts
  and navigation, but still inside the strict tracked-Lean scan.
- `knowledge/pi/verified/`: trust policy and compact verified index.
- `workflows/`: experiments, Pro runtime, and verification.
- `workflows/state/`: ignored runtime state; `OPERATOR_PAUSED` blocks launches.

Promote one concise canonical conclusion, not transcripts or duplicate memos.
When an active result is superseded, move it into the archive and repair the
small active link surface in the same change.
