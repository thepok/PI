# Pi Lab agent guidance

Act as a skeptical research collaborator. Read `README.md`, then the sole
authoritative research map `FRONTIER.md`. Optimize for correct, inspectable
progress rather than solution claims. If a local judgment skill exists at
`~/.Codex/skills/marcel-judgment/SKILL.md` or
`~/.claude/skills/marcel-judgment/SKILL.md`, read it before engineering work.

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
Never silently upgrade a label.

## Research rules

- `FRONTIER.md` states the target, the target ladder, the first open π lemma,
  and the three admission tests for a new candidate. Every proposed rung must
  identify where actual-π target-signed information enters.
- **Separator first.** Before building a Lean rung, run the numerical
  word-avoider check on its premise. A premise shared by a digit-avoiding
  replacement constant cannot prove V1.
- **Find before prove.** A named, testable, surprising conjecture about π with
  a falsification experiment and an explicit avoider on which it fails is
  worth more than another closed route.
- Route closures are not progress. Record them in the attempt ledger as
  reason, strongest retained lemma, and reopening condition, and move on.
- Equivalent consumers, representation-only identities, finite replay, and
  workflow changes are not π progress.

## Repository boundary

- `FRONTIER.md`: the only current research map.
- `knowledge/pi/workstreams/`: exact target, open rung, FMR specification,
  attempt ledger, and property admission audit.
- `knowledge/pi/results/`: current machine-checked, intermediate, and
  relevant negative results. Keep it small; Git history is the archive.
- `TheoryLib/` and `audit/`: verified Lean core.
- `workflows/`: reproducible experiments and verification only, with all
  their inputs tracked here.
- `workflows/state/`: ignored runtime state; never store raw transcripts in
  the knowledge tree.
- [`AllMath`](https://github.com/thepok/MathMyth): project roadmap,
  orchestration, model runners, prompts, and runtime tools. Nothing in this
  repository depends on it.
