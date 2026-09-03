# Pi Lab

This repository studies whether every finite decimal word occurs in the
decimal expansion of π. Nothing here proves that claim.

The sole current research map is [`FRONTIER.md`](FRONTIER.md). Formal proof
authority is [`TheoryLib/`](TheoryLib/) plus
[`audit/AxiomAudit.lean`](audit/AxiomAudit.lean).

Verify the tracked Lean core and axiom audit with:

```powershell
pwsh workflows/verification/check.ps1
```

`workflows/` is limited to reproducible mathematical experiments and
verification. Project orchestration, model runners, prompts, and runtime tools live in a
separate private project repository. PI tracks all inputs required by its
experiments in this repository.
