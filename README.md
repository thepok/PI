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
