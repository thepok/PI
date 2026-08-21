# Pi Lab

A compact, machine-checked research workspace for the question:

> Does every finite digit string occur in the decimal expansion of π?

The repository separates trusted mathematics from research machinery:

- `TheoryLib/` and `TheoryLib.lean`: canonical Lean proof source.
- `audit/AxiomAudit.lean`: explicit theorem-by-theorem axiom audit.
- `knowledge/pi/`: statements, milestone reports, negative results, continuation state, and active workstreams.
- `workflows/`: sandboxed model runners, task definitions, runtime/container tools, and verification scripts.

No theorem here resolves the main digit-occurrence question. A green build means only that the stated Lean declarations are machine-checked under the exact axiom allowlist.

## Verify the core

```bash
lake build TheoryLib
pwsh workflows/verification/check.ps1
```

The gate rejects `sorry`, `admit`, `native_decide`, new axioms, opaque proof declarations, unsafe declarations, and other compiler-trusting shortcuts. Allowed foundational axioms remain exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Run the sandboxed Ox workflow

```bash
.venv/bin/python workflows/modelbench/runner.py \
  --sandbox \
  --sandbox-image localhost/allmath-research:latest \
  --tasks-dir workflows/modelbench/tasks/pi/current \
  --models ox,oxzen \
  --concurrency 14 \
  --out workflows/state/runs/pi-current
```

Use provider-specific launches when enforcing distinct concurrency limits. All model work runs in pods; only artifacts that independently pass the Lean and axiom gates may enter `TheoryLib/`.

See [knowledge/pi/README.md](knowledge/pi/README.md) for the research-state map and [workflows/README.md](workflows/README.md) for workflow operations.
