# Pi Lab

A compact, machine-checked research workspace for the question:

> Does every finite digit string occur in the decimal expansion of π?

The repository separates trusted mathematics from research machinery:

- `TheoryLib/` and `TheoryLib.lean`: canonical Lean proof source.
- `audit/AxiomAudit.lean`: explicit theorem-by-theorem axiom audit.
- `knowledge/pi/`: statements, milestone reports, negative results, continuation state, and active workstreams.
- `workflows/`: sandboxed model runners, task definitions, runtime/container tools, and verification scripts.
- `GPTPro/`: file-based coordination and concrete deliverables for separately invoked high-capability research models.

No theorem here resolves the main digit-occurrence question. A green build means only that the stated Lean declarations are machine-checked under the exact axiom allowlist.

## Default operating model

Normal research runs use four clearly separated roles:

1. **Main operator:** one persistent oversight agent owns the run. It keeps the
   free workers supplied with bounded tasks, watches provider utilization and
   pod health, repairs general workflow failures, retires stale directions, and
   reports only material progress.
2. **Research director:** one maximum-intelligence subagent owns the current
   mathematical direction. It audits the verified frontier and negative-result
   memory, chooses the next highest-value questions, and challenges weak or
   redundant task proposals. It does not spend its time on routine worker jobs.
3. **Knowledge integrator:** one subagent, using as much intelligence as the
   current integration requires, reviews returned artifacts, deduplicates them,
   preserves negative and intermediate findings, and prepares narrowly scoped
   candidates for the trusted core. It also reviews newly committed `GPTPro/`
   work and integrates supported conclusions into the same knowledge hierarchy
   instead of leaving isolated handoffs.
4. **Ox workers:** the free Ox Alpha providers perform the high-volume research
   inside isolated pods. Their output is untrusted input, never a result by
   itself. The current machine-wide ceilings are four concurrent OpenRouter
   `ox` calls and ten concurrent OpenCode `oxzen` calls.

Agents do not constitute the trust boundary. The operator may promote a formal
finding only after the independent kernel build, exploit scan, exact statement
contract, and axiom audit pass. The research director and knowledge integrator
must remain separate roles so choosing a direction, producing an artifact, and
accepting it are not one self-confirming step.

## Verify the core

```bash
lake build TheoryLib
pwsh workflows/verification/check.ps1
```

The gate rejects `sorry`, `admit`, `native_decide`, new axioms, opaque proof declarations, unsafe declarations, and other compiler-trusting shortcuts. Allowed foundational axioms remain exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Run one GPT Pro research turn

Give a capable model the prompt in [`GPTPro/PROMPT.md`](GPTPro/PROMPT.md). Each invocation atomically claims one task through that task file's current Git blob SHA, completes a bounded deliverable under `GPTPro/Deliverables/`, and closes the task as `done` or `blocked`.

The main operator may also invoke Marcel's authenticated web ChatGPT Pro through
the `chatgpt-pro` skill for one sharply bounded research-director task. There
must be at most one active web-Pro call at a time. Every prompt names this Git
repository, branch, exact deliverable, and claim boundary; the returned answer
is still untrusted external input until the knowledge integrator reviews it.
If login/account resumption, a browser permission, or a capacity/break warning
blocks the call, stop it and notify Marcel immediately rather than guessing
credentials or starting a second call.

## Run the sandboxed Ox workflow

```bash
.venv/bin/python workflows/modelbench/runner.py \
  --sandbox \
  --sandbox-image localhost/allmath-research:latest \
  --tasks-dir workflows/modelbench/tasks/pi/current \
  --models ox,oxzen \
  --concurrency 20 \
  --out workflows/state/runs/pi-current
```

The runner enforces the provider ceilings itself; the larger feeder pool prevents
threads waiting for one provider from starving free slots at the other. All
model work runs in pods; only artifacts that independently pass the Lean and
axiom gates may enter `TheoryLib/`.

See [knowledge/pi/README.md](knowledge/pi/README.md) for the research-state map, [workflows/README.md](workflows/README.md) for workflow operations, and [GPTPro/README.md](GPTPro/README.md) for pro-model coordination.
