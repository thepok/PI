# GPT Pro research coordination

This directory lets separately invoked GPT Pro-class models cooperate through the repository without a central chat session. The mechanism is deliberately small: one Markdown file per task, optimistic concurrency through the task file's Git blob SHA, and concrete outputs under `Deliverables/`.

`GPTPro/` is a control plane and staging area only. It does not replace `workflows/`, and nothing here is proof authority. Accepted research must be promoted under the repository rules to `knowledge/pi/`, `TheoryLib/`, and `audit/`.

## Directory layout

- `Tasks/`: one mutable state file per task plus `TEMPLATE.md`.
- `Deliverables/`: one subdirectory per task containing concrete, inspectable outputs.
- `PROMPT.md`: reusable invocation prompt.

There is intentionally no shared task index or global append-only log. Those become conflict magnets. Task files are the coordination state; deliverable files are the evidence paths.

## One-turn protocol

### 1. Orient

Read, in order:

1. repository-root `AGENTS.md`;
2. repository-root `GOAL.md` and `VERIFICATION.md`;
3. `GPTPro/AGENTS.md`;
4. this file;
5. every file in `GPTPro/Tasks/`;
6. repository material referenced by candidate tasks.

Create a unique `agent_id` containing a UTC timestamp and a model/random suffix.

### 2. Choose one eligible task

A task is eligible when:

- `status: open`;
- every `depends_on` task is `done`;
- it is not duplicate of completed, claimed, or canonical repository work.

Choose highest priority first (`P0`, then `P1`, `P2`, `P3`), then the oldest task. Claim one primary task per invocation.

### 3. Claim atomically

Fetch the task and retain its current Git blob SHA. Update that same file to:

```yaml
status: claimed
claimed_by: <agent_id>
claimed_at: <UTC ISO-8601>
lease_until: <claimed_at plus 24 hours>
```

Commit the update against the fetched blob SHA. This is the lock. If GitHub rejects the update because the SHA is stale, another model won the race: do not force, do not overwrite, refetch the tasks, and claim another one.

Do not edit another model's unexpired claimed task.

### 4. Execute, do not merely plan

Complete the task's bounded work in this invocation. Inspect existing work before generating new work. Prefer falsification, exact theorem/interface identification, reproducible checks, and small reviewable changes over broad speculation.

For formal changes, obey the repository verification gate exactly. Never present finite computation, model consensus, literature recollection, or a green build as proof of the main problem.

### 5. Produce a concrete deliverable

Write to `GPTPro/Deliverables/<task-id>/`. Every task directory must contain a `README.md` stating:

- claim label from the repository vocabulary;
- exact result or verdict;
- evidence and changed paths;
- reproduction or verification commands and outcomes;
- rejected alternatives;
- limitations and next unresolved bottleneck;
- intended promotion path into canonical repository locations.

Put Lean candidates, scripts, source manifests, data, counterexamples, and other artifacts beside that README. Do not commit raw transcripts, provider logs, private data, or copied sandboxes.

### 6. Finish the task in the same invocation

Write result artifacts first, then update the task using its latest blob SHA.

For success:

```yaml
status: done
finished_at: <UTC ISO-8601>
result_paths:
  - GPTPro/Deliverables/<task-id>/README.md
verification:
  - <check and outcome>
```

For a real blocker:

```yaml
status: blocked
finished_at: <UTC ISO-8601>
```

A blocked deliverable must document the blocker, evidence, failed routes, and the smallest action that would unblock it. A weak idea is not a blocker; reject it and complete the audit.

Every invocation ends with its task `done` or `blocked`. There is no asynchronous continuation and no valid reason to leave a task `claimed` after the call ends.

### 7. When no open task exists

Do not stop at “nothing to do.” Inspect the current verified frontier, completed tasks, active workstreams, negative results, and existing deliverables. Create one non-duplicate, one-turn-sized, high-value task from `Tasks/TEMPLATE.md`, using a globally unique filename such as:

```text
20260821T191635Z-<agent-id>-<short-slug>.md
```

Create it already `claimed`, execute it, and finish it in the same invocation. After completing a task, create at most two genuinely necessary follow-up tasks; avoid backlog inflation.

## Claim recovery

A claim may be recovered only after `lease_until` has passed. Before recovery, inspect commits and result paths for evidence that the original model completed work without updating the task. Record the previous claimant and recovery reason in the task work log. Never use a forced branch update.

## Task quality bar

A valid task has one precise objective, explicit bounded deliverables, acceptance checks another model can falsify, exact repository context, and a statement explaining why it is not duplicate work. “Explore this area” is not a task.

Use the repository claim vocabulary exactly: `experiment`, `conjecture`, `proof sketch`, `machine-checked`, `literature-checked`, `candidate resolution`, and `verified resolution`. Never silently upgrade a label.

Use `GPTPro/PROMPT.md` for future invocations.
