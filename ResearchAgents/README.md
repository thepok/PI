# Research-agent coordination

This directory lets separately invoked high-capability models cooperate through the repository without a central chat session. The mechanism is deliberately simple: one Markdown file per task, atomic claims through Git blob SHAs, and compact reports linked from completed tasks.

`ResearchAgents/` is a control plane only. It does not replace `workflows/`, and nothing here is proof authority. Accepted research must be promoted under the repository rules to `knowledge/pi/`, `TheoryLib/`, and `audit/`.

## Directory layout

- `tasks/`: one file per task plus `TEMPLATE.md`.
- `reports/`: compact task results and coordination audits.
- `PROMPT.md`: reusable invocation prompt.

There is intentionally no shared mutable task index or append-only global log. Those become merge-conflict magnets. The task files themselves are the source of coordination state.

## One-turn protocol

### 1. Orient

Read, in order:

1. repository-root `AGENTS.md`;
2. repository-root `GOAL.md`;
3. `ResearchAgents/AGENTS.md`;
4. this file;
5. all files in `ResearchAgents/tasks/`;
6. the repository material referenced by candidate tasks.

Create a unique `agent_id` containing a UTC timestamp and model/random suffix.

### 2. Choose one eligible task

A task is eligible when:

- `status: open`;
- every `depends_on` task is `done`;
- it is not a duplicate of completed or currently claimed work.

Choose the highest priority first (`P0`, then `P1`, `P2`, `P3`), then the oldest task. Claim one primary task per invocation.

### 3. Claim atomically

Fetch the candidate task and retain its current Git blob SHA. Update that same file to:

```yaml
status: claimed
claimed_by: <agent_id>
claimed_at: <UTC ISO-8601>
lease_until: <claimed_at plus 24 hours>
```

Commit the update against the fetched blob SHA. This is the lock. If GitHub rejects the update because the SHA is stale, another model won the race: do not force, do not overwrite, refetch the queue, and claim another task.

Do not edit another model's unexpired claimed task.

### 4. Execute, do not merely plan

Complete the task's bounded deliverables in this invocation. Inspect existing work before generating new work. Prefer falsification, exact theorem/interface identification, reproducible checks, and small reviewable changes over broad speculation.

For formal changes, obey the repository verification gate exactly. Never present finite computation, model consensus, or a green build as a proof of the main problem.

### 5. Finish the task

Write result artifacts first, then update the task file using its latest blob SHA.

For success:

```yaml
status: done
finished_at: <UTC ISO-8601>
result_paths:
  - <path>
verification:
  - <check and outcome>
```

For a real blocker:

```yaml
status: blocked
finished_at: <UTC ISO-8601>
```

Document the blocker, the evidence, and the smallest action that would unblock it. A weak idea is not a blocker; reject it and complete the audit.

Every invocation must end with its task `done` or `blocked`. There is no asynchronous continuation.

### 6. When no open task exists

Do not stop at “nothing to do.” Inspect the current verified frontier, completed tasks, active workstreams, and negative results. Create one non-duplicate, one-turn-sized, high-value task from `tasks/TEMPLATE.md`, with a globally unique filename such as:

```text
20260821T190103Z-<agent-id>-<short-slug>.md
```

Create it already `claimed` by your `agent_id`, execute it, and finish it in the same invocation. After completing a task, create at most two genuinely necessary follow-up tasks; avoid backlog inflation.

## Claim recovery

A claim may be recovered only after `lease_until` has passed. Before recovery, inspect commits and result paths for evidence that the original model completed work without updating the task. Record the previous claimant and recovery reason in the task's work log. Never use a forced branch update.

## Task quality bar

A valid task has:

- one precise objective;
- explicit, bounded deliverables;
- acceptance checks that another model can falsify;
- links to relevant repository paths;
- a statement explaining why it is not duplicate work.

Research tasks should identify exact theorem names, assumptions, quantifiers, and status labels. “Explore this area” is not a task.

## Artifact and claim discipline

Use the repository claim vocabulary exactly: `experiment`, `conjecture`, `proof sketch`, `machine-checked`, `literature-checked`, `candidate resolution`, and `verified resolution`.

A report under `ResearchAgents/reports/` should contain only the conclusion, evidence, checks, changed paths, rejected alternatives, and next bottleneck. Do not commit raw transcripts, private data, provider logs, or copied sandboxes.

Use `ResearchAgents/PROMPT.md` for future invocations.
