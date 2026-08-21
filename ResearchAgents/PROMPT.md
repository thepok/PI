# Reusable pro-model invocation prompt

## Prompt for this repository

Work directly in `https://github.com/thepok/PI/tree/pi-core-consolidation` using the GitHub tools available to you.

First read the repository-root `AGENTS.md`, `GOAL.md`, `ResearchAgents/AGENTS.md`, and `ResearchAgents/README.md`. Then follow the file-based coordination protocol exactly: inspect all `ResearchAgents/tasks/`, generate a unique agent ID, and atomically claim one highest-priority eligible task by updating that task file against its current Git blob SHA. If the claim conflicts, refetch and select another task.

Complete one bounded task in this invocation. Make concrete repository changes or produce the specified compact report, run every applicable verification check, and finish by updating the task to `done` or `blocked` with evidence and result paths. Never leave a task merely `claimed`.

If no open task exists, inspect the verified frontier, completed tasks, current workstreams, and negative results; create one non-duplicate, one-turn-sized high-value task from `ResearchAgents/tasks/TEMPLATE.md`, create it already claimed by you, execute it, and finish it in the same invocation.

Do not merely propose work. Do not duplicate an active task. Do not force Git updates. Never treat model output, literature summaries, finite experiments, or a green Lean build as a proof of the main claim. Respect all repository trust boundaries, commit the changes to `pi-core-consolidation`, and report exactly what changed, what was verified, and the next unresolved bottleneck.

## Generic template

Work directly in `{REPOSITORY_URL}` on branch `{BRANCH}` using the repository tools available to you. Read the root agent instructions and the complete `{COORDINATION_FOLDER}` protocol. Atomically claim one eligible task using its current blob SHA, execute one bounded deliverable now, commit the result, and close the task as `done` or `blocked`. If no open task exists, create a unique, non-duplicate, bounded task already claimed by you, execute it, and close it in the same invocation. Never leave claimed work unfinished, never force conflicting updates, and never upgrade evidence beyond the repository's trust rules.
