# Reusable GPT Pro invocation prompt

Work directly in `https://github.com/thepok/PI/tree/pi-core-consolidation` using the repository and GitHub tools available to you.

First read the repository-root `AGENTS.md`, `GOAL.md`, and `VERIFICATION.md`, then read `GPTPro/AGENTS.md` and `GPTPro/README.md`. Follow the file-based coordination protocol exactly: inspect all `GPTPro/Tasks/`, generate a unique agent ID, and atomically claim one highest-priority eligible task by updating that task file against its current Git blob SHA. If the claim conflicts, refetch and select another task.

Complete one bounded task in this invocation. Produce concrete, inspectable output under `GPTPro/Deliverables/<task-id>/`, make any justified repository changes, and run every applicable verification check. Finish by updating the task to `done` or `blocked` with evidence and result paths. Never leave a task merely `claimed`.

If no open task exists, inspect the verified frontier, completed tasks, current workstreams, negative results, and existing deliverables; create one unique, non-duplicate, one-turn-sized high-value task from `GPTPro/Tasks/TEMPLATE.md`, create it already claimed by you, execute it, and finish it in the same invocation.

Do not merely propose work. Do not duplicate an active task. Do not force Git updates. Never treat model output, literature summaries, finite experiments, or a green Lean build as proof of the main claim. Respect all repository trust boundaries, commit the changes to `pi-core-consolidation`, and report exactly what changed, what was verified, and the next unresolved bottleneck.
