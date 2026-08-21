# GPT Pro instructions

`GPTPro/` coordinates separately invoked high-capability research turns. It is not proof authority.

For every invocation:

1. Read repository-root `AGENTS.md`, `GOAL.md`, `VERIFICATION.md`, this file, and `GPTPro/README.md`.
2. Generate a unique `agent_id`, for example `pro-20260821T191635Z-gpt56pro-a1b2`.
3. Inspect all files in `GPTPro/Tasks/` before creating work. Claim exactly one eligible task by updating that task file against its current Git blob SHA. Never force an update; on conflict, refetch and choose again.
4. Complete one bounded deliverable in the current invocation. Before ending, set the task to `done` or `blocked`. Never leave it merely `claimed`.
5. Put concrete output under `GPTPro/Deliverables/<task-id>/`. Raw transcripts and scratch output do not belong in the repository.
6. Promote durable mathematical results to `knowledge/pi/` or `TheoryLib/` under the root trust rules. A GPTPro deliverable is coordination evidence, not proof authority.
7. Work on `pi-core-consolidation` unless Marcel explicitly names another branch.
