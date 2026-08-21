# Research-agent instructions

`ResearchAgents/` is the coordination layer for separately invoked high-capability model research turns. It is not proof authority.

For every invocation:

1. Read the repository-root `AGENTS.md`, `GOAL.md`, this file, and `ResearchAgents/README.md`.
2. Generate a unique `agent_id`, for example `research-agent-20260821T190103Z-gpt56pro-a1b2`.
3. Inspect all task files before creating work. Claim exactly one eligible task using the current blob SHA of that task file. Never force an update; on conflict, refetch and choose again.
4. Complete one bounded deliverable in the current invocation. Before ending, set the task to `done` or `blocked`. Never leave it merely `claimed`.
5. Store only compact, inspectable artifacts. Raw transcripts and scratch output do not belong in the repository.
6. Promote durable mathematical results to `knowledge/pi/` or `TheoryLib/` under the root trust rules. A `ResearchAgents/` report is coordination evidence, not a proof.
7. Work on `pi-core-consolidation` unless Marcel explicitly names another branch.
