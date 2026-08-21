---
id: RA-0001
title: Bootstrap research-agent coordination and map the current repository frontier
status: done
priority: P0
created_at: 2026-08-21T19:01:03Z
created_by: research-agent-20260821T190103Z-gpt56pro-bootstrap
claimed_by: research-agent-20260821T190103Z-gpt56pro-bootstrap
claimed_at: 2026-08-21T19:01:03Z
lease_until: 2026-08-22T19:01:03Z
finished_at: 2026-08-21T19:01:03Z
depends_on: []
result_paths:
  - GPTPro/README.md
  - GPTPro/PROMPT.md
  - GPTPro/Deliverables/RA-0001/README.md
verification:
  - Repository path and trust-boundary audit completed; no Lean source changed.
---

## Objective

Create a low-conflict coordination protocol for future pro-model calls and perform enough repository reconnaissance to seed non-duplicate, high-value tasks.

## Why this is not duplicate work

No independent pro-model coordination layer existed before this task. Existing orchestration under `workflows/` targets sandboxed model runners rather than separately invoked GPT Pro turns.

## Deliverables

- Atomic per-task claim protocol.
- Reusable invocation prompt.
- Compact map of the current verified frontier and open bottlenecks.
- Initial bounded tasks.

## Acceptance checks

- No shared mutable queue/index is introduced.
- Claim races are resolved using task-file blob SHAs without force.
- Every invocation is required to end `done` or `blocked`.
- Mathematical authority remains in `TheoryLib/` and `audit/`.

## Context

- `AGENTS.md`
- `GOAL.md`
- `knowledge/pi/OVERVIEW.md`
- `knowledge/pi/workstreams/pi-quantitative-block-hitting/`
- `TheoryLib.lean`

## Work log

- 2026-08-21T19:01:03Z: Inspected repository guidance, knowledge layout, current overview, verified import surface, and active workstream.
- 2026-08-21T19:01:03Z: Chose one-task-per-file coordination with optimistic concurrency through Git blob SHAs.
- 2026-08-21T19:16:35Z: Coordination was consolidated from `ResearchAgents/` into the user-requested `GPTPro/` hierarchy; concrete results now live under `GPTPro/Deliverables/`.

## Completion summary

The coordination layer is initialized. The reconnaissance report identifies the fixed-orbit relative-cancellation/prescribed-cell steering gap as the central unresolved frontier and seeds tasks that audit exact proof interfaces rather than launching generic exploration.
