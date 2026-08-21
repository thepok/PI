# Task template

Copy this file to a globally unique filename. Remove instructional placeholders before committing.

```yaml
---
id: RA-YYYYMMDDTHHMMSSZ-UNIQUE
title: Precise one-turn objective
status: open
priority: P1
created_at: YYYY-MM-DDTHH:MM:SSZ
created_by: <agent_id-or-marcel>
claimed_by:
claimed_at:
lease_until:
finished_at:
depends_on: []
result_paths: []
verification: []
---
```

## Objective

State one exact question or change.

## Why this is not duplicate work

Name the completed, claimed, and repository work checked before creating this task.

## Deliverables

- One bounded artifact or code change.
- Exact paths to create or update.

## Acceptance checks

- Checks another model can independently run or falsify.
- Required claim/status labels.
- Explicit exclusions.

## Context

Link exact repository files, theorem names, workstream records, or prior task IDs.

## Work log

Add compact timestamped notes only when they change continuation state.

## Completion summary

Fill this before changing the status to `done` or `blocked`. Include the conclusion, evidence, rejected alternatives, verification outcome, and next bottleneck.
