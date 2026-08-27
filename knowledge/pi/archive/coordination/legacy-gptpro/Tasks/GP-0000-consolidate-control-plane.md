---
id: GP-0000
title: Consolidate the Pro-model control plane under GPTPro and map the post-T17 frontier
status: done
priority: P0
created_at: 2026-08-21T19:16:35Z
created_by: pro-20260821T191635Z-gpt56pro-consolidation
claimed_by: pro-20260821T191635Z-gpt56pro-consolidation
claimed_at: 2026-08-21T19:16:35Z
lease_until: 2026-08-22T19:16:35Z
finished_at: 2026-08-21T19:16:35Z
depends_on:
  - RA-0001
result_paths:
  - GPTPro/README.md
  - GPTPro/PROMPT.md
  - GPTPro/Deliverables/GP-0000/README.md
verification:
  - Inspected root policies, T9 audit, quantitative-block-hitting program state, and T17 theorem source; no Lean source changed.
---

## Objective

Consolidate the concurrently created research-agent control plane into the user-requested top-level `GPTPro/` directory, name the concrete-results directory `Deliverables/`, preserve the stronger SHA-based claim protocol, and seed exact post-T17 tasks.

## Why this is not duplicate work

RA-0001 created a technically sound control plane under a different temporary name and with generic reports. This task performs a non-destructive logical migration, preserves its completed work and open tasks, and adds the requested concrete deliverable structure plus a sharper post-T17 frontier map.

## Deliverables

- Canonical `GPTPro/` protocol and reusable prompt.
- Migrated RA-0001 through RA-0004 task state.
- `GPTPro/Deliverables/GP-0000/README.md`.
- Focused GP-0001 through GP-0005 tasks.
- Removal of the obsolete temporary compatibility directory after consolidation.

## Acceptance checks

- Exactly one active task queue remains.
- Task claims still use current task-file blob SHAs.
- Existing RA task history is preserved.
- Concrete results live under `GPTPro/Deliverables/`.
- No mathematical claim is upgraded and no Lean source is changed.

## Work log

- 2026-08-21T19:16:35Z: Detected that the branch moved during preparation and inspected the newly added temporary control plane before writing.
- 2026-08-21T19:16:35Z: Adopted its stronger optimistic-concurrency lock rather than creating a second claim mechanism.
- 2026-08-21: Removed the obsolete compatibility directory at Marcel's request; `GPTPro/` is now the sole coordination path.

## Completion summary

The repository has one canonical GPT Pro control plane under the requested name. Existing bootstrap work is preserved, the result folder is `Deliverables/`, the queue includes both broad frontier audits and exact post-T17 theorem tasks, and no legacy coordination directory remains.
