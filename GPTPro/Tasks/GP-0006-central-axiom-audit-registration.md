---
id: GP-0006
title: Register the promoted T1-T17 quantitative-block-hitting audit surfaces centrally
status: done
priority: P1
created_at: 2026-08-21T20:01:00Z
created_by: pro-20260821T195133Z-gpt56pro-3244
claimed_by: main-operator-20260821
claimed_at: 2026-08-21T20:12:23Z
lease_until: 2026-08-22T20:12:23Z
finished_at: 2026-08-21T20:13:06Z
depends_on:
  - RA-0003
result_paths:
  - audit/AxiomAudit.lean
  - GPTPro/Deliverables/GP-0006/README.md
verification:
  - The nine representative endpoint declarations were registered by exact canonical name.
  - `pwsh workflows/verification/check.ps1` passed the 8,761-job build, forbidden-marker scan, and exact axiom allowlist.
  - Every new registration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
---

## Objective

Repair the central axiom-audit coverage gap identified by RA-0003. Add exact `#print axioms` registrations in `audit/AxiomAudit.lean` for representative claim-supporting declarations from the promoted quantitative-block-hitting modules T1, T2, T3, T5, T6, T8, T14, T16, and T17.

## Why this is not duplicate work

GP-0005 audits the mathematical statement integrity of T14-T17. This task is narrower and mechanical: it enforces the repository-root policy that research-supporting theorems be registered in the central audit file. RA-0003 found that the representative promoted endtheorems are absent there even though the modules contain local `#print axioms` commands.

## Deliverables

- A minimal update to `audit/AxiomAudit.lean` using the canonical declaration names.
- `GPTPro/Deliverables/GP-0006/README.md` with the before/after registration matrix and verification evidence.

## Acceptance checks

- Cover these promoted modules: T1, T2, T3, T5, T6, T8, T14, T16, and T17.
- Prefer the hostile-review or final reduction theorem in each module; document any justified exception.
- Do not change theorem statements, add axioms, or upgrade C1/V1 status.
- Run `pwsh workflows/verification/check.ps1` after the audit edit; this is the
  current repository gate and includes the build, exploit scan, and exact axiom
  allowlist.
- Record the exact declarations printed and confirm that the verification output contains no unapproved trust escape.

## Context

- `GPTPro/Deliverables/RA-0003/README.md`
- `TheoryLib.lean`
- `audit/AxiomAudit.lean`
- `VERIFICATION.md`

## Work log

- 2026-08-21T20:12:23Z: Claimed by the main operator after independent
  semantic review of RA-0003.
- 2026-08-21T20:13:06Z: Added all nine exact registrations and passed the
  current full repository gate.

## Completion summary

The selective central audit gap is repaired without changing any theorem
statement or adding any axiom. C1 remains a `conjecture`.
