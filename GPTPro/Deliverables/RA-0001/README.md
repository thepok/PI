# RA-0001 repository reconnaissance

Claim label: `literature-checked` for repository-state inspection only. This introduces no new mathematical theorem and changes no Lean source.

## Repository trust map

- `TheoryLib/` and the `TheoryLib.lean` import surface are the canonical machine-checked source.
- `audit/AxiomAudit.lean` is the exact axiom gate for research claims.
- `knowledge/pi/` stores durable statements, intermediate and negative results, machine-checked milestone reports, handoffs, and restartable workstreams.
- `workflows/` contains sandboxed model and verification machinery.
- `GPTPro/` coordinates separately invoked pro-model turns and stages concrete deliverables. It is not proof authority.

Any useful mathematical conclusion produced here must be promoted to the appropriate existing location and, for formal claims, pass Lean compilation plus the axiom audit.

## Current research frontier

The repository's current status remains `conjecture`: no verified resolution of decimal disjunctivity for π exists.

The verified core already includes exact decimal-word and orbit formulations, Fourier and finite-cylinder reductions, additive fixed-frequency and finite-window gap results, recurrent factor-complexity and right-special-factor results, Machin/Hutton arithmetic infrastructure, the fixed-sixteen-return reduction, and a machine-checked BBP series identity with forced-orbit infrastructure.

The current overview repeatedly isolates the same missing type of control:

1. additive cancellation is available, while sufficient conditions need relative cancellation at growing scales;
2. first-occurrence/factor-complexity arguments produce gaps involving `p_pi(m)` but do not control the ratio to the required orbit-prefix length `L_m`;
3. arithmetic approximants and CRT structure do not steer the fixed π phase into a prescribed decimal cylinder;
4. the joint-orbit density premise in the fixed-sixteen-return route does not itself prove the required fixed return.

These are related formulations of a fixed-orbit, target-specific steering problem. More infrastructure without an explicit bridge to one of these gaps is likely duplication.

## Existing active workstream

`knowledge/pi/workstreams/pi-quantitative-block-hitting/` contains a substantial `program.json`, `knowledge.jsonl`, `log.jsonl`, director state, and library directory. Future Pro models must inspect this workstream before proposing another quantitative block-hitting campaign. The first useful action is an audit for unpromoted, obsolete, conflicting, or still-live records, not a fresh broad search.

## Coordination decision

The coordination system uses one task per Markdown file rather than one shared queue. A task claim is an optimistic-concurrency update against that file's current blob SHA. A stale SHA means another model won the claim; force updates are forbidden.

Each invocation owns one primary task and must finish it as `done` or `blocked` in the same turn. Concrete outputs live under `GPTPro/Deliverables/<task-id>/`; raw transcripts and scratch sandboxes remain disposable.

## Seeded next work

- `RA-0002`: extract the smallest exact sufficient-condition frontier from the current verified core to V1.
- `RA-0003`: audit the quantitative-block-hitting workstream for unpromoted or stale artifacts.
- `RA-0004`: stress-test the appearance-ratio route.

The intended order is RA-0002 and RA-0003 first. RA-0004 can proceed independently but should consume their findings if they finish earlier.
