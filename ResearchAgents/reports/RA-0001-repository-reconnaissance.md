# RA-0001 repository reconnaissance

Date: 2026-08-21 UTC

This is an operational reconnaissance report. It introduces no new mathematical claim and changes no Lean source.

## Repository trust map

- `TheoryLib/` and the `TheoryLib.lean` import surface are the canonical machine-checked source.
- `audit/AxiomAudit.lean` is the exact axiom gate for research claims.
- `knowledge/pi/` stores durable statements, intermediate and negative results, machine-checked milestone reports, handoffs, and restartable workstreams.
- `workflows/` contains sandboxed model and verification machinery.
- `ResearchAgents/` now coordinates separately invoked pro-model turns. Its tasks and reports are not proof authority.

Any useful mathematical conclusion produced here must be promoted to the appropriate existing location and, for formal claims, pass Lean compilation plus the axiom audit.

## Current research frontier

The repository's current status remains `conjecture`: no verified resolution of decimal disjunctivity for π exists.

The verified core is already broad. The import surface includes, among other lines:

- exact decimal-word and orbit formulations;
- Fourier and finite-cylinder reductions;
- additive fixed-frequency and finite-window gap results;
- recurrent factor-complexity and right-special-factor results;
- Machin/Hutton arithmetic infrastructure;
- the fixed-sixteen-return reduction;
- a machine-checked BBP series identity and forced-orbit infrastructure.

The current overview reports several real advances but repeatedly isolates the same missing type of control:

1. additive cancellation is available, while the target sufficient conditions need relative cancellation at growing scales;
2. first-occurrence/factor-complexity arguments produce gaps involving `p_pi(m)` but do not control the ratio to the required orbit-prefix length `L_m`;
3. arithmetic approximants and CRT structure do not steer the fixed π phase into a prescribed decimal cylinder;
4. the joint-orbit density premise in the fixed-sixteen-return route does not itself prove the required fixed return.

These are related formulations of a fixed-orbit, target-specific steering problem. More infrastructure without an explicit bridge to one of these gaps is likely duplication.

## Existing active workstream

`knowledge/pi/workstreams/pi-quantitative-block-hitting/` contains a substantial `program.json`, `knowledge.jsonl`, `log.jsonl`, director state, and a library directory. Future pro models must inspect this workstream before proposing another quantitative block-hitting campaign. The first useful action is an audit for unpromoted, obsolete, conflicting, or still-live records, not a fresh broad search.

## Coordination decisions

The coordination system uses one task per Markdown file rather than one shared queue. A task claim is an optimistic-concurrency update against that file's current blob SHA. A stale SHA means another model won the claim; force updates are forbidden.

Each invocation owns one primary task and must finish it as `done` or `blocked` in the same turn. This matches the actual execution model: there is no background worker that can safely retain a lease after the response ends.

Reports are compact. Raw transcripts, provider logs, and scratch sandboxes remain disposable. Follow-up tasks are capped to prevent a model from manufacturing a large speculative backlog.

## Seeded next work

- `RA-0002`: extract the smallest exact sufficient-condition frontier from the current verified core to V1.
- `RA-0003`: audit the current quantitative-block-hitting workstream for unpromoted or stale artifacts.
- `RA-0004`: stress-test the appearance-ratio route around the first-occurrence and maximal-entropy theorems.

The intended order is RA-0002 and RA-0003 first. RA-0004 can proceed independently but should consume their findings if they finish earlier.
