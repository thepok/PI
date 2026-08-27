# Operator pause handoff — 2026-08-10 UTC

The research system was stopped at Marcel's explicit request.

- Durable guard: `.research/OPERATOR_PAUSED` exists. The official launcher
  was replayed and correctly refused to start research.
- Supervisor: `allmath-research-orchestrator.service` is `inactive (dead)`
  with `MainPID=0` and successful stop result.
- Surviving work: stopping the service alone left workflow parents alive
  because the service uses `KillMode=process`. Those exact T136 builder and
  director workflow parents, their worker containers, and the regenerated
  microstep containers were separately terminated. A delayed inspection found
  no matching research supervisor, workflow parent, OpenCode worker, or
  AllMath research pod.
- The operational root cause is repaired by
  `scripts/pause-research-orchestrator.sh`. Ordinary supervisor restarts still
  preserve workers as designed, while an explicit pause now installs the
  durable guard, requests the loop's authoritative record-based cleanup,
  performs a bounded orphan sweep, removes the consumable stopfile, and
  verifies supervisor quiescence. Its live cleanup-only replay passed while
  paused, and the full orchestration regression suite passed with
  `358 passed, 2 xfailed`.
- T135 produced an independent skeptic JSON with verdict `accept` just before
  the pause, but the supervisor did not project it into `program.json` before
  stopping. Reconcile that completed result on resume; do not rerun it merely
  because T135 still appears `active` in the program snapshot.
- T136 was interrupted during builder verification. Its internal artifact
  verifier had passed, but no builder result or independent skeptic result was
  completed. Treat its record and `active` program status as stale interrupted
  state, not as an accepted result.
- The concurrent director was interrupted during proposal delivery. Any
  partial proposal is untrusted and must not be scheduled without normal
  validation after resume.

The Ultrapi cross-program intake is recorded separately in
`ULTRAPI_INTEGRATION_2026-08-10.md` and linked from `DIRECTION.md`.
