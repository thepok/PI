# Next Evolution controlled trial v1

Status: **aborted safely after a material invariant failure**. The durable operator pause is active. This is an architecture trial report, not a mathematical claim.

## Dispatches

1. `todo:theory-pi-lacunary-near-return-sparsity:t189`, retry 0: Terra execution, bounded graph packet (10 records, 19,922 bytes, SHA-256 `b75d638af6eb33f5750d176f45efeba1a644f8023c407c8bdf289f0a89e5ecab`), deterministic gate, Fixed-π Sol review, reviewed result, ledger incorporation, graph projection, and v2 telemetry all ran.
2. The same todo, retry 1: Terra execution started with a fresh 10-record packet (19,646 bytes) and was terminated by the operator pause after the invariant failure. It is interrupted work, not a result.
3. Not dispatched.

The hard cap worked: no fourth dispatch occurred.

## Correct behavior observed

- Director routing was medium-effort Terra preparation followed by high-effort Sol decision.
- Builder routing was Terra-only.
- Fixed-π review routed to Sol after deterministic gating.
- A proposed parallel successor depending on unfinished T189 was rejected mechanically.
- No trusted verifier receipt or proof label was created by the knowledge projector.
- Phase telemetry recovered execution and review token/cache counts from the actual microstep traces.

## Material failure and correction

The T189 r0 reviewer returned `revise` for a mistranscribed theorem hypothesis and inaccurate page locators, while using the broad `failure_cause=mathematical` bucket. The first projector policy treated any mathematical `revise` or `reject` as a durable obstruction and therefore created an active obstruction for a repairable citation delivery.

The trial was stopped immediately. Corrections are append-only:

- `knowledge/corrections/t189-projection-correction-v1.json` supersedes the erroneous T189 obstruction interpretation.
- `knowledge/corrections/revise-obstruction-lifecycle-v1.json` supersedes the four other still-active historical revise-derived obstruction interpretations.
- Live projection and future snapshot generation now require a terminal `reject` before automatically creating a durable mathematical obstruction.
- Retrieval computes the effective lifecycle through `supersedes` edges while retaining the originally declared lifecycle for audit.

The post-correction knowledge audit passed. A fresh three-item trial is required before deployment can be called validated.
