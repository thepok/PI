# T117 unscaled-Q workflow false positive

Status: `experiment`

Date: 2026-08-21 UTC

## Executive finding

The OpenRouter Ox candidate at
`workflows/state/runs/t117-wave-a-ox-workflow-r0` passed its marker-based
artifact gate and its own 13/13 self-test, but it does not compute the
contracted sampled-BBP rational. Both `shard_generate.py` and
`shard_verify.py` assign the checkpoint partial sum directly as `Q`:

```python
Q = S
```

The canonical quantity is instead
`Q_N = 10^N * bbpPartial(7*N)`. The missing factor changes every reduced
pair and normalized tuple for `N>0`. At `N=4`, the stored tuple digest
`9562c62a...` matches the wrong unscaled tuple; the correct scaled-
`Q_N` tuple digest is `90f02bff...`. Generator/verifier agreement therefore
provided no independent evidence: they shared the decisive bug.

No census output from this candidate is retained or treated as mathematical
evidence.

## Exact guard added

The task contract now defines `S_N=bbpPartial(7*N)` and
`Q_N=10^N*S_N` explicitly and requires both routes to enforce:

- `Q_0 = 47/15`;
- `Q_1 = 16331158360096799798177512637 /
  519836915885323158521118720` in lowest terms;
- a mutation deleting the `10^N` scaling must fail;
- literal-pole verification of every record and both shard endpoints;
- exact `k` and `e` in every compact record;
- independently generable shards, with ordering bound at aggregation.

The completed artifact also had weaker manifest, environment, endpoint,
resource, and mutation bindings than the hardened controller contract. Its
42-shard table, inclusive `47/15` recurrence, and sequential four-pole
checkpoint audit may be used only as implementation ideas after fresh review.

## Boundary

This is a workflow rejection, not a counterexample to K1 or K2. It proves
nothing about cancellation, cell occupancy, density, V1, or decimal-word
occurrence. The normalized census remains unrun pending a genuinely
independent workflow.
