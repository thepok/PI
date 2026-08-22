# T120 S0 candidate guidance

Status: `experiment`. Implement only the pure T120 S0 validation library
specified by the controller-owned files under `inputs/`. Produce exactly
`t120_s0_schema.py` and `REPORT.md`; do not create a self-test, manifest, CAS
record, receipt, or any other deliverable.

The copied planned files are frozen provenance snapshots, so their
`planned_inactive_unimplemented`, `active=false`, and `launch_authorized=false`
lifecycle fields intentionally describe the earlier planning state. This
current task activates implementation of S0 only under the standing operator
policy. It changes none of their API, trust, arithmetic, or claim boundaries
and does not authorize a production experiment.

The Python module must expose exactly the seven non-underscore callables in
`inputs/s0/TASK_CONTRACT.json`. Follow their exact return and `ValueError`
conventions, canonical-byte rules, schemas, frozen windows, resource limits,
and integer-only recomputation requirements. Inputs are immutable copies for
reference. Editing or echoing them, printing a pass marker, or claiming a
digest confers no acceptance authority; the fixed controller owns all hidden
fixtures, mutations, expected values, and the verdict.

Keep module structure deliberately plain: imports, immutable scalar/tuple
constants, ordinary undecorated function/class definitions, and docstrings
only. Do not use decorators, comprehensions or calls at module scope,
`getattr`, `hasattr`, `sys`, or computed/mutable module state. The frozen
two-million-digit integer-string boundary exceeds Python's default `int()`
conversion limit. Parse long canonical decimal strings manually in fixed
chunks small enough for `int(chunk)` (for example nine digits), accumulating
with a literal integer base; do not change interpreter-global limits.

This stage must not implement BBP terms, T118 arithmetic, point provenance,
production windows, filesystem or CAS writes, receipt minting, subprocesses,
network access, reflection, randomness, floats, or environment-dependent
behavior. The supplied `n` sequence is metadata only: S0 does not authenticate
that supplied `r,w` came from T118 at orbit `N+1`.

`REPORT.md` must begin with the literal text **Status: `experiment`** and
describe only this S0 validation surface. Include this exact sentence without
added punctuation inside the phrase: **T118 `r,w` provenance is deferred to a
later disjoint arithmetic verifier.** Do not use the standalone words `PASS`,
`passed`, or `pass`, and do not claim that any test, gate, or controller
accepted the artifact. Also avoid spelling the phrases `production result`,
`production outcome`, or `production window`, even as a negated non-claim.
Describe the scope positively as validation-only. Do not claim an existing CAS
object or accepted receipt, a J10 outcome, occupancy, density, cancellation,
V1, decimal occurrence, or any result about Pi.
