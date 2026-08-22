# T120 S0 strict schema/statistic gate guidance

Status: planned and inactive. This file specifies a future bounded task; it
does not authorize a model call or implementation run.

The future candidate may implement only a pure validation library over bytes,
JSON values, and supplied normalized point records. It must have no knowledge
of BBP terms or recurrence arithmetic and must not read or write files, spawn
processes, access a network, inspect its environment, generate random tests,
store CAS data, or mint receipts.

Every validator returns exactly `None` on acceptance and raises `ValueError`
on rejection. `canonical_json_bytes` returns exact built-in `bytes`;
`decode_canonical_json` returns the parsed JSON value; `recompute_window`
returns a new complete artifact object; and `validate_window_bytes` returns
the decoded complete object only after recomputing and matching every field.
No API may mutate an input, retain cross-call state, or vary across calls.

The controller owns all test inputs and verdicts. `REPORT.md`, stdout, a
self-test, a manifest, a claimed digest, or a candidate-created receipt never
constitutes acceptance. The fixed controller gate must independently bind the
parent spec hashes, invoke each API, recompute every statistic and decision,
and apply every mutation in `CONTROLLER_TESTS.json`.

Only the frozen spec bundle
`fe180d8a5db818d3b4a9b3931779b3cc3d313a2437e9f4db808f3afecba51f98`
and the fourteen exact parent windows are accepted. The controller binds
`TASK_CONTRACT.json` separately, resolves one immutable image ID, passes that
ID into the fixed gate, and requires the isolated pod to execute the same ID.

Strict bytes mean exact bytes, not parse equivalence. Reject duplicate keys,
floats and non-finite tokens, BOM, CRLF, malformed or missing final LF,
whitespace, noncanonical integer strings, excessive size/nesting, and any
raw input that differs from compact sorted-key ASCII JSON plus one LF.
The exact byte, depth, collection, integer-digit, source, report, timeout,
CPU, memory, PID, and tmpfs limits in `TASK_CONTRACT.json` are binding.

From exactly 256 supplied points, recompute the ten counts, `J`, every
positive-lag `C_l,A_l,Z_l`, the raw maximum same-cell determinant ratio and
lexicographically first witness, and the frozen window-13 decision. Validate
CAS-record and receipt schemas only against controller-supplied bindings. Do
not create or claim that any CAS object or accepted receipt exists.

S0 checks that `n` is the exact consecutive metadata sequence for the frozen
window. It cannot establish that otherwise valid supplied `r,w` originated
from T118 at orbit index `N+1`; that is deliberately deferred to the later
disjoint arithmetic verifier. Do not simulate or claim that provenance check.

The exact CAS expected-binding keys are artifact digest, byte size,
experiment, bundle, and window/range. The exact receipt expected-binding keys
add generator/verifier source digests, verifier result, and controller gate
ID as enumerated in `TASK_CONTRACT.json`. Expected bindings have exact key
sets and types; syntactically valid substitute hashes or ranges are rejected.

Only `t120_s0_schema.py` and a concise `REPORT.md` are future deliverables.
That enumeration covers candidate-authored outputs only; controller-created
guidance, inputs, contracts, logs, sandbox state, responses, and archived
attempts remain outside it and confer no authority.
No implementation is requested or accepted by this planned specification.
