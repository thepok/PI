# T120 S0 strict schema/statistic gate guidance

Status: planned and inactive. This file specifies a future bounded task; it
does not authorize a model call or implementation run.

The future candidate may implement only a pure validation library over bytes,
JSON values, and supplied normalized point records. It must have no knowledge
of BBP terms or recurrence arithmetic and must not read or write files, spawn
processes, access a network, inspect its environment, generate random tests,
store CAS data, or mint receipts.

The controller owns all test inputs and verdicts. `REPORT.md`, stdout, a
self-test, a manifest, a claimed digest, or a candidate-created receipt never
constitutes acceptance. The fixed controller gate must independently bind the
parent spec hashes, invoke each API, recompute every statistic and decision,
and apply every mutation in `CONTROLLER_TESTS.json`.

Strict bytes mean exact bytes, not parse equivalence. Reject duplicate keys,
floats and non-finite tokens, BOM, CRLF, malformed or missing final LF,
whitespace, noncanonical integer strings, excessive size/nesting, and any
raw input that differs from compact sorted-key ASCII JSON plus one LF.

From exactly 256 supplied points, recompute the ten counts, `J`, every
positive-lag `C_l,A_l,Z_l`, the raw maximum same-cell determinant ratio and
lexicographically first witness, and the frozen window-13 decision. Validate
CAS-record and receipt schemas only against controller-supplied bindings. Do
not create or claim that any CAS object or accepted receipt exists.

Only `t120_s0_schema.py` and a concise `REPORT.md` are future deliverables.
No implementation is requested or accepted by this planned specification.
