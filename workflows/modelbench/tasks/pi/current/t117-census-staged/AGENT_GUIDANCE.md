# T117 staged census S1 guidance

This task is only the shared structural schema layer. The controller-owned
files in `inputs/` are immutable specifications. Produce only `schema_v1.py`
and `REPORT.md`.

Do not implement or import BBP terms, fractions, sampled sums, Q/F arithmetic,
normalization, gcds, inequalities, checkpoints, shards, manifests, generators,
verifiers, aggregation, subprocesses, networking, or filesystem mutation.
Later stages independently own all mathematics and orchestration.

The required public API is:

- `canonical_json(value) -> str`
- `sha256_hex_obj(value) -> str`
- `validate_contract(document)`: return normally for a valid document and
  raise an exception for invalid input.
- `validate_record(document)`: the same convention for compact and failure
  records from `INTERFACE_V1.json`.

Use only Python's `hashlib`, `json`, `re`, and `typing` modules. Validation
must enforce exact key sets and distinguish JSON integers from booleans. It
also enforces the structural invariants that denominator strings are positive
and a K2 failure tag requires K1. It must not evaluate either inequality.
