Status: `experiment`

# T120 S0 validation library report

`t120_s0_schema.py` implements the bounded pure validation library
specified by `inputs/s0/TASK_CONTRACT.json`. It exposes exactly the seven
contracted non-underscore callables and nothing else.

1. `canonical_json_bytes(value)` — returns built-in bytes containing compact
   sorted-key ensure_ascii ASCII JSON plus exactly one final LF; rejects
   values outside the exact built-in `None`/`bool`/`int`/`str`/`list`/`dict`
   domain and enforces the frozen nesting-depth, collection-size, and
   integer-digit limits.
2. `decode_canonical_json(raw)` — accepts exact built-in bytes only;
   requires UTF-8 without BOM, LF-only line endings, exactly one final LF,
   no duplicate keys, no float or non-finite numeric tokens, and byte-exact
   equality with the canonical reserialization within the frozen size
   limits; returns the parsed value.
3. `validate_point(value, expected_n)` — checks the exact point key set,
   integer-not-boolean fields `n` and `cell`, canonical nonnegative decimal
   strings for `r` and `w`, and the laws `n == expected_n`, `w > 0`,
   `0 <= r < w`, `cell == (10*r)//w`, and `0 <= cell < 10`.
4. `recompute_window(points, window_index, start_n, end_exclusive_n,
   spec_bundle_sha256)` — binds its arguments to one of the fourteen frozen
   window rows together with the single frozen specification-bundle digest,
   requires exactly 256 ordered points carrying consecutive `n` metadata,
   and returns a newly allocated complete window artifact whose derived
   fields are recomputed by integer-only arithmetic: the ten cell counts
   `n0..n9` summing to 256, `J` as the sum of squared cell counts, the
   boolean outcome of the frozen threshold `9*J < 65536`, the 255 ordered
   lag records `(lag, C_l, A_l, Z_l)` for l = 1..255, the raw maximum
   same-cell determinant ratio `num = 10*abs(r_N*w_M - r_M*w_N)` and
   `den = w_N*w_M` over distinct same-cell pairs with the lexicographically
   first witness under integer cross multiplication, and the decision
   object under the frozen priority rule.
5. `validate_window_bytes(raw, ...)` — decodes strictly, checks the
   complete stored schema field-by-field, independently recomputes every
   derived field from the stored points, and returns the decoded object
   only after type-exact equality of every stored field with that
   recomputation.
6. `validate_cas_record(value, expected_bindings)` — checks the exact CAS
   record schema and constants, lowercase 64-hex digest fields, nonnegative
   integer fields, the exact expected-binding key set and types, and exact
   agreement of every binding.
7. `validate_receipt(value, expected_bindings)` — checks the exact receipt
   schema and constants, four lowercase 64-hex digest fields, the exact
   expected-binding key set and types, and exact agreement of every
   binding.

Every validator returns exactly `None` on acceptance and raises
`ValueError` on rejection. All seven functions are deterministic, never mutate a
supplied value, and retain no state between calls.

## Deferred determination

This library checks only that a supplied window carries the exact
consecutive `n` metadata of one frozen window row. It does not determine
whether supplied `r,w` values originate from T118 at orbit index `N+1`;
that determination is deferred to a later disjoint arithmetic verifier and
is neither performed nor approximated here.

## Boundary statement

The module is pure: it performs no filesystem writes, subprocesses,
network access, dynamic imports, reflection, randomness, floating-point
arithmetic, or environment inspection, and it creates no stored objects or
records of any kind. This report describes only the implemented validation
surface listed above and establishes nothing beyond it.
