# q=10 exact diagnostic interface

Status: `experiment` specification; inactive and unimplemented.

The controller owns the experiment ID, the three frozen specification files,
the external spec binding, CAS, receipts, process isolation, execution order,
and final aggregation. Candidate code never chooses ranges, hashes, or pass
criteria.

## Exact arithmetic interface

For every record index `N`, reconstruct canonical T118 data
`Q_N,F_N,H_N,d_N,e_N,X_N,k_N,W_N,R_N` for the successor orbit point
`sampledBBPOrbit (N+1)`. Store only `n,r,w,cell`, with

`cell = Int.ediv (10*R_N) W_N`.

Both routes must establish `0<=R_N<W_N`, `0<=cell<10`, and `W_N>0`.
Neither `%10` nor floating-point/decimal evaluation is an equivalent cell
interface.

The verifier must independently reproduce the full T118 construction before
comparing the stored projection. It must not infer `R` or `W` from generator
intermediates. Canonical T119 supplies the checked conditional inequality for
same-cell pairs; it does not replace exact recomputation.

Each production artifact contains exactly one contracted 256-index window,
256 ordered point records, exact `n0` through `n9`, `J`, the strict-test
boolean, 255 lag-ordered records `(l,C_l,A_l,Z_l)` for `l=1..255`, and the exact maximum
same-cell determinant ratio with its deterministic witness. Here

- `C_l` counts same-cell pairs `(N,N+l)` once;
- `A_l` counts all pairs with `10*|Delta|<W_N*W_(N+l)`;
- `Z_l` counts all pairs with `Delta=0`.

The controller derives and enforces `C_0=256` separately; it is not a lag-array record.
It also enforces
`J=C_0+2*sum_{l=1}^{255} C_l`, `C_l<=A_l`, and `Z_l<=A_l`.
The stored maximum omits diagonals and keeps the raw exact numerator and
denominator `10*|Delta|, W_N*W_M`; it is not replaced by a float or a reduced
surrogate. All ratio comparisons use integer cross multiplication.

## Process and artifact interface

- Generator input: controller-created job bytes binding experiment/spec digest,
  window index, exact range, canonical T118/T119 source commits, and generator
  source digest.
- Generator output: one canonical raw JSON artifact; stdout is diagnostic only.
- Verifier input: a controller CAS copy of the generator bytes plus a separate
  controller-created job binding the verifier source digest.
- Verifier output: a structured result to the controller. Only the controller
  may convert a successful result into an immutable receipt.
- Aggregate input: exactly fourteen controller receipts and their CAS objects,
  ordered by numeric window index with no missing, duplicate, or swapped range.

Generator and verifier source directories must be disjoint. Neither may import,
read, execute, hash, or introspect the other. Shared code is limited to
controller-frozen serialization/schema primitives that contain no BBP,
normalization, cell, lag, determinant, or pass/fail arithmetic.

The external binding is noncircular: it hashes the already-frozen raw spec
files; those files do not contain their own hash. Controller receipts bind the
external digest and source/artifact digests. A candidate-written manifest,
self-test flag, or `VERIFIED` string has no authority.

No CLI or source implementation is specified or accepted yet.

The strict gate has one-way finite meaning: `9J<65536` certifies all ten cells
inside that window. Failure rejects this stronger test but does not prove an
empty cell. No statistic is interpreted across window boundaries.
