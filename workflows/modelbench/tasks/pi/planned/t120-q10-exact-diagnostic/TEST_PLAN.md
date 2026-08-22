# q=10 diagnostic controller test plan

Status: planned and inactive; no implementation or production run has started.

## Static acceptance

1. Freeze and externally bind exact raw bytes of `CONTRACT.json`,
   `INTERFACE.md`, and this file without adding a self-hash.
2. Reject source overlap, cross-imports, dynamic imports, reflection, network
   access, subprocess escape, undeclared files, candidate manifests, and any
   float/decimal arithmetic dependency.
3. Require strict schemas, canonical raw-byte equality after controller
   reserialization, exact key sets/types, and controller-selected job inputs.

## Tiny execution before any production window

Use controller-owned uneven half-open tiny shards `[0,2)`, `[2,7)`, and
`[7,11)`. Execute them in order `2,0,1` so the highest tiny shard succeeds
without predecessor artifacts. Independently reconstruct every point by both
routes and test assembly rejection for a gap, overlap, duplicate, reorder,
range swap, endpoint shift, and missing predecessor-independent state.

Controller-owned synthetic summary vectors must include:

- a passing 256-count vector `(26,26,26,26,26,26,25,25,25,25)`, for which
  `J=6556` and `9J=59004<65536`;
- a failing missing-cell vector `(29,29,29,29,28,28,28,28,28,0)`, for which
  `J=7284` and `9J=65556>65536`;
- a failing vector with every cell present, such as
  `(100,18,18,18,17,17,17,17,17,17)`, demonstrating that failure does not
  imply an empty cell;
- mutations that flip `j10_strict_pass`, alter one count, alter `J`, alter one
  `C_l`, `A_l`, or `Z_l`, violate `J=256+2*sum_l C_l`, violate `C_l<=A_l`, or
  violate `Z_l<=A_l`;
- determinant mutations with a float, zero/negative denominator, unreduced
  replacement for the required raw pair, `num>=den`, wrong cross-product
  maximum, wrong witness/lag/cell, an included diagonal, and
  non-lexicographic tie witness;
- point mutations for `N` versus `N+1`, negative/out-of-range `R`, zero `W`,
  wrong `Int.ediv` cell, `%10` substitution, leading-zero integer strings,
  duplicate/extra JSON keys, CRLF,
  BOM, whitespace, missing final LF, NaN, and parsed-equivalent noncanonical
  bytes;
- digest, experiment ID, spec bundle, source hash, window range, CAS object,
  receipt, controller gate ID, and canonical-source commit substitutions.

Every mutation must be rejected by the controller or independent verifier,
not by a candidate-authored self-test boolean.

## First bounded production check

Only after all static and tiny tests pass, generate and verify contracted
window 13 `[3840,4096)` first, with no lower-window artifact mounted. Compare
both exact routes record-by-record and statistic-by-statistic, then freeze its
CAS object and controller receipt. Stop there for review.

Derive `C_sum=(J-256)/2` and `A_sum=sum_l A_l`. Since `J` is even, the strict
test is equivalent to `J<=7280`, hence `C_sum<=3512`. Apply the following
pre-data decision rule exactly:

1. stop as invalid on any route, byte, T118, identity, or T119 mismatch;
2. stop the local conjecture if `9*J>=65536`, without changing the window or
   threshold;
3. stop and symbolically audit the witness if any distinct-pair `Z_l>0`;
4. continue to the frozen holdout windows 0--12 if the J test passes and
   `A_sum<=3512`;
5. if J passes but `A_sum>3512`, stop the determinant-only route unless the
   operator first freezes one low-complexity, cutoff-independent BBP-specific
   refinement whose displayed summed bound would imply the 3512 target. A
   fitted list of exceptional lags is not eligible.

Do not run windows 0--12, aggregate fourteen windows, inspect a full-census
answer, retune the criterion, or extend the range until the operator reviews
window 13 and records a go decision under the standing PI research mission.
Any eventual output remains an `experiment` only. External publication,
submission, or reviewer contact remains outside this experiment authority.
