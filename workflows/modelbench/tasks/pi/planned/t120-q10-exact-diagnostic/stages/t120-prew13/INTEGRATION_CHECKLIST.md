# T120 tiny-controller integration checklist

Status: planned and inactive. This checklist cannot authorize production.

Any S1/S2/third-route controller patch is rejected unless it preserves commit
`706eb15aece38b229e198d66f8bbc8fdd01f3667` as its arithmetic-contract base
and independently rechecks the frozen parent, S1, S2, PREW13, S0, and
T74/T77/T98/T106/T113/T118/T119 raw hashes.

## Trusted structure

- Controller gate, third-route oracle, hidden harness, tests, and runner
  bindings are distinct controller-owned files.
- The runner noncircularly binds every controller source byte and records the
  resulting bundle digest, immutable image ID, candidate source digest, job
  digest, artifact digest, fixture seed, and gate outcome.
- Controller files are copied, rehashed, and executed from the exact snapshot.
  Candidate and output bytes are rechecked after every isolated process exits.
- S1, S2, and the third route have disjoint source roots, images, mounts, and
  arithmetic. S2 sees only controller-ingested S1 bytes after S1 exits.

## Static and capability rejection

S1 must expose only `t120_s1_generator.py` and `REPORT.md`, implement the
frozen combined `b_k/P_N/Q_N/F_N` route, reconstruct from term zero, and reject
literal poles, checkpoints, expected-answer tables, arbitrary reads, dynamic
imports, reflection, subprocesses, network, time/random/environment input, and
controller/S2/oracle access.

S2 must expose only `literal_four_pole_verifier.py` and `REPORT.md`, implement
the four frozen literal poles with custom normalized signed numerator/positive
denominator gcd arithmetic and the exact `10^(N+1)` forcing scale, and reject
`Fraction`, the combined identity, shared helpers, expected tables, unscaled
forcing, and S1 source/runtime access.

Alias-aware AST checks must reject `__import__`, `getattr`, `globals`, `locals`,
`eval`, `exec`, `compile`, `sys.modules`, `importlib`, serialized code loading,
and undeclared paths. Substring-only screening is insufficient.

## Isolation and hidden evidence

- Accept only `[7,11)`, `[0,2)`, `[2,7)` in that order. The first shard has no
  predecessor artifact or checkpoint. No job contains endpoint states,
  expected points, arithmetic, statistics, decisions, or receipts.
- Use only immutable lowercase 64-hex image IDs with no network, read-only root,
  dropped capabilities, no-new-privileges, and frozen PID/CPU/RSS/time/tmpfs
  limits. Mutable tags, host source trees, shared caches, or sibling sources are
  blockers.
- Require point-by-point agreement of S1, S2, and the controller-owned global-
  LCM integer-lift route. Mutate indices/endpoints, Q/F scales, every pole,
  gcd/remainder/cell handling, shard order/coverage, digests, jobs, sources, and
  images.
- Controller-hidden synthetic 256-point fixtures must exercise both candidate
  statistic hooks: counts, J, all 255 C/A/Z rows, internal non-emitted C0=256,
  raw maximum ratio by cross multiplication, lexicographically first tie,
  identities, every decision branch and precedence, strict bytes, and mutation
  rejection. `window13_action` is inert outside index 13.
- Candidate stdout, reports, self-tests, manifests, booleans, hashes, verdicts,
  CAS records, or receipts never influence acceptance.

## Production firewall

Reject any patch that dispatches an index in `[512,4096)`, enables
`future_window_256`, mints a production CAS object or receipt, activates
PREW13, sets `window13_authorized=true`, or treats finite agreement as a PI
claim. Successful tiny gates remain `experiment` evidence and stop at readiness
for later operator review.
