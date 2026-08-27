# T117 census stop, q=10 diagnostic, and T119 direction

Date: 2026-08-22 UTC

Status: `machine-checked` (T119) and `experiment` (planned finite q=10 diagnostic)

## Direction decision

Stop the K1/K2-only census after the committed S1 schema foundation. Do not
build S2 or run the 42-shard census merely to classify
`k^2 <= e` or `k^2 <= d*e`. Those inequalities are finite, indirect
diagnostics; generic counterexamples already show that neither follows from
reduced-pair algebra alone, and finite survival would prove no orbit-wide
statement. S1 remains useful as controller-owned strict JSON, canonical
serialization, and hashing infrastructure.

Any new computation must instead be a small exact diagnostic of the canonical
T118 normalized residue/cell representation. For a finite half-open window
`W` of length `L`, let `n_c` be the number of sampled successors in decimal
cell `c` and set

`J_10(W) = sum_{c=0}^9 n_c^2`.

If a decimal cell is absent, Cauchy--Schwarz gives
`J_10(W) >= L^2/9`. Thus the exact integer test `9*J_10(W) < L^2` certifies
all ten cells only inside that finite window.

## Frozen continue/stop criteria

Run no q=10 diagnostic until canonical T118 and T119 exist and the full
repository gate passes with both. A run must reconstruct the T118 signed
numerator, positive denominator, Euclidean remainder, and cell by two
independent exact routes; any mismatch invalidates the run.

Use the preregistered fourteen consecutive 256-index windows covering
`[512,4096)`, without moving boundaries or tuning the threshold after seeing
data. Continue from the diagnostic to a new proof task only if all of the
following hold:

1. every route agrees on every exact input and cell;
2. every window satisfies the frozen strict test `9*J_10(W) < 256^2`;
3. the result suggests a cutoff-independent, Lean-shaped mechanism controlling
   actual sampled-BBP transitions, same-cell multiplicity, or a signed
   exponential sum, rather than another denominator or occupancy histogram.

Stop the route on the first replay discrepancy or failed frozen window. Also
stop after a fully surviving finite run if no stronger symbolic mechanism is
identified: finite full occupancy is still only an `experiment`, and extending
the cutoff is not a substitute for a theorem.

### Window-13 calibration rule

For a 256-point window, let

`C_sum = sum_{l=1}^{255} C_l = (J-256)/2`

count distinct same-cell pairs once, and let

`A_sum = sum_{l=1}^{255} A_l`

count pairs satisfying T119's necessary near-determinant inequality. Since
`J` has the parity of 256, `9*J<65536` is equivalent to `J<=7280`, hence
`C_sum<=3512`. T119 implies `C_sum<=A_sum`, so `A_sum<=3512` is the decisive
signal that the determinant condition alone is selective enough to imply the
finite collision threshold.

Run window 13 first and freeze its controller receipt before seeing any other
production window. Stop as invalid on any exact-route, byte, identity, T118,
or T119 mismatch. Stop the local conjecture if `9*J>=65536`. If any distinct
pair has determinant zero, stop the production wave and audit that exact
rational-phase repeat symbolically. If the J test passes and `A_sum<=3512`,
continue to windows 0--12 as a frozen holdout. If J passes but `A_sum>3512`,
stop the determinant-only route unless exactly one low-complexity,
cutoff-independent BBP refinement is frozen before opening the holdout and its
summed target would imply 3512. Never fit a list of exceptional lags.

Finite occupancy, balanced histograms, random-looking counts, or repeated
passes are not decision evidence by themselves. After all fourteen windows,
pursue a symbolic pair-count theorem only if every J test passes and either
every `A_sum<=3512` or the single preregistered refinement survives every
holdout window.

### Smallest safe implementation split

No existing workflow is safe to promote wholesale. Reuse only the hardened
controller patterns: networkless read-only pods, declared-artifact copying,
frozen fixture hashes, and controller-owned mutation tests. Implement T120 in
four separately gated stages:

1. a controller-only strict-byte/schema/statistic/CAS/receipt gate with no BBP
   production arithmetic;
2. a generator-only combined-term exact CLI for uneven tiny ranges;
3. a physically separate verifier-only literal-four-pole exact CLI;
4. controller orchestration over minimal disjoint pod inputs, highest tiny
   shard first, then window 13 only.

Existing runner hashes are provenance, not a CAS receipt; existing canonical
JSON accepts forbidden inputs; T117 candidate self-tests are insufficient;
and T116 code is monolithic and fixed below the T120 production range. These
are implementation hazards, not reusable assurances.

## Canonical T119: same-cell cross determinant

Status: `machine-checked`. Six independent candidates passed the isolated gate.
The selected Oxzen candidate was independently source-audited, integrated as
canonical T119, registered in the central axiom audit, and passed the full
repository verification gate.

For positive integers `q,W_N,W_M`, if two normalized residues occupy the same
half-open q-cell `a`, then elementary interval arithmetic should give

`q * |R_N*W_M - R_M*W_N| < W_N*W_M`.

The canonical T119 module first proves this generic integer interval lemma and
then specializes it using T118's exact endpoint-safe cell equivalence for two
sampled successors. The specialization is deliberately conditional on both
successors being in the same explicitly named cell. It does not prove that
such indices exist or repeat, nor does it bound how many same-cell pairs occur.

The controller contract is retained as provenance at
`workflows/modelbench/tasks/pi/planned/t119-same-cell-cross-determinant/TASK_CONTRACT.json`.
Its task definition was activated only after canonical T118 passed the full
gate. The accepted theorem and verification evidence are recorded in
`knowledge/pi/results/machine-checked/t119_sampled_bbp_same_cell_cross_determinant_20260822.md`.
The q=10 diagnostic now remains blocked only on completion of its staged
controller implementation and trust gates.

## ChatGPT Pro architecture audit

Status: `proof sketch` workflow audit, not a code-verification result.

An independent ChatGPT Pro review agreed that the proposed staged experiment
can be sound for a finite computation, but only with a controller-owned,
noncircular artifact graph and immutable byte authority. The review audited an
older pushed branch head rather than the later local S1/T118 changes, so its
findings are design requirements, not evidence that current code implements
them.

If the q=10 diagnostic pipeline is built, it must additionally:

- bind a new experiment identity, exact math specification, and shard plan;
- define shard `[a,b)` from exact endpoint states `P_a` and `P_b`, with records
  only `a..b-1` and no trusted intermediate prefix;
- run the combined and literal arithmetic routes in physically disjoint,
  allowlisted, networkless images rather than rely on import bans;
- ingest exited candidate outputs into controller-owned content-addressed
  storage before verification, and mint controller-authenticated receipts over
  those same immutable bytes to eliminate verify-then-copy races;
- require canonical raw JSON bytes (including duplicate-key, BOM, CRLF,
  missing-final-newline, integer-grammar, size, and nesting rejection), not
  merely equivalence after parsing;
- exercise non-null failure/equality paths with synthetic vectors, use an
  uneven two-shard tiny run, and run the highest production shard first in
  isolation before any full production wave;
- keep aggregation selection-only: it may select the earliest
  controller-verified projection, never recalculate or classify a law.

Prompt SHA-256:
`1b2cd730597f88b477235ada702812c276e0798d0a98f2e5f48bb67409d021fe`.
Response SHA-256:
`0e69e8d483934d2e649aa0d0c0258329c5093c33f6dc41102214a746e61086c1`.
The Pro browser job completed normally and required no re-login.

## Claim firewall

T118 and machine-checked T119 are representation-only interfaces. The q=10
calculation, if run, remains an `experiment`. Nothing here proves an
arbitrarily-late cell hit, recurrence,
occupancy beyond a checked finite window, density, Weyl cancellation,
normality, decimal-block occurrence, V1, or a resolution of the Pi problem.
