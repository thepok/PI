# T66 terminality-dropped live-SCC experiment

Status: `experiment`. Every conclusion in this package is finite experimental
evidence only.

## Provenance and scope

The canonical statement is vendored byte-for-byte as
`pi-positive-decimal-factor-entropy.txt`. Its SHA-256 is
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
The problem was formulated locally and has no external source URL.

The canonical question asks whether the decimal factor complexity of pi has
one uniformly positive exponential rate at all sufficiently large lengths.
T66 does not evaluate pi digits. It evaluates finitely many instances of the
T48 carry/KMP sibling graph used by the conditional C6 route. It proves
neither the uniform linear-depth hypothesis nor C6 nor C1.

## Normalized finite task

For a nonempty decimal word `w` and depth `R >= 0`, the declared T48 states are
the synthetic root and tuples

```text
(k_0,...,k_R; c_0,...,c_(R-1)),
```

where each `k_i` is a proper-prefix KMP state of `w` and each endpoint-complete
carry is in `[-1,16]`. Thus the declared count is

```text
1 + |w|^(R+1) * 18^R.
```

A digit column satisfies T48's exact recurrence

```text
16*d_j + c'_j = d_(j+1) + 10*c_j.
```

An edge is rejected if any coordinate completes `w`. Initial labels include
the starting carry tuple and digit column; later labels include the digit
column. Distinct labels remain distinct edges.

For every completed reachable graph, T66 computes T46 reachability, liveness,
cyclicity, and SCCs. It evaluates T65's relaxed condition on every cyclic
reachable-live SCC:

1. Every state has exactly one reachable-live edge staying in that SCC.
2. Reachable-live edges with the same source and projected label have the same
   target.

T65 omits T46 terminality. T66 therefore never tests or requires that a live
edge remain in its source SCC. Projected determinism is structural for T48's
partial transition function, but T66 still recomputes and records it.

## Quantifiers and edge cases

The baseline means exactly the 16 T52 rows whose reachable graphs completed.
T52's capped depth-3 row is not silently promoted into the baseline.

The extension is predeclared in `instances.json`. After the baseline, it uses
word-major then depth-major order: one-digit words `0` through `9`, each at
depths `1`, `2`, and `3`, omitting pairs already in the baseline. Results do
not affect later instance selection.

The state cap is 2,500 discovered states per instance and the wall-time cap is
120 seconds per instance. A completed row is issued only after every label of
every reachable state has been exhausted and certificate analysis has
finished. A cap produces a `resource_frontier` row with null reachable count,
reachable-live count, certificate, witness, and finite experimental verdict.

## Exact imported conventions

`t52_experiment.py` is a byte-exact copy of the accepted T52 graph generator.
`T46T46LiveSCC.lean`, `T48EndpointCarryKMP.lean`, and
`T65RationalCoreCertificate.lean` are byte-exact copies of the kernel-checked
sources. `instances.json` pins all four hashes and names T65's theorem
`relaxedLiveSCCCriterion_iff_internal_and_projected_determinism`.

The experiment does not claim a new Lean theorem. The Lean files are included
to make graph and predicate drift inspectable; replay verifies their hashes.

## Certificates and witnesses

Every completed row contains `t65_relaxed_certificate`. It records the exact
reachable and reachable-live counts and hashes, the live SCC partition hash,
and a per-state table for every cyclic reachable-live SCC. Each state row
records all internal edge IDs, the internal uniqueness Boolean, all
reachable-live outgoing labels through a target-table hash, and the projected
determinism Boolean.

Every failing row contains `violating_recurrent_scc_witness`. An
`internal_cycle_violation` gives the entire recurrent SCC, a root-to-branch
path, all internal edges at the branch, and two distinct internal edges each
completed to a closed walk in the SCC. The evaluator also supports a
`projected_determinism_violation` witness with equal-labelled edges to distinct
live targets and explicit continuations to cycles. No such projected failure
occurred in this run.

Replay rebuilds each graph, validates every T48 edge equation and KMP step,
recomputes all live/SCC tables, validates each displayed path and closed walk,
and compares regenerated JSON and CSV byte-for-byte.

## One-command replay

From a directory containing only these artifacts, run:

```sh
sh ./verify.sh
```

No network access, nonstandard Python package, random seed, or repository path
is used.

## Finite results

| Cohort | Completed | T65 pass | T65 failure | Resource frontier |
|---|---:|---:|---:|---:|
| T52 completed baseline | 16 | 0 | 16 | 0 |
| Deterministic extension | 18 | 0 | 18 | 10 |

All 34 completed instances fail through internal branching in a cyclic
reachable-live SCC. Projected-label determinism passes throughout. The ten
depth-3 one-digit instances stop at the 2,500-state cap and receive no graph or
mathematical classification.

This is evidence that merely dropping terminality does not remove the finite
obstructions in these cases. It does not show that every word or every depth
fails T65, does not determine a uniform depth bound, and does not prove or
disprove the uniform linear-depth hypothesis, C6, C1, or positive decimal
factor entropy for pi.

## Files

- `t66_experiment.py`: T65 classifier, certificates, witnesses, and replay.
- `t52_experiment.py`: byte-exact imported T48 finite graph generator.
- `instances.json`: immutable order, caps, and source hashes.
- `results.json`: detailed finite output and replay objects.
- `instance_table.csv`: compact classifications and state counts.
- `verify.sh`: one-command artifact-only replay.
- `replay_output.txt`: captured raw output of the replay command.
- `T46T46LiveSCC.lean`: kernel-checked graph predicate source.
- `T48EndpointCarryKMP.lean`: kernel-checked graph convention source.
- `T65RationalCoreCertificate.lean`: kernel-checked relaxed criterion source.
- `pi-positive-decimal-factor-entropy.txt`: canonical statement.
- `SHA256SUMS`: artifact integrity manifest.
