# T52 endpoint-complete carry/KMP experiment

Status: `experiment`.

## Provenance and scope

The canonical statement is vendored byte-for-byte as
`pi-positive-decimal-factor-entropy.txt`. Its required SHA-256 is
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
The question was formulated locally, so it has no external source URL.

The canonical question asks whether one fixed `eta > 0` gives
`p_pi(n) >= 10^(eta*n)` for every sufficiently large `n`. T52 instead studies
fixed finite instances of the sibling T44/T48 invariant-core route to C6. It
does not prove the universal linear finite-core hypothesis, C6, positive
decimal factor entropy for pi, or decimal disjunctivity.

## One-command replay

From a directory containing only the delivered artifacts, run:

```sh
sh ./verify.sh
```

This regenerates `results.json`, `instance_table.csv`, and `t38_overlap.json`
in a temporary artifact-only directory, compares them byte-for-byte, and then
rechecks all transitions, tables, SCC verdicts, and witnesses.

## Exact graph convention

For a nonempty decimal word `w` and depth `R`, raw states are

```text
(k_0,...,k_R; c_0,...,c_(R-1)),
```

where each `k_i` is a proper-prefix KMP state of `w` and every carry is in the
endpoint-complete interval `[-1,16]`. The declared graph has

```text
1 + |w|^(R+1) * 18^R
```

states, including T48's synthetic root. A most-significant-first digit column
`d_0,...,d_R` gives the exact recurrence

```text
16*d_j + c'_j = d_(j+1) + 10*c_j.
```

Completing `w` in any KMP coordinate rejects the edge. The initial edge label
records the entire starting carry tuple; later labels record the digit column.
Distinct labels are distinct edges even when their endpoints agree.

The evaluator is lazy only in state discovery: once a state is reachable, all
of its labels are exhausted before a completed verdict is issued. Therefore a
completed reachable graph is exact. A state-cap or time-cap interruption is
reported as `resource_frontier` with `criterion_boolean`, witness, and
mathematical verdict all null.

## Boolean certificate and witnesses

For a completed graph, replay computes exact reachable, live, cyclic, and SCC
tables. It then evaluates T46's condition on every cyclic reachable-live SCC:

1. no live edge may leave that SCC;
2. every state has exactly one labelled live edge remaining in that SCC.

T48 machine-checks that this Boolean criterion is equivalent to finiteness of
the fixed endpoint-safe core. The experiment does not re-prove T48. Positive
rows, if any, are accepted only through this complete Boolean check. Every
negative row contains one replay-checked witness:

- `branching_cyclic_scc`: two distinct labelled internal edges, each completed
  to a closed walk, plus a path from the synthetic root;
- `nonterminal_delay_corridor`: a live edge leaving a cyclic SCC, a path from
  the root, and a continuation from the target to a displayed cycle.

These are fixed-instance conclusions only. No trend is extrapolated.

The exact machine-checked dependencies are vendored as
`T46T46LiveSCC.lean` and `T48EndpointCarryKMP.lean`. Replay verifies their
source hashes from `instances.json`; that manifest also names the imported
theorems and records the prior allowed-axiom kernel-gate receipt. This T52
experiment claims no new Lean theorem.

## Deterministic order and caps

`instances.json` fixes the order: all ten length-one words at `R=0` form the
small complete baseline, followed by selected `R=1`, `R=2`, and `R=3` resource-probe
instances. Every instance has a hard cap of 2,500 discovered states and 120
seconds. A process-level alarm covers graph generation, SCC analysis, and
witness/certificate construction. Any alarm discards all tables and produces a
null-verdict resource-frontier row. Wall time is neither recorded nor used in
completed tables.

## T38 reconciliation

`t38_overlap.json` contains only two structural overlap checks, not T38's
entropy-gap table or tau table. At `R=1`, T38's state
`(carry,leftKMP,rightKMP)` and label `(a,b)` coincide with the induced T48 raw
subgraph after restricting carries to `[0,15]` and omitting T48's synthetic
root. The carry orientation is unchanged:

```text
16*a + carry_right = b + 10*carry_left.
```

Full T48 is deliberately larger: carries `-1` and `16` retain the two decimal
expansions of circle endpoints. T38 explicitly made no endpoint claim. Replay
imports the byte-exact vendored `t38_experiment.py`, checks its source hash,
and compares its graph with an independent restricted-T48 construction. It
requires equality of their complete labelled edge sets and derives all
reported structural fields directly from those graphs.

## Files

- `t52_experiment.py`: generator and exact verifier.
- `instances.json`: deterministic order, caps, and compact T38 fixtures.
- `results.json`: detailed counts, KMP data, Boolean tables, and witnesses.
- `instance_table.csv`: compact result table.
- `t38_overlap.json`: convention-normalized structural overlap checks.
- `t38_experiment.py`: byte-exact T38 source used only for overlap replay.
- `T46T46LiveSCC.lean`: byte-exact machine-checked criterion dependency.
- `T48EndpointCarryKMP.lean`: byte-exact machine-checked graph dependency.
- `pi-positive-decimal-factor-entropy.txt`: byte-exact canonical statement.
- `replay_output.txt`: raw output from the delivered replay command.
- `verify.sh`: one-command artifact-only replay.

All extrapolation from resource growth or bounded instances is heuristic.
