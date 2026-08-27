# T51 exact postprocessing of T50 fixed-pi chains

Status: `experiment` (finite heuristic evidence only).

## Scope

This is the bounded A14 sibling, not canonical A1. The canonical statement is
vendored byte-for-byte and hash-pinned. Only T50's fixed-pi structural
`GeometricResonanceChain` records are consumed. T50's chain search, controls,
APC, FSFS, primitive classes, and aggregate tables are not recomputed. No T50
APC/FSFS computation is presented as new.

## Literal predicates

At node k, the complete legal T24 indices are s >= 1 and j+s < M_k, with
Q=10^j(10^s-1). A triple (j,s,a) is retained exactly when the certified
interval proves |Q beta_k-a| < inverseError(nodeTau(D,k)). Integer search
bounds come from the enclosing open interval and therefore certify completeness.
For every adjacent witness pair, edges use all seven conjuncts of kernel-checked
T28 `AdjacentPairCompatible`; no equality of j, s, or Q is imposed.
Preperiod ranges and denominator positivity/formulas are exact audits, not extra
edge clauses; coefficient transport is diagnosed by Q0*a1-U*Q1*a0.

## Results

| chain | node witness counts | edges | matching | left/right Hall deficiency | longest path vertices |
|---|---:|---:|---:|---:|---:|
| pi-M3-D4-r2-h1-s1 | 1/0 | 0 | 0 | 1/0 | 1 |

The sole selected chain has W_0={(j,s,a)=(0,1,2799)} and W_1 empty.
Thus there is no literal T28 edge, the maximum matching has size 0, the
left Hall deficiency is 1, and the longest path has one vertex.
`raw_output.json` records every legal index, completeness window, interval
decision, literal edge record, Hall witness, matching, and path certificate.

## Premise audit and exact counterexample scope

T26's nodewise inverse theorem requires `chainLengthRequest(D,d) <= K`.
For the selected T50 chain this is 32768 <= 2, which is false. Therefore
the empty terminal T24 set does not refute T28 `CoherentAdjacentSelection`,
JWMO, compatibility on failure-derived chains, C1, or canonical A1. It only
refutes the explicitly tested finite selection property that every
T50-selected structural fixed-pi chain has a T24 witness at every node.
The failure is partitioned as terminal-node signed-error exclusion; there
are no witness pairs on which a coefficient-transport clause could fail.

## Certification and replay

Pi is enclosed by exact rational alternating-series bounds in Machin's
formula. Inverse-error inequalities use rational cosine Taylor bounds and
96 exact bisections. Discrete predicates and denominators use exact integers.
T50 node-resonance intervals are pinned inherited inputs, not recomputed or
presented as T51 results; every new T24/T28 phase decision is recertified.
Any unresolved strict comparison aborts before graph statistics are emitted.
Run `bash reproduce.sh` in a directory containing only these artifacts.
It checks all pinned hashes, regenerates byte-identical output and report,
then independently checks witness completeness, literal edges, and graph
certificates. Budget: 300 seconds and 2048 MiB; no network is used.

## Required limitation

All positive observations are finite heuristic evidence. They prove neither
compatibility nor canonical C1, neither canonical A1 nor any asymptotic
property of pi. The finite missing-edge and Hall results apply only to the
listed T50 structural chain and the explicitly stated selection property.
