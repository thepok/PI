# T20 statement alignment

## Reviewed object

The reviewed object is the finite experiment implemented by `experiment.py`,
replayed by `run_experiment.sh`, and recorded in `raw_output.json` and
`REPORT.md`. The accepted T9 and T14 Lean sources are semantic dependencies,
not T20 results, and are therefore pinned by hash in `THEORY_PINS.json` rather
than enclosed as candidate theorem artifacts. T20 claims no Lean theorem.

## Canonical statement and quantifiers

`canonical_statement.txt` is a byte-for-byte snapshot of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
Canonical A1 asks whether, for every integer `A >= 1`, there is an integer
`n_0 >= 1` such that, for every integer `n >= n_0`, there is an integer
`N >= 1` satisfying the stated ordered, diagonal-inclusive near-return bound.
T20 does not test those quantifiers. It is a bounded A14 sibling experiment on
declared finite prefixes. The seeded-iid and Champernowne datasets are controls,
not substitutes for fixed pi.

## Deliverable map

The complete rational Pareto envelope is computed from all exact row
breakpoints rather than from T16's parameter grid. `config.json` declares the
depths, checkpoints, affine parameters, control generator and seed, and naive
prefixes. `pi_digits.txt` and `T17_certificate.json` pin the T17-certified pi
input. `raw_output.json` contains reduced rational row envelopes, global Pareto
points, exact affine margins, optimal increasing checkpoint subsequences, and
weighted dominant-successor obstructions for pi and both controls.

## Acceptance map

Run `bash run_experiment.sh` in this directory. The command:

1. verifies every file listed in `SHA256SUMS`;
2. regenerates and byte-compares `raw_output.json` and `REPORT.md`;
3. checks each retained T14 boundary by integer cross-multiplication;
4. checks exact T9 successor-energy refinement on every measured row;
5. independently re-enumerates the complete global Pareto frontier and optimal
   subsequences; and
6. compares 54 declared small-prefix cases with the separately implemented
   ordered-pair oracle in `naive_check.py`.

The declared replay budget is 300 seconds and 4 GiB RAM, using Python 3.11+
and standard Unix tools without network access or third-party packages.

## Claim status

Every reported conclusion is finite `experiment` evidence only. T20 neither
proves nor refutes C2, and it neither proves nor refutes canonical A1.
