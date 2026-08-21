# T20 exact successor-splitting Pareto experiment

Status: `experiment` (finite heuristic evidence only).

## Scope and normalization

The immutable canonical statement is retained byte-for-byte with SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`. Canonical A1 keeps its literal
quantifiers: every A, every sufficiently large n, and an N depending on A,n.
This experiment instead measures the bounded A14 sibling on declared decimal
prefixes. The seeded-iid and Champernowne rows are controls, not claims about pi.
`STATEMENT_ALIGNMENT.md` maps every acceptance clause to the experiment files.
The accepted T9/T14 Lean sources are hash-pinned semantic dependencies, are not
enclosed as T20 theorem artifacts, and no Lean theorem is claimed by T20.

For a level, parent occupancy c and its ten successor occupancies c_e are
computed as integers. A parent is eta-split exactly when its second-largest
c_e satisfies eta*c <= c_e. The row split mass S is the sum of c^2 over
split parents and E=sum c^2. Thus T14's finite weighted condition is exactly
mu*E <= S. Every stored boundary is reduced rational data and the verifier
checks numerator(mu)*E <= denominator(mu)*S by integer cross-multiplication.
Open mu=1 boundaries are stored as open and have a strict rational witness.

## Declared finite ranges

- Checkpoints: `[16, 31, 64, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]`.
- Levels: `0 <= l < 14`; affine depths: `4 <= m <= 14`.
- Optimized increasing subsequences have length `5` from `[256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]`.
- Affine intercept: `B=1/1`.
- Eta domain: `0 < eta <= 1/10`; mu domain: `0 < mu < 1`.

## Completeness of the finite envelope

For each measured row, split membership changes only when eta crosses the
exact ratio (second-largest successor count)/c. The output lists every such
cell below 1/10 plus the terminal 1/10 cell. Within a cell, S/E is the exact
mu cap. The global calculation takes the union of all row eta breakpoints and
all resulting mu caps, so splitting counts are constant inside every enumerated
parameter cell. It evaluates every cell and removes only coordinatewise dominated
(eta,mu,d) cells. This is a complete finite rational Pareto envelope, not T16's grid.

For each parameter cell, exact dynamic programming selects the increasing
checkpoint subsequence maximizing the common d in d*m-B <= splitting_count(m).
All retained margins and every T9 weighted dominant-successor obstruction are
stored in `raw_output.json` as integers or reduced numerator-denominator pairs.

## Results

### pi

Measured `168` rows; exact T9 refinement held on `168`/`168` rows.
Evaluated `117` global parameter cells over `3` eta cells; retained `5` Pareto points.
One maximum-d retained point (not privileged as a theorem target):
`eta=1/10`, `mu-boundary=6/1027` (`inclusive=true`), `d=4/7`, checkpoints `[4096, 8192, 16384, 32768, 65536]`.

### seeded_iid

Measured `168` rows; exact T9 refinement held on `168`/`168` rows.
Evaluated `128` global parameter cells over `3` eta cells; retained `6` Pareto points.
One maximum-d retained point (not privileged as a theorem target):
`eta=1/10`, `mu-boundary=2/2049` (`inclusive=true`), `d=9/14`, checkpoints `[4096, 8192, 16384, 32768, 65536]`.

### champernowne

Measured `168` rows; exact T9 refinement held on `168`/`168` rows.
Evaluated `2144` global parameter cells over `45` eta cells; retained `23` Pareto points.
One maximum-d retained point (not privileged as a theorem target):
`eta=1/10`, `mu-boundary=6/4099` (`inclusive=true`), `d=5/7`, checkpoints `[4096, 8192, 16384, 32768, 65536]`.

## Replay and independent check

Run `bash run_experiment.sh` in this directory. It verifies pinned hashes,
regenerates and byte-compares the JSON and report, checks all exact inequalities,
independently re-enumerates the complete global nondominated frontier,
and runs a separately implemented naive pair-counting oracle on the declared
small prefixes. Requirements are Python 3.11+ and standard Unix `bash`,
`sha256sum`, `cmp`, and `mktemp`; there are no third-party packages or network calls.
Declared budget: 300 seconds and 4 GiB RAM.

The retained output contains `504` measured rows, `569` row-envelope cells, `34` global Pareto points, and `1470` explicit dominant-obstruction rows.

## Limitation

Every conclusion here is finite heuristic evidence. The calculation neither
proves nor refutes C2, and it neither proves nor refutes canonical A1. It does
not establish normality, an asymptotic positive density, a coherent weak limit,
or any statement beyond the declared finite prefixes and controls.
