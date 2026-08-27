# T6 finite collision-energy experiment

> **EXPERIMENT ONLY. Every result here concerns a finite digit prefix. It is
> heuristic evidence only and cannot prove or refute sibling conjecture C1 or
> canonical statement A1. No universal claim about pi follows.**

## Scope and definitions

For each `n` and `N`, the sample consists of the length-`n` contiguous blocks
starting at fractional-digit positions `d_1, ..., d_N`. If `m_w` is the
multiplicity of block `w`, the exact integer energy is `E(n,N) = sum_w m_w^2`;
diagonal ordered collisions are included. The reported exact reduced ratio is
`R(n,N) = N^2/(n E(n,N))`. This tests the stronger sibling statistic C1, not A1
itself. The grid is `1 <= n <= 12` and `N in {1000,10000,100000,1000000}`.
Here C1 is the unproved sibling statement: for every real `C>0`, eventually for
every `n` there exists `N>=1` such that `N^2 > C n E_pi(n,N)`. The experiment
checks only the displayed finite grid and does not establish any C1 quantifier.

The ideal iid-uniform comparison has exact expected energy
`N + N(N-1)/10^n`: the `N` diagonal ordered pairs always match, and each of
the `N(N-1)` off-diagonal pairs matches with probability `10^-n`. This remains
true for overlapping starts because equality reduces the free digit count by `n`.
Three deterministic controls use the same grid and exactly
`1000011` digits. Their SplitMix64 seeds are listed in `results.json`; rejection
of words at or above `2^64-(2^64 mod 10)` makes each accepted residue uniform
under an ideal uniform 64-bit generator. The seeds are the decimal run date
`20260722` followed by control indices `01`, `02`, and `03`; they were fixed before
inspecting these control outputs. Since the generator is deterministic, the controls
are reproducible pseudorandom comparators, not independent empirical samples.

## Reproduction

From this artifact directory, with Python 3.11 or later and network access:

```sh
python3 run_experiment.py prepare --output pi_fractional_1000011.txt
python3 run_experiment.py compute --digits pi_fractional_1000011.txt --output-dir rerun
python3 verify_results.py --artifact-dir rerun --digits pi_fractional_1000011.txt --checksums CHECKSUMS.sha256
sha256sum rerun/results.json rerun/results.csv rerun/comparison.csv rerun/REPORT.md
```

`prepare` verifies both complete downloaded-file hashes, checks all one million
shared fractional digits, then verifies the extracted digit-file hash. Computation
uses only Python's standard library. `results.csv` has all 192 exact rows;
`comparison.csv` aligns pi and all controls on all 48 grid points; `results.json`
records definitions, hashes, seeds, and the same exact values structurally.

## Finite comparison

Across the tested grid, pi's `E/E_iid` ranges from
`19818/19999` (0.99094954748) to
`101400/100999` (1.0039703363).
Across all individual control rows, `E/E_iid` ranges from
`10720/10999` (0.97463405764) to
`813/785` (1.0356687898).
For the limited descriptive phrase `same tested scale`, this report uses the declared
criterion `0.9 <= E/E_iid <= 1.1` at every grid point. Pi and every individual
control satisfy that finite criterion. It is only a coarse numerical comparison; it
is not an uncertainty interval or evidence of convergence, normality, C1, or A1.

At `N=1000000` the exact comparison is:

| n | pi E | control energies | pi E/E_iid | control mean E/E_iid | pi R |
|---:|---:|---:|---:|---:|---:|
| 1 | 100000550908 | 100000425826, 100001077070, 100000332706 | 25000137727/25000225000 | 150000917801/150001350000 | 250000000000/25000137727 |
| 2 | 10000942278 | 10000917678, 10001082514, 10000861200 | 5000471139/5000495000 | 1875178837/1875185625 | 250000000000/5000471139 |
| 3 | 1000958200 | 1001062684, 1001018640, 1001029706 | 5004791/5004995 | 100103701/100099900 | 5000000000/15014373 |
| 4 | 100997870 | 101006734, 100997390, 101004726 | 10099787/10099990 | 2020059/2019998 | 25000000000/10099787 |
| 5 | 11003796 | 11001492, 11002412, 11005254 | 5501898/5499995 | 16504579/16499985 | 50000000000/2750949 |
| 6 | 2001632 | 2000190, 1999508, 2000914 | 28192/28169 | 2000204/1999999 | 15625000000/187653 |
| 7 | 1100756 | 1099650, 1099970, 1100114 | 11007560/10999999 | 32997340/32999997 | 250000000000/1926323 |
| 8 | 1010078 | 1009906, 1009946, 1009972 | 101007800/100999999 | 302982400/302999997 | 62500000000/505039 |
| 9 | 1001042 | 1000948, 1001016, 1000910 | 1001042000/1000999999 | 1000958000/1000999999 | 500000000000/4504689 |
| 10 | 1000092 | 1000102, 1000110, 1000078 | 10000920000/10000999999 | 1579100000/1579105263 | 25000000000/250023 |
| 11 | 1000014 | 1000012, 1000012, 1000006 | 100001400000/100000999999 | 100001000000/100000999999 | 500000000000/5500077 |
| 12 | 1000002 | 1000002, 1000000, 1000000 | 1000002000000/1000000999999 | 3000002000000/3000002999997 | 125000000000/1500003 |

The complete exact tables, including every smaller `N`, are the generated CSV
and JSON files. Decimal columns are displays only; integer and reduced-fraction
columns are authoritative.

## Interpretation boundary

This finite computation neither supplies the eventual quantifiers in C1 nor
controls the full arbitrary-position factor language in A1. It therefore cannot
prove or refute either statement. Its only role is to measure tested finite
behavior and expose departures from the naive iid comparison for later analysis.
