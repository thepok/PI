# T8 bounded fixed-pi experiment

Status: `experiment`

This self-contained bundle evaluates the canonical ordered, diagonal-inclusive
circle-distance count for fixed `pi`. The strict threshold is `10^(-n)`. The
included `canonical_statement.txt` is byte-identical to the immutable problem
statement and has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
No external source URL is recorded by that local statement.

## Reproduction

Install the pinned dependency if needed, enter this artifact directory, and run:

```bash
python3 -m pip install -r requirements.txt
bash run_experiment.sh
sha256sum -c SHA256SUMS
```

The experiment itself uses no network access or randomness. It regenerates
`raw_output.json` and `SHA256SUMS`; all paths are relative to the launcher's own
directory, so `bash run_experiment.sh` also works when called from elsewhere.
The observed runtime in this sandbox was 2.94 seconds on Python 3.11.2.

Pinned hashes for the computation and its inputs are:

| File | SHA-256 |
|---|---|
| `canonical_statement.txt` | `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8` |
| `fixed_pi_experiment.py` | `61b28588e02fbbac71a628c2f0b3d210345e077a5e9c2a62c732d2c4fd1034eb` |
| `requirements.txt` | `a699f46ed76bd216f1081b6b2330e4fb45d7c8c5a5354b208694d6590a5a8645` |
| `raw_output.json` | `1aa4b979a5e1767b6c97adf702baf285fae61803716ea0934a18b081e0f7fd6e` |

`SHA256SUMS` additionally pins the launcher and this report without including
itself. The output embeds the statement, code, and dependency-version pins.

## Declared search and checks

- Searched `n`: `{3,4,5,6,7,8}`.
- Searched `N`: `{1000,2000,4000,8000,16000,32000}`; no intermediate `N`.
- Quadratic-check `n`: `{1,2,3,4,5,6}`.
- Quadratic-check `N`: `{8,16,32,64,128}`, giving 30 cases.
- Retained orbit-tail digits: 24 initially, increments of 12, maximum 60.
- Pi precision: required fractional digits plus 25 guard digits.

At each retained precision the program regenerates the decimal prefix of pi.
It accepts results only after the longer prefix extends the previous prefix,
the complete count signature is unchanged, and every tested sort gap,
near-return threshold margin, and cylinder-boundary margin exceeds two units
of the retained scale. These are numerical stability checks, not formal
certification of the `mpmath` implementation.

The 24- and 36-digit runs had the identical complete-count signature
`80e812e7e01456becb8f1b94d6c1957138620d7c913c4c9bfda4807f0ff2543c`,
and the 36-digit pi prefix exactly extended the 24-digit prefix. At 36 retained
digits, the minimum sort gap was
`1993581282622446302194628764e-36`, the minimum distance-to-threshold margin
was `46482883491872656112074924e-36`, and the minimum cylinder-boundary margin
was `1627021950048940268268e-36`. All exceeded two units at scale `1e-36`, so
the adaptive check stopped at 36 digits rather than reaching its 60-digit cap.

The main count sorts the first `N` orbit points and scans forward on a doubled
circle. Its cost is `O(N log N + K)`, with `K` the unordered non-diagonal
near-return count. It then restores ordered-pair normalization by reporting
`Q_pi=N+2K`. Cylinder energy is `sum_a c_a^2` for half-open length-`n`
decimal cylinders. Lag concentration uses `h_r/K`, reporting the largest lag
and the ten largest lags. An independent nested-loop implementation checks
`Q_pi`, the complete lag histogram, and cylinder energy in all 30 small cases.

## Minima

Every row reports only a minimum over the six declared `N` values.

| n | minimizing N | Q_pi | min n Q_pi / N^2 | minimizing N | E | min n E / N^2 |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 32000 | 2078634 | 0.006089748046875 | 32000 | 1055334 | 0.003091798828125 |
| 4 | 32000 | 236540 | 0.000923984375 | 32000 | 134050 | 0.0005236328125 |
| 5 | 32000 | 52294 | 0.000255341796875 | 32000 | 42054 | 0.000205341796875 |
| 6 | 32000 | 34016 | 0.0001993125 | 32000 | 32974 | 0.00019320703125 |
| 7 | 32000 | 32206 | 0.000220158203125 | 32000 | 32114 | 0.000219529296875 |
| 8 | 32000 | 32030 | 0.000250234375 | 32000 | 32016 | 0.000250125 |

| n | minimizing N | K | min largest-lag share | min top-10-lag share |
|---:|---:|---:|---:|---:|
| 3 | 32000 | 1023317 | 93 / 1023317 | 895 / 1023317 |
| 4 | 32000 | 102270 | 19 / 102270 | 170 / 102270 |
| 5 | 32000 | 10147 | 6 / 10147 | 52 / 10147 |
| 6 | 32000 | 1008 | 3 / 1008 | 30 / 1008 |
| 7 | 32000 | 103 | 2 / 103 | 20 / 103 |
| 8 | 32000 | 15 | 1 / 15 | 10 / 15 |

## Interpretation

The minima broadly follow diagonal-plus-uniform collision scaling on this
bounded grid. At `n=3,4,5`, near returns are spread over many lags. At `n=7,8`,
the non-diagonal sample is too small for lag shares to distinguish mechanisms.
This is heuristic evidence that larger cutoffs would be needed to compare
global random-model cancellation with persistent bad-lag effects.

Every conclusion is an `experiment`: bounded heuristic evidence only. The
computation neither proves nor refutes C1 or C2, does not establish the
canonical statement for fixed `pi`, and makes no universal, eventual,
asymptotic, normality, or fixed-`pi` proof claim.
