# T18 reproducible calibration

This directory is a self-contained finite experiment for agenda item T18. It
uses Python's standard library only and does not read the repository or the
canonical statement at runtime.

## One-command reproduction

Run from this directory with Python 3.11 (validated with Python 3.11.2):

```bash
PYTHONDONTWRITEBYTECODE=1 python3 calibrate.py --verify
```

The command independently computes 10,003 decimal digits of pi with an
integer fixed-point Machin series and a Decimal Chudnovsky series. It requires
the digit strings and their SHA-256 hashes to agree, checks a fixed known
50-digit prefix, regenerates every computational artifact in a temporary
directory, reruns all integer certificate checks, and compares every generated
file byte-for-byte through the hashes in `expected_results.json`. Success is
reported as `"status": "REPRODUCED_OK"`.

The verifier deliberately requires all retained files under their exact
co-located names. This prevents the missing-input and renamed-file failures of
the earlier T17 attempts.

## Fixed experiment

The full predeclared configuration is `ranges.json`:

- Prefix cutoffs: `N = 1000, 3000, 10000`.
- Exhaustive occurrence tables: every decimal word of lengths `1,2,3,4`.
- T1 counting convention: all starts `0 <= n < N`; a word may extend beyond
  position `N-1`.
- Fully-contained block scales: `L = 1,2,4,8,16,32`, with exactly `N+1-L`
  sampled starts.
- Forbidden words: `0,1,00,01,11,000,001,012,123,0000,0123`.
- Exact matrix powers: `r = 0,1,2,4,8,16,32`.
- Streams: decimal pi, one fixed SHA-256/rejection pseudorandom realization of
  an iid-uniform model, Champernowne, the exact T4 balanced stream, and the
  exact T2 sparse-island stream.

The iid entry is a reproducible finite pseudorandom realization, not an
infinite independently sampled object. Bytes below 250 from SHA-256 counter
blocks are accepted and reduced modulo 10, avoiding modulo bias in each
accepted byte.

## Stream definitions

`champernowne` is `123456789101112...`.

T4 stage `m` is the first `3^m` Champernowne digits followed by `3^m` zeros.
The Champernowne prefix restarts at index zero in each stage.

T2 stage `k` is `(k+1)^4` zeros followed by the usual decimal representation
of `k+1`.

These definitions reproduce the accepted T2 and T4 artifacts, including their
zero-based stage indices.

## Files

- `calibrate.py`: generator and verifier.
- `ranges.json`: fixed ranges, conventions, words, seed, and stream order.
- `digit_hashes.json`: independently cross-checked pi hash and all control
  hashes.
- `word_counts.csv`: 166,650 exhaustive exact occurrence-count rows.
- `block_entropies.csv`: exact count spectra and entropy expressions for 90
  stream/cutoff/scale combinations. Decimal entropy columns are derived from
  the exact spectra.
- `forbidden_calibration.csv`: 990 exact frequency, contamination, forbidden
  start, and T15 integer-bound rows.
- `automaton_certificates.json`: full T14 transition matrices, exact matrix
  powers, row sums, independent KMP counts, and T16 maxima.
- `certificate_checks.json`: aggregate check counts and fixtures.
- `expected_results.json`: locked SHA-256 values for all generated files.
- `REPORT.md`: interpretation and explicit claim limits.

## Matrix convention

For nonempty forbidden word `v` of length `ell`, states are all bit masks on
`0,...,ell-1` containing bit zero, including unreachable states. Matrix rows
are sources, columns are destinations, and entries count digit labels rather
than Boolean adjacency. A digit completing `v` has no transition; there is no
sink state.

For every tested `v,r`, the verifier checks with Python arbitrary-precision
integers:

```text
initial-row-sum(M_v^r) = independent-KMP forbidden-word count
max-row-sum(M_v^r)     = initial-row-sum(M_v^r)
every row sum          <= initial-row-sum(M_v^r)
```

It also checks the T14 fixture `M_00 = [[9,1],[9,0]]` and the length-four
avoidance count `9720`.
