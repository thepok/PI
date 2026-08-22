# T120 metric-near-pair and forcing obstructions

Date: 2026-08-22 UTC

Status: `experiment` (canonical window 13) and `proof sketch` (generic deductions)

## Result

The determinant-only T119 continuation is closed at its frozen threshold.  In
the independently reproduced exact T120 window `3840 <= N < 4096`, all ten
decimal cells occur, but

```text
C_sum = 3302
A_sum = 6319 = 3302 + 3017 adjacent-cell near pairs
```

Here T119's condition is exactly

`|R_i/W_i - R_j/W_j| < 1/10`.

It contains every same-cell pair but also many pairs in neighboring cells.
The observed `A_sum > 3512` therefore rejects the determinant-only counting
route, not decimal-cell coverage.  Exact evidence and hashes are recorded in
[`../intermediate/20260822-t120-window13-direct-experiment.md`](../intermediate/20260822-t120-window13-direct-experiment.md).

## Correctly aligned finite statistic

Let `n_a` be the ten cell counts, let `zeta` be a primitive tenth root of
unity, and put

```text
A_r = sum_{j=0}^{255} zeta^(r*c_j),  1 <= r <= 9
E   = sum_{r=1}^9 |A_r|^2.
```

Finite Fourier orthogonality gives the `proof sketch` identities

```text
E = 10 * sum_a n_a^2 - 65536
C = sum_a choose(n_a,2) = (62976 + E)/20.
```

If a cell is missing, the most balanced nine-cell count vector is a
permutation of `(29,29,29,29,28,28,28,28,28)`.  Consequently

```text
missing cell  ->  C >= 3514  ->  E >= 7304.
```

Thus `E < 7304` is the sharp energy certificate for ten-cell coverage.  The
window-13 counts give `sum_a n_a^2 = 6860` and hence `E = 3064`; this is an
arithmetic restatement of the recorded `experiment`, not a new asymptotic
result.  A useful positive continuation would require a genuinely
BBP-specific bound for this exact energy (perhaps on average), rather than a
bound for its metric near-pair superset.

## Further route boundaries

- The canonical sampled-BBP forcing is an exact tail coboundary.  With
  `e_N = 10^N (pi-P_(7N))` and the correctly indexed seven-term forcing
  `F_N = 10^(N+1) sum_{j=1}^7 b_(7N+j)`, one has
  `F_N = 10e_N-e_(N+1)`.  The associated moving translation conjugates the
  forced recurrence to the ordinary decimal map.  This duplicates the
  machine-checked T106 obstruction: the forcing is not an independent mixing
  source.
- Denominator or gcd growth alone yields only
  `|R/W-S/V| >= gcd(W,V)/(WV) = 1/lcm(W,V)` for distinct reduced rationals.
  Growing denominators weaken this generic Archimedean bound and cannot give
  fixed separation at scale `1/10`.
- Fixed-prime residue separation can certify a nonzero determinant, but
  without a product-scale modulus it cannot produce the magnitude needed for
  decimal anti-concentration.
- An every-cutoff inequality `E_N < 7304` is probably incompatible with
  normal-like decimal behavior, but this is only a `conjecture`; normality of
  pi is open.  A missing 256-digit window would refute this auxiliary uniform
  target, not V1.

## Pro provenance and audit

ChatGPT Pro was used only for creative mathematical exploration.  Its answer
SHA-256 was
`6cd55b5a12ce8bd5b34ad2229929ac2c61f370ec7ab4b4dbd473cb0604a61f39`;
the downloaded memo SHA-256 was
`2b819b8f2cb53f5e2516faf4f80610d8b35b2fb015b1ff767a6d8cdb66ea62cf`.
Independent direction and integration reviews caught an off-by-one forcing
display, stale repository state, unreplayed early-window counts, and repeated
unsupported `verified resolution` labels.  None of those claims is promoted
here.

## Nonclaims

This note proves no uniform energy bound, density, digit gap, cell recurrence,
normality, prescribed word occurrence, or V1 statement.  V1 remains open.
