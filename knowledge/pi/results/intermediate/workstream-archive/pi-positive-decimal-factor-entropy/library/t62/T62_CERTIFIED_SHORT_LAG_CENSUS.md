# T62: certified finite short-lag census for pi

Status: `experiment`. Every result is finite heuristic evidence only. This
artifact proves neither C7, C2, C1, nor positive decimal factor entropy.

## 1. Provenance and normalized task

The canonical question is local and has no original source URL. Its byte-exact
copy is `pi-positive-decimal-factor-entropy.txt`, with SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

For each integer `2 <= n <= 12`, define

```text
L_n = 10^(n // 2),
```

where `//` is natural-number division. For every lag and start in the strict
ranges

```text
1 <= r < n,  r < L_n,  0 <= j < L_n-r,
```

the script classifies

```text
circleDistance(10^j*(10^r-1)*pi) < 10^(-n).          (1.1)
```

The per-lag count uses the smaller index `j`. The ordered short-lag count is
twice the sum over lags, restoring both orientations exactly as in T56's lag
identity. Diagonal pairs are reported separately.

### Ambiguities fixed

1. The experiment counts raw short-lag near returns, not
   `shortResidualPairCount(mu,c,Q0,...)`. The latter depends on arithmetic
   parameters absent from T62's agenda.
2. The cutoff in (1.1) is strict. Equality is a miss, never a hit.
3. `j=0` begins with the first fractional decimal digit of pi; the integer
   digit `3` disappears modulo one.
4. `diagonal_plus_short` excludes every lag `r>=n` and is not the full `Q_pi`.
5. The mandatory baseline is exactly `2<=n<=12`. Larger scales are a separate,
   disabled-by-default mode with declared caps.

## 2. Certified pi interval

The analytic input is Milla, *A detailed proof of the Chudnovsky formula with
means of basic complex analysis*, arXiv:1809.00533v6, Theorem 10.12, p. 58 of
the English half, DOI `10.48550/arXiv.1809.00533`. The pinned PDF, extracted
text, URLs, and hashes are recorded in `SOURCE_MANIFEST.md`. In the
normalization used here,

```text
c_k = (6k)! / ((3k)!*(k!)^3*640320^(3k)),
S   = sum_(k>=0) (-1)^k*c_k*(13591409+545140134k),
pi  = 426880*sqrt(10005)/S.                          (2.0)
```

The replay computes exact Chudnovsky binary-splitting triples. If `S_N` and
`S_(N+1)` are consecutive partial sums, their positive term magnitudes decrease
strictly because, for every `k>=0`,

```text
u_(k+1)/u_k < 24*72*42/640320^3
              = 72576/640320^3 < 1.                 (2.1)
```

The inequalities use

```text
(6k+1)(2k+1)(6k+5) < 72(k+1)^3
```

and `(A+B(k+1))/(A+Bk) <= (A+B)/A < 42`, where
`A=13591409` and `B=545140134`. Thus the alternating-series theorem puts the
infinite sum strictly between the two computed rational partial sums.

For integer scale `M`, the script sets

```text
R = isqrt(10005*M^2),
```

and checks exactly that

```text
R^2 < 10005*M^2 < (R+1)^2.                           (2.2)
```

Combining the correct opposite endpoints under division in

```text
pi = 426880*sqrt(10005)/S
```

gives directed rational lower and upper bounds. The two endpoint computations
agree on `floor(pi*10^1000027)`. Therefore the reported million-digit integer
`P` certifies the explicit interval

```text
P/10^1000027 <= pi < (P+1)/10^1000027.               (2.3)
```

`census_results.json` contains `P`, endpoint hashes, the first and last 64
digits, and all interval parameters. Classification does not call a
floating-point pi implementation.

## 3. Boundary-safe classification

Fix a prefix width `K=n+16` and `B_K=10^K`. Certified digits give integers
`a_j` satisfying

```text
a_j/B_K <= frac(10^j*pi) < (a_j+1)/B_K.
```

For `q=a_(j+r)-a_j`, the difference lies inside the conservative closed
interval

```text
[(q-1)/B_K, (q+1)/B_K].                              (3.1)
```

The code compares (3.1), using integers only, with all relevant neighborhoods
of `-1`, `0`, and `1`. It declares a hit only when the complete enclosure is
strictly inside a cutoff neighborhood. It declares a miss only when the
complete enclosure is disjoint from every open cutoff neighborhood. Anything
else is `unresolved`; the mandatory run aborts unless that count is zero.

Every per-lag row records the candidate closest to the strict boundary, its
prefix delta, nearest integer, lower and upper distance numerators, common
denominator, cutoff numerator, classification, and certified margin. All hit
witnesses would be listed separately. Replay recomputes the census and checks
every one of these witness records against the pinned output.

## 4. Mandatory baseline result

The complete 66-row table is under
`mandatory_baseline.tables[*].per_lag` in `census_results.json`. The finite
result is:

| n | L_n | short lags | ordered short count | unresolved |
|---:|---:|---:|---:|---:|
| 2 | 10 | 1 | 0 | 0 |
| 3 | 10 | 2 | 0 | 0 |
| 4 | 100 | 3 | 0 | 0 |
| 5 | 100 | 4 | 0 | 0 |
| 6 | 1000 | 5 | 0 | 0 |
| 7 | 1000 | 6 | 0 | 0 |
| 8 | 10000 | 7 | 0 | 0 |
| 9 | 10000 | 8 | 0 | 0 |
| 10 | 100000 | 9 | 0 | 0 |
| 11 | 100000 | 10 | 0 | 0 |
| 12 | 1000000 | 11 | 0 | 0 |

Every normalized ordered short total is exactly `0/1`; every
`diagonal_plus_short/L_n` value is exactly `1/1`. These statements concern only
the displayed finite ranges. They are not estimates uniform in `n`.

The pinned baseline run used CPython 3.11.2 on Linux and recorded
190.948859 seconds elapsed and 82556 KiB peak RSS. Replay reports its own
observed values, which are intentionally excluded from deterministic equality.

## 5. One-command replay

From a directory containing only these delivered artifacts, run:

```sh
sh ./verify.sh
```

The command hash-checks the canonical statement, reconstructs (2.3), reruns
all baseline classifications, checks the deterministic result and all 66
closest-boundary witnesses, requires zero unresolved cases, and verifies the
required artifact manifest before executing the census program. It needs
Python 3.11 or later, a POSIX shell, and the commonly available `sha256sum`
and `mktemp` command-line tools. The reference replay takes about three minutes
on the recorded machine.

## 6. Optional larger scales

No larger-scale result is part of the mandatory baseline. Optional work is
enabled only with all three resource caps, for example:

```sh
python3 t62_census.py --optional-max-n 13 \
  --max-length 1000000 --max-candidates 12000000 --max-seconds 600 \
  --output optional.json --quiet
```

The output keeps optional tables under `optional_larger_scales`, separate from
the immutable baseline. Length and candidate caps are checked before each
scale. The time cap applies only to optional work after the mandatory baseline
and is checked cooperatively during pi certification, digit-window generation,
and each lag census. A single large integer operation can cause a small
overshoot, whose measured optional elapsed time and interruption stage are
recorded. A completed optional table is retained only when it has zero
unresolved boundaries. Any cap or unresolved cutoff records the computational
frontier and stops progression; it is not extrapolated.

## 7. Interpretation

The absence of raw short-lag hits in these 66 finite lag rows is heuristic
calibration of the missing fixed-pi estimate only. It does not control long
lags, establish an eventual linear bound, or prove C7. Consequently it proves
neither C2 nor C1 and says nothing universal about decimal factor entropy.
