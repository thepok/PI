# T97: complete finite census of T56's long-lag sector

Status: `experiment`. Every result below is finite heuristic evidence only.
This package proves no eventual estimate, C7, C2, C1, or positive decimal
factor entropy.

## 1. Scope and normalized conventions

The canonical question is recorded in the byte-exact local file
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

That question asks for one positive entropy rate at all sufficiently large
lengths. T97 is instead the bounded sibling A14: a finite-prefix experiment at
exactly the eleven scales `2 <= n <= 12`.

The census imports T56's literal conventions:

```text
L_n = 10^(n // 2),                 n <= r < L_n,
0 <= j < L_n-r,                    x_j = frac(10^j*pi),
circleDistance(x_j,x_(j+r)) < 10^(-n).
```

Here `//` is natural-number division, `j=0` begins with the first fractional
digit of pi, and the cutoff is strict. Each upper-triangular incidence
`(j,j+r)` has ordered multiplicity two. No diagonal or short lag is included
in the reported long total.

The following ambiguities are fixed rather than inferred:

1. Every lag `n <= r < L_n` is covered, including both endpoints.
2. Every start `0 <= j < L_n-r` is covered; there is no circular wrap in the
   index range.
3. Circle distance, rather than ordinary absolute distance, is used.
4. Equality at the cutoff is a miss, never a hit.
5. T71's `W5` is a cyclic-adjacent decimal-cell superset and is not identified
   with the strict raw near-return count.
6. T56's parameterized short residual is compared only through T71's accepted
   convention and its pinned finite baseline; no arithmetic parameters are
   invented.

## 2. Certified input and boundary decisions

The replay reuses T62's exact Chudnovsky binary splitting. The identity is
pinned to Lorenz Milla, *A detailed proof of the Chudnovsky formula with means
of basic complex analysis*, arXiv:1809.00533v6, Theorem 10.12, PDF p. 44.
Exact URLs and hashes are in `SOURCE_MANIFEST.md`.

Consecutive exact partial sums and directed integer square-root bounds isolate
`floor(pi*10^1000043)`. The run used 71,443 series terms. It records hashes of
the scaled integer, decimal digits, and rational interval endpoints in
`census_results.json`; no floating-point value of pi is used.

At scale `n` and guard `g`, each orbit point is enclosed in its certified
decimal-prefix cell of width `10^(-(n+g))`. For two prefix integers whose
nearest circular difference is `d`, the true distance is enclosed between
`max(0,d-1)/10^(n+g)` and `(d+1)/10^(n+g)`. A hit is declared only if the upper
bound is strictly below `10^(-n)`; a miss is declared only if the lower bound
is at least the cutoff. Any overlap is `unresolved`.

The adaptive guard schedule is `4, 8, 16, 32`. All eleven mandatory scales
resolved at guard 4, so the unresolved-boundary total is zero. A mandatory run
aborts rather than reporting a table if any case remains unresolved.

## 3. Complete subquadratic scan

For each scale the code constructs the exact decimal-prefix integers, sorts
their indices around the circle, and scans forward only while the circular
prefix difference is at most `10^g`. Its complexity is
`O(L_n log L_n + K_n)`, where `K_n` is the number of enumerated prefix
candidates.

Completeness is integer-exact. If a pair is not enumerated, its prefix-circle
difference is an integer strictly greater than `10^g`, hence at least
`10^g+1`. Subtracting the one-unit interval uncertainty leaves a lower bound
at least `10^g/10^(n+g) = 10^(-n)`, so the omitted pair cannot satisfy the
strict cutoff. The virtual doubled-circle scan covers the endpoint wrap
without allocating a second tuple array.

The main pass accumulates a dense per-lag vector. Independently, replay
reaggregates every exact witness by its recorded lag, compares the resulting
vector with the main vector, and then sums the vector to recover the total.
All three representations agree for every scale.

## 4. Mandatory results

The complete dense per-lag vectors, exact witnesses, interval bounds, adaptive
precision attempts, T71 comparisons, and performance data are in
`census_results.json`. `T97_mandatory_table.csv` is the compact table.

| n | L_n | long lag range | ordered total | total/L_n | positive lags | largest contributing lag | guard | unresolved |
|---:|---:|:---|---:|:---|---:|---:|---:|---:|
| 2 | 10 | 2..9 | 2 | 1/5 | 1 | 6 | 4 | 0 |
| 3 | 10 | 3..9 | 0 | 0/1 | 0 | - | 4 | 0 |
| 4 | 100 | 4..99 | 0 | 0/1 | 0 | - | 4 | 0 |
| 5 | 100 | 5..99 | 0 | 0/1 | 0 | - | 4 | 0 |
| 6 | 1000 | 6..999 | 2 | 1/500 | 1 | 293 | 4 | 0 |
| 7 | 1000 | 7..999 | 0 | 0/1 | 0 | - | 4 | 0 |
| 8 | 10000 | 8..9999 | 0 | 0/1 | 0 | - | 4 | 0 |
| 9 | 10000 | 9..9999 | 0 | 0/1 | 0 | - | 4 | 0 |
| 10 | 100000 | 10..99999 | 4 | 1/25000 | 2 | 54109 | 4 | 0 |
| 11 | 100000 | 11..99999 | 0 | 0/1 | 0 | - | 4 | 0 |
| 12 | 1000000 | 12..999999 | 2 | 1/500000 | 1 | 410309 | 4 | 0 |

The five upper-triangular long-sector witnesses are:

| n | j | j+r | r | left block | right block | T69 cell case |
|---:|---:|---:|---:|:---|:---|:---|
| 2 | 3 | 9 | 6 | 59 | 58 | predecessor |
| 6 | 700 | 993 | 293 | 420199 | 420198 | predecessor |
| 10 | 69596 | 86281 | 16685 | 1349261582 | 1349261581 | predecessor |
| 10 | 21760 | 75869 | 54109 | 0410219447 | 0410219446 | predecessor |
| 12 | 447672 | 857981 | 410309 | 756130190263 | 756130190263 | equal |

Each witness has ordered multiplicity two. The JSON records the certified
prefixes, nearest integer, common denominator, strict-cutoff numerator, and
lower, upper, and boundary-margin numerators for direct inspection.

## 5. Accepted short-sector comparison

For every scale, a fresh strict raw short-lag scan gives ordered count zero,
agreeing with T71's pinned `T56_short_residual` value zero under the accepted
raw-emptiness convention. A separate recomputation of T69's five-case `W5`
matches the pinned T71 baseline exactly: `W5=2` only at `n=6` and `W5=0` at
the other ten scales. The `n=6` `W5` incidence is not a strict raw near return;
the JSON therefore reports these quantities in separate fields.

## 6. One-command replay

From a directory containing only these delivered artifacts, run:

```sh
sh ./verify.sh
```

The command verifies all pinned hashes, regenerates the certified pi interval,
reruns all eleven mandatory scales, compares the full deterministic projection
and compact table, rechecks all five witnesses, reconstructs every dense
per-lag vector, and requires zero unresolved cases. The baseline generation
run recorded 179.693350 seconds and 562004 KiB peak RSS on CPython 3.12.3/Linux.
Replay reports its own runtime and memory, which are excluded from deterministic
equality.

## 7. Optional scales and interpretation

Optional scales are disabled by default. They require all declared caps, for
example:

```sh
python3 -B ./t97_long_sector_census.py --optional-max-n 13 \
  --max-length 1000000 --max-candidates 2000000 --max-seconds 600 \
  --output optional.json --quiet
```

Length, enumerated-candidate, and time caps are recorded under
`optional_larger_scales`. A capped scale is a computational frontier, not a
mathematical verdict, and optional output is separate from the mandatory
baseline.

The observed counts are sparse at these eleven finite scales. This is only
heuristic calibration of the missing fixed-pi long-sector estimate. It gives
no uniform bound in `n`, does not establish C7, and consequently proves neither
C2 nor C1.
