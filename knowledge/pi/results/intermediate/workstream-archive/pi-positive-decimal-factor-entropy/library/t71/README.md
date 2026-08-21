# T71: certified T56/T69 finite pi census

Status: `experiment`. Every observation in this package is finite heuristic
evidence only. It proves no eventual estimate, C7, C2, C1, or positive decimal
factor entropy.

## Scope and provenance

The byte-exact canonical statement is
`pi-positive-decimal-factor-entropy.txt`, SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
The canonical question asks for one positive entropy rate valid at every
sufficiently large length. This experiment instead addresses only the bounded
sibling A14 at the eleven scales `2 <= n <= 12`.

`T71ConventionAudit.lean` imports the kernel-checked T69 module, which imports
T56. The vendored `T56LagSectorAudit.lean` and `T69FiveCaseCharging.lean` are
exact hash-pinned inspection copies. The audit file is machine-checked and
contains no new definitions replacing their conventions.

## Exact conventions

For each baseline scale,

```text
L_n = 10^(n // 2),                 q = 10^n,
1 <= r < n, r < L_n,               0 <= j < L_n-r.
```

Natural-number division is used in `n // 2`. Label `x_i` is T69's
`piCylinderCode n i`, namely the length-`n` block beginning at fractional
decimal digit `i+1`. The integer digit `3` is excluded.

For each `(j,r)`, T69's deterministic five-case priority is equality,
predecessor, successor, wrap-predecessor, then wrap-successor. `W5` is twice
the number of classified upper-triangular starts, restoring both orientations.
The base equality-component load is the sum of squared nonempty label-fiber
sizes, and T69's `E3` is exactly three copies of this load.

T56's `shortResidualPairCount(mu,c,Q0,n,L_n)` depends on arithmetic parameters.
No parameters are invented here. Instead, the certified strict near-return
census finds every containing raw set empty. The public Lean lemma
`shortResidualPairCount_eq_zero_of_raw_empty` then shows that the residual is
zero for every `mu,c,Q0` on these finite instances.

The reported T69 charging slack is defined explicitly as

```text
(L_n + E3) - W5.
```

## Certified decimal input

The replay reuses T62's exact Chudnovsky binary splitting. Consecutive rational
partial sums and directed integer square-root bounds isolate
`floor(pi*10^1000027)`. The analytic identity is pinned to Lorenz Milla,
*A detailed proof of the Chudnovsky formula with means of basic complex
analysis*, arXiv:1809.00533v6, Theorem 10.12, PDF p. 44. Exact URLs and hashes
are in `SOURCE_MANIFEST.md`.

For each strict raw near-return test the code encloses both decimal tails by
integer intervals at width `n+16`. A hit requires the entire enclosure to lie
strictly inside the cutoff; a miss requires disjointness. Any overlap is
`unresolved`, and the mandatory run aborts unless the total is zero.

## Baseline summary

The complete component histograms, all 66 per-lag rows, five-case counts,
strict-boundary witnesses, adjacency witnesses, exact ratios, and charging
slack are in `census_results.json`.

| n | L_n | W5 | W5/L_n | E3 | E3/L_n | short residual | charging slack | max component |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 10 | 0 | 0/1 | 30 | 3/1 | 0 | 40 | 1 |
| 3 | 10 | 0 | 0/1 | 30 | 3/1 | 0 | 40 | 1 |
| 4 | 100 | 0 | 0/1 | 300 | 3/1 | 0 | 400 | 1 |
| 5 | 100 | 0 | 0/1 | 300 | 3/1 | 0 | 400 | 1 |
| 6 | 1000 | 2 | 1/500 | 3000 | 3/1 | 0 | 3998 | 1 |
| 7 | 1000 | 0 | 0/1 | 3000 | 3/1 | 0 | 4000 | 1 |
| 8 | 10000 | 0 | 0/1 | 30000 | 3/1 | 0 | 40000 | 1 |
| 9 | 10000 | 0 | 0/1 | 30000 | 3/1 | 0 | 40000 | 1 |
| 10 | 100000 | 0 | 0/1 | 300000 | 3/1 | 0 | 400000 | 1 |
| 11 | 100000 | 0 | 0/1 | 300000 | 3/1 | 0 | 400000 | 1 |
| 12 | 1000000 | 0 | 0/1 | 3000006 | 1500003/500000 | 0 | 4000006 | 2 |

There is one `W5` upper-triangular incidence: at `n=6`, lag `1`, start
`j=761`, labels `999999` and `999998`, classified as predecessor. The factor
two gives `W5=2`. At `n=12`, label `756130190263` occurs at positions `447672`
and `857981`; this sole size-two component accounts for the excess of `E3`
over `3L_n`. These are finite witnesses, not asymptotic patterns.

The generation run recorded 128.953416 seconds and 272856 KiB peak RSS on
CPython 3.12.3/Linux. Replay records its own runtime and memory; these fields
are excluded from deterministic equality.

## One-command replay

From a directory containing only these artifacts, run:

```sh
sh ./verify.sh
```

The command verifies every source and artifact hash, reconstructs the certified
pi interval, regenerates all eleven scales, compares the full deterministic
projection with `census_results.json`, and independently checks every reported
adjacency witness, component position, and all 66 strict-boundary witnesses.
The expected runtime is about two to three minutes.

## Optional larger scales

Optional work is disabled by default and is accepted only when all three
resource caps are supplied, for example:

```sh
python3 t71_census.py --optional-max-n 13 \
  --max-length 1000000 --max-candidates 12000000 --max-seconds 600 \
  --output optional.json --quiet
```

Length and candidate caps are checked before a scale. The time cap is checked
cooperatively during pi certification, boundary classification, component
work, and lag classification. A capped or unresolved optional scale is not
reported as completed and is never extrapolated.

## Interpretation

The baseline suggests that these short-lag `W5` incidences and equality
collisions are sparse in the tested prefix. The charging slack is nevertheless
close to `L_n+E3`, so T69's global upper bound is numerically very loose here.
Both statements are heuristic evidence about this finite sample only. They do
not control long lags or imply any universal estimate.
