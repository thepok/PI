# T84 certified finite fourth-moment experiment

Classification: `experiment`.

This artifact measures a finite fixed-pi phase sum. It does not prove an
asymptotic estimate. In particular, the finite scales neither prove nor refute
C2, G10, C1, or C3. The random-phase controls are heuristic evidence only.

## Pinned statement and interfaces

`CANONICAL_STATEMENT.txt` is a byte-exact copy of the canonical local statement.
Its required SHA-256 is
`db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`.
The canonical question has no external source URL; its provenance is recorded
inside that file.

The three vendored Lean sources are byte-exact accepted library interfaces:

- `T63ExactFiniteFourthMoment.lean`, especially
  `C_eq_fourthMoment` and `complete_selected_defect_recombination`;
- `T29WidthWeightedSquareFunction.lean`, especially `widthWeight` and
  `WidthWeightedSquareFunctionAt`;
- `T12ScaleMatchedSpectralFrontier.lean`, especially `scaleMatchedTarget`.

This experiment imports those formulas semantically; it adds no Lean theorem.
The files are supplied so a reviewer can inspect the literal statements and
verify their hashes without access to the repository.

## Exact finite quantities

For every integer `6 <= t <= 16`, set

```text
N = 4*2^t+1
S_h = sum_(k=0)^(N-1) exp(2*pi*i*h*10^k*pi),  1 <= h <= 10
X_h = |S_h|^2
F_t = sum_(h=1)^10 X_h^2.
```

T63's complete two-orientation recombination is retained literally:

```text
P_t = sum_(h=1)^10
        (X_h^2 - 4*(N-1)*X_h + 2*N^2 - 3*N),
W_t = sqrt(N^2-1),
Y_t = P_t/W_t.
```

Thus `P_t = F_t - 4*(N-1)*sum_h X_h + 20*N^2 - 30*N`.
`Y_t` equals the left side of T63's
`complete_selected_defect_recombination`, including its factor `2` for the two
signed orientations. The positive-representative selected-plus-defect sum is
`Y_t/2`; both are reported separately.

At `m=1`, T29's literal target, using T12's definition, is

```text
10*(N + N^2*10^(-s)),  0 < s < 1.
```

The agenda did not select `s`. Therefore `results.json` preserves this ratio as
a parameterized expression rather than silently choosing an exponent. It also
reports reproducible illustrations at `s=1/2`, `s=log_10(2)`, and
`s=log_10(5)`. These are benchmark evaluations, not substitutes for T29's
quantifier over every `s`.

The signed T63 contribution is not the full nonnegative T29 square function.
Small signed ratios can arise from cancellation and do not establish C2.

## Pi certificate

`pi_digits.txt` contains 262224 certified fractional decimal digits. The replay
recomputes them from exact integer binary splitting for

```text
pi = 426880*sqrt(10005) / S,
S = sum_(n>=0) (-1)^n
      (6n)!*(13591409+545140134*n)
      / ((3n)!*(n!)^3*640320^(3n)).
```

The positive term magnitudes decrease. A deliberately loose global check used
by the code is

```text
6^6*(13591409+545140134) < 640320^3*13591409.
```

Consequently consecutive partial sums enclose `S`. The replay computes an
integer-square-root enclosure of `sqrt(10005)`, checks the next omitted term
against the recorded decimal remainder, forms lower and upper rational bounds
for pi, and accepts digits only when both bounds have the same decimal floor.
`pi_certificate.json` records the term count, bounds, precision, and hashes.

The maximum index is `k=262144`. Sixty additional certified digits are retained
after every decimal shift. For each `k`, the replay checks that the entire turn
interval lies in one rational eighth-turn interval. A boundary crossing aborts
the replay; no midpoint-only branch decision is accepted.

## Arithmetic enclosure

No floating-point value enters a reported interval. After eighth-turn
reduction, sine and cosine are evaluated at integer scale `10^40` with 24
Taylor recurrence steps. For `0 <= x <= pi/4 < 1`, the omitted remainders are
bounded by

```text
cos: 1/(2*24+2)!
sin: 1/(2*24+3)!.
```

Truncating one fixed-point recurrence contributes less than one scale unit.
Summing the propagated errors contributes at most
`24*25/(2*10^40)`. Argument rounding and the certified turn/pi widths contribute
less than `1/10^40`. These terms are added exactly in
`BASE_COMPONENT_ERROR`.

Powers `h=1,...,10` use fixed-point complex multiplication. Component errors
satisfy the conservative recurrence `E_(j+1) <= 4*E_j+4*E_1`; the code uses the
larger common bound `4^10*E_1`. Exact integer addition then gives component
error `N*E_h` for each `S_h`. The resulting norm-square enclosure is clamped to
the mathematical bound `0 <= X_h <= N^2`.

The T63 polynomial is evaluated as one convex polynomial on each `X_h`
interval. Its minimum is tested at `clamp(2*(N-1), X_lower, X_upper)` and its
maximum at both endpoints. This avoids the dependency inflation caused by
separately interval-evaluating `X_h^2` and `-4*(N-1)*X_h`. Division by the
positive width tests all four endpoint quotients, so negative numerators are
handled correctly.

All decimal interval endpoints in `results.json` are rounded outward using
exact `Fraction` arithmetic.

## Random controls

Three independent streams use the explicitly implemented `xorshift64*`
generator with seeds recorded in `results.json`. Each 64-bit output is treated
as the exact turn `u/2^64` and passes through the same certified trigonometric
and summation path. These controls can expose gross indexing or scaling errors,
but are labeled heuristic evidence only and carry no implication for fixed pi.

## Replay

Use a directory containing only these delivered files. Python 3.11 or newer is
recommended; no third-party package or network access is used.

```bash
python3 replay.py --quick
python3 replay.py --verify
```

`--quick` verifies `SHA256SUMS`, the canonical statement pin, and the stored pi
digit hash. `--verify` additionally regenerates the pi enclosure, all fixed-pi
intervals, all random controls, and compares `results.json` byte for byte.

Reference generation on the allocated 5-core/20 GiB environment took 146.30
seconds using one Python process. The full verification is budgeted at 300
seconds and 2 GiB RAM. The implementation is single-threaded, deterministic,
and writes no file during `--verify`.

`--generate` is producer mode and overwrites only `pi_digits.txt`,
`pi_certificate.json`, and `results.json` in the artifact directory.

## Interpretation

The output is finite-scale heuristic evidence about the remaining fixed-pi
phase-cancellation frontier after the kernel-checked T63 identity. It is not a
proof, counterexample, candidate resolution, or verified resolution. It does
not discharge any all-scale, all-`m`, all-`N`, or all-`s` quantifier.
