# Machin critical-shell conjectures from mining cycle 2

Status: `experiment` (reconnaissance on 1,048,596 digits, script `workflows/experiments/t198_mining_cycle2_machin_critical_shells.py`), statements are `conjecture`.
Date: 2026-09-04. Produced by a ChatGPT Pro mining run against PI `ca85d26`; Independently reproduced 2026-09-04 on the 1,048,596-digit file (all shell rows identical) and extended to the complete shell e = 9 on `data/pi_digits_4700000.txt` (`t198_mining_cycle2_machin_critical_shells.4700000.out.md`): shell 9 expected 1.800445 per side, observed 2 (zero side) and 6 (nine side); both laws survive; first incomplete shell is now e = 10 (needs ~24 M digits).

# Track B conjecture-mining cycle 2: Machin critical shells

Status: `experiment` for the reconnaissance and `conjecture` for the two laws below. Nothing here is a theorem, a proof of `MC0`, or a proof of `CW0`, `CW9`, `E`, or `V1`.

## 1. Audit boundary and novelty check

I read the public PI repository in the required order at main commit `ca85d264161d5713b32c34dcd5019b188b968cc5`: `AGENTS.md`, `FRONTIER.md`, `knowledge/pi/INDEX.yaml`, then the cycle-1 report and experiments `t195`, `t196`, and `t197`. I also read `ROADMAP.md` and every `paper/docB/*.tex` file exposed by the private MathMyth connector. The numerical input was the tracked file `workflows/experiments/data/pi_digits_1048596.txt`: 1,048,596 digits after the point, zero-based, with newline-inclusive SHA-256

```text
77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684
```

The retained laws are not the cycle-1 dyadic signed-cut law, affine fixed-point reformulation, BBP five-adic shell saturation, top-prime projection sweep, or Bailey--Crandall pole-class law. They are also not the existing `MC0` or `SOH-3/7` propositions in `INDEX.yaml`: those allow arbitrary `m,n` after a lower cutoff, whereas the new laws demand a hit in **every specified five-adic shell**, at one canonical width-matched decimal position for each `m`, and separately prescribe the zero and nine orientations.

The onset `e >= 4` was mined from this corpus. The same rule has no zero-side hit in shells `e=2,3`, and no nine-side hit in shell `e=3`. Thus shells `e=4,...,8` are discovery data, not a holdout. The first prospective complete shell is `e=9`.

## 2. Common exact setup

For `j >= 0`, put

```text
S_j(x) = sum_{r=0}^j (-1)^r x^(2r+1)/(2r+1),
L_m    = 8 S_(2m+1)(1/3) + 4 S_(2m+1)(1/7),
U_m    = 8 S_(2m)(1/3)   + 4 S_(2m)(1/7).
```

Document B/T198 machine-checks

```text
L_m < pi < U_m,
W_m := U_m-L_m
     = 8/((4m+3)3^(4m+3)) + 4/((4m+3)7^(4m+3)).
```

Its five-adic denominator law is presently a `proof sketch`, numerically checked by `t196` for `m=0,...,400`: the reduced denominators of both endpoints have five-adic valuation `floor(log_5(4m+3))` on that range.

For every integer `e >= 4`, define the critical shell

```text
S_e = {m in N_0 : 5^e <= 4m+3 < 5^(e+1)}.
```

Exactly `|S_e|=5^e`. Put

```text
k_e       = floor(e log_10 5),
h_m       = floor(log_10(1/W_m)),
n_(e,m)   = h_m-k_e-1,
w_(e,m)   = 10^n_(e,m) W_m,
c_(e,m)   = 10^k_e w_(e,m).
```

Then `n_(e,m) >= 0` in the stated range and, by construction,

```text
10^-2 < c_(e,m) <= 10^-1,
w_(e,m) = c_(e,m) 10^-k_e.
```

For a real `alpha`, let `x_n(alpha)={10^n alpha}` under the canonical decimal convention. The inequalities below are strict, so decimal endpoint ambiguity is irrelevant.

For the route certificate, also set

```text
D_m       = lcm(den(L_m),den(U_m)),
R_(m,n)   = res_(D_m)(10^n D_m L_m),
Delta_m   = D_m W_m.
```

## 3. Conjecture M5CS0: Machin five-adic critical-shell zero law

### Exact statement

For every integer `e >= 4`, there exists `m in S_e` such that, with `k=k_e`, `n=n_(e,m)`, and `w=w_(e,m)`,

```text
w < x_n(pi) < 10^(-k)-w.                         (M5CS0)
```

Equivalently as a fully quantified formula,

```text
forall e in N, e>=4 -> exists m in N_0,
  5^e <= 4m+3 < 5^(e+1)
  and 10^n W_m < {10^n pi} < 10^(-k_e)-10^n W_m,
where n=floor(log_10(1/W_m))-k_e-1.
```

### Target and exact Machin certificate

`x_n(pi)<10^(-k)` says that the `k` digits beginning at zero-based position `n` are `0^k`. Since `k_e -> infinity`, M5CS0 implies `CW0`, hence also `E`.

Moreover, the two margins force the whole scaled T198 bracket into the same zero cylinder. Therefore every M5CS0 witness satisfies the exact rational numerator inequality

```text
10^k R_(m,n) + 10^(n+k) Delta_m < D_m.           (Z-SOH)
```

This is stronger than merely observing a zero block: it gives the one-sided, no-wrap Machin certificate that the audited route lacks.

### Why π-specific, and why the null model does not already predict it

The named arithmetic input is the **exact Machin 3/7 bracket with its exact width**, coupled to the five-adic denominator shell. The shell contributes `5^e` candidates while the requested cylinder has scale

```text
10^(-k_e),  with  5^e 10^(-k_e) in [1,10).
```

Thus each shell is at the critical first-moment scale: it has only order-one expected hits, not a growing surplus. Requiring every shell to hit is therefore much stronger than a normal-number or independent-digit heuristic. The hoped-for extra mechanism is an actual π-specific orientation of the Machin numerators in `(Z-SOH)`, not generic equidistribution under a renamed selector.

### Word-avoiding replacement constant

Take `alpha=1/9=0.1111...` in its canonical decimal expansion. It avoids every `0^k` and every `9^k`, and `{10^n alpha}=1/9` for all `n`. For `e>=4`, `k_e>=2`, while the M5CS0 interval is contained in `(0,10^-2)`. Hence M5CS0 is false for this avoider in every shell. This is the recorded `D=9` orbit separator for the closed Machin-3/7 route, not an ad hoc finite-prefix replacement.

### Falsification experiment

For each complete shell `S_e`, compute `k_e,n_(e,m),c_(e,m)` for every `m`. If the first `k_e` digits at `n_(e,m)` are zero, write the following fractional tail as `T`. The event is exactly

```text
c_(e,m) < T < 1-c_(e,m).
```

The script encloses `T` with its next 18 digits. A complete shell with zero exact hits and no unresolved boundary case kills M5CS0. Under iid decimal digits, the expected count is exactly

```text
mu_e = sum_(m in S_e) (1-2c_(e,m)) 10^(-k_e),
```

by linearity of expectation; overlapping suffixes affect the distribution, not this mean. A Poisson empty-shell probability `exp(-mu_e)` is only a rough heuristic.

### Closed route reopened

M5CS0 would reopen `route-machin-37`, which dies at `Missing:one-sided-endpoint-hit.`, under the exact recorded reopening condition

```text
Needs:oriented-Machin-numerator-bound.
```

Indeed `(Z-SOH)` is precisely such a bound, in every critical shell, and it separates the recorded `1/9` orbit.

## 4. Conjecture M5CS9: Machin five-adic critical-shell nine law

### Exact statement

For every integer `e >= 4`, there exists `m in S_e` such that, with the same definitions,

```text
w_(e,m) < 1-x_n(pi) < 10^(-k_e)-w_(e,m).         (M5CS9)
```

Equivalently,

```text
forall e in N, e>=4 -> exists m in N_0,
  5^e <= 4m+3 < 5^(e+1)
  and 10^n W_m < 1-{10^n pi} < 10^(-k_e)-10^n W_m,
where n=floor(log_10(1/W_m))-k_e-1.
```

### Target and exact Machin certificate

This places `x_n(pi)` strictly inside the terminal cylinder `(1-10^-k,1)`, so the `k` digits at position `n` are `9^k`. Since `k_e -> infinity`, M5CS9 implies `CW9`, hence `E`.

The margins again contain the entire scaled Machin bracket in that cylinder. Every witness therefore satisfies

```text
10^k (D_m-R_(m,n)) < D_m,
R_(m,n) + 10^n Delta_m < D_m.                    (N-SOH)
```

The first inequality selects the terminal side; the second kills the wrap at `1`.

### π-specific plausibility, avoider, and falsification

The same T198 bracket, five-adic shell, and critical first-moment matching are the named π-specific mechanism. What changes is the prescribed orientation: `(N-SOH)` asks for the upper endpoint rather than reusing unsigned proximity.

The replacement `alpha=1/9` again kills the law: `1-{10^n alpha}=8/9`, while the target interval lies below `10^-2`. The finite test is identical except that the required initial block is `9^k`; after stripping those nines, the same tail condition `c<T<1-c` results. A complete shell with no exact nine-side hit and no boundary ambiguity kills M5CS9.

As a route statement, the upper branch meets the broader `route-machin-pade-carriers` obstruction `Missing:orientation/integer-lift-selection.` Its recorded reopening condition is

```text
Needs:pi-specific-half-plane/numerator-theorem.
```

A proof of `(N-SOH)` on all critical shells would be such a π-specific oriented numerator theorem. The paired law M5CS0+M5CS9 would simultaneously supply the lower-endpoint condition recorded for `route-machin-37` and both directed constant-word targets. The binding separator on `route-machin-pade-carriers` is `Shared-by:4/9–5/9-derivative-twins.` Those twins rule out any proof based only on the shared derivative-sign data. Reopening therefore requires the literal actual-π least-residue inequalities in `(N-SOH)`; a recycled carrier argument would not qualify.

## 5. Numerical reconnaissance on 1,048,596 digits

All positions are zero-based after the decimal point. `E_null` is the iid expected count **per side** over the tested candidates.

| shell `e` | `k_e` | candidates tested / full shell | `E_null` tested | zero hits | nine hits |
|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 25 / 25 | 2.276085 | 0 | 5 |
| 3 | 2 | 125 / 125 | 1.154171 | 0 | 0 |
| 4 | 2 | 625 / 625 | 5.756065 | 6 | 6 |
| 5 | 3 | 3,125 / 3,125 | 2.881034 | 3 | 1 |
| 6 | 4 | 15,625 / 15,625 | 1.440429 | 1 | 3 |
| 7 | 4 | 78,125 / 78,125 | 7.201665 | 8 | 8 |
| 8 | 5 | 390,625 / 390,625 | 3.600882 | 3 | 3 |
| 9 | 6 | 61,146 / 1,953,125 | 0.056368 | 0 | 0 |

For the five complete retained shells `e=4,...,8`, the null expectation is `20.880075597699` per side; the observed counts are `21` zero-side and `21` nine-side. This is survival, not statistical confirmation. The rough Poisson empty probabilities for shells `e=4,...,8` are respectively `0.0032, 0.0561, 0.2368, 0.00075, 0.0273`; after mining the onset, no combined p-value is legitimate.

Representative strongest observed witnesses (`k_8=5`) are:

```text
M5CS0: e=8, m=110589, n=211057, c=0.02377927,
        digits 00000312015134146214627...
M5CS9: e=8, m=101145, n=193033, c=0.01404378,
        digits 99999928333379487659821...
```

The 18-digit tail enclosures produced no ambiguous classifications. Across tested candidates, the nearest `-log_10(W_m)` came to an integer was `2.63215e-7`, versus the script's `5e-10` numerical pad. These are robustness diagnostics, not formal interval arithmetic.

Shell `e=9` is only 3.13% observed. Its full null mean is about `1.800445` per side, and complete testing with the same 18-digit guard requires 4,659,409 fractional digits. Zero hits in the present partial shell therefore kill nothing.

## 6. Candidates rejected in cycle 2

A Ramanujan valuation-budget selector was tested using T202's

```text
lambda_n=12n+4-3s_2(n),
p_n=floor(lambda_n log_10 2),
k_n=max(1,floor(3s_2(n)log_10 2)).
```

The quantitative rule “for each `K`, find both signs with `k_n>=K` before `n<2^(4K+2)`” survives the fully observable horizons `K=1,...,4`; its per-side expected/observed pairs are `(2.316;3,2)`, `(1.437;1,1)`, `(1.235;1,3)`, and `(1.079;1,1)`. It is **rejected**, not retained: the T202 two-adic ramp fixes a selector and a scale but supplies no sign, carry, or location bridge from the Ramanujan series for `1/pi` to decimal digits of `pi`. It therefore repeats cycle 1's renamed-randomness defect and does not meet `route-erdos-carry`'s recorded reopening condition `Needs:divisible-block-positive-tail-series.`

The exact reciprocal-coefficient valuations checked by `t197` were likewise not promoted to a digit conjecture: divisibility without a controlled one-sided tail does not target a decimal cylinder. New BBP/affine shrinking-target variants were rejected as cycle-1 duplicates.

## 7. Retention decision

Retain exactly two conjectures: `M5CS0` and `M5CS9`. Their attraction is not the finite hit count, which is ordinary under the null, but the stronger all-shell assertion at the exact critical cardinality/width balance and its explicit one-sided Machin numerator certificates. Their weakness is equally explicit: the onset was mined, only five retained shells are complete, and no known argument controls the required numerator orientation. The decisive next falsification is the complete `e=9` shell, not another reformulation or Lean wrapper.
