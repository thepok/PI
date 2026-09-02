# Quantitative constant-word conjectures from mining cycle 1

Status: `experiment` (reconnaissance reproduced), statements are `conjecture`.
Date: 2026-09-02.

A conjecture-mining run on the exact BBP objects produced five named,
fully quantified conjectures with explicit word-avoiding separators and kill
tests. Their reconnaissance on the first 1,048,595 decimal digits was
reproduced independently by
[`t195_pro_conjecture_recon_20260902.py`](../../../../workflows/experiments/t195_pro_conjecture_recon_20260902.py)
with identical numbers. Two statements are retained here; the other three
(five-adic shell cylinder saturation of the T157 carrier, top-prime projection
sweep via T159, pole-class Weyl law for the Bailey–Crandall base-16 orbit)
are recorded in the project repository only.

## Retained statements

Let `x_n = {10^n pi}`, `t_j = j/2^j`, `eps_n = (4/15)(5/8)^n`.

**Dyadic signed cut law (quantitative CW0 and CW9).** For every `j >= 12`
the block `2^j <= n < 2^(j+1)` contains `n^+` with `eps_n < x_n < t_j - eps_n`
and `n^-` with `eps_n < 1 - x_n < t_j - eps_n`. This implies
`liminf x_n = 0` and `limsup x_n = 1`, i.e. CW0 and CW9. It is the
Erdős–Rényi run-length law for a normal number with an explicit margin.
Reconnaissance: blocks `j = 12..19` pass; the largest normalized extreme
`(2^j/j) * min` observed is `0.2803` (block 16, upper side), a factor `3.6`
below the threshold. Separator: `1/3`, whose orbit is constant `1/3`.

**Affine fixed-point form.** With `v_n = {(10^n - 16) pi}`,
`beta = {144 pi}`, `c = {16 pi}`, `a = 1 - c = 51 - 16 pi`:

```text
v_(n+1) = {10 v_n + beta},      10 a + beta = a + 7,      x_n = {v_n + c}.
```

So `v_n` is the orbit of the affine circle map `y -> 10y + beta` and CW0
(resp. CW9) is exactly approach to its carry-7 fixed point `a` from the right
(resp. left). Checked numerically to `10^-59`. This is an exact translation
conjugacy and carries no information beyond `x_n` itself.

## Assessment

All five pass admission test 1 trivially, since any statement implying CW0
fails on a word avoider. None passes test 2: the only "π-specific input" is
that the objects are built from π, and each statement is the random-model
prediction. The retained value is a named quantitative form of the CW0/CW9
rung and explicit kill tests. First informative kill points not yet reachable
with 1M digits: block `j = 22` (8.4M digits) for the two-step carry-7 run,
five-adic shell 12 (21.8M digits) for word length four.
