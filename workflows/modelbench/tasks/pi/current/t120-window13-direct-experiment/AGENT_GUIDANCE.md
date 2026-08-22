# T120 direct window-13 experiment

Status: `experiment`.

This task computes mathematics, not workflow infrastructure. Work only on the
actual T118 successor points indexed by `3840 <= N < 4096`. Each record `N`
represents

`S_N = 10^(N+1) * bbpPartial(7*(N+1))`,

reduced as a signed numerator over a positive denominator. Store
`R_N = S_N.num mod S_N.den`, `W_N = S_N.den`, and
`cell_N = (10*R_N)//W_N`. The partial sum is inclusive at its endpoint.

The literal BBP poles at index `k` are

- `4 / ((8*k+1)*16^k)`;
- `-1 / (2*(2*k+1)*16^k)`;
- `-1 / ((8*k+5)*16^k)`;
- `-1 / (2*(4*k+3)*16^k)`.

Their independently proved combined term is

`(120*k^2+151*k+47) /
 ((2*k+1)*(4*k+3)*(8*k+1)*(8*k+5)*16^k)`.

Use exact integers only. No floats, decimal approximations, `%10`, external
digit files, web answers, expected-point tables, or lower-window artifacts.
Reconstruct from index zero inside the delivered script. Optimize the exact
arithmetic if needed, but do not weaken it. Emit canonical compact sorted JSON
with one LF. Every point has exactly `n,r,w,cell`, with `r,w` decimal strings.

The output is finite evidence only. It proves no normality, density, decimal
occurrence, V1 statement, or solution of the PI problem. A route mismatch is
an invalid experiment, never a majority vote.

