---
id: DYADIC-SIGNED-CUT
title: Dyadic-cut law
label: conjecture
lean: []
file: knowledge/pi/results/intermediate/20260902-pro-conjecture-mining-cycle1.md
statement: ∀j≥12,∃n⁺,n⁻∈[2^j,2^(j+1)):the-two-stated margins hold.
does_not_show: Tested-only:j=12,…,19.
source: knowledge/pi/results/intermediate/20260902-pro-conjecture-mining-cycle1.md#retained-statements
---
> ## Retained statements
>
> Let `x_n = {10^n pi}`, `t_j = j/2^j`, `eps_n = (4/15)(5/8)^n`.
>
> **Dyadic signed cut law (quantitative CW0 and CW9).** For every `j >= 12`
> the block `2^j <= n < 2^(j+1)` contains `n^+` with `eps_n < x_n < t_j - eps_n`
> and `n^-` with `eps_n < 1 - x_n < t_j - eps_n`. This implies
> `liminf x_n = 0` and `limsup x_n = 1`, i.e. CW0 and CW9. It is the
