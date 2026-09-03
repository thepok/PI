---
id: FIXED-HORIZON-RAY
title: Fixed-horizon ray
label: proof sketch
lean: []
file: knowledge/pi/results/intermediate/20260827-fixed-horizon-signed-predecessor-ray.md
statement: ∀r≥0,∃coherent A_r:q_r=1000·10^r∧the-displayed fixed-10000 score is positive.
does_not_show: Not-proved:natural-horizon-V1.
source: knowledge/pi/results/intermediate/20260827-fixed-horizon-signed-predecessor-ray.md#statement
---
> ## Statement
>
> Put `q_r = 1000 * 10^r` and keep the horizon fixed at `N = 10000`. Starting
> from `A_0 = 334`, there are digits `d_r < 10` and coherent left extensions
>
> \[
>  A_{r+1}=A_r+d_rq_r,\qquad 0\le A_r<q_r,
> \]
