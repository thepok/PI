---
id: LEIBNIZ-CARRIER
title: Leibniz carrier
label: proof sketch
lean: []
file: knowledge/pi/results/intermediate/20260828-endpoint-corrected-leibniz-carrier.md
statement: Prime(p)∧p≥17∧p≡1(mod4)⇒π−c_p=(1/4)∫₀¹x^(p−1)(1−x)^8/(1+x²)dx>0.
does_not_show: Not-proved:same-child-sign.
source: knowledge/pi/results/intermediate/20260828-endpoint-corrected-leibniz-carrier.md#fixed-order-carrier
---
> ## Fixed-order carrier
>
> Let `p>=17` be prime with `p=1 mod 4`, put `M=(p-3)/2`, and define
>
> ```text
> L_p = 4*sum_(k=0)^M (-1)^k/(2*k+1),
> t(x) = (1-x)^4/4,
> P0(x) = 1-x/2+(1-x)^2/4,
