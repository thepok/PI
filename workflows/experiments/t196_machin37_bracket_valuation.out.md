# T196 Machin 3/7 bracket valuation experiment

## Claim failures

| m | failed claim(s) | details |
|---|---|---|
| -- | none | -- |

## Sample denominator valuations

Entries are `v_p(den L_m)/v_p(den U_m)`.

| m | p_m | v2 | v3 | v5 | v7 |
|---|---|---|---|---|---|
| 0 | 3 | 0/0 | 4/1 | 0/0 | 3/1 |
| 1 | 7 | 0/0 | 7/5 | 1/1 | 8/5 |
| 6 | 27 | 0/0 | 30/25 | 2/2 | 27/25 |
| 31 | 127 | 0/0 | 127/125 | 3/3 | 127/125 |
| 156 | 627 | 0/0 | 628/625 | 4/4 | 627/625 |
| 400 | 1603 | 0/0 | 1603/1601 | 4/4 | 1604/1601 |

## Summary

- Range: `m=0..400` (401 cases); exact rational arithmetic; `mpmath` pi at 2000 decimal digits.
- Brackets `L_m < pi < U_m`: PASS (401/401).
- Width `U_m-L_m=8/(p_m*3^p_m)+4/(p_m*7^p_m)`: PASS (401/401, exact).
- Odd reduced denominators with `v_5=floor(log_5(4m+3))`: PASS (401/401).
- Failing values of `m`: 0.
