# T197 Ramanujan inverse-series valuation experiment

Finite numerical verification only; this report is an `experiment`, not a proof.

## Verdicts

| check | verdict | detail |
|---|---|---|
| (a) | PASS | Computed A_n and r_n exactly for 0<=n<=600; checked F(z)R(z)=1 through z^600. |
| (b) | PASS | 0 < 4/pi-S_600 <= explicit tail bound < 10^-200. |
| (c) | PASS | All six listed coefficients agree exactly. |
| (d) | PASS | v_2(r_n)=3*s_2(n) for 1<=n<=600. |
| (e) | REPORT | v_5(r_n) tabulated for 0<=n<=40; zero search covers 0<=n<=600. |
| (f) | REPORT | Signed inverse-series errors reported at N=100, 300, 600. |
| (g) | PASS | v_10(g_(8n))=2+3*s_2(n) for 1<=n<=600. |

## (b) Ramanujan 4/pi identity check

- Exact partial sum: `S_600=sum_(n=0)^600 A_n/256^n`.
- `4/pi` (210 significant digits): `1.27323954473516268615107010698011489627567716592365158998133875247117438107381228072091042213002468764858274181406366429514329476891662922302373928585359871383391973549927262058462197117540246150973914316973918`
- `S_600` (210 significant digits): `1.27323954473516268615107010698011489627567716592365158998133875247117438107381228072091042213002468764858274181406366429514329476891662922302373928585359871383391973549927262058462197117540246150973914316973918`
- Observed `4/pi-S_600`: `8.50359310374512187328310526002e-364`.
- Explicit bound: using `C(2n,n)<=4^n`, the omitted positive tail is at most `(8k+4)/4^k` for `k=601`, namely `6.98667964872965632948999034878e-359`.
- Bound below `10^-200`: PASS.

## (c) Listed inverse coefficients

| n | expected r_n | observed r_n | verdict |
|---|---|---|---|
| 0 | 1 | 1 | PASS |
| 1 | -56 | -56 | PASS |
| 2 | 328 | 328 | PASS |
| 3 | -13120 | -13120 | PASS |
| 4 | -249304 | -249304 | PASS |
| 5 | -14947264 | -14947264 | PASS |

## (a) Inverse-convolution failures

None.

## (d) 2-adic valuation failures

None.

## (e) 5-adic valuations

| n | v_5(r_n) | n | v_5(r_n) | n | v_5(r_n) |
|---|---|---|---|---|---|
| 0 | 0 | 14 | 0 | 28 | 0 |
| 1 | 0 | 15 | 0 | 29 | 0 |
| 2 | 0 | 16 | 0 | 30 | 0 |
| 3 | 1 | 17 | 0 | 31 | 3 |
| 4 | 0 | 18 | 0 | 32 | 0 |
| 5 | 0 | 19 | 0 | 33 | 0 |
| 6 | 0 | 20 | 0 | 34 | 0 |
| 7 | 0 | 21 | 0 | 35 | 0 |
| 8 | 0 | 22 | 0 | 36 | 1 |
| 9 | 0 | 23 | 0 | 37 | 0 |
| 10 | 0 | 24 | 0 | 38 | 0 |
| 11 | 0 | 25 | 0 | 39 | 0 |
| 12 | 1 | 26 | 0 | 40 | 0 |
| 13 | 0 | 27 | 0 |  |  |

Zero coefficients for `0<=n<=600`: none.

## (f) Inverse-series truncation errors

The sign is that of `pi/4-sum_(n=0)^N r_n/256^n`.

| N | sign | absolute error |
|---|---|---|
| 100 | negative | 3.00666842530004325728497313397e-65 |
| 300 | negative | 2.26906584752979784089426178389e-186 |
| 600 | negative | 1.93943662451450620152013530418e-367 |

## (g) Decimal valuation failures

None.

## Ledger gate

PASS: checks (a), (b), (c), (d), and (g) all passed.
