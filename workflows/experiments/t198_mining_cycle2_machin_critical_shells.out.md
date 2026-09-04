# Conjecture-mining cycle 2 numerical output

Status: `experiment`; finite reconnaissance only; no theorem is claimed.

- input: `/home/Marcel/dev/PI/workflows/experiments/data/pi_digits_1048596.txt`
- decimal digits: `1048596` (zero-based after the point)
- SHA-256: `77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684`
- safety tail: `18` digits

## Machin matched critical shells

| e | k_e | m range | coverage | null E tested/side | null E full/side | 0 hits | 9 hits | ambig 0/9 |
|---|---|---|---|---|---|---|---|---|
| 2 | 1 | [6,31) | 25/25 full | 2.276085 | 2.276085 | 0 | 5 | 0/0 |
| 3 | 2 | [31,156) | 125/125 full | 1.154171 | 1.154171 | 0 | 0 | 0/0 |
| 4 | 2 | [156,781) | 625/625 full | 5.756065 | 5.756065 | 6 | 6 | 0/0 |
| 5 | 3 | [781,3,906) | 3,125/3,125 full | 2.881034 | 2.881034 | 3 | 1 | 0/0 |
| 6 | 4 | [3,906,19,531) | 15,625/15,625 full | 1.440429 | 1.440429 | 1 | 3 | 0/0 |
| 7 | 4 | [19,531,97,656) | 78,125/78,125 full | 7.201665 | 7.201665 | 8 | 8 | 0/0 |
| 8 | 5 | [97,656,488,281) | 390,625/390,625 full | 3.600882 | 3.600882 | 3 | 3 | 0/0 |
| 9 | 6 | [488,281,2,441,406) | 61,146/1,953,125 partial | 0.056368 | 1.800445 | 0 | 0 | 0/0 |

Complete retained shells e=4..8: expected `20.880075597699` and observed `21` zero-side, `21` nine-side hits.
Closest tested `-log10(W_m)` to an integer: `2.63215042651e-07`; numeric pad `5e-10`.

### First robust hit in each complete retained shell

| e | side | first hit |
|---|---|---|
| 4 | 0 | m=188, n=359, c=0.06289205, digits=00113305305488204665 |
| 4 | 9 | m=240, n=458, c=0.02829407, digits=99627495673518857527 |
| 5 | 0 | m=837, n=1597, c=0.03504217, digits=000816470600161452491 |
| 5 | 9 | m=1545, n=2948, c=0.01178075, digits=999839101591956181467 |
| 6 | 0 | m=7016, n=13389, c=0.01237764, digits=0000907151058236267293 |
| 6 | 9 | m=9425, n=17987, c=0.02654895, digits=9999112099164646441191 |
| 7 | 0 | m=25703, n=49054, c=0.04669061, digits=0000415525118657794539 |
| 7 | 9 | m=22056, n=42094, c=0.09561991, digits=9999548450027106659878 |
| 8 | 0 | m=110589, n=211057, c=0.02377927, digits=00000312015134146214627 |
| 8 | 9 | m=101145, n=193033, c=0.01404378, digits=99999928333379487659821 |

The first incomplete shell is e=9: `61,146/1,953,125` candidates are observable; zero hits there do not falsify either law.

## Rejected Ramanujan valuation-budget selector

| K | horizon | coverage | null E/side | 0 hits | 9 hits |
|---|---|---|---|---|---|
| 1 | n<64 | full | 2.315610 | 3 | 2 |
| 2 | n<1,024 | full | 1.437425 | 1 | 1 |
| 3 | n<16,384 | full | 1.234984 | 1 | 3 |
| 4 | n<262,144 | full | 1.079204 | 1 | 1 |
| 5 | n<4,194,304 | partial | 0.257192 | 0 | 0 |

This selector is reported for reproducibility but rejected: the T202 ramp supplies no wrap-aware decimal carry or target-location mechanism.

