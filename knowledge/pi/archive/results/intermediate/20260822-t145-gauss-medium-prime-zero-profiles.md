# T145: exact finite Gauss medium-prime zero profiles

Status: `experiment`  
Last audited: 2026-08-22

## Exact experiment

For `delta=1/12`, an odd prime `X/2<p<2X`, and the T143/P19 direct and
reflected rays, the inclusive ranges simplify exactly to

```text
R_D = [max(X-p+1,ceil(p/11),1),
       min(2X-p,floor(p/3),floor((p-1)/2))],

R_R = [max(2p-1-2X,ceil((2p-1)/13),1),
       min(2p-X-2,floor((2p-1)/5),floor((p-2)/2))].
```

Empty ranges contribute zero.  The script computes `A_r mod p` through the
exact recurrence

```text
(r+1)A_(r+1)=2(2r+1)A_r+4rA_(r-1),
A_0=1, A_1=2.
```

All ray indices satisfy `r<p`, so division by `r+1` is valid in `F_p`.
It records the complete profile
`(p,R_D,R_R,Z_p^D,Z_p^R,Z_p)` for every prime in every band.

It also computes the exact order of

```text
rho=-3+2sqrt(2)
```

in `Z[sqrt(2)]/p`.  For split primes this is the common order of the two
inverse components in `F_p x F_p`; for inert primes it is the order in the
norm-one subgroup of `F_(p^2)^*`.  The order is reduced from `p-1` or `p+1`
using exact factorization and powering.

## Aggregate profiles

Here `P` is the number of primes, `NZ` the number with `Z_p>0`, and `sumZ2`
is `sum_p Z_p^2`.

| `X` | `P` | `NZ` | `sumZ` | `sumZ2` | `maxZ` |
|---:|---:|---:|---:|---:|---:|
| 2048 | 392 | 71 | 99 | 165 | 4 |
| 4096 | 719 | 126 | 178 | 308 | 4 |
| 8192 | 1336 | 242 | 339 | 581 | 4 |
| 16384 | 2484 | 422 | 576 | 948 | 4 |
| 32768 | 4642 | 837 | 1165 | 1999 | 6 |

The complete mod-8 strata, each written `(P,NZ,sumZ,sumZ2,maxZ)`, are:

| `X` | `p=1 mod 8` | `p=3 mod 8` | `p=5 mod 8` | `p=7 mod 8` |
|---:|---:|---:|---:|---:|
| 2048 | (95,20,29,55,4) | (101,21,28,44,3) | (98,8,10,14,2) | (98,22,32,52,2) |
| 4096 | (179,38,59,115,4) | (179,30,41,69,4) | (181,27,33,45,2) | (180,31,45,79,4) |
| 8192 | (331,54,70,116,4) | (331,63,92,164,4) | (334,63,91,163,4) | (340,62,86,138,3) |
| 16384 | (614,106,148,256,4) | (630,109,133,181,2) | (623,104,142,236,4) | (617,103,153,275,4) |
| 32768 | (1150,216,296,486,4) | (1158,192,251,393,4) | (1166,214,300,518,5) | (1168,215,318,602,6) |

Maximum-zero examples occur at very different orders:

```text
X=2048:  (Z,p,ord,Z_D,Z_R)=(4,2137,534,2,2)
X=8192:  (4,6709,305,2,2), (4,5683,5684,0,4)
X=16384: (4,17359,17358,2,2)
X=32768: (6,35423,35422,3,3), (5,29629,14815,2,3),
         (4,37649,18824,3,1).
```

Thus the observed maximum occurs both at comparatively small order and at
orders essentially `p-1` or `p+1`; the largest observed value `Z=6` occurs at
the near-maximal order `35422=p-1`.  The finite data establish no implication
from large `Z_p` to bounded or small root-ratio order.

Reproducer:
[`workflows/research/pi/t145_gauss_medium_prime_profiles.py`](../../../../workflows/research/pi/t145_gauss_medium_prime_profiles.py)

Audited script SHA-256:

```text
1d7a98700f304744a8093af0d05732e73550a9420900f9fbea472e9216f117bd
```

## Scope

These are exact finite profiles, not an anti-concentration theorem.  They do
not prove a P19 GO or STOP outcome, do not establish the punctured
confluent-Vandermonde implication proposed in T144, and give no first-band,
`(D)`, or `V1` progress.

V1 remains open.
