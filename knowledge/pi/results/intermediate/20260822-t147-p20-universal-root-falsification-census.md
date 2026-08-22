# T147: finite P20 universal-root falsification census

Status: `experiment`  
Last audited: 2026-08-22

## Frozen screen

For each odd prime `p<=503`, put

```text
m=(p-1)/2,
N_p=p-(2/p),
I_p=[ceil(p/11),floor(2p/5)],
k_p=min{k:k^2>=p},
D_p=max{d:d^3<=p},

F_j(X)=sum_t binom(m,t)binom(m,j-m+t)X^t,
```

with `max(0,m-j)<=t<=min(m,2m-j)`.  Primes with `|I_p|<k_p` are omitted.
For split primes the script enumerates every `x` in `F_p^*`; for inert primes
it enumerates every norm-one `x=a+b sqrt(2)` in `F_(p^2)`.  These are exactly
the `N_p` roots of `X^(N_p)-1`.  It computes the exact multiplicative order,
discards `ord(x)<=D_p`, and counts

```text
#{j in I_p:F_j(x)=0}.
```

A counterexample to the frozen P20 universal-subset criterion would give one
such high-order root with at least `k_p` zeros: any `k_p` of those indices
would be a common-zero subset.  Conversely, a common high-order root for a
`k_p`-subset is detected by this enumeration.

## Exact result

There are `92` eligible odd primes through `503`.  No enumerated high-order
root has `k_p` simultaneous zeros.  The global maximum is `4`, attained at
exactly the following four primes (one conjugate/inverse representative is
shown where there are symmetric witnesses):

| `p` | root `x` | `ord(x)` | zero indices in `I_p` |
|---:|---|---:|---|
| 197 | `16+63sqrt(2)` | 99 | `30,42,46,67` |
| 251 | `17+12sqrt(2)` | 42 | `25,41,75,83` |
| 367 | `25` | 61 | `63,86,94,121` |
| 479 | `36` | 239 | `59,159,179,182` |

At each of these primes `k_p>=15`, so the observed maximum remains far below
the frozen threshold.  All membership, field arithmetic, orders, polynomial
values, interval endpoints, and thresholds are computed with exact integers.
The recurrence used for the polynomial values follows from

```text
F_j(x)=x^m[z^j](1+z)^m(1+x^(-1)z)^m;
```

the script retains the nonzero factor `x^m` explicitly.

Reproducer:
[`workflows/research/pi/t147_p20_universal_root_falsification.py`](../../../../workflows/research/pi/t147_p20_universal_root_falsification.py)

Audited script SHA-256:

```text
38fab9a5231f6664ccfd2c4ac1afd92b3d6d6843e96f42118b72911d04552175
```

## Scope

This finite failure-to-falsify is not evidence that the universal-subset
criterion holds for all primes, and it is not a theorem or a Pro-model
trigger.  It proves no P20 GO or STOP outcome, no diagonal power saving, and
no `(D)` or `V1` progress.

V1 remains open.
