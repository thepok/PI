# Active-scale cross-energy heredity separator

Status: `proof sketch` supported by a directed-interval `experiment`

Date: 2026-08-29 UTC

This result is not about the actual pi tail and proves no failure on the
actual pi tree. It closes one orbit-generic hope: corrected cross-energy
positivity is not inherited along a fixed legal FMR edge even when the edge
starts at the active scale `q=1000`, both endpoint nodes have positive score,
the replacement shares the T173-certified pi prefix, and an arbitrarily small
continuation is transcendental with irrationality exponent two.

## Reproducible terminating core

Let `p` be the first 10015 fractional decimal digits certified by T173 and put

```text
W = p ++ 0^9985 ++ 5133428,
alpha_0 = 0.W0000...
```

Thus `W` has length 20007. Its mathematical word hashes are

```text
sha256(p) = 97f28d126aefbf16c98d17737197bf41ca8d32bc3b204aedcde293c338ffc331
sha256(W) = 7fb44517b3d61021d9ad7edf6257ef5478cbbb9b3d2d9159ab9e4050dde36ee0
```

The tracked reproducer generates `W` from the pinned pi digit source, checks
the T173 numeral and both hashes, and retains the exact primitive endpoint.
For the generalized T139 score `B_alpha`, define at `(q,A)`, `Q=10q`,

```text
G_d = B_alpha(Q,A+dq,q)-B_alpha(q,A,q),
D_d = B_alpha(Q,A+dq,Q)-B_alpha(Q,A+dq,q),
F_d = G_d+D_d,
E   = sum_d D_d*F_d-sum_d D_d^-*F_d^-.
```

A 30-decimal outward-interval replay certifies the explicit fixed edge

```text
(1000,334) --d=1--> (10000,1334).
```

At its root,

```text
B_alpha(1000,334,1000) > 3671.2580,
E_alpha(1000,334)      > 5889773540.6322,
FMR digits             = {0,1,2,3,4,8,9},
D_1                    > 17344.3767,
F_1                    > 12499.2388.
```

Hence digit `1` is a legal FMR edge and the reached parent remains positive:

```text
B_alpha(10000,1334,10000) > 16170.4968.
```

At that reached node,

```text
E_alpha(10000,1334)
  in [-4380913919.534852428946566927,
      -4380913919.534852428626660839],
FMR digits = {5},
D_5 > 40906.1957,
F_5 > 2423.7368.
```

The final child score is also positive. Thus literal FMR survives uniquely
while corrected cross-energy becomes strictly negative.

## Exact failure mechanism

At the bad node all common-negative coordinates cancel from `E`; the only
remaining coordinates are

```text
E = D_5*F_5 + D_8*F_8,
D_5*F_5 in [99145855.64, 99145855.66],
D_8*F_8 in [-4480059775.19, -4480059775.17].
```

The packet places the literal child `5` just above its same-child threshold,
while the inherited child-8 score turns the long zero-tail loss into a much
larger opposite-sign product. The packet lies at orbit time `20000`, inside
the literal natural fresh horizon `10000<=n<100000`; no translated auxiliary
block is used.

## Open stability and a `mu=2` realization

The exact coefficients give the elementary bounds

```text
sum_u |p_(m,C)(u)| < 12,
sum_u u*|p_(m,C)(u)| < 12m,

|B_xi(m,C,L)-B_eta(m,C,L)|
  < (8*pi/3)*m^2*(10^L-1)*|xi-eta|.
```

Set

```text
alpha_TM = alpha_0 + 10^-100050 * tau_10,
```

where `tau_10` is the base-ten Thue--Morse--Mahler number. Since `alpha_0`
is zero after place 20007, there is no carry. Every score above changes by
less than `9*10^-40`, every `D_d,F_d` by less than `1.8*10^-39`, and `E` by
less than `10^-32`. All strict signs and complete FMR sets persist.

Yann Bugeaud proves that these Thue--Morse--Mahler numbers have irrationality
exponent exactly two and records the classical Mahler transcendence input in
[On the rational approximation to the Thue--Morse--Mahler numbers](https://doi.org/10.5802/aif.2666).
Rational-affine invariance therefore makes `alpha_TM` transcendental with
`mu(alpha_TM)=2` (`literature-checked`).

## Exact scope

The following orbit-universal implication is false, already at `q=1000`:

```text
B_alpha(q,A,q)>0 and E_alpha(q,A)>0
and D_d>0 and F_d>0
  -> E_alpha(10q,A+dq)>0.
```

It remains false after requiring a genuine decimal orbit, a positive reached
node, a legal FMR child there, the T173 10015-digit pi prefix,
transcendence, and irrationality exponent two. This closes same-edge generic
heredity at the active scale; the previous scale-free-only qualification is
obsolete.

It does **not** refute an existential selector which may choose another of
the seven root FMR children, and it gives no actual-pi sign. Reopen the
cross-energy route only with an adaptive selector theorem or an actual-pi
joint-character estimate controlling the opposite-sign leakage.

The standalone reproducer is
[`t189_active_scale_cross_energy_edge_interval.py`](../../../../workflows/experiments/t189_active_scale_cross_energy_edge_interval.py).
It uses the exact T139/T174 closed kernel and endpoint, asserts both complete
FMR sets, and exits only after every displayed strict interval is certified.

An independent 191-periodic construction sharing 10020 pi digits also gives
the same active edge with reached `E<-3.183*10^9` and unique reached FMR digit
`0` (`experiment`). It is omitted as a second active artifact because the
terminating one-packet construction above is shorter, faster, and stronger.
