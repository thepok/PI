# Pathwise cross-energy heredity separator

Status: `proof sketch` supported by a directed-interval `experiment`

Date: 2026-08-29 UTC

This result is not about pi and proves no failure on the actual pi tree. It
separates a specific orbit-generic hope: corrected cross-energy positivity is
not inherited merely from earlier positive cross-energy, legal same-child
regeneration, decimal recurrence, transcendence, and irrationality exponent
two.

## Reproducible periodic core

Let `w=uv`, where

```text
u = first 1000 digits of (6666 0^64)^infinity,
v = first 9000 digits of (2666 0^48)^infinity,
xi_0 = 0.overline(w).
```

The word has SHA-256

```text
8e896b260071cfcde983fe89d509cfbf007ef6a0d25d773bf72d3545c346496c.
```

For the exact generalized T139 score `B_xi`, set at a node `(q,A)`

```text
G_d = B_xi(10q,A+dq,q)-B_xi(q,A,q),
D_d = B_xi(10q,A+dq,10q)-B_xi(10q,A+dq,q),
F_d = G_d+D_d,
E   = sum_d D_d*F_d-sum_d D_d^-*F_d^-.
```

An outward-rounded replay of the exact rational orbit gives the fixed path

```text
(10,6) --6--> (100,66) --6--> (1000,666) --6--> (10000,6666)
```

and certifies:

```text
node             P lower bound    E bound                    FMR digits
(10,6)           46               > 204311                   {0,6}
(100,66)         719              > 1445101901               {0,6}
(1000,666)       32281.8468       < -3080140823.433564       {6}
```

At the bad node the preselected child remains strongly legal:

```text
D_6 > 42249,
F_6 > 10884.
```

Thus child `6` passes two preceding literal FMR edges and reaches a positive
parent where it is the unique FMR witness, yet the complete corrected energy
is negative. The failure is genuine opposite-sign leakage: the
common-positive product at digit `6` is overwhelmed by opposite-sign products
at digits `0` and `2`; common-negative coordinates cancel by definition.

The standalone reproducer is
[`t189_periodic_cross_energy_path_interval.py`](../../../../workflows/experiments/t189_periodic_cross_energy_path_interval.py).
It generates and hashes the word, reuses the existing directed T139 interval
implementation, checks every strict sign and complete FMR set, and uses at
most four workers.

## Open stability and a `mu=2` realization

The machine-checked coefficient formulas imply the elementary `proof sketch`
bounds, for generalized real seeds,

```text
sum_u |p_(m,C)(u)| < 12,
sum_u u*|p_(m,C)(u)| < 12m,

|B_xi(m,C,L)-B_eta(m,C,L)|
  < (8*pi/3)*m^2*(10^L-1)*|xi-eta|.
```

Consequently every seed within `10^-10020` of `xi_0` preserves all displayed
strict signs; the nonlinear clipping term changes each energy by less than
`1.008`. Put

```text
xi_TM = xi_0 + 10^-10020 * tau_10,
```

where `tau_10` is the base-ten Thue--Morse--Mahler number. There is no carry:
the periodic digits lie in `{0,2,6}` and the shifted tail in `{0,1}`. Hence
`xi_TM` shares the first 10020 digits of `xi_0`. The already
`literature-checked` Mahler/Bugeaud input and rational-affine invariance give
transcendence and `mu(xi_TM)=2`. The same path and inequalities therefore
hold for a genuine nonperiodic decimal orbit (`proof sketch` supported by the
replayed strict intervals).

## Exact scope

This destroys only **scale-free orbit-generic heredity** of `E>0`. The
immediate positive predecessor of the bad node has `q=100`, so it does not
refute a theorem whose heredity premise begins only at the active range
`q>=1000`. The construction also does not share a finite pi prefix, does not
show an infinite adversarial path, and says nothing about actual-pi
cross-energy.

Reopen generic heredity only with an additional premise false for this open
`mu=2` family. For the live frontier, the required input remains a
pi-specific joint-character order theorem that bounds the opposite-sign
leakage at recursively reached targets. A sharper active-scale separator
would require one fixed edge with `q>=1000`, positive `E` at its parent, and
negative `E` at its legal FMR child.
