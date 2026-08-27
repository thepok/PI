# Topological orbit spread does not force a signed T189 sector

Date: 2026-08-27 UTC

Claim labels: the Chen--Ye--Zheng source boundary is `literature-checked` by
the repository's pinned source audit; the sparse-packet construction is a
`proof sketch`; the inherited root MR table is an `experiment`.  No statement
about the actual pi orbit, unbounded MR failure, V1, density, or normality is
proved.

## Live literature input

[Chen--Ye--Zheng, arXiv:2604.14036v1](https://arxiv.org/abs/2604.14036v1),
Theorem 1.3 and Corollary 3.4, give genuinely pointwise information for the
applicable fixed-pi decimal sequence: an infinite omega-limit set, a limsup
distance at least `1/11` from the integers, and spread at least `1/10` in one
slice of every arithmetic progression.  The source pins and applicability
audit are recorded in the archived one-character and centered-carry reports.

These conclusions are topological.  They contain no return frequency, gap
bound, prescribed target, predecessor label, or signed block estimate.  The
following decimal-orbit construction shows that this distinction is fatal for
using those conclusions alone as the T189 arithmetic rung.

## Sparse-packet construction

Write `alpha=0.a_1 a_2 ...` and

```text
x_n(alpha) = fract(10^n alpha) = 0.a_(n+1) a_(n+2) ... .
```

Choose:

- positions `t_j` with `lcm(1,...,j) | t_j`;
- lengths `ell_j -> infinity`;
- disjoint packets with gaps tending to infinity;
- `sum_(i<=j) ell_i = o(t_j)` and `ell_j=o(t_j)`;
- a circle sequence `y_j` whose every tail is dense.

Set every decimal digit to `3`, except that positions
`a_(t_j+1),...,a_(t_j+ell_j)` copy the first `ell_j` digits of `y_j`.  Use
canonical decimal expansions.  Then

```text
distance_circle(x_(t_j)(alpha), y_j) <= 10^(-ell_j).
```

For each fixed progression modulus `M`, every sufficiently late `t_j` is
zero modulo `M`.  Hence the omega-limit set of
`{x_n(alpha): n=0 mod M}` is the full circle.  In particular this construction
satisfies conclusions much stronger than spread `1/10` and limsup distance
`1/11`.

Let `E` be the set of non-`3` digit positions.  The packet hypotheses make
`E` density zero.  For fixed `K`, the first `K` suffix digits of `x_n` differ
from those of `1/3` only when `[n+1,n+K]` meets `E`, also a density-zero set.
Uniform continuity therefore gives

```text
(1/L) * sum_(n<L) delta_(x_n(alpha))  ->  delta_(1/3).
```

Thus full progression-slice omega spread is compatible with an orbit spending
asymptotic density one near the harmful fixed point `1/3` and with arbitrarily
long gaps between its dense excursions.

## Consequence for the literal signed sector

At the registered root parameters `q=1000,A=334,d=3`, the exact fixed-point
T189 nonzero-sector summand at `x_n=1/3` has the directed sign

```text
K < -0.03417.
```

Inside packet-free runs of `3` digits with a sufficiently long guard before
the next packet, the predecessor digit is exactly `3` and the suffix converges
geometrically to `1/3`.  Continuity of the literal T179 kernel yields, for
arbitrarily large block lengths `L`,

```text
Xi_3(block) / L -> K < -0.03417.
```

Hence even full omega spread in every progression does not force a favorable
fresh target-signed sector, a positive frequency of favorable sectors, or a
bounded wait for one.

This does **not** by itself show MR failure.  MR uses

```text
P_d + q*(Delta_0 + Xi_d - 21/q)
```

and maximizes over all improving digits.  The fixed-point computation signs
only the root digit-3 nonzero sector; `Delta_0` and the other digits can change
the conclusion.  No all-scale sign for `A=(q+2)/3` is claimed.

For the finite root experiment, one may prescribe the first `N=10000` pi
digits, continue with a sufficiently long `3` block beyond `H=100000`, and
start the first dense packet arbitrarily late.  By continuity this converges
to the independently replayed pi-prefix-plus-`333...` control, whose strict
floating-point margins have positive root capital but no surviving child.
This inherits only an `experiment`, not a directed MR separator.

## Exact boundary and reopening condition

The Gottschalk--Hedlund route fails because the orbit closure is not minimal
and contains the fixed subsystem `{1/3}`.  A positive-drift subaction for the
root signed sector would contradict its negative fixed-point value.  A
stopping-time route fails because topological spread permits arbitrarily long
negative waits before every rare excursion.

Reopen this route only with a quantitative actual-pi theorem giving positive
lower frequency or bounded gaps for a target-signed good set jointly labelled
by predecessor digit and suffix.  More omega-limit diameter, infinitude, or
unquantified excursions cannot feed MR.
