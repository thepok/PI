# Topological orbit spread does not force a signed T189 sector

Date: 2026-08-27 UTC

Claim labels: the Chen--Ye--Zheng source boundary is `literature-checked` by
the repository's pinned source audit; the Fishman input below is
`literature-checked`; the sparse-packet and missing-word constructions are
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

## Independent-base density does not collapse to the decimal orbit

A 2026-08-28 PaperSearch audit of
[Haynes--Munday](https://arxiv.org/abs/1303.1661) gives another exact
pointwise boundary.  Put `T(x)=10*x mod 1`, `S(x)=16*x mod 1`, and

```text
X = closure {T^n(pi mod 1) : n>=0}.
```

Since `10` and `16` are multiplicatively independent and `pi` is irrational,
their theorem makes `{T^a S^b(pi mod 1):a,b>=0}` dense.  Commutation and
continuity then prove the exact equivalence

```text
S(pi mod 1) in X
  <-> S(X) subset X
  <-> X is the full circle.
```

Indeed the first condition makes every `S(T^n pi)=T^n(S pi)` lie in `X`,
hence gives the second by closure.  The second puts the entire dense mixed
orbit in `X`.  Thus the tempting assertion `16*pi mod 1 in X` is already
equivalent here to decimal-orbit density, not a weaker transfer lemma.

Mixed density alone does not even transfer one fixed sign.  Choose an
irrational `alpha` whose decimal digits all lie in `{0,1}`.  Its pure decimal
orbit closure lies in `[0,1/9]`, so `-cos(2*pi*x)<0` throughout that closure,
whereas the mixed `(10,16)` orbit is dense and takes both signs.  For a
specific `L`-Lipschitz carrier, a mixed value of margin `eta-mu>0` transfers
only if its point lies within `(eta-mu)/L` of `X`.  For a chronological block
of length `H`, the Lipschitz cost grows by

```text
(10^H-1)/9,
```

so the needed pure-orbit shadow is exponentially fine.  Even that transfers
only the fresh block; T189 still requires the same return and predecessor
digit to cover the inherited `G_d` deficit.  Independent-base density
controls neither quantity.

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

## Missing-word shifts remain Diophantine-rich

There is also a direct obstruction to replacing signed orbit information by
generic transcendence or irrationality-measure input.  Let `w` be any
nonempty decimal word of length `m`, and let `P` be any finite `w`-free
prefix.  Put `a` equal to the first digit of `w` and choose a digit `b`
different from both the first and last digits of `w`.  Append the guard
`b^m`, then restrict every later digit to

```text
D_a = {0,...,9} \ {a}.
```

No copy of `w` ends in the guard, because its last digit would be `b`; the
guard is long enough that no copy can cross both boundaries; and no later copy
can start because the tail contains no `a`.  Thus every resulting digit string
begins with `P` and avoids `w`; excluding the countable ambiguous decimal
endpoints makes these the canonical expansions.

The unrestricted `D_a` tails form the self-similar attractor of the nine maps

```text
x |-> (d+x)/10,  d in D_a,
```

with Hausdorff dimension `log(9)/log(10)`.  The maps satisfy the open set
condition.  [Fishman's theorem](https://arxiv.org/abs/math/0606298) therefore
gives full attractor dimension after intersection with the badly approximable
numbers.  Rational affine insertion into the cylinder `P b^m` preserves bad
approximability.  Removing the countable algebraic numbers and the countable
ambiguous decimal endpoints leaves a positive-dimensional family of
transcendental, badly approximable, `w`-avoiding continuations of `P`.

Consequently, even under a hypothetical missing word in pi, every finite pi
prefix admits hostile continuations with transcendence and irrationality
exponent exactly `2`, stronger Diophantine approximation control than is known
for pi.  Lindemann--Weierstrass, a finite irrationality exponent, digit-change
bounds, and finite-prefix certificates therefore cannot exclude membership in
a positive-entropy missing-word shift.  A reopening theorem must use a
genuinely pi-specific constraint on the digit language or directly recover
target-signed orbit information.

## Fresh-window nine-label upgrade

An independently audited `proof sketch` strengthens the preceding construction
from positive entropy to exact eventual label abundance. Let `p` be a finite
prefix not already containing the nonempty word `w`. Delete one digit `a`
occurring in `w` and put `B={0,...,9}\{a}`. A bridge of length `|w|-1` over
`B` can be chosen greedily so that `w` does not cross the prefix boundary;
every later `B`-tail then avoids `w`.

Choose one fixed interior digit `c in B intersect {1,...,8}`. Under the uniform
Bernoulli measure on `B^N`, sample disjoint `(k+1)`-blocks starting at

```text
n_j = 10^k + j*(k+1),
0 <= j < floor(9*10^k/(k+1)).
```

For a fixed `u in B^k`, the failure probability for `uc` is at most
`exp(-M_k/9^(k+1))`. A union bound over all `9^k` labels is summable because
`M_k>=8*10^k/(k+1)`. Borel--Cantelli therefore gives, for almost every tail
and all sufficiently large `k`,

```text
forall u in B^k, exists n in [10^k,10^(k+1)):
  digits_(n+1 ... n+k+1) = u c.
```

The same Bernoulli measure is friendly/extremal by Kleinbock--Lindenstrauss--
Weiss, [*On fractal measures and Diophantine approximation*](https://doi.org/10.1007/s00029-004-0378-2),
so this full-measure event can be intersected with `mu=2`; removing the
countable algebraic points makes the continuation transcendental. Rational
prefix insertion preserves the exponent.

For a literal scale-`10^k` label, the normalized radius is exactly

```text
y_k(n) = fract(10^k*x_n)-1/2 = x_(n+k)-1/2.
```

The following interior digit gives `|y_k(n)|<=2/5<9/22`. Hence a paper-level
orbit-generic replay of T191--T193 gives a central positive primitive unit for
every encoded label in `B^k` inside the exact fresh window. Eventually the
set of available central fresh labels is exactly the encoded set `B^k`.

This is a tree of available labels, not a coherent T176/T189 edge tree: the
witness times for `u` and `du` may be unrelated. It refutes criteria based
only on uniform proper-alphabet arity or positive-label abundance. It does
not refute a nine-branch criterion carrying additional transition-sensitive
or genuinely pi-specific signed information. Only `w` is globally absent;
other words containing `a` may occur in the finite prefix.

## Exact boundary and reopening condition

The Gottschalk--Hedlund route fails because the orbit closure is not minimal
and contains the fixed subsystem `{1/3}`.  A positive-drift subaction for the
root signed sector would contradict its negative fixed-point value.  A
stopping-time route fails because topological spread permits arbitrarily long
negative waits before every rare excursion.

Reopen this route only with a quantitative actual-pi theorem giving positive
lower frequency or bounded gaps for a target-signed good set jointly labelled
by predecessor digit and suffix.  More omega-limit diameter, infinitude, or
unquantified excursions cannot feed MR.  A mixed-to-decimal route additionally
needs a coefficient-specific quantitative return jointly aligned with `G_d`;
global `16`-invariance merely assumes decimal density in disguise.
