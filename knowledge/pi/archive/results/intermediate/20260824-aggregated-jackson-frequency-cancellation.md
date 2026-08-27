# Aggregating equal Jackson frequencies removes the low-mode surcharge

Status: `machine-checked` core and one actual-Jackson strict separator;
closed formulas and the all-`q >= 5` separator remain `proof sketch`

Date: 2026-08-24 UTC

Source branch and commit:
`pi-core-consolidation` at
`3733305a2e85f57c91d669b7acaad47f5bee3299`.

Integration note: T123 machine-checks exact same-frequency regrouping, the
aggregated empty-interval obstruction, `aggregated <= raw`, the implication
from the aggregated pi premise to V1, and an actual Jackson threshold-crossing
separator at `q=2`. The stronger closed coefficient formulas, surcharge
identity, more-than-fourfold bound, and uniform `q>=5` separator below remain
`proof sketch`. The Lean source and axiom audit are proof authority.

## Frontier edge attacked

[`T120T120WeightedNaturalScaleFrontier.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T120T120WeightedNaturalScaleFrontier.lean)
takes absolute values term by term in the unaggregated order-`q` Jackson
presentation.  Many different Jackson indices have the same integer
frequency.  The triangle inequality is therefore applied before exact
same-frequency cancellation.

Grouping equal frequencies first gives a strictly smaller useful load.  This
is not an equivalent repackaging:

- an empty `1/q` interval still forces the grouped load above the same exact
  zero-mode threshold;
- the current T120 load equals the grouped load plus an explicit nonnegative
  low-frequency surcharge; and
- for every `q >= 5` there is an explicit finite sequence for which the grouped
  criterion succeeds while the current T120 criterion fails.

The fixed-pi grouped cancellation estimate remains open.

## Exact grouped Jackson coefficients

Write

\[
 e_h(t)=\exp(2\pi i h t),\qquad
 S_h(x,N)=\sum_{n<N}e_h(x_n).
\]

For `q >= 1`, let

\[
 a_q(m)=
 \begin{cases}
 (q-|m|)/q,& |m|<q,\\
 0,& |m|\ge q,
 \end{cases}
 \qquad
 B_q(h)=\sum_{m\in\mathbb Z}a_q(m)a_q(h-m).
\]

The normalized Fejer factor already present in
[`T6PiNaturalScaleResonanceObstruction.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean)
is

\[
 F_q(t)=\sum_m a_q(m)e_m(t).
\]

The exact order-`q` Jackson minorant used by T19 and T120 is

\[
 J_q(t)
 =\left(\frac{2}{q^2}-1+\cos(2\pi t)\right)F_q(t)^2.
 \tag{1}
\]

Indeed, the main quadruple term is `(2/q^2) F_q^2`, while the edge
term is

\[
 -\frac12 |(1-e_1(t))F_q(t)|^2
 =-(1-\cos(2\pi t))F_q(t)^2.
\]

Let `A_q(h)` be the coefficient of `e_h` after collecting equal
frequencies in (1).  Then

\[
 A_q(h)=
 \left(\frac{2}{q^2}-1\right)B_q(h)
 +\frac{B_q(h-1)+B_q(h+1)}2.
 \tag{2}
\]

For `0 <= h <= q`,

\[
 B_q(h)=
 \frac{3h^3-6qh^2-3h+4q^3+2q}{6q^2},
\]

and for `q <= h <= 2q`,

\[
 B_q(h)=
 \frac{(2q-h)((2q-h)^2-1)}{6q^2}.
\]

Substitution into (2) gives the following positive closed form.  For
`0 <= h <= q`,

\[
 A_q(h)=
 \frac{
   2q(q^2-1)+3hq^2+6h(q-h)^2+6(q-h)
 }{6q^4},
 \tag{3}
\]

while for `q <= h <= 2q-1`, with `d=2q-h`,

\[
 A_q(h)=
 \frac{d(3q^2+2d^2-2)}{6q^4}.
 \tag{4}
\]

Also `A_q(-h)=A_q(h)` and `A_q(h)=0` for `|h| >= 2q`.
Every coefficient in the actual support `|h| <= 2q-1` is strictly positive:
(3) is a sum of nonnegative terms with at least one positive term, and in
(4) one has `d >= 1` and `3q^2+2d^2-2 > 0`.

In particular, the constant coefficient is exactly

\[
 A_q(0)=\frac{q^2+2}{3q^3}
       =\frac1{3q}+\frac2{3q^3}.
 \tag{5}
\]

Thus T19's triangular zero-frequency lower bound is sharp for this fixed
Jackson polynomial.  Further counting of zero-frequency Jackson indices
cannot improve the threshold without changing the kernel.

Since `F_q(0)=q`, equation (1) also gives

\[
 \sum_h A_q(h)=J_q(0)=2.
 \tag{6}
\]

Because all `A_q(h)` are positive, the total nonzero grouped coefficient mass
is exactly `2-A_q(0)`, rather than the unaggregated absolute mass `4`.

## Grouped empty-interval obstruction

Define

\[
 \mathcal L_q^{\rm agg}(x,N)
 =\frac1N\sum_{0<|h|\le 2q-1}A_q(h)|S_h(x,N)|.
 \tag{7}
\]

If the first `N>0` points of `x` lie in `[0,1)` and avoid an interval of
length `1/q`, the existing pointwise Jackson-minorant inequality gives, after
summing over the sample,

\[
 0\ge
 N A_q(0)+
 \Re\sum_{h\ne0}A_q(h)e_h(-c)S_h(x,N),
\]

where `c` is the interval centre.  Applying the triangle inequality only after
frequency aggregation yields

\[
 A_q(0)\le \mathcal L_q^{\rm agg}(x,N).
 \tag{8}
\]

Consequently, for the decimal orbit of pi, the premise

\[
 \forall k\ge1\ \exists N>0:\quad
 \mathcal L_{10^k}^{\rm agg}(\pi,N)
 < A_{10^k}(0)
 \tag{9}
\]

implies canonical V1 by the same missing-cylinder contrapositive used in
[`T121T121WeightedNaturalScaleCriterion.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T121T121WeightedNaturalScaleCriterion.lean).

A direct pointwise corollary of (6)--(8) is also stronger than T19.  It is
enough that, simultaneously for

\[
 0<|h|\le 2q-1,
\]

one has

\[
 \frac{|S_h(x,N)|}{N}
 <
 \frac{A_q(0)}{2-A_q(0)}
 =
 \frac{q^2+2}{6q^3-q^2-2}.
 \tag{10}
\]

T19 uses

\[
 \frac1{24q}+\frac1{12q^3}
 =\frac{q^2+2}{24q^3}.
\]

The ratio of the threshold in (10) to the T19 threshold is

\[
 \frac{24q^3}{6q^3-q^2-2}>4.
\]

Thus aggregation gives a more-than-fourfold pointwise threshold improvement
and removes the unused endpoint frequency `|h|=2q`.  This remains a
conditional finite criterion, not a fixed-pi cancellation theorem.

## Exact comparison with the current T120 load

Let `R_q(h)` be the sum of the absolute values of all unaggregated Jackson
coefficients having frequency `h`.  Grouping the existing T120 definition by
frequency gives

\[
 \mathcal L_q^{\rm raw}(x,N)
 =\frac1N\sum_{0<|h|\le2q-1}R_q(h)|S_h(x,N)|.
\]

The main quadruple coefficients are positive, so the only loss comes from the
edge term.  Its frequency set is

\[
 \{-q+1,\ldots,0,1,\ldots,q\},
\]

with sign `+1` on the nonpositive part and `-1` on the positive part.  For
`1 <= h < q`, there are `2q-h` ordered edge pairs with difference `h`;
exactly `h` cross the sign boundary and `2q-2h` stay on one side.  Hence

\[
 R_q(h)-A_q(h)=\frac{2(q-h)}{q^2}
 \quad (1\le h<q),
\]

whereas every pair crosses the sign boundary for `q <= h <= 2q-1`, so

\[
 R_q(h)=A_q(h)
 \quad (q\le h\le2q-1).
\]

Using `|S_{-h}|=|S_h|` gives the exact load identity

\[
 \boxed{
 \mathcal L_q^{\rm raw}(x,N)
 -
 \mathcal L_q^{\rm agg}(x,N)
 =
 \frac4{q^2}\sum_{h=1}^{q-1}(q-h)
 \frac{|S_h(x,N)|}{N}.
 }
 \tag{11}
\]

Therefore the grouped premise is always weaker than the current T120 premise,
and it is strictly weaker whenever at least one of the first `q-1`
exponential sums is nonzero.

## Separator at every decimal scale

The strictness can be made compatible with every decimal scale, rather than
only with the `q=1` toy separator used in T121.

Fix `q >= 5`, put `M=6q`, and define the first `M` sample points by

\[
 x_0=\frac1M,\qquad x_j=\frac jM\quad(1\le j<M).
\]

This is the full `M`-point grid with `0` replaced by a second copy of `1/M`.
For `1 <= h <= 2q-1 < M` the complete grid sum vanishes, so

\[
 S_h(x,M)=e_h(1/M)-1,
 \qquad
 \frac{|S_h(x,M)|}{M}
 =\frac{\sin(\pi h/(6q))}{3q}.
 \tag{12}
\]

The coefficient formulas give the exact moments

\[
 \sum_{h=1}^{2q-1}hA_q(h)
 =\frac{24q^4-5q^2-4}{30q^3},
 \tag{13}
\]

\[
 \sum_{h=1}^{2q-1}hR_q(h)
 =\frac{34q^4-15q^2-4}{30q^3},
 \tag{14}
\]

and

\[
 \sum_{h=1}^{2q-1}h^3R_q(h)
 =\frac{230q^6-168q^4+35q^2+8}{210q^3}.
 \tag{15}
\]

These are finite polynomial sums obtained by inserting (3)--(4) and using the
standard power-sum identities.

From `sin y < y`, (12), and (13),

\[
 \mathcal L_q^{\rm agg}(x,M)
 <
 \frac{\pi}{9q^2}\sum_{h=1}^{2q-1}hA_q(h)
 <
 \frac{4\pi}{45q}
 <
 \frac1{3q}
 <
 A_q(0).
 \tag{16}
\]

For the raw load, `0 < \pi h/(6q) < \pi/3` and
`sin y >= y-y^3/6`.  Equations (14)--(15) imply, for `q >= 5`,

\[
 \sum hR_q(h)\ge\frac{11q}{10},
 \qquad
 \sum h^3R_q(h)\le\frac{23q^3}{21}.
\]

Therefore

\[
 \mathcal L_q^{\rm raw}(x,M)
 \ge
 \frac1q\left(
   \frac{11\pi}{90}
   -\frac{23\pi^3}{40824}
 \right).
\]

Using the elementary bounds `157/50 < pi < 22/7`,

\[
 \frac{11\pi}{90}-\frac{23\pi^3}{40824}
 >
 \frac{320562187}{875164500}
 >
 \frac9{25}.
\]

Finally, `q >= 5` gives

\[
 A_q(0)
 =\frac1q\left(\frac13+\frac2{3q^2}\right)
 \le\frac9{25q}.
\]

Combining these inequalities yields the strict separator

\[
 \boxed{
 \mathcal L_q^{\rm agg}(x,6q)
 < A_q(0)
 < \mathcal L_q^{\rm raw}(x,6q)
 }
 \qquad(q\ge5).
 \tag{17}
\]

In particular, (17) holds for every `q=10^k`, `k>=1`.  This proves strictness
of the generic finite cancellation predicates on the actual decimal-scale
family.  It does not assert that either fixed-pi premise holds.

## Exact gain and remaining gap

The mathematical gain is a new proof mechanism: combine equal Jackson
frequencies before taking absolute values.  It yields:

1. the exact positive aggregated coefficient kernel (3)--(4);
2. the exact zero mode (5), closing further same-kernel zero-mode counting;
3. total coefficient mass `2` instead of unaggregated absolute mass `4`;
4. the exact low-frequency surcharge identity (11);
5. a more-than-fourfold pointwise threshold improvement over T19; and
6. the decimal-scale strict separator (17).

The remaining fixed-pi gap is precisely to prove, for every `k>=1`, the
existence of `N>0` such that

\[
 \sum_{0<|h|\le 2\cdot10^k-1}
 A_{10^k}(h)
 \frac{|S_h(N)|}{N}
 <
 \frac1{3\cdot10^k}
 +\frac2{3\cdot10^{3k}}.
\]

No such estimate is proved here.  This note proves no density, normality,
decimal disjunctivity, prescribed-word occurrence, or fixed-pi cancellation.

The remaining formalization gap is exact: prove the convolution formulas,
positivity, raw-minus-grouped identity, moment identities, and the full
decimal-scale `q>=5` separator in Lean. The core grouped obstruction and a
concrete actual-Jackson strict separator are already checked in T123; the
stronger claims in this paragraph remain `proof sketch`.
