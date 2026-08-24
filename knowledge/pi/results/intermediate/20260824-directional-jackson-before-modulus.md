# Directional Jackson cancellation before taking a modulus

Status: `machine-checked` core and actual-Jackson separators at `q=1` and
decimal scale `q=10`; the general closed coefficient formulas remain
`proof sketch`

Date: 2026-08-24 UTC

Source branch and commit:
`pi-core-consolidation` at
`a9b62f2a61d7acf4e3a86ae3d2c2f4fdd5f016c3`.

Integration note: T124 machine-checks the directional obstruction,
`directional <= aggregated`, the wordwise pi premise, its implication to V1,
and actual-Jackson threshold separators at `q=1` and `q=10`. At `q=10`, Lean
checks the exact directional value and proves aggregated failure from the
single `h=10` term. The general coefficient formulas and exact full aggregate
load remain `proof sketch`. The Lean source and axiom audit are proof authority.

## Claim boundary

The preceding note
[`20260824-aggregated-jackson-frequency-cancellation.md`](20260824-aggregated-jackson-frequency-cancellation.md)
collects equal Jackson frequencies before applying the triangle inequality.
This note removes the next loss: for a prescribed decimal cylinder, retain the
signed real part of the centered Fourier sum instead of taking its modulus.

The result is a strictly weaker finite Jackson predicate, separated from the
new aggregated predicate at the actual decimal scale `q=10`.  A wordwise
fixed-pi version would imply canonical V1, and its cutoff may depend on the
actual word rather than only on its length.

No such fixed-pi estimate is proved here.  This note proves no density,
normality, V1, prescribed-word occurrence, or fixed-pi cancellation, and makes
no novelty or optimality claim.

## Exact directional quantity

Use the positive aggregated Jackson coefficients `A_q(h)` established in the
preceding note.  They satisfy

\[
 A_q(-h)=A_q(h),\qquad A_q(h)>0\quad(0<|h|\le 2q-1),
\]

\[
 A_q(0)=C_0(q):=\frac1{3q}+\frac2{3q^3},
 \tag{1}
\]

and

\[
 \sum_{|h|\le2q-1} A_q(h)=2.
 \tag{2}
\]

For a sample `x_0,...,x_{N-1}` define

\[
 S_h(x,N)=\sum_{n<N}e^{2\pi i h x_n}.
\]

For the interval `[a,a+1/q)`, let

\[
 c=a+\frac1{2q}
\]

be its center and set

\[
 Z_q(x,N,c)
 =\sum_{0<|h|\le2q-1}
   A_q(h)e^{-2\pi i h c}S_h(x,N).
 \tag{3}
\]

The **directional Jackson defect** for that interval is

\[
 D_q(x,N,a)=-\frac{\Re Z_q(x,N,c)}N.
 \tag{4}
\]

Unlike both the T120 load and the aggregated load, `D_q` is tied to the target
cylinder and can use cancellation in the signed real part.

## Empty interval forces a directional defect

Assume `N>0`, every sample point lies in `[0,1)`, and the interval
`[a,a+1/q)` is empty.  The verified Jackson minorant is nonpositive at every
shifted sample point.  Summing its real part and using the aggregated Fourier
expansion gives

\[
 0\ge
 N A_q(0)+
 \Re\sum_{h\ne0}A_q(h)e^{-2\pi i h c}S_h(x,N).
\]

Hence

\[
 \boxed{D_q(x,N,a)\ge C_0(q).}
 \tag{5}
\]

Therefore

\[
 D_q(x,N,a)<C_0(q)
 \tag{6}
\]

forces a hit in `[a,a+1/q)`.

This is the Jackson argument before applying even the first modulus.  With
`L_q^agg` denoting the aggregated load from the preceding note and
`L_q^raw` the current T120 load, one has pointwise

\[
 \boxed{
 D_q(x,N,a)
 \le \frac{|Z_q(x,N,c)|}{N}
 \le L_q^{\rm agg}(x,N)
 \le L_q^{\rm raw}(x,N).
 }
 \tag{7}
\]

The first inequality is `-Re z <= |z|`; the second is the triangle inequality
after frequency aggregation; the third is the exact low-frequency surcharge
identity already proved in the preceding note.

## Exact separator at the one-digit decimal scale

Take the genuine decimal scale `q=10`, the first cylinder `[0,1/10)`, and a
single sample at its center:

\[
 N=1,\qquad a=0,\qquad x_0=c=\frac1{20}.
\]

For every integer frequency,

\[
 e^{-2\pi i h c}S_h(x,1)=1.
\]

Equations (1)--(2) therefore give

\[
 Z_{10}(x,1,c)=2-C_0(10).
\]

Since

\[
 C_0(10)=\frac1{30}+\frac1{1500}=\frac{17}{500},
\]

one obtains the exact directional value

\[
 \boxed{D_{10}(x,1,0)=-\frac{983}{500}<\frac{17}{500}.}
 \tag{8}
\]

The same sample has `|S_h(x,1)|=1` for every `h`. Positivity of all aggregated
nonzero coefficients and (2) give at proof-sketch level

\[
 \boxed{
 L_{10}^{\rm agg}(x,1)
 =2-C_0(10)
 =\frac{983}{500}
 >\frac{17}{500}.
 }
 \tag{9}
\]

Lean does not need the full equality in (9): the single exact coefficient
`A_10(10)=83/1000` already exceeds `17/500`, so the aggregated criterion
fails. Consequently the directional finite criterion succeeds while the
aggregated criterion fails; by (7), the current T120 raw criterion fails as well. This is
an exact threshold-crossing separator using the actual Jackson kernel, an
actual decimal cylinder, and `q=10`.  It is not an equivalent reformulation,
a duplicated-frequency artifact, or computational orbit evidence.

Together with the separator in the preceding note, the verified consumer now
has three genuinely distinct finite levels:

\[
 \text{directional signed defect}
 \quad<\quad
 \text{frequency-aggregated modulus load}
 \quad<\quad
 \text{unaggregated T120 load},
\]

where each strictness is witnessed on the decimal-scale family.

## Wordwise directional premise for pi

For a nonempty decimal word `s` of length `k`, let

\[
 q_s=10^k,
 \qquad
 a_s=\operatorname{decimalCylinderLeft}(s).
\]

Consider the premise

\[
 \forall s\ne[]\ \exists N_s>0:\qquad
 D_{q_s}(\operatorname{piOrbit},N_s,a_s)<C_0(q_s).
 \tag{10}
\]

If `s` were missing before `N_s`, its cylinder would be empty and (5) would
contradict (10).  Thus every nonempty word occurs, while the empty word is
trivial.  Hence (10) implies canonical V1.

This premise is weaker than the uniform aggregated premise at two independent
places:

1. it retains the signed center-dependent real part instead of taking a
   modulus and then a triangle inequality; and
2. `N_s` may depend on the actual word, whereas the aggregated and T121
   premises use one cutoff for all words of a fixed length.

The existing T121 weighted premise implies (10): use its cutoff for length
`k` and apply (7).  The decimal-scale separator (8)--(9) proves strictness of
the underlying finite predicates.  It does not prove a logical separation
between two already established properties of pi.

## Why this is not T111 in disguise

T111 already contains a signed full-DFT trough criterion for occupancy of a
fixed finite cyclic mesh cell.  The present quantity is different: it is the
signed real part of the natural-scale Jackson minorant used by T120/T121, with
bandwidth `2q-1`, exact zero mode `C_0(q)`, and the phase fixed by a prescribed
real decimal cylinder.  No claim of novelty for signed Fourier occupancy
certificates in general is made.

## Relation to the negative-result memory

The mechanism uses none of the routes already retired in
`t120_t119_metric_nearpair_and_forcing_obstructions_20260822.md`.  It assumes no
BBP independence, no determinant-size conversion, no denominator-to-
Archimedean separation, and no fixed-prime residue lower bound.  It only
removes losses internal to the verified Jackson consumer.

## Exact remaining gap

The live external obligation is now

\[
 \boxed{
 \forall s\ne[]\ \exists N_s>0:\quad
 -\frac1{N_s}\Re\sum_{0<|h|\le2\cdot10^{|s|}-1}
 A_{10^{|s|}}(h)
 e^{-2\pi i h c_s}
 S_h(\operatorname{piOrbit},N_s)
 <
 \frac1{3\cdot10^{|s|}}+
 \frac2{3\cdot10^{3|s|}},
 }
\]

where

\[
 c_s=\operatorname{decimalCylinderLeft}(s)+\frac1{2\cdot10^{|s|}}.
\]

No theorem currently in the repository controls this signed,
center-dependent fixed-pi sum.  A successful arithmetic argument must retain
phase information tied to the target cylinder; once absolute values are taken,
the gain in (7) cannot be recovered.

T124 now formalizes (3)--(5), (7), the directional value in (8), aggregated
threshold failure at `q=10`, and the implication (10) `->` V1. The remaining
formalization gap is the general closed coefficient formula, its positivity,
and the exact full-load identity (9).

## Verification performed

- The obstruction (5) was derived directly from the verified T120/T121 finite
  Fourier identity before `-Re z <= |z|` is applied.
- The hierarchy (7) was checked term by term against the aggregated
  coefficients and the current unaggregated load.
- The separator uses the exact identities `A_q(0)=C_0(q)` and
  `sum_h A_q(h)=2` established in the preceding commit; at `q=10` all displayed
  values reduce to exact rational arithmetic.
- The implication to V1 is the same missing-cylinder contrapositive as T121,
  with the cutoff allowed to depend on the word.

The T124 declarations cited above are kernel-checked and registered in the
central axiom audit. The remaining general formulas retain `proof sketch`
status.
