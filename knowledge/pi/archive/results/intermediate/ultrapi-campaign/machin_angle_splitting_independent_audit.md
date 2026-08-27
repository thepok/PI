# Independent audit: recursive Machin-angle splitting

Audit date: **2026-08-12 UTC**  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Audit scope: [`machin_angle_splitting_attack.md`](machin_angle_splitting_attack.md)
and its finite replay

## Verdict

**PASS at the corrected `proof sketch` level.**  The six named splits, four
positive Machin identities, alternating bracket, denominator bounds, local
upper-band prime coordinate, indefinite balanced refinement, and fixed-Taylor-
depth convergence all re-derive correctly.  The construction genuinely
avoids a linear base-ten preperiod: both bracket endpoints have odd reduced
denominator and 5-adic denominator exponent (O(\log R)), independently of
the split-tree depth.

Five precision corrections were made during review:

1. The original general construction assumed (\gcd(b,10)=1) while its
   introduction claimed every positive rational argument.  The proof now
   covers every reduced (x=a/b\in(0,1)): choose the splitting numerator with
   parity opposite to (b), rather than merely requiring (ac) even.
2. Equal positive coordinates of the Gaussian product determine the angle
   only modulo (2\pi).  The report and checker now add the exact bound
   (0<\sum c_i\arctan x_i<\sum c_ix_i<1), which excludes every other branch.
3. The denominator discussion originally treated only the lower endpoint.
   It now gives and tests a safe denominator and logarithmic preperiod for the
   upper endpoint as well.
4. The replay formerly called two width-algebra assertions an “alternating
   bracket” check even though a finite script does not certify the analytic
   alternating-series inequality.  The count is now named accurately, and
   the script separately tests the displayed local congruence rather than
   only its denominator-valuation consequence.
5. The affine-phase conclusion is now stated at its proved strength:
   multiple identities do not create independent CRT coordinates merely by
   being different.  The exact affine relation does not prove that no future
   theorem could exploit several shadows.  The near-boundary rate caveat is
   likewise qualified as not following from the geometric estimate alone.

No decimal-cylinder hit follows.  Canonical V1 remains a `conjecture`.
This work is not `machine-checked`, not a `candidate resolution`, and not a
`verified resolution`.

## Audited pins

| Artifact | SHA-256 |
|---|---|
| Canonical target | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| Corrected report | `6af74d35fd2fbb6b584491d275c70c5ec5b1f9f02182f69e986b50aa33e60124` |
| Corrected primary checker | `7c72b87b9a6e2b9ae7d0db27db6aeb5c06745173719144539c4cd94e96b028aa` |
| Independent checker | `c36ebe182109cc0f4cf5394fbc6f448d5d6ee55fd60b6f9c70223f7a6de126f5` |

The three versioned primary PDFs were fetched afresh:

| Source | SHA-256 |
|---|---|
| Farhi, arXiv:2601.10300v1 | `86cdd17355a4462db9ac18b6e7dcfe2559e14089ed02272247df6cd71ce7b90e` |
| Gasull--Luca--Varona, arXiv:2302.00154v2 | `33dd2d6dc90d34e8e03d9c044ba416e4a843e81654917de03ad3f556565890fa` |
| Abrarov--Quine, arXiv:1706.08835v3 | `7500ccc8cb55f651b81dd6310f02e428d2455ca6739dfb0c382435bfac8b6c3c` |

## 1. Named identities and branch control

For (0<u<x<1), set

\[
 v=\frac{x-u}{1+xu}.
\]

Direct expansion gives

\[
 0<v<x,
 \qquad
 \frac{u+v}{1-uv}=x,
 \qquad
 1-uv=\frac{1+u^2}{1+xu}>0.
\]

Thus both angles are positive, their sum lies below (\pi/2), and the
principal tangent-addition branch gives

\[
 \arctan x=\arctan u+\arctan v.
\]

Substitution independently reproduces all six displayed children:

\[
\begin{array}{c|c|c}
x&u&v\\ \hline
1/3&1/7&2/11\\
2/11&1/7&3/79\\
1/7&1/11&2/39\\
1/11&1/23&6/127\\
2/39&1/39&39/1523\\
3/79&1/53&8/419
\end{array}
\]

Copying the parent coefficient to both children preserves positivity.
Collecting equal children gives exactly the coefficients (3,2), then
(5,5,2), then (5,5,5,5,2,2) in the report.

For an identity (\sum c_i\arctan(a_i/b_i)), the Gaussian product

\[
 Z=\prod_i(b_i+ia_i)^{c_i}
\]

has argument equal to the angle sum modulo (2\pi).  The independent replay
finds equal positive real and imaginary coordinates for all four identities.
That fact alone would leave a branch ambiguity.  The separately checked
linear sums

\[
 \frac{17}{21},\quad\frac{61}{77},\quad
 \frac{26669}{33891},\quad
 \frac{3027502731497}{3852884231859}
\]

all lie in ((0,1)).  Since (0<\arctan x<x), the angle sum lies in
((0,1)); consequently the Gaussian angle is (\pi/4), not
(\pi/4+2k\pi).  The named identities are exact.

## 2. Alternating bracket and convergence slope

For (R\equiv1\pmod4), truncation through (R-2\equiv3\pmod4) contains an
even number of alternating arctangent terms.  For every (x\in(0,1)), the
alternating-series theorem gives

\[
 0<\arctan x-
 \sum_{\substack{1\le r\le R-2\\r\text{ odd}}}
 \frac{\chi_4(r)x^r}{r}<\frac{x^R}{R}.
\]

All (c_i) are positive.  Multiplication by (4c_i) and summation proves

\[
 L_R<\pi<U_R,
 \qquad U_R-L_R=\frac4R\sum_i c_ix_i^R.
\]

For the first split, the width is exactly

\[
 \frac{12}{R7^R}+\frac{8\,2^R}{R11^R},
\]

so the larger base (2/11) gives limiting decimal slope
(\log_{10}(11/2)).  The maxima (1/3,2/11,1/11,6/127) and all four table
slopes were recomputed exactly before applying decimal logarithms.  The
decimal values are `experiment` diagnostics; the limiting formula is the
`proof sketch` deduction.

## 3. Whole-bracket denominator and decimal transient

Let (T=R-2), and write each leaf as (x_i=a_i/b_i) with
(\gcd(b_i,10)=1).  Termwise clearing gives

\[
 \operatorname{den}(L_R)\mid
 \operatorname{lcm}(1,3,\ldots,T)\prod_i b_i^T.
\]

The next terms have a common denominator dividing
(R\prod_i b_i^R), hence

\[
 \operatorname{den}(U_R)\mid
 \operatorname{lcm}\!\left(
 \operatorname{lcm}(1,3,\ldots,T)\prod_i b_i^T,
 R\prod_i b_i^R\right).
\]

Every factor displayed is odd.  The leaf denominators contribute no factor
of (5), while the odd exponent lcm contributes at most
(\lfloor\log_5T\rfloor) and (R) contributes at most
(\lfloor\log_5R\rfloor).  Therefore

\[
 v_2(\operatorname{den}L_R)=v_2(\operatorname{den}U_R)=0,
\]

\[
 v_5(\operatorname{den}L_R)\le\lfloor\log_5T\rfloor,
 \qquad
 v_5(\operatorname{den}U_R)\le\lfloor\log_5R\rfloor.
\]

This is a genuine (O(\log R)) decimal preperiod for the full bracket.  It
does not grow with split depth (h), even though the coprime part of the
denominator becomes enormous.  Thus the angle-splitting route really does
remove the Euler shadow's linear two-adic transient.

## 4. Indefinite balanced, denominator-safe refinement

Let (x=a/b\in(0,1)) be reduced; no hypothesis on (b\bmod10) is needed.
Choose (d\equiv1\pmod {10}) so large that the open interval

\[
 I=\left(\frac{ad}{3b},\frac{2ad}{3b}\right)
\]

has length greater than (10).  Require (c\in I\) to have parity opposite
to (b).  Among the five resulting residue classes modulo (10), at most
one makes (bd+ac\equiv0\pmod5): if (5\nmid a), one class is forbidden;
if (5\mid a), reducedness gives (5\nmid b), so none is forbidden.
The interval therefore contains an admissible (c).

Put

\[
 u=\frac cd,
 \qquad
 v=\frac{ad-bc}{bd+ac}.
\]

The integer (d) is coprime to (10).  If (b) is odd, then (c) is even
and (bd+ac) is odd.  If (b) is even, then reducedness makes (a) odd,
while (c) is odd, so (bd+ac) is again odd.  The mod-(5) choice makes
the same raw denominator 5-coprime.  Reduction can only divide these raw
denominators, hence both child denominators are coprime to (10).

The interval choice gives

\[
 \frac x3<u<\frac{2x}3,
 \qquad
 0<v=\frac{x-u}{1+xu}<x-u<\frac{2x}3.
\]

Thus every child is positive and at most (2/3) of its parent.  If all
leaves are split, coefficient mass doubles and the largest argument
contracts:

\[
 C_h=2^hC_0,
 \qquad X_h<\left(\frac23\right)^hX_0.
\]

At any fixed first-omitted exponent (R\ge5),

\[
 W_{R,h}<\frac{4C_0X_0^R}{R}
 \left[2\left(\frac23\right)^R\right]^h.
\]

The bracketed factor is at most (64/243<1), so the widths tend to zero.
This verifies the report's arbitrary-accuracy claim with **Taylor depth
fixed and split depth growing**.  The independent checker also verifies the
construction for all 489 reduced fractions (a/b\in(0,1)) with (b\le40),
including denominators divisible by (2) or (5), and checks five recursive
levels at (R=5).  Those finite rows are `experiment`; the residue-class
argument is the `proof sketch` proof.

## 5. Upper-band prime coordinate

For (T/3<p\le T), the only odd Taylor exponent at most (T) divisible by
the odd prime (p) is (p): the next odd multiple is (3p>T).  Suppose
(p\nmid\prod b_i).  All nonsingular terms become zero modulo (p) after
multiplication by (p), whereas the (r=p) terms give

\[
 pL_R\equiv4\chi_4(p)\sum_i c_ix_i^p
 \equiv4\chi_4(p)S\pmod p.
\]

The second congruence is Fermat's theorem in the localization at (p).
The denominator of (S) divides a product of the (b_i), so the additional
condition (p\nmid\operatorname{num}(S)) makes the residue nonzero.  No term
has denominator valuation below (-1), hence

\[
 v_p(L_R)=-1.
\]

Thus (p) occurs exactly once in the reduced denominator.  For each fixed
identity, only finitely many primes divide the fixed bases or numerator of
(S); the prime number theorem then makes the product of surviving primes in
((T/3,T]) exponential in (T).  This is genuine denominator support, but
it says nothing about the ordering of the selected numerator modulo that
product.  The independent replay checks both the congruence and exact
denominator valuation, rather than inferring one finite assertion from the
other.

## 6. Cylinder and affine separators

The endpoint inequalities in the report are a correct sufficient certificate
for a word cell.  For fixed (s,m), the nested-width argument eventually
resolves the actual cell containing (10^s\pi), because irrationality of
(\pi) excludes a decimal-grid boundary.  The resulting quantifier is

\[
 \forall s\ \forall m\ \exists h:
 \text{the actual cell at }s\text{ is resolved}.
\]

It is not V1's order

\[
 \forall m\ \forall a<10^m\ \exists s:
 \text{the cell equals }a.
\]

For any two rational lower shadows (L,L'), exact fractional-part algebra
gives

\[
 \{10^sL'\}=\big\{\{10^sL\}+10^s(L'-L)\big\}.
\]

The independent checker verifies this for every pair of the four shadows and
41 shifts.  More importantly, it is an identity, not a statistical theorem:
different split trees remain deterministic affine translates approximating
the same fixed real phase.  What is justified is that identity count alone
does not furnish independent samples.  It would be too strong to infer that
no joint arithmetic theorem could ever use several shadows; the corrected
report no longer says that.

Arbitrary refinement can compute any particular finite prefix by exact
endpoint comparison.  Scanning longer prefixes for a requested word is still
only a semidecision procedure: it halts exactly if that word occurs.  The
geometric width estimate controls resolution, not which cell contains pi.

## 7. Source audit

The source claims are `literature-checked` as of 2026-08-12:

1. [DLMF 4.24.E3](https://dlmf.nist.gov/4.24#E3) states the arctangent power
   series used in the bracket.
2. The pinned local mathlib file has SHA-256
   `f2503a1e4710591b3dbadf5502e2dd14681b4f69c0498d1cb073ecd634c65238`
   and contains `Real.arctan_add` and
   `Real.two_mul_arctan_inv_3_add_arctan_inv_7`.
3. Farhi, [*On refinements of two-term Machin-like formulas*](https://arxiv.org/abs/2601.10300v1),
   constructs decreasing positive rational arguments and corresponding
   integer-coefficient Machin formulas, with a geometrically convergent
   associated rational approximation.
4. Gasull--Luca--Varona,
   [*Three essays on Machin's type formulas*](https://arxiv.org/abs/2302.00154v2),
   prove that two-term Machin formulas can have arbitrarily small Lehmer
   measure.
5. Abrarov--Quine,
   [*An iteration procedure for a two-term Machin-like formula for pi with small Lehmer's measure*](https://arxiv.org/abs/1706.08835v3),
   explicitly record rapidly growing intermediate rational data and a
   522-million-digit numerator/denominator example.

These sources support the analytic series and the claim that rapid Machin
refinement is known computational infrastructure.  None supplies a
prescribed decimal-cylinder theorem.  The bounded source set does not
establish novelty for the elementary parity/mod-(5) construction.

## 8. Independent computational replay

The corrected primary checker completed with:

```text
gaussian_and_identity_exact_checks=20
bracket_width_algebra_exact_checks=168
natural_denominator_exact_checks=168
base_ten_transient_exact_checks=336
upper_band_prime_survival_exact_checks=558
upper_band_local_congruence_exact_checks=558
general_congruence_split_exact_checks=489
recursive_denominator_safe_exact_checks=16
all exact assertions passed
```

The separate checker
[`machin_angle_splitting_independent_check.py`](machin_angle_splitting_independent_check.py)
does not import the submitted implementation.  It reports:

```text
claim_status=experiment
named_split_exact_checks=6
identity_branch_exact_checks=16
endpoint_denominator_transient_exact_checks=984
upper_band_local_exact_checks=7624
general_congruence_split_exact_checks=489
fixed_R_recursive_contraction_exact_checks=20
affine_coupling_exact_checks=246
all independent exact assertions passed
```

These finite checks corroborate the exact algebra.  They are not a proof of
the alternating-series theorem, the prime number theorem, or V1.

## Sharp conclusion

This branch achieves a real technical improvement: arbitrary geometric
resolution at fixed Taylor depth with no linear decimal transient.  It also
retains an exponentially large coprime moving-prime modulus.  Neither fact
steers the unique phase of pi into a prescribed decimal cylinder.  The
remaining requirement is still an ordered selected-numerator or direct
cylinder-hitting theorem, not a stronger convergence or denominator-support
estimate.
