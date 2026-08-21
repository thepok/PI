# Recursive Machin-angle splitting: sharper brackets without phase steering

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained.  Canonical
V1 remains a `conjecture`.

The proposed split is exact and useful:

\[
 \arctan {1\over3}=\arctan {1\over7}+\arctan {2\over11},
 \qquad
 {\pi\over4}=3\arctan {1\over7}+2\arctan {2\over11}.       \tag{1}
\]

It improves the first-omitted-term decay from \(3^{-R}\) to
\((2/11)^R\), while all fixed argument denominators remain coprime to ten.
Two further exact refinements improve the largest argument to \(1/11\) and
then \(6/127\).  More generally, every rational argument in \((0,1)\) can be
split into two balanced positive rational arguments whose reduced
denominators are coprime to ten; the construction can then be iterated.  At
any fixed Taylor depth this gives rational brackets for pi of arbitrarily
small width, with only an \(O(\log R)\) base-ten preperiod.

That strong approximation statement does **not** solve the digit-cylinder
problem.  A split bracket resolves the one decimal cell already occupied by
the fixed number pi; it does not steer the phase into a prescribed cell.
Growing the split depth merely computes a longer prefix through larger
rational identity data.  The missing quantifier remains

\[
 \forall m\ \forall a<10^m\ \exists s:\quad
 \left\lfloor10^m\{10^s\pi\}\right\rfloor=a.              \tag{V1}
\]

The exact algebra and asymptotic deductions below have status `proof sketch`:
they are inspectable but are not formalized in Lean.  The finite replay has
status `experiment`.  The source search is `literature-checked` as of the
date above.  This note is not a `candidate resolution`.

## 1. Exact rational split and three concrete levels

For rational numbers \(0<u<x<1\), put

\[
                         v={x-u\over1+xu}.                  \tag{2}
\]

Then \(0<v<x\) and exact rational arithmetic gives

\[
 {u+v\over1-uv}=x.                                         \tag{3}
\]

All angles are positive and their sum is below \(\pi/2\), so the principal
branch of the tangent addition formula gives

\[
                         \arctan x=\arctan u+\arctan v.     \tag{4}
\]

Applying (2) to \(x=1/3,u=1/7\) gives \(v=2/11\), proving
(1) from Hutton's identity

\[
 {\pi\over4}=2\arctan {1\over3}+\arctan {1\over7}.         \tag{5}
\]

The same operation gives

\[
 \arctan {2\over11}=\arctan {1\over7}+\arctan {3\over79},
 \qquad
 \arctan {1\over7}=\arctan {1\over11}+\arctan {2\over39}.
                                                                    \tag{6}
\]

Substitution and collection therefore produce

\[
 {\pi\over4}=
 5\arctan {1\over11}+5\arctan {2\over39}
 +2\arctan {3\over79}.                                    \tag{7}
\]

One simultaneous balanced refinement of the three angles in (7) is

\[
\begin{aligned}
 \arctan {1\over11}&=\arctan {1\over23}+\arctan {6\over127},\\
 \arctan {2\over39}&=\arctan {1\over39}+\arctan {39\over1523},\\
 \arctan {3\over79}&=\arctan {1\over53}+\arctan {8\over419}.
\end{aligned}                                               \tag{8}
\]

Thus

\[
\begin{aligned}
 {\pi\over4}={}&5\arctan {1\over23}+5\arctan {6\over127}
 +5\arctan {1\over39}+5\arctan {39\over1523}\\
 &+2\arctan {1\over53}+2\arctan {8\over419}.             \tag{9}
\end{aligned}
\]

Every displayed denominator is coprime to ten.  The checker also verifies
each full identity by multiplying the Gaussian integers
\((b+ia)^c\): in every case the product has equal positive real and imaginary
parts.  Together with
\(0<\sum_i c_i\arctan(x_i)<\sum_i c_ix_i=S<1\), this excludes a hidden
\(2\pi\) branch shift.  The combination is an exact branch certificate, not
a floating-point angle comparison.

## 2. Exact alternating brackets and the resolution gain

Consider any fixed positive identity

\[
                 {\pi\over4}=\sum_{i=1}^J c_i\arctan x_i,
 \qquad c_i\in\mathbb N_{>0},\quad x_i\in\mathbb Q\cap(0,1).
                                                                    \tag{10}
\]

Let \(R\equiv1\pmod4\), \(R\ge5\), and define the even Taylor truncation

\[
 L_R=4\sum_i c_i
   \sum_{\substack{1\le r\le R-2\\r\ {\rm odd}}}
     {\chi_4(r)x_i^r\over r},
 \qquad \chi_4(r)=(-1)^{(r-1)/2}.                          \tag{11}
\]

Adding the next positive term in every component gives

\[
 U_R=L_R+{4\over R}\sum_i c_i x_i^R.                      \tag{12}
\]

The alternating-series inequalities give the exact rational bracket

\[
 L_R<\pi<U_R,
 \qquad
 W_R:=U_R-L_R={4\over R}\sum_i c_i x_i^R.                 \tag{13}
\]

For (1), for example,

\[
 W_R={12\over R7^R}+{8\,2^R\over R11^R},                 \tag{14}
\]

so its asymptotic decimal-resolution slope is

\[
 -{1\over R}\log_{10}W_R\longrightarrow\log_{10}(11/2)
 =0.7403626894\ldots,                                      \tag{15}
\]

instead of the Hutton slope \(\log_{10}3=0.4771212547\ldots\).
The successive largest arguments and slopes are

| identity | largest \(x_i\) | asymptotic slope \(\log_{10}(1/x_i)\) |
|---|---:|---:|
| Hutton (5) | \(1/3\) | \(0.4771212547\ldots\) |
| first split (1) | \(2/11\) | \(0.7403626895\ldots\) |
| second split (7) | \(1/11\) | \(1.0413926852\ldots\) |
| third split (9) | \(6/127\) | \(1.3256524706\ldots\) |

This is a genuine improvement in rational approximation.  It means that
the interval can potentially resolve starts \(s\) up to roughly
\(-\log_{10}W_R-m\) for a fixed block length \(m\).  It does **not** mean
that those starts visit all \(10^m\) cells: interval width and interval
location are different assertions.

## 3. Exact denominator and base-ten transient structure

Write every \(x_i=a_i/b_i\) in lowest terms and assume
\(\gcd(b_i,10)=1\).  Let

\[
 \Lambda_T^{\rm odd}=\operatorname{lcm}\{1,3,5,\ldots,T\},
 \qquad T=R-2.                                             \tag{16}
\]

Term-by-term denominator clearing gives the safe natural denominator

\[
 \operatorname{den}(L_R)\mid
 D_R:=\Lambda_T^{\rm odd}\prod_{i=1}^J b_i^T.             \tag{17}
\]

Consequently the reduced denominator of \(L_R\) is odd and

\[
 v_5(\operatorname{den}(L_R))
 \le v_5(\Lambda_T^{\rm odd})=\lfloor\log_5T\rfloor.       \tag{18}
\]

After at most \(\lfloor\log_5T\rfloor\) decimal shifts, the remaining
denominator is coprime to ten.  Recursive splitting therefore avoids the
fatal linear two-adic transient of the direct Euler \(1/2,1/3\) shadow.  It
does produce a long post-transient rational orbit.

For completeness, the upper endpoint has the safe denominator

\[
 \operatorname{den}(U_R)\mid
 \operatorname{lcm}\!\left(D_R,
 R\prod_{i=1}^J b_i^R\right).                              \tag{18a}
\]

It is also odd, and its 5-adic denominator exponent is at most
\(\lfloor\log_5R\rfloor\).  Thus the whole rational bracket, not only its
lower endpoint, has logarithmic base-ten preperiod.  The checker tests both
endpoint bounds separately.

There is also a fixed-depth prime-survival statement.  Put

\[
                              S=\sum_i c_i x_i.             \tag{19}
\]

If \(p\) is an odd prime satisfying

\[
 {T\over3}<p\le T,\qquad
 p\nmid\prod_i b_i,\qquad p\nmid\operatorname{num}(S),    \tag{20}
\]

then exponent \(p\) is the only Taylor exponent divisible by \(p\).  Fermat's
theorem gives, in the localization at \(p\),

\[
 pL_R\equiv4\chi_4(p)\sum_i c_i x_i^p
       \equiv4\chi_4(p)S\not\equiv0\pmod p.               \tag{21}
\]

Hence \(v_p(L_R)=-1\), and \(p\) occurs exactly once in the reduced
denominator.  The four values of \(S\) in the checker are

\[
 {17\over21},\quad {61\over77},\quad {26669\over33891},
 \quad {3027502731497\over3852884231859}.                  \tag{22}
\]

Thus a fixed split retains an exponentially large moving-prime coordinate
outside finitely many exceptional primes.  Equation (21) is still only
local denominator information.  It neither orders the selected numerator
modulo that product nor puts the real fraction in a decimal cell.

## 4. Denominator-safe splitting can continue indefinitely

The coprime-to-ten examples are not a finite accident.  Suppose
\(x=a/b\in(0,1)\) is reduced.  Choose a sufficiently large integer
\(d\equiv1\pmod {10}\), and choose an integer \(c\) in

\[
                        {ad\over3b}<c<{2ad\over3b}          \tag{23}
\]

such that \(c\) has parity opposite to \(b\), and
\(bd+ac\not\equiv0\pmod5\).  Such a \(c\) exists once the interval is long
enough: the parity condition uses one parity class, and at most one of its
five residue classes modulo five is forbidden.  Indeed, if \(5\mid a\),
coprimality gives \(5\nmid b\), so no class is forbidden.  Put

\[
 u={c\over d},\qquad
 v={ad-bc\over bd+ac}.                                     \tag{24}
\]

If \(b\) is odd, then \(c\) is even and \(bd+ac\) is odd.  If \(b\) is
even, reducedness makes \(a\) odd, while \(c\) is odd, so \(bd+ac\) is
again odd.  Thus (2)--(4) apply, both reduced denominators divide integers
coprime to ten, and

\[
                 0<u<{2x\over3},\qquad0<v<x-u<{2x\over3}. \tag{25}
\]

Splitting every leaf to recursion depth \(h\) therefore gives

\[
 C_h:=\sum_i c_i=2^hC_0,\qquad
 X_h:=\max_i x_i<\left({2\over3}\right)^hX_0.             \tag{26}
\]

For the bracket at a fixed first-omitted exponent \(R\ge5\), (13) yields

\[
 W_{R,h}
 <{4C_0X_0^R\over R}
   \left[2\left({2\over3}\right)^R\right]^h
 \longrightarrow0.                                       \tag{27}
\]

So recursive rational identities really do give arbitrarily accurate
brackets even with \(R\) fixed.  This phenomenon is classical computational
power, not evidence of decimal normality.

There is a visible size trade.  The explicit leaf list has \(2^hJ_0\)
occurrences, and every reduced leaf denominator is at least \(1/X_h\).
Thus the sum of the leaf-denominator bit lengths is
\(\Omega(2^h h)\), while the displayed bound (27) certifies a gain of order
at least \(hR\) decimal places (without claiming that bound is optimal).  The
safe common denominator (17) consequently has an unreduced description of
logarithmic size \(\Omega(R2^h h)\).  This statement is about the explicit
denominator certificate, not a lower bound for the fully reduced denominator
after all cross-leaf cancellations.

## 5. Exact cylinder separator: resolution is not steering

For a word value \(a<10^m\), a split bracket certifies occurrence at start
\(s\) only if there is an integer \(z\) such that

\[
 z+{a\over10^m}\le10^sL_{R,h}
 \quad\hbox{and}\quad
 10^sU_{R,h}<z+{a+1\over10^m}.                             \tag{28}
\]

Then the whole interval containing \(10^s\pi\) lies in the desired decimal
cell.  Recursive splitting makes the interval in (28) thinner; it gives no
reason for its center to move into a chosen cell.

Indeed, at each fixed \(s,m\), the brackets contain pi and their widths tend
to zero by (27).  Since pi is irrational, \(10^s\pi\) is not on a decimal
grid boundary.  Eventually (28) holds for exactly the cell already containing
\(10^s\pi\), and for no other cell.  This proves only the representation
quantifier

\[
 \forall s\ \forall m\ \exists h:\quad
 \text{the depth-}h\text{ bracket resolves the actual pi code at }s. \tag{29}
\]

It does not imply V1's differently ordered quantifiers

\[
 \forall m\ \forall a<10^m\ \exists s:\quad
 \text{the actual pi code at }s\text{ equals }a.           \tag{30}
\]

Two different split trees are not independent samples merely by virtue of
using different identities.  If their
lower shadows are \(L,L'\), then at every shift

\[
 \{10^sL'\}=\{\{10^sL\}+10^s(L'-L)\},                    \tag{31}
\]

and their errors to pi differ by the same known rational translation with
opposite sign.  This is the same rank-one affine/coboundary obstruction
already found for the \(3/7\) and \(5/239\) shadows.  Increasing the number
of identities alone supplies no independent CRT coordinates for the one
fixed Archimedean phase.

Choosing a growing depth \(h=h(R)\) can make the *geometric* resolution
horizon superlinear.  Exact endpoint comparison can compute any prescribed
finite prefix by refining until both rational endpoints have the same prefix,
but no unconditional rate follows from (27) alone near decimal boundaries.
Scanning such a computed prefix supplies
`experiment` evidence.  Unless one proves an a priori bound on where each
word must occur, the scan is only a semidecision procedure: it terminates for
a word precisely when that word is encountered.  That is the original
problem, not a proof of it.

## 6. Library and literature check

The relevant source search was rerun before treating the splitting process
as new infrastructure.

- DLMF [4.24.E3](https://dlmf.nist.gov/4.24#E3) records the arctangent power
  series used in (11)--(13).
- The pinned mathlib file
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`, SHA-256
  `f2503a1e4710591b3dbadf5502e2dd14681b4f69c0498d1cb073ecd634c65238`,
  contains `Real.arctan_add` and
  `Real.two_mul_arctan_inv_3_add_arctan_inv_7`.  It supports a future Lean
  formalization without inventing a new analytic series layer.
- Farhi, [*On refinements of two-term Machin-like formulas*,
  arXiv:2601.10300v1](https://arxiv.org/abs/2601.10300v1), constructs derived
  identities with decreasing positive rational arguments and growing integer
  coefficients.  This confirms that refinement itself is known.  The paper
  proves approximation results, not prescribed decimal-word occurrence.
- Gasull--Luca--Varona, [*Three essays on Machin's type formulas*,
  arXiv:2302.00154v2](https://arxiv.org/abs/2302.00154v2), constructs Machin-type
  formulas with arbitrarily small Lehmer measure.  Arbitrarily rapid
  arctangent convergence is therefore not a distribution theorem.
- Abrarov--Quine, [*An iteration procedure for a two-term Machin-like formula
  for pi with small Lehmer's measure*,
  arXiv:1706.08835v3](https://arxiv.org/abs/1706.08835v3), explicitly discusses
  the large rational-data cost accompanying very small arguments.

No checked source supplies an ordered-residue estimate or a cylinder-hit
theorem for the selected rational numerators generated by these identities.
This negative search finding is bounded to the sources recorded here; it is
not a novelty claim.

## 7. Exact finite replay

The companion checker is
[`machin_angle_splitting_check.py`](machin_angle_splitting_check.py).  It uses
only integer arithmetic and Python `Fraction` for all exact assertions.  Its
bracket count checks the exact rational width algebra; the analytic
alternating-series inequality in (13) comes from the cited theorem and is not
misrepresented as a finite script assertion.  A clean run reports

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
exact_named_split_checks=6
gaussian_and_identity_exact_checks=20
bracket_width_algebra_exact_checks=168
natural_denominator_exact_checks=168
base_ten_transient_exact_checks=336
upper_band_prime_survival_exact_checks=558
upper_band_local_congruence_exact_checks=558
general_congruence_split_exact_checks=489
recursive_denominator_safe_exact_checks=16
finite_scale_table_status=experiment
scale R=81 identity=Hutton width_digits=39.65 reduced_denominator_digits=133
scale R=81 identity=split-1 width_digits=60.97 reduced_denominator_digits=176
scale R=81 identity=split-2 width_digits=84.96 reduced_denominator_digits=387
scale R=81 identity=split-3 width_digits=107.98 reduced_denominator_digits=1022
all exact assertions passed
```

The finite denominator sizes illustrate the trade but are not an asymptotic
theorem and are not used as a proof of the phase separator.

## Sharp conclusion

Recursive angle splitting clears a real technical threshold: it produces
arbitrarily sharp rational brackets with denominator bases coprime to ten,
only logarithmic decimal transient, and substantial moving-prime support.
It therefore improves computation and removes the direct Euler shadow's
two-adic obstruction.

It does not clear the decisive threshold.  Every bracket remains centered on
the same fixed Archimedean phase, and all alternative shadows are exactly
affinely coupled.  The route can reveal more digits of pi, but it cannot
choose what those digits are.  A viable continuation would need a new
theorem controlling the **ordered selected numerators across shifts or split
depths**—not another convergence-rate, denominator-support, or CRT theorem.
