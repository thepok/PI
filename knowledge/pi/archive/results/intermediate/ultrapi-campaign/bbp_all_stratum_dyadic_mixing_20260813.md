# All-stratum BBP dyadic mixing: exact raw isometry and reduced-unit bijections

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9;
- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3;
- [bbp_even_depth_dyadic_mixing_20260813.md](bbp_even_depth_dyadic_mixing_20260813.md),
  SHA-256
  3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623;
- [bbp_even_depth_dyadic_mixing_20260813_check.py](bbp_even_depth_dyadic_mixing_20260813_check.py),
  SHA-256
  d05ed720b94c23d3d59c23b6bc300d46e6d88dc9f37d31ab5dddb604ce19a839.

## Outcome and quantifier boundary

Canonical V1 remains a `conjecture`: for every finite decimal word \(w\),
there should exist a position at which \(w\) occurs in the decimal expansion
of pi.  This note proves no such occurrence, and it does not silently replace
the existential position by a recurrence or density assertion.

The new result has status `proof sketch`.  Define

\[
                  Z(n)=5^nF(7n+1)\qquad(n\geq0),                \tag{1}
\]

where \(F\) is the frozen two-adic BBP function.  Then for every pair of
distinct nonnegative integers,

\[
             \boxed{v_2\!\left(Z(n)-Z(n')\right)=v_2(n-n').}    \tag{2}
\]

Thus the **scaled raw selected coordinate itself**, not merely
\(F(7n+1)\), is a bijective isometry modulo every fixed power of two.

There is also an exact result after the depth-dependent cancellation.  For
each fixed \(r\geq0\), parameterize the valuation stratum
\(v_2(7n+1)=r\) by

\[
             n=n_r(m)=a_r+2^{r+1}m,\qquad m\geq0,              \tag{3}
\]

where \(a_r\) is given explicitly by

\[
 0\leq a_r<2^{r+1},\qquad
 a_r\equiv7^{-1}(2^r-1)\pmod {2^{r+1}}.              \tag{3a}
\]

Put

\[
                         U_r(m)={Z(n_r(m))\over2^r}.            \tag{4}
\]

Then

\[
       \boxed{v_2\!\left(U_r(m)-U_r(m')\right)
                    =1+v_2(m-m')}                             \tag{5}
\]

for \(m\ne m'\).  Consequently, at every fixed precision \(s\geq1\),
\(U_r\) bijects \(\mathbb Z/2^{s-1}\mathbb Z\) onto all odd residues
modulo \(2^s\).

The earlier even-depth theorem is exactly the case \(r=0\), for which
\(a_0=0\), \(n_0(m)=2m\), and \(U_0(m)=25^mF(14m+1)\).

Equations (2) and (5) remain fixed-level statements.  The complete selected
coordinate at depth \(n\) has \(27n-v_2(7n+1)\) bits, so its relevant period
is exponential in the same index that determines the precision.  No
moving-diagonal distribution, colored return, or V1 follows.

The exact finite replay is an `experiment`.  Nothing in this note is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Frozen two-adic input and selected coordinate

Use the four-pole coefficient

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}.                           \tag{6}
\]

The frozen all-depth audit defines

\[
                  F(X)=\sum_{j\geq0}16^ja(X-1-j)               \tag{7}
\]

on \(\mathbb Z_2\), proves \(F(0)=0\), and proves the coefficientwise
congruence \(F(X)\equiv X\pmod2\).  Hence

\[
                         F(X)=X+2G(X)                         \tag{8}
\]

for an analytic \(G\in\mathbb Z_2[[X]]\).  For \(x,y\in\mathbb Z_2\), the
power-series difference \(G(x)-G(y)\) is divisible by \(x-y\).  Therefore

\[
 F(x)-F(y)=(x-y)(1+2H(x,y))
\]

with \(H(x,y)\in\mathbb Z_2\), and consequently

\[
\begin{aligned}
 F(0)&=0,\\
 v_2(F(x)-F(y))&=v_2(x-y)
       \qquad(x,y\in\mathbb Z_2).                    \tag{9}
\end{aligned}
\]

In particular,

\[
                         v_2(F(x))=v_2(x).                    \tag{10}
\]

If \(L_N,A_N,B_N\) are the exact common denominator, selected numerator,
and BBP partial sum used in the frozen reports, then

\[
                         F(N+1)={A_N\over L_N}=16^NB_N.       \tag{11}
\]

At sevenfold depth define

\[
\begin{aligned}
 D_n&=2^{27n}L_{7n},&
 V_n&=5^nA_{7n},\\
 r_n&=v_2(7n+1),&
 \kappa_n&=27n-r_n.                                  \tag{12}
\end{aligned}
\]

Because \(L_{7n}\) is odd, for \(n\geq1\) the raw dyadic coordinate of the selected
numerator is

\[
                         [Z(n)]_{2^{27n}},                    \tag{13}
\]

and the complete reduced coordinate is

\[
                         w_n=
 \left[\,{Z(n)\over2^{r_n}}\,\right]_{2^{\kappa_n}}.          \tag{14}
\]

Here \([x]_{2^s}\) denotes the canonical residue of a two-integral rational.
Equation (10) shows that \(v_2(Z(n))=r_n\), so (14) divides by exactly the
full common dyadic factor.

## 2. The five-power lifting identity

For every positive integer \(d\),

\[
                         v_2(5^d-1)=2+v_2(d).                  \tag{15}
\]

For completeness, write \(d=2^tu\) with \(u\) odd.  The factorization

\[
                 5^u-1=(5-1)(1+5+\cdots+5^{u-1})
\]

has valuation two: the first factor is \(4\), while the second factor is a
sum of an odd number of odd terms.  At every doubling,

\[
                 5^{2e}-1=(5^e-1)(5^e+1),
\]

and \(5^e+1\equiv2\) or \(6\pmod8\), so the second factor has valuation
exactly one.  The \(t\) doublings prove (15), including the even-\(d\)
case.

## 3. Proof of the raw selected-coordinate isometry

Let \(n>n'\geq0\), and put \(d=n-n'>0\).  From (1),

\[
\begin{aligned}
 Z(n)-Z(n')=5^{n'}\bigl(&5^d(F(7n+1)-F(7n'+1))\\
                         &+(5^d-1)F(7n'+1)\bigr).              \tag{16}
\end{aligned}
\]

The outer factor is a two-adic unit.  By (9), the first term in parentheses
has valuation

\[
                         v_2(7(n-n'))=v_2(d).                  \tag{17}
\]

By (10) and (15), the second term has valuation

\[
                         2+v_2(d)+v_2(7n'+1).                 \tag{18}
\]

The value in (18) exceeds (17) by at least two.  Two summands of unequal
two-adic valuation have a sum with the smaller valuation, so (16) proves
(2).  Interchanging the indices covers \(n<n'\).  There is no cancellation
assumption: the valuations are rigorously separated.

Fix \(s\geq1\).  Equation (2) gives

\[
 Z(n)\equiv Z(n')\pmod {2^s}
 \quad\Longleftrightarrow\quad
 n\equiv n'\pmod {2^s}.                              \tag{19}
\]

Thus \(Z\bmod2^s\) is an injection of a finite set of \(2^s\) residues into
itself, hence a bijection:

\[
 \boxed{
 Z:\mathbb Z/2^s\mathbb Z\longrightarrow
   \mathbb Z/2^s\mathbb Z\ \text{is bijective}.}       \tag{20}
\]

This strengthens the frozen permutation statement for \(F(7n+1)\): the
depth-dependent multiplier \(5^n\) preserves the exact isometry.

## 4. Exact valuation strata and reduced-unit mixing

For each \(r\geq0\), the congruence \(7n+1\equiv0\pmod {2^r}\) has one
solution modulo \(2^r\), because \(7\) is a unit.  Its two lifts modulo
\(2^{r+1}\) cannot both remain divisible by \(2^{r+1}\); exactly one does.
Therefore exactly one of the two lifts has valuation equal to \(r\).
The explicit formula (3a) is the solution of
\(7a_r+1\equiv2^r\pmod {2^{r+1}}\).  This proves

\[
 v_2(7n+1)=r
 \quad\Longleftrightarrow\quad
 n\equiv a_r\pmod {2^{r+1}},                          \tag{21}
\]

and justifies the parameterization (3).

For distinct \(m,m'\), equations (2)--(4) now give

\[
\begin{aligned}
 v_2(U_r(m)-U_r(m'))
 &=v_2(Z(n_r(m))-Z(n_r(m')))-r\\
 &=v_2(2^{r+1}(m-m'))-r\\
 &=1+v_2(m-m'),                                      \tag{22}
\end{aligned}
\]

which is (5).  Equations (10) and (21) also show that every \(U_r(m)\) is a
two-adic unit.

It follows that for every \(s\geq1\),

\[
 U_r(m)\equiv U_r(m')\pmod {2^s}
 \quad\Longleftrightarrow\quad
 m\equiv m'\pmod {2^{s-1}}.                          \tag{23}
\]

The source has \(2^{s-1}\) elements, as does the set of odd residues modulo
\(2^s\).  Hence

\[
 \boxed{
 U_r:\mathbb Z/2^{s-1}\mathbb Z
 \longrightarrow(\mathbb Z/2^s\mathbb Z)^\times
 \ \text{is bijective}.}                             \tag{24}
\]

At \(s=1\), both sides are singletons and (24) remains valid.

Combining (14), (21), and (24), any complete block of \(2^{s-1}\)
consecutive values of the stratum parameter \(m\), taken far enough that
\(s\leq\kappa_{n_r(m)}\) throughout the block, makes the low \(s\) bits of
the actual reduced coordinates \(w_{n_r(m)}\) run through every odd residue
exactly once.

## 5. Why all strata still miss the moving diagonal

The complete reduced precision on the \(r\)-stratum is

\[
 \kappa_{n_r(m)}
 =27\bigl(a_r+2^{r+1}m\bigr)-r.                      \tag{25}
\]

Using (24) at this precision would require a block of

\[
                         2^{\kappa_{n_r(m)}-1}                 \tag{26}
\]

stratum parameters.  This is exponential in \(m\), while the diagonal
sequence contributes only the one parameter \(m\) whose value also sets the
precision.  The all-stratum theorem removes neither this quantifier mismatch
nor the need to control the high bits of the canonical representative.

More decisively, the frozen high-dyadic separator preserves the complete raw
and reduced dyadic coordinate at every depth, and also preserves the
next-depth dyadic forcing class.  Yet its centered states eventually have
zero carries and only the all-nine endpoint color.  It changes the selected
odd coordinate.  Therefore even the simultaneous collection of (20) and
(24) over every \(r\) cannot force a decimal cylinder without a mixed
odd--dyadic--Archimedean estimate for the actual selected numerator.

The theorem is consequently a complete fixed-level description, not a
moving-diagonal equidistribution theorem and not evidence that a prescribed
word occurs in pi.

## 6. Exact replay

The companion
[bbp_all_stratum_dyadic_mixing_20260813_check.py](bbp_all_stratum_dyadic_mixing_20260813_check.py)
imports no earlier checker.  It reconstructs the rational four-pole
coefficient and \(F\) modulo powers of two; exhausts the raw map through ten
bits; exhausts ten valuation strata through nine reduced bits; tests
adversarial distances with large two-adic orders; verifies (15); and
reconstructs exact selected BBP numerators through sevenfold depth 100.

Run from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_check.py

Retained output:

    status: PASS
    finite_claim_label: experiment
    theorem_claim_label: proof sketch
    maximum_raw_precision: 10
    maximum_stratum_precision: 9
    maximum_stratum: 9
    maximum_sevenfold_depth: 100
    raw_bijection_checks: 2046
    raw_scaled_isometry_checks: 698027
    stratum_representative_checks: 20
    stratum_bijection_checks: 5110
    stratum_scaled_isometry_checks: 434350
    adversarial_raw_checks: 240
    five_power_lifting_checks: 240
    exact_rational_identity_checks: 500
    exact_raw_coordinate_checks: 500
    exact_reduced_coordinate_checks: 500
    asserts_moving_diagonal_mixing: false
    asserts_colored_return: false
    asserts_v1: false

Every bounded row has label `experiment`.  The all-index result is the
elementary valuation proof (15)--(24), conditional only on the frozen
`proof sketch` identities (8)--(11).

## 7. Literature, formalization, and coordination boundary

This supplement makes no novelty claim.  Its external mathematical source is
the BBP coefficient of Bailey--Borwein--Plouffe, pinned and applicability-
checked in the frozen reports.  The only additional arithmetic input,
equation (15), is proved directly above.  The bounded 2026-08-13 literature
and mathlib searches in the frozen high-dyadic report found no theorem that
turns fixed-level two-adic permutation into moving-precision distribution
for this selected numerator.

No declaration is added to the verified Lean track.  The theorem depends on
the frozen `proof sketch` analytic input behind (8)--(11), and
machine-checking a finite replay
would not promote that analytic input.

The branch uses the descendant-area watch `ultrapi-high-dyadic-20260813` on
`local:pi-digits` for agent `codex-ultrapi-high-dyadic`.  Its latest poll
was empty at delivered sequence 56,947, so no event was acknowledged.
Observation events are coordination signals only and were not used as
evidence.

## Sharp handoff

The scaled raw selected coordinate is now exactly understood at every fixed
two-adic precision, and the same is true of the reduced unit on every exact
valuation stratum.  The even-depth theorem was only the first stratum of this
general law.

The endpoint remains sharp: the precision required by the actual coordinate
grows linearly with the depth, while the exact permutation period grows
exponentially.  An exact separator preserves all these dyadic statements and
still avoids every required color except the all-nine boundary once its odd
coordinate is allowed to change.  A complete proof still needs a mixed
least-residue or exponential-sum estimate for the one actual selected
numerator.  No such estimate is obtained here, so canonical V1 remains a
`conjecture`.
