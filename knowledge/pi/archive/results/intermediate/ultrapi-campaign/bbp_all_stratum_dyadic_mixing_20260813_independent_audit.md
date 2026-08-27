# Independent audit: all-stratum BBP dyadic mixing

Audit date: **2026-08-13 UTC**

Verdict: **PASS**.  The frozen all-stratum report correctly derives the raw
isometry, the exact valuation-stratum parameterization, the reduced-unit
bijections, and their relation to the complete dyadic coordinate of the
actual selected BBP rational.  No moving-diagonal distribution, colored
return, or occurrence of a decimal word follows.

The audited all-index result has claim status `proof sketch`.  Every bounded
calculation in the independent checker has claim status `experiment`.  This
audit is not `machine-checked`, a `candidate resolution`, or a `verified
resolution`, and canonical V1 remains a `conjecture`.

## 1. Frozen scope, provenance, and source pins

The canonical target is
[problems/local/pi-digits.txt](../../problems/local/pi-digits.txt), SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It is Marcel's immutable local question and has no external source URL; this
audit does not invent one.

The exact primary pair audited here is:

- [bbp_all_stratum_dyadic_mixing_20260813.md](bbp_all_stratum_dyadic_mixing_20260813.md),
  SHA-256
  `5089d63f83de1978731c50964c7fce45e7a4cc88e989a29acd99e08b8a9c8360`;
- [bbp_all_stratum_dyadic_mixing_20260813_check.py](bbp_all_stratum_dyadic_mixing_20260813_check.py),
  SHA-256
  `dbbf1cbeba9915f3377ae5dbb4a03026be031b1112bc924ab7211227dccc0fcf`.

The primary proof explicitly depends on these frozen inputs, which were also
hash-checked by the independent replay:

- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9`;
- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  `d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`;
- [bbp_even_depth_dyadic_mixing_20260813.md](bbp_even_depth_dyadic_mixing_20260813.md),
  SHA-256
  `3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623`.

The external source used for the four-pole coefficient is
Bailey--Borwein--Plouffe,
[*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9),
Theorem 1.  The local source copy is
[bbp-1997-nasa.pdf](../theory/pi-digits/library/t6/bbp-1997-nasa.pdf),
SHA-256
`e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`.
The source supplies the BBP formula, not the new two-adic conclusions and not
decimal normality.

The independent checker is
[bbp_all_stratum_dyadic_mixing_20260813_independent_check.py](bbp_all_stratum_dyadic_mixing_20260813_independent_check.py),
SHA-256
`8a71e6b3d337c4fe848978d600411f8735b3fd1e533eeb8f0a913c041338ad73`.
It imports no primary checker.

## 2. Exact dependency boundary for the function \(F\)

Write

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}.
\]

The frozen all-depth report supplies the `proof sketch` inputs

\[
 F(0)=0,\qquad F(X)-X\in2\mathbb Z_2[[X]],
 \qquad
 F(N+1)=\frac{A_N}{L_N}=16^N B_N.                 \tag{A1}
\]

The last equality is an ordinary rational equality: the recurrence
\(F(X+1)=16F(X)+a(X)\), initialized by \(F(0)=0\), gives the finite BBP sum
at positive integer arguments.  The all-stratum note does not need any new
literature result beyond these pinned inputs.

For clarity, the isometry used in the primary note follows directly from the
coefficientwise middle assertion in (A1).  Put
\(E(X)=(F(X)-X)/2\in\mathbb Z_2[[X]]\).  For every
\(x,y\in\mathbb Z_2\), the divided difference of the convergent power series
is integral:

\[
 E(x)-E(y)=(x-y)K(x,y),\qquad K(x,y)\in\mathbb Z_2.
\]

Consequently

\[
 F(x)-F(y)=(x-y)(1+2K(x,y)),
\]

and the final factor is a two-adic unit.  Hence

\[
 v_2(F(x)-F(y))=v_2(x-y).                            \tag{A2}
\]

Taking \(y=0\) and using the exact first assertion of (A1) gives

\[
 v_2(F(x))=v_2(x)\quad(x\ne0).                      \tag{A3}
\]

Thus the stronger isometry invoked by the all-stratum report is a valid
one-line consequence of the frozen coefficientwise congruence; it is not an
extra assumption.  Its status remains `proof sketch` because the analytic
input (A1) has that status and has not been formalized in Lean.

## 3. Independent lifting calculation

For every positive integer \(d\), write \(d=2^t u\) with \(u\) odd.  Then

\[
 5^u-1=(5-1)(1+5+\cdots+5^{u-1}).
\]

The first factor has valuation two and the second is a sum of an odd number
of odd terms, hence is odd.  Starting with \(e=u\) and repeatedly doubling,

\[
 5^{2e}-1=(5^e-1)(5^e+1).
\]

Here \(5^e+1\equiv6\pmod8\) for odd \(e\), and
\(5^e+1\equiv2\pmod8\) for even \(e\); in either case its valuation is one.
After \(t\) doublings,

\[
                    v_2(5^d-1)=2+v_2(d).             \tag{A4}
\]

This includes both parities of \(d\); there is no omitted LTE edge case.

## 4. Raw isometry, including zero and both orientations

Define

\[
                         Z(n)=5^nF(7n+1),\qquad n\ge0. \tag{A5}
\]

First take \(n>n'\ge0\), let \(d=n-n'>0\), and expand without approximation:

\[
\begin{aligned}
 Z(n)-Z(n')=5^{n'}\bigl(&5^d(F(7n+1)-F(7n'+1))\\
                       &+(5^d-1)F(7n'+1)\bigr).       \tag{A6}
\end{aligned}
\]

The outer factor is a unit.  By (A2), the first inner summand has valuation

\[
 v_2(7(n-n'))=v_2(d),                                \tag{A7}
\]

whereas (A3)--(A4) give the second inner summand valuation

\[
 2+v_2(d)+v_2(7n'+1).                                \tag{A8}
\]

The valuation in (A8) exceeds (A7) by at least two, so cancellation at the
minimum is impossible.  In particular, the endpoint \(n'=0\) is valid:
\(v_2(7n'+1)=v_2(1)=0\), leaving the same strict two-bit gap.  Thus

\[
             v_2(Z(n)-Z(n'))=v_2(n-n').              \tag{A9}
\]

If \(n<n'\), apply the established result after swapping the indices; the
two differences merely change sign.  This proves (A9) for every distinct
ordered pair of nonnegative integers.

For fixed \(s\ge1\), (A9) implies both periodicity and separation:

\[
 Z(n)\equiv Z(n')\pmod {2^s}
 \quad\Longleftrightarrow\quad
 n\equiv n'\pmod {2^s}.                              \tag{A10}
\]

Therefore the induced map on the \(2^s\) nonnegative residue representatives
is injective and hence bijective.  This justifies the quotient-map notation
in the primary report; it does not require silently extending the original
definition from \(n\ge0\) to negative integers.

## 5. Exact valuation strata and the representative \(a_r\)

Fix \(r\ge0\).  An integer has valuation exactly \(r\) precisely when it is
congruent to \(2^r\) modulo \(2^{r+1}\).  Since 7 is invertible modulo every
power of two,

\[
\begin{aligned}
 v_2(7n+1)=r
 &\Longleftrightarrow 7n+1\equiv2^r\pmod {2^{r+1}}\\
 &\Longleftrightarrow
 n\equiv 7^{-1}(2^r-1)\pmod {2^{r+1}}.               \tag{A11}
\end{aligned}
\]

There is therefore a unique representative

\[
 0\le a_r<2^{r+1},\qquad
 a_r\equiv7^{-1}(2^r-1)\pmod {2^{r+1}},              \tag{A12}
\]

and every nonnegative member of the exact stratum is uniquely

\[
 n_r(m)=a_r+2^{r+1}m,\qquad m\ge0.                   \tag{A13}
\]

This proves both directions of the primary equations (3a)/(21), rather than
only showing that the displayed class lies inside the stratum.

Define

\[
                         U_r(m)=\frac{Z(n_r(m))}{2^r}. \tag{A14}
\]

Equation (A3) and (A11) show that the quotient is a two-adic unit.  For
\(m\ne m'\), equation (A9) gives

\[
\begin{aligned}
 v_2(U_r(m)-U_r(m'))
 &=v_2(n_r(m)-n_r(m'))-r\\
 &=v_2(2^{r+1}(m-m'))-r\\
 &=1+v_2(m-m').                                      \tag{A15}
\end{aligned}
\]

Hence, for \(s\ge1\),

\[
 U_r(m)\equiv U_r(m')\pmod {2^s}
 \quad\Longleftrightarrow\quad
 m\equiv m'\pmod {2^{s-1}}.                         \tag{A16}
\]

There are \(2^{s-1}\) source classes and exactly \(2^{s-1}\) odd target
classes modulo \(2^s\), so (A16) is a bijection onto all odd residues.  At
\(s=1\), both sides contain exactly one class; no valuation of a nonzero
difference is needed, and the statement remains valid.

For \(r=0\), (A12) gives \(a_0=0\), so
\(n_0(m)=2m\) and

\[
 U_0(m)=Z(2m)=25^mF(14m+1).
\]

Thus the earlier even-depth result is exactly, not just analogously, the
zero stratum.

## 6. Relation to the actual reduced BBP coordinate

Let \(L_N\) be the odd common denominator and \(A_N\) the selected numerator
from (A1).  At \(N=7n\), set

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n}.
\]

Direct cancellation of powers of 2 in the BBP scale gives

\[
 10^nB_{7n}
 =\frac{10^nA_{7n}}{2^{28n}L_{7n}}
 =\frac{V_n}{D_n}.                                   \tag{A17}
\]

Put \(r_n=v_2(7n+1)\).  From (A1) and (A3), using that \(L_{7n}\) is odd,

\[
 v_2(V_n)=v_2(A_{7n})=r_n.                           \tag{A18}
\]

Let the full ordinary gcd of \(V_n,D_n\) be \(2^{r_n}g_n\), where \(g_n\)
is odd.  The fraction in (A17), in lowest terms, is

\[
 \frac{P_n}{2^{\kappa_n}Q_n},\qquad
 \kappa_n=27n-r_n,\quad
 P_n=\frac{V_n}{2^{r_n}g_n},\quad
 Q_n=\frac{L_{7n}}{g_n}.                             \tag{A19}
\]

For every \(n\ge1\), \(7n+1<2^{27n}\), so \(\kappa_n\ge1\).  Reducing
modulo the exact dyadic denominator and cancelling the same odd factor on
top and bottom yields

\[
\begin{aligned}
 P_nQ_n^{-1}
 &\equiv \frac{V_n/2^{r_n}}{L_{7n}}
  =\frac{5^nF(7n+1)}{2^{r_n}}
  =U_{r_n}(m) \pmod {2^{\kappa_n}},                  \tag{A20}
\end{aligned}
\]

when \(n=n_{r_n}(m)\).  Therefore the primary

\[
 w_n=\left[\frac{Z(n)}{2^{r_n}}\right]_{2^{\kappa_n}} \tag{A21}
\]

really is the complete reduced dyadic coordinate of the actual selected BBP
rational, even after all possible odd common factors have been cancelled.
In particular, whenever \(s\le\kappa_{n_r(m)}\), the low \(s\) bits of the
actual \(w_{n_r(m)}\) equal \(U_r(m)\bmod2^s\).  A complete block of
\(2^{s-1}\) consecutive \(m\)-values is one complete residue system modulo
\(2^{s-1}\), so it realizes every odd low-bit residue exactly once.

The index \(n=0\) was correctly included in the abstract isometry (A9), but
it has \(\kappa_0=0\) and therefore is not used as a positive-precision
actual coordinate.  The primary report already restricts its raw-coordinate
formula to \(n\ge1\) and requires the blocks in the final low-bit statement
to be far enough out.

## 7. Fixed-level result versus the moving diagonal

On the \(r\)-stratum,

\[
 \kappa_{n_r(m)}=27(a_r+2^{r+1}m)-r,
\]

which grows linearly with \(m\).  The exact period needed to enumerate the
odd residues at that precision is
\(2^{\kappa_{n_r(m)}-1}\), exponential in the same parameter.  Equations
(A9) and (A15) therefore give fixed-level permutations only; substituting a
precision that itself depends on \(m\) reverses the quantifier order and is
not justified.

The frozen separator result supplies an even sharper boundary: complete
dyadic data can be preserved while changing odd selected data and retaining
only the all-nine endpoint color.  The all-stratum theorem consequently
does not establish moving-diagonal mixing, a colored return, or V1.  The
primary report states this boundary accurately.

## 8. Independent replay and hygiene

The independent checker evaluates nonnegative \(F\)-values using the forward
recurrence from (A1), rather than importing or copying the primary checker's
infinite-series evaluator.  It separately evaluates the reflected series to
cross-check the recurrence and the null value at zero.  It also constructs
the ordinary gcd of \(V_n,D_n\), so (A19)--(A21) are tested after full odd as
well as dyadic reduction.

Commands run from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_check.py \
      work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_independent_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_independent_check.py

Both checkers returned PASS.  The retained independent output is:

    status: PASS
    finite_claim_label: experiment
    audited_theorem_claim_label: proof sketch
    maximum_raw_precision: 10
    maximum_stratum: 6
    maximum_stratum_precision: 8
    maximum_exact_sevenfold_depth: 48
    reflected_zero_checks: 40
    recurrence_series_cross_checks: 240
    five_power_lifting_checks: 4096
    raw_bijection_checks: 2046
    raw_isometry_checks: 698027
    zero_endpoint_checks: 80
    orientation_checks: 320
    stratum_representative_checks: 261
    stratum_bijection_checks: 1785
    stratum_isometry_checks: 75565
    s_one_checks: 7
    low_bit_period_checks: 357
    rational_recurrence_checks: 48
    selected_state_checks: 48
    reduced_fraction_checks: 48
    full_precision_checks: 96
    low_bit_actual_w_checks: 240
    asserts_moving_diagonal_mixing: false
    asserts_colored_return: false
    asserts_v1: false

The primary files were not changed.  Python compilation, exact hash pins,
the primary replay, the independent replay, Markdown-link checks, duplicate
equation-label checks, control-character checks, tab checks, and trailing-
whitespace checks all pass for this audit package.

## 9. Coordination record and final verdict

This audit registered the descendant-area watch
`watch:local:pi-digits:independent-all-stratum-audit-20260813` on
`local:pi-digits` for agent `codex-independent-all-stratum-audit`.  Its
initial and pre-verdict polls were empty at cursor and delivered sequence
57,050, so no event was acknowledged.  Observation events were coordination
signals only and were not used as mathematical evidence.

**Final verdict: PASS.**  No gap was found in the frozen all-stratum
supplement.  The exact result is a useful `proof sketch` description of every
fixed two-adic level of the selected numerator, but the exponential
moving-precision barrier remains, and no claim toward V1 is promoted.
