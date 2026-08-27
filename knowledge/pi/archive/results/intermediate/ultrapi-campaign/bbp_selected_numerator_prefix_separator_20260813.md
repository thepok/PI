# BBP selected numerator: a full-odd and growing-dyadic-prefix separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_colored_zero_carry_v1_20260813.md](bbp_colored_zero_carry_v1_20260813.md),
  SHA-256
  `159ff0d1c94d9fb145790e0ca4f11db571d0af211ef2c588b094201122ff279a`;
- [bbp_centered_carry_recurrence_20260813.md](bbp_centered_carry_recurrence_20260813.md),
  SHA-256
  `3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6`;
- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9`;
- [bbp_rational_phase_density_separator_20260813.md](bbp_rational_phase_density_separator_20260813.md),
  SHA-256
  `1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  This report does not prove that every
finite decimal word occurs in pi.

The result is a sharper selected-numerator method separator, with status
`proof sketch`.  At every sevenfold BBP depth, it retains substantially more
than denominator size or a valuation:

1. the exact selected numerator modulo the **complete odd raw denominator**
   \(L_{7n}\), including every prime power and every CRT component;
2. the first \(2n+4\) least-significant binary digits of that selected
   numerator;
3. the exact gcd with the raw denominator, hence the complete reduced
   denominator and every fixed-repunit reduced denominator;
4. the exact forcing modulo the complete next odd denominator and the first
   \(2n+6\) least-significant binary digits at the next depth; and
5. a positive normalized forcing whose relative error from the exact BBP
   forcing is

   \[
      O\!\left(n^2(4/5)^n\right).                 \tag{1}
   \]

Nevertheless the alternative rational centered orbit has zero carry at
every sufficiently large transition.  For every fixed period \(P\), it is
eventually confined to the all-nine boundary color and has zero
\((10^P-1)\)-centered carries forever.  It therefore fails the all-color
condition maximally.

More generally, \(2n+4\) may be replaced, after a finite onset, by
\(\lfloor cn\rfloor\) for any fixed

\[
                         0<c<\log_2 5.             \tag{2}
\]

The construction deliberately changes the unpreserved high dyadic and
Archimedean part of the selected numerator.  It is not another BBP
truncation, not a counterexample concerning pi, and not evidence against
V1.  Its exact consequence is that odd-prime formulas, CRT decomposition,
shared-factor or determinant gcds, the exact valuation, and a linear
low-dyadic prefix cannot by themselves force an all-color return.  A valid
continuation must control the remaining selected high dyadic/Archimedean
coordinate, or use different information.

The finite replay has label `experiment`.  The bounded source search is
`literature-checked` on the displayed date.  Nothing here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Normalized statement and quantifiers

Write the nonterminating decimal expansion of pi.  Canonical V1 is

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists r\geq0\ \forall i<m:\quad d_{r+i}(\pi)=w_i.       \tag{3}
\]

Occurrence is contiguous, leading zeroes are allowed, and the empty word is
vacuous.  This is not the false assertion that every infinite word occurs as
a suffix, and it is not subsequence occurrence.

The colored predecessor proves the exact equivalent condition

\[
\begin{split}
 \forall P\geq1\ \forall k\pmod {10^P-1}\ \forall H\geq1\
 \forall N\geq0\ \exists n\geq N:\qquad\qquad\\
 \widehat z_{n,P}\equiv k\pmod {10^P-1},\qquad
 \widehat\gamma_{n,P}=\cdots=\widehat\gamma_{n+H-1,P}=0.
                                                               \tag{4}
\end{split}
\]

The separator below does not assert (4).  It shows that a precisely listed
collection of exact numerator invariants is compatible with the opposite
behavior: only one boundary color and zero carries.

## 2. Exact selected BBP numerator and its zero-carry solution

Use the four-pole coefficient

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}                        \tag{5}
\]

and write

\[
\begin{aligned}
 L_m&=\mathop{\rm lcm}(d_0,\ldots,d_m),\\
 A_m&=\sum_{k=0}^m(120k^2+151k+47)16^{m-k}{L_m\over d_k},\\
 B_m&={A_m\over16^mL_m}.
\end{aligned}                                                    \tag{6}
\]

At sevenfold depth put

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 {V_n\over D_n}=10^nB_{7n}.                         \tag{7}
\]

For

\[
 R_n={L_{7n+7}\over L_{7n}},\qquad
 \Lambda_n=2^{27}R_n,                              \tag{8}
\]

the exact selected-numerator recurrence is

\[
 D_{n+1}=\Lambda_nD_n,\qquad
 V_{n+1}=10\Lambda_nV_n+K_n,                       \tag{9}
\]

where \(K_n=5^{n+1}H_n>0\) is the seven-term increment from the frozen
predecessor.

The exact bounded zero-carry solution for the normalized forcing is

\[
 t_n=-10^n(\pi-B_{7n})<0.                           \tag{10}
\]

Indeed, with

\[
 \delta_n={K_n\over D_{n+1}}
 =10^{n+1}(B_{7n+7}-B_{7n})>0,                     \tag{11}
\]

one has

\[
                         t_{n+1}=10t_n+\delta_n.    \tag{12}
\]

This solution is irrational.  The construction will not replace it by an
equal rational value; it selects an extremely close rational in the exact
BBP congruence class described next.

## 3. Full-odd, growing-dyadic-prefix selection

For the concrete version set

\[
 \kappa_n=2n+4,\qquad M_n=2^{\kappa_n}L_{7n}.       \tag{13}
\]

For \(n\geq1\), \(M_n\mid D_n\).  Choose \(S_n^*\in\mathbb Z\) to be a
closest member to \(D_nt_n\) of the arithmetic progression

\[
                         S_n^*\equiv V_n\pmod {M_n}. \tag{14}
\]

Put

\[
 e_n^*={S_n^*\over D_n},\qquad
 \eta_n=e_n^*-t_n.                                 \tag{15}
\]

Nearest-grid selection gives

\[
 |\eta_n|\leq{M_n\over2D_n}=2^{3-25n}.             \tag{16}
\]

The first omitted positive BBP term supplies a lower bound for (10).  For
\(k\geq1\), the elementary inequalities

\[
 d_k\leq(3k)(7k)(9k)(13k)=2457k^4,qquad
 120k^2+151k+47\geq120k^2
\]

give \(a(k)>1/(21k^2)\).  Consequently, with
\(\lambda=10/16^7=5/2^{27}\),

\[
 |t_n|\geq{\lambda^n\over336(7n+1)^2}.             \tag{17}
\]

Combining (16)--(17),

\[
 { |\eta_n|\over |t_n|}
 \leq2688(7n+1)^2(4/5)^n\longrightarrow0.         \tag{18}
\]

It follows that, for every sufficiently large \(n\),

\[
                         -\tfrac12<e_n^*<0.         \tag{19}
\]

Define its least positive phase numerator by

\[
                         r_n^*=D_n+S_n^*.           \tag{20}
\]

Then \(0<r_n^*<D_n\), \(\{e_n^*\}=r_n^*/D_n\), and (14) gives

\[
 \boxed{
 r_n^*\equiv V_n\pmod {L_{7n}},\qquad
 r_n^*\equiv V_n\pmod {2^{2n+4}}.}                \tag{21}
\]

Thus every odd prime-power coordinate of the actual selected numerator is
retained, not merely its support or valuation.

## 4. Exact reduced denominators and determinant gcds are retained

The audited two-adic identity is

\[
                         v_2(V_n)=v_2(7n+1).        \tag{22}
\]

Since \(v_2(7n+1)<2n+4\), the second congruence in (21) gives

\[
                         v_2(r_n^*)=v_2(V_n).       \tag{23}
\]

The first congruence in (21), taken modulo every complete prime power in
\(L_{7n}\), preserves every odd gcd valuation.  Therefore

\[
 \boxed{\gcd(r_n^*,D_n)=\gcd(V_n,D_n).}             \tag{24}
\]

In particular \(r_n^*/D_n\) and \(V_n/D_n\) have exactly the same reduced
denominator.  More strongly, for every fixed integer \(q\geq1\),

\[
 \gcd(qr_n^*,D_n)=\gcd(qV_n,D_n).                  \tag{25}
\]

Every color determinant has the same shared-factor data.  For arbitrary
\(z\in\mathbb Z\),

\[
\boxed{
 \gcd(qr_n^*-zD_n,D_n)
 =\gcd(qV_n,D_n).}                                  \tag{26}
\]

Thus a determinant or shared-factor argument which only uses the exact
gcd, even for every repunit \(q=10^P-1\), cannot distinguish this separator
from the actual selected numerator.

The same applies termwise to CRT characters.  Write
\(e_m(x)=\exp(2\pi i x/m)\).  For every
\(m\mid2^{2n+4}L_{7n}\) and every integer \(h\),

\[
              e_m(hr_n^*)=e_m(hV_n).               \tag{27}
\]

An exponential sum assembled only from these local characters is therefore
identical for the two sequences.  An estimate must include one of the
unpreserved high dyadic/Archimedean coordinates to say anything different.

## 5. Cross-depth forcing congruence and exponential closeness

Define the alternative exact integer forcing by

\[
                         K_n^*=S_{n+1}^*-10\Lambda_nS_n^*. \tag{28}
\]

Equations (12) and (15) give the exact coboundary identity

\[
 {K_n^*\over D_{n+1}}
 =\delta_n+\eta_{n+1}-10\eta_n.                    \tag{29}
\]

From (16),

\[
 \left|{K_n^*\over D_{n+1}}-\delta_n\right|
 \leq81\,2^{-25n}.                                 \tag{30}
\]

The first term in (11) and \(a(7n+1)>1/(21(7n+1)^2)\) give

\[
 \delta_n\geq{5\over168(7n+1)^2}\lambda^n.        \tag{31}
\]

Hence (1) follows, and \(K_n^*>0\) eventually.

The exact selected forcing residue is retained as well.  From (14), the
odd part of \(S_n^*-V_n\) contains \(L_{7n}\); multiplication by
\(R_n=L_{7n+7}/L_{7n}\) promotes it to \(L_{7n+7}\).  Its dyadic part gains
28 powers of two under \(10\Lambda_n\).  Since
\(\kappa_{n+1}=\kappa_n+2\), equations (9), (14), and (28) prove

\[
 \boxed{
 K_n^*\equiv K_n
 \pmod {\,2^{2n+6}L_{7n+7}}.}                     \tag{32}
\]

Thus even the cross-depth congruence is not being discarded: all odd
forcing coordinates and a growing dyadic prefix agree exactly at every
late transition.

For the general form (2), take
\(\kappa_n=\lfloor cn\rfloor\) after an onset at which
\(\kappa_n>v_2(7n+1)\).  Then

\[
 |\eta_n|\leq2^{-(27-c)n+O(1)},\qquad
 { |\eta_n|\over|t_n|}
 \leq n^{O(1)}(2^c/5)^n=o(1).                     \tag{33}
\]

Also \(\kappa_{n+1}-\kappa_n\leq3<28\), so the forcing congruence proof is
unchanged.  This explains the exact threshold \(\log_2 5\): it is the
binary numerator scale in the first omitted BBP tail.

## 6. All fixed periods collapse to one boundary color

Regard \(e_n^*=S_n^*/D_n\) as the centered state of a rational recurrence
with forcing \(K_n^*/D_{n+1}\).  Equation (28) is exactly

\[
 e_{n+1}^*=10e_n^*+{K_n^*\over D_{n+1}}.           \tag{34}
\]

By (19), both states remain in the centered cell, so the centered carry in
(34) is zero at every sufficiently large transition.

Fix \(P\geq1\) and put \(q=10^P-1\).  Since \(e_n^*\to0\) from below,
eventually

\[
                         -\tfrac12<qe_n^*<0.        \tag{35}
\]

Multiplying (34) by \(q\) shows that the \(q\)-centered carry is again zero
forever after that period-dependent onset.  On the fractional circle the
phase is \(r_n^*/D_n=1+e_n^*\), so its split color is

\[
 \left\lfloor q{r_n^*\over D_n}+{1\over2}\right\rfloor=q. \tag{36}
\]

This is the all-nine endpoint color.  No interior color ever appears after
the onset, even though (21)--(32) retain all the listed selected-numerator
data.  Therefore those data do not imply the all-color condition (4).

## 7. What this does and does not close

The separator closes the following well-defined routes.

- **Odd CRT alone.**  The complete residue modulo \(L_{7n}\), including all
  explicit high-prime localization formulas and the remaining odd cofactor,
  is identical term by term.
- **Shared factors or color determinants.**  Equation (26) preserves the
  exact gcd for every proposed color integer and every fixed repunit.
- **Valuation plus a growing bit prefix.**  The exact two-adic valuation and
  \(2n+4\) low bits are identical; the more general construction preserves
  any slope below \(\log_2 5\).
- **Odd recurrence congruences.**  Equation (32) retains the complete next
  odd forcing class, not only the numerator classes separately.
- **Asymptotically exact positive forcing.**  Equations (1) and (29)--(31)
  show exponential relative agreement, yet all carries vanish.

It does not close a route that uses the exact full integer \(V_n\), the
unpreserved high dyadic bits, or the exact equality \(K_n^*=K_n\).  Exact
equality at every transition together with one initial state determines the
actual recurrence and cannot be varied.  The result therefore localizes the
remaining information rather than proving it unusable.

## 8. Literature and mathlib boundary

Status: bounded `literature-checked` search on **2026-08-13 UTC**.

| primary source | checked relevance and boundary | local pin |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | Supplies the exact four-pole series.  It does not prove distribution of the selected decimal numerator. | SHA-256 `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Bailey--Crandall, [*On the Random Character of Fundamental Constant Expansions*](https://doi.org/10.1080/10586458.2001.10504441), Hypothesis A | The relevant rational-perturbation distribution statement is explicitly a hypothesis. | SHA-256 `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2), Theorems 3.1, 3.3, and 4.1 | Gives general perturbed-radix shadowing and conditional BBP dichotomies; it supplies no theorem controlling this selected numerator's missing Archimedean coordinate. | SHA-256 `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |

Fresh searches covered `BBP selected numerator distribution`, `BBP partial
sum numerator exponential sums`, `BBP CRT numerator normality`, and
`BBP dynamical system equidistribution`.  They returned the classical
conditional BBP program, formula families, digit-extraction computations,
and generic/metric lacunary results.  No primary theorem found in this
bounded search proves the all-color return or contradicts the separator.
No novelty claim is made.

A repository/mathlib search found the standard Chinese-remainder interfaces
in `Mathlib/Data/Nat/ChineseRemainder.lean` and
`Mathlib/Data/ZMod/QuotientRing.lean`, but no Weyl/equidistribution theorem
for this moving selected rational orbit.  No formal infrastructure was
invented, and this report adds no declaration to the verified track.

## 9. Exact finite replay

The companion
[bbp_selected_numerator_prefix_separator_20260813_check.py](bbp_selected_numerator_prefix_separator_20260813_check.py),
SHA-256
`017c7d17b68700bea23f89f859df16390de4e1f65f6cb1a6298eb27d04b6171d`,
uses only integer and `Fraction` arithmetic.  To avoid importing a decimal
approximation to pi, it replaces pi by one common deeper exact BBP partial
sum.  The resulting rational targets still satisfy (12) exactly throughout
the replay window.

It independently reconstructs (L_{7n},A_{7n},D_n,V_n); selects the exact
CRT representatives; checks every full-odd and \(2n+4\)-bit congruence,
valuation, gcd, fixed-period denominator, boundary color, zero-carry
recurrence, forcing congruence, and coboundary identity for
(100\leq n\leq150).  The common rational tail cutoff is depth 170.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_check.py
```

Retained output:

```text
status: PASS
bounded_replay_label: experiment
construction_label: proof sketch
depth_range: [100, 150]
rational_tail_cutoff: 170
periods_checked: [1, 2, 3, 4]
state_identity_checks: 408
complete_denominator_checks: 102
color_and_zero_carry_checks: 812
transition_identity_checks: 300
maximum_relative_tail_error: 0.04570856678993249
maximum_relative_forcing_error: 0.04570856699243523
preserves_full_odd_selected_residue: true
preserved_dyadic_bits: 2*n+4
preserves_complete_reduced_denominator: true
asserts_actual_bbp_carries_are_zero: false
asserts_all_color_return: false
asserts_v1: false
```

The bounded rows are only an `experiment`.  The all-index claims are the
elementary construction and estimates (13)--(36), with the frozen BBP and
two-adic identities as stated dependencies.

## Sharp handoff

The selected-numerator attack has reached a precise boundary.  Full odd CRT
data across every depth, exact determinant gcds, the exact two-adic order,
almost \((\log_2 5)n\) low binary digits, and the corresponding forcing
congruences can all coexist with permanent zero carries and only the
all-nine color.  These routes cannot establish (4).

The surviving target is the exact high-dyadic/Archimedean selection made by
the four-pole numerator.  A useful positive continuation must estimate that
coordinate itself—for example through a genuinely coefficient-specific
short exponential sum that includes the omitted dyadic character—or prove a
different fixed-pi return.  No such estimate is obtained here, so V1 remains
a `conjecture`.
