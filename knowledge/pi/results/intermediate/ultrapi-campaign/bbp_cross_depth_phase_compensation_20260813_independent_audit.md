# Independent audit: BBP cross-depth phase compensation

Audit date: **2026-08-13 UTC**

Verdict on the frozen primary pair: **PASS**.

The exact event formula and its support, the complete high-prime plus static
5-primary CRT phase, the adjacent-depth compensation identity and bound, the
fixed-exponent column diameter, the triangular double-mean reduction, the
$x=1/45$ pigeonhole countermodel, and the stated period claim boundaries all
withstand an independent derivation and exact replay.

The infinite identities and asymptotic estimates retain label
`proof sketch`.  Every bounded computation has label `experiment`.  The
source applicability record retains label `literature-checked`.  No
fixed-sixteen return is proved, and canonical V1 remains a `conjecture`.
Nothing here is `machine-checked`, a `candidate resolution`, or a
`verified resolution`.

## 1. Frozen scope, provenance, and hygiene

The target is
[problems/local/pi-digits.txt](../../problems/local/pi-digits.txt), SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It is Marcel's immutable local question and has no external source URL; none
is invented here.

The audited primary pair is:

- [bbp_cross_depth_phase_compensation_20260813.md](bbp_cross_depth_phase_compensation_20260813.md),
  SHA-256
  `3ff784ebad18c8dda7c63691ba99120f80299953361362f7d2f2f8cd26f89d3f`;
- [bbp_cross_depth_phase_compensation_20260813_check.py](bbp_cross_depth_phase_compensation_20260813_check.py),
  SHA-256
  `0a62b6d88414536fdb160a25a4d177e12d95cd712f76d980a0a0d40405541724`.

The primary files were not changed.  Both are UTF-8, have no control
characters other than line feeds, no carriage returns, no tabs, and no
trailing whitespace.  The primary report has no duplicate equation labels
and its local links resolve.

The independent checker is
[bbp_cross_depth_phase_compensation_20260813_independent_check.py](bbp_cross_depth_phase_compensation_20260813_independent_check.py).
It imports no primary or earlier checker.  It starts from the original BBP
partial fractions, reconstructs every sampled reduced rational and local
coordinate, and pins both primary hashes.

## 2. Independent reconstruction of the full phase

The checker starts from

\[
 a(k)={4\over8k+1}-{1\over4k+2}
      -{1\over8k+5}-{1\over8k+6}                 \tag{A1}
\]

and independently verifies its equality with the four-pole rational
coefficient in every sampled row.  It forms

\[
 B_M={P_M\over2^{K_M}R_M},\qquad
 16B_M=y_M+{c_M\over R_M},                         \tag{A2}
\]

directly from the reduced `Fraction` numerator and denominator.

For every actual prime $p>M$ in $R_M$, the replay computes the singular
terms in $16pB_M$ from (A1), rather than calling the primary localization
function.  Their residue agrees with the actual additive coordinate

\[
 c_M(R_M/p)^{-1}\pmod p.                           \tag{A3}
\]

CRT reconstruction confirms

\[
 {c_M\over R_M}\equiv
 \Xi_M^>+{\eta_M\over C_M^>}\pmod1.                \tag{A4}
\]

The full 5-primary valuation is independently read from the reduced
denominator and agrees with

\[
 e_M=v_5(R_M)=\lfloor\log_5(8M+5)\rfloor.          \tag{A5}
\]

Writing $C_M^>=5^{e_M}C_{0,M}$ and splitting its additive coordinate into
$\beta_{5,M}$ and $\beta_{0,M}$ gives

\[
 {\eta_M\over C_M^>}\equiv
 {\beta_{5,M}\over5^{e_M}}+{\beta_{0,M}\over C_{0,M}}
 \pmod1.                                           \tag{A6}
\]

The primary report correctly restricts to $M\ge48$ and exponents $n\ge M$.
Thus

\[
 n\ge M\ge48\ge\max(4,e_M),                       \tag{A7}
\]

so $A_n=(10^n-16)/16$ is an integer and
$A_n\equiv-1\pmod {5^{e_M}}$.  Multiplication of (A6) is legitimate, and
the independent replay confirms the combined phase

\[
 (10^n-16)B_M\equiv
 A_ny_M+A_n\Xi_M^>
 -{\beta_{5,M}\over5^{e_M}}
 +A_n{\beta_{0,M}\over C_{0,M}}\pmod1.             \tag{A8}
\]

The replacement
$\Xi_M^>\equiv J_M/105+H_M\pmod1$ is inherited from the separately frozen
high-prime lift and is compatible with (A8).  No independent-phase claim is
made about the auxiliary factor $5$ in $105$; the primary correctly warns
that it cancels internally with $H_M$.

## 3. Boundary events and the constant 320

Let $k=M+1$.  When the depth grows from $M$ to $M+1$, a rational
localization $G_{M,p}$ can change only if a new singular term is introduced
at index $k$.  The possible pole values are

\[
                         2k+1,\quad4k+3,\quad8k+1,\quad8k+5.   \tag{A9}
\]

For a prime $p>k$, each value is less than $9p$ and its odd multiplier is
one of $1,3,5,7$.  Pairwise resultants of the four pole families have no
prime divisor above five, so one prime $p>k$ cannot be singular in two
families at the same index.  Each family contributes at most one such
prime.  Thus there are at most four new event terms, each of absolute
rational weight at most $64$.

The support cutoff changes from $p>M$ to $p>M+1$.  The only possible loss
is $p=M+1$, if that number is prime and its actual coordinate survives.
The six-row localization table gives $|G_{M,M+1}|\le64$.  Therefore

\[
 H_{M+1}-H_M=
 \sum_{p\in\mathcal N_{M+1}}{\varepsilon_{M+1,p}\over p}
 -\mathbf1_{\{M+1\ \mathrm{\,prime},\ M+1\mid R_M\}}
 {G_{M,M+1}\over M+1},                             \tag{A10}
\]

and, since every denominator is at least $M+1$,

\[
                         |H_{M+1}-H_M|\le{5\cdot64\over M+1}.
                                                               \tag{A11}
\]

The independent checker compares supports before and after every sampled
depth, verifies every entering or changed coordinate against exactly one
new pole in (A9), permits only the boundary prime to leave, and reconstructs
the rational difference term by term.  This confirms both the support and
the constant in the primary statement.

## 4. Compensation identity and inequality

Directly from the finite BBP sum,

\[
                         B_{M+1}-B_M={a(M+1)\over16^{M+1}}.    \tag{A12}
\]

For a common proportional-row exponent

\[
 M+1\le n\le\lfloor(\log_{10}16)M\rfloor,                     \tag{A13}
\]

multiplication by $10^n-16$ proves exactly

\[
 \Phi_{M+1,n}-\Phi_{M,n}
 =(10^n-16){a(M+1)\over16^{M+1}}.                \tag{A14}
\]

It is positive.  To audit the displayed upper bound without assuming a
pointwise coefficient estimate, use positivity of every BBP term and the
frozen tail bound:

\[
 {a(M+1)\over16^{M+1}}
 \le\pi-B_M\le{16^{-M}\over15(M+1)^2}.             \tag{A15}
\]

Equation (A13) gives $10^n\le16^M$; hence

\[
 0<\Phi_{M+1,n}-\Phi_{M,n}
 <10^n{a(M+1)\over16^{M+1}}
 \le{1\over15(M+1)^2}.                            \tag{A16}
\]

Subtraction of (A8) at adjacent depths confirms that the visible
high-prime plus static 5-primary increment and the hidden dyadic plus
residual increment sum to (A14) modulo one.  The bounded replay observes
many macroscopic visible jumps, but that observation is correctly labelled
`experiment`; the exact compensation law does not require such jumps.

## 5. Column diameter and triangular double mean

For every admissible pair $(M,n)$, the tail estimate gives

\[
 |(10^n-16)(\pi-B_M)|
 <{10^n16^{-M}\over15(M+1)^2}
 \le{1\over15(M+1)^2}.                              \tag{A17}
\]

At fixed $n$, admissible depths satisfy

\[
 \left\lceil{n\over\log_{10}16}\right\rceil\le M\le n.      \tag{A18}
\]

Thus every point in the column lies within $O(n^{-2})$ of the same point
$(10^n-16)\pi$, and any two column points differ by $O(n^{-2})$.  The
stronger monotone telescope in the primary report follows by summing
(A14), and the independent checker verifies it exactly on every finite
column.

For

\[
 \mathcal D_X=\{(M,n):48\le M\le X,\ M\le n\le
 \lfloor(\log_{10}16)M\rfloor\},                  \tag{A19}
\]

let $w_X(n)$ count admissible depths.  Reindexing a finite double sum gives
the exact equality

\[
 \sum_{(M,n)\in\mathcal D_X}e(hz_n)
 =\sum_nw_X(n)e(hz_n),                              \tag{A20}
\]

where $z_n=(10^n-16)\pi$.  Since
$|e(hu)-e(hv)|\le2\pi|h||u-v|$, (A17) gives total replacement error at most

\[
 {2\pi|h|\over15}
 \sum_{M=48}^X
 {\lfloor(\log_{10}16)M\rfloor-M+1\over(M+1)^2}
 =O_h(\log X).                                     \tag{A21}
\]

The numerator in each summand is $O(M)$, so the last assertion is uniform
for fixed $h$.  Also

\[
 |\mathcal D_X|=
 {\log_{10}16-1\over2}X^2+O(X),                   \tag{A22}
\]

by summing $(\log_{10}16-1)M+O(1)$.  Division by (A22) makes the normalized
error $O_h(\log X/X^2)=o(1)$.  The primary wording is therefore correct:
the depth parameter supplies triangular weights, not independent orbit
points.

## 6. Pigeonhole countermodel and period boundary

For $x=1/45$ and every $n\ge1$,

\[
 10^n\equiv10\pmod {45},\qquad
 (10^n-16)x\equiv-{2\over15}\equiv{13\over15}\pmod1.          \tag{A23}
\]

All pair distances are zero, while every point has distance $2/15$ from
the prescribed target zero.  This independently verifies the exact logical
countermodel: close pairs alone do not imply the inhomogeneous return.

After the true 5-primary factor is removed, the remaining modulus is
coprime to ten and its exact moving-term period divides, and for a unit
coefficient equals,

\[
                         \operatorname {ord}_{C_{0,M}}(10).    \tag{A24}
\]

The primary correctly makes no asymptotic lower-bound claim for this order.
It states only the general upper bound
$\operatorname {ord}_{C_{0,M}^{\square}}(10)\le
C_{0,M}^{\square}=\exp(o(M))$ and labels the observed fact that every
sampled period exceeds its row length as `experiment`.  The independent
checker obtains orders from the Carmichael exponent and strips prime
factors independently; both canonical and square-root residual periods
exceed every sampled row length.  This is a replay agreement, not a promoted
claim.

## 7. Independent exact replay

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_independent_check.py \
  --max-depth 280
```

Retained output:

```text
status: PASS
independent_bounded_label: experiment
audited_infinite_label: proof sketch
depth_range: [48, 280]
coefficient_identity_checks: 281
actual_coordinate_checks: 29323
crt_reconstruction_checks: 233
five_valuation_checks: 233
static_five_checks: 7918
complete_phase_checks: 7918
event_support_checks: 415
event_formula_checks: 232
event_constant_checks: 232
compensation_checks: 7628
macroscopic_visible_jumps: 3722
maximum_visible_jump: 0.499855002416626
column_checks: 290
double_array_points: 7918
distinct_columns: 290
exact_error_sum: 0.024293342630223
harmonic_scale_checks: 2
period_checks: 233
sqrt_period_checks: 233
periods_longer_than_rows: 233
sqrt_periods_longer_than_rows: 233
pigeonhole_countermodel_checks: 200
asserts_fixed_sixteen_return: false
asserts_v1: false
```

Every displayed finite count has label `experiment`.  The replay is not
evidence for asymptotic period growth or a return.

## 8. Literature and formal-scope audit

The primary's dated applicability discussion is correctly scoped.  The
Konyagin--Shparlinski theorem cited in the frozen parent concerns prime
moduli and primitive roots, while the selected residual modulus here is
composite and changing.  The cited 2024 Bhakta--Shparlinski paper gives
power-generator discrepancy estimates under order and length hypotheses
not established for this selected composite modulus, and does not include
the synchronized full phase (A8).  The primary claims no exhaustiveness or
novelty from this search.

The primary mathlib note is also accurate in scope: general finite-order and
cyclic-group infrastructure does not supply the missing pointwise short
power-generator discrepancy theorem.  Since this branch proves no theorem
supporting a research resolution in the verified track, it correctly adds
no Lean declaration and no axiom-audit entry.

## Final verdict

**PASS.**  The primary report's new mathematical content is an exact local
increment formula and an exact compensation/telescoping analysis.  Its
conclusion is appropriately negative: depth averaging reconstructs a
weighted version of the original pi orbit, periods and pair pigeonhole do
not hit the prescribed target, and no fixed return follows.

The proof labels, quantifiers, inequalities, and separation between finite
experiment and infinite proof sketch are correct.  Canonical V1 remains a
`conjecture`.
