# Independent audit of even-depth BBP dyadic mixing

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Audited final frozen pair:

- [bbp_even_depth_dyadic_mixing_20260813.md](bbp_even_depth_dyadic_mixing_20260813.md),
  SHA-256
  3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623;
- [bbp_even_depth_dyadic_mixing_20260813_check.py](bbp_even_depth_dyadic_mixing_20260813_check.py),
  SHA-256
  d05ed720b94c23d3d59c23b6bc300d46e6d88dc9f37d31ab5dddb604ce19a839.

Independent replay:

- [bbp_even_depth_dyadic_mixing_20260813_independent_check.py](bbp_even_depth_dyadic_mixing_20260813_independent_check.py),
  SHA-256
  0ec0eef61677f5d963d936ad8e52e2ee285f998de50b8a90b7876b8f474ac29b.

The replay pins both audited files and every frozen mathematical dependency.
It does not import or execute any function from the supplied checker.

## Verdict

**PASS with no correction.** The theorem and its stated dependence on the
frozen two-adic function are valid as a *proof sketch*. The supplied and
independent finite replays are *experiment* evidence. Neither proves a
colored decimal return, diagonal mixing, or canonical V1; V1 remains a
*conjecture*.

The potentially delicate points all survive independent checking:

1. the pairwise isometry of \(F\) follows from the frozen coefficientwise
   power-series congruence, rather than being inferred from the weaker
   one-point valuation alone;
2. at \(n=2m\), \(H(m)\) is exactly the selected complete \(54m\)-bit dyadic
   coordinate, including all bits and all ordinary odd cancellation;
3. the two terms in the difference formula have valuations separated by
   exactly two, so no cancellation hypothesis is hidden;
4. the quotient and bijection include the \(s=1\) singleton case and every
   complete block, not just a block beginning at zero; and
5. every fixed-\(s\) conclusion remains logically separate from the moving
   diagonal \(s=54m\).

## 1. Normalized statement and quantifiers

The audited all-index claim is

\[
 H(m)=25^mF(14m+1),\qquad
 v_2\!\left(H(m)-H(m')\right)=1+v_2(m-m')             \tag{1}
\]

for all **distinct** nonnegative integers \(m,m'\). The valuation at equal
indices is never invoked. For each independently fixed integer \(s\geq1\),
(1) induces a set bijection

\[
 \mathbb Z/2^{s-1}\mathbb Z
 \longrightarrow
 \{\hbox{odd residues modulo }2^s\}.                  \tag{2}
\]

This is not asserted to be a group homomorphism. The complete selected
coordinate exists at positive precision when \(m\geq1\), and its low \(s\)
bits agree with (2) only under the explicit condition \(s\leq54m\). Thus
“any complete block far enough” means a block whose least index satisfies
that inequality. At \(m=0\), (1) is valid, while the positive-precision
coordinate assertion is vacuous.

There is no interchange of quantifiers: (2) says that for every fixed \(s\)
a block of \(2^{s-1}\) indices is complete. It does not say that the single
index \(m\) is distributed when \(s\) is simultaneously chosen as \(54m\).

## 2. The inherited pairwise isometry really follows

The frozen all-depth report proves \(F(0)=0\) and, coefficientwise as a
restricted integral power series,

\[
                         F(X)\equiv X\pmod2.           \tag{3}
\]

The report there emphasizes the factorization \(F(X)=XU(X)\) to obtain the
one-point identity \(v_2(F(x))=v_2(x)\). That one-point identity by itself
would not imply pairwise isometry. However, (3) gives the stronger and
immediate representation

\[
                         F(X)=X+2G(X)                 \tag{4}
\]

for a restricted \(G\in\mathbb Z_2[[X]]\). For \(x\ne y\) in
\(\mathbb Z_2\), termwise factorization of the restricted series gives

\[
 G(x)-G(y)=(x-y)Q(x,y),\qquad Q(x,y)\in\mathbb Z_2.
\]

Consequently

\[
 F(x)-F(y)=(x-y)\bigl(1+2Q(x,y)\bigr),
\]

and the parenthesized factor is a unit. Hence

\[
 \boxed{v_2(F(x)-F(y))=v_2(x-y).}                    \tag{5}
\]

Taking \(y=0\) recovers the needed unit statement for
\(F(14m+1)\). This derivation is coefficientwise and analytic; it does not
assume any orbit-distribution conclusion or the theorem being audited.

## 3. Exact selected coordinate at even depth

The corrected high-dyadic report proves the ordinary rational identity

\[
                         F(N+1)=A_N/L_N.              \tag{6}
\]

At sevenfold depth \(n=2m\), the endpoint is \(N=7n=14m\), while

\[
 r_{2m}=v_2(14m+1)=0,\qquad
 \kappa_{2m}=27(2m)-r_{2m}=54m.                      \tag{7}
\]

Substitution in the frozen selected-coordinate formula gives

\[
 w_{2m}
 =\left[5^{2m}F(14m+1)\right]_{2^{54m}}
 =\left[H(m)\right]_{2^{54m}}.                       \tag{8}
\]

This equality survives reduction of the ordinary fraction. Indeed,
\(L_{14m}\) is odd and (5) makes \(A_{14m}\) odd. Therefore the fraction

\[
 \frac{25^mA_{14m}}{2^{54m}L_{14m}}
\]

retains exactly \(2^{54m}\) in its reduced denominator. Any cancellation is
odd, and multiplying the reduced numerator by the inverse of the reduced
odd denominator gives precisely the residue of \(25^mF(14m+1)\). No prefix,
tail approximation, or lost raw bit is present in (8).

The independent replay reconstructs \(A_{14m},L_{14m}\) from the four
original BBP poles for \(0\leq m\leq80\), checks (6) after every one of 1,121
coefficient steps, and compares all \(54m\) bits of (8) at every positive
endpoint. It also independently reaches the same complete residue by the
functional recurrence through \(m=20\).

## 4. Scaled-isometry proof and the exact valuation gap

Assume \(m>m'\), put \(d=m-m'>0\), and abbreviate
\(F_m=F(14m+1)\). Direct algebra gives

\[
\begin{aligned}
 H(m)-H(m')=25^{m'}\bigl(&25^d(F_m-F_{m'})\\
                         &+(25^d-1)F_{m'}\bigr).       \tag{9}
\end{aligned}
\]

The first inner term has valuation

\[
 v_2(F_m-F_{m'})
 =v_2(14d)=1+v_2(d),                                  \tag{10}
\]

by (5), since powers of 25 are units. The second has valuation

\[
 v_2(25^d-1)+v_2(F_{m'})=3+v_2(d).                    \tag{11}
\]

For completeness, write \(d=2^tu\) with \(u\) odd. The factor

\[
 25^u-1=(25-1)(1+25+\cdots+25^{u-1})
\]

has valuation three because the second factor is a sum of an odd number of
odd terms. Each subsequent doubling multiplies by \(25^e+1\equiv2\pmod8\),
adding exactly one valuation. This proves
\(v_2(25^d-1)=3+t\), including both parity cases.

The valuations in (10) and (11) differ by exactly two. The equality case of
the ultrametric inequality therefore forces the valuation of their sum to
be the smaller one. The outer factor \(25^{m'}\) is a unit, proving (1).
Swapping \(m,m'\) only negates the difference and changes no valuation.

The independent rational replay checks the algebraic decomposition for all
3,240 pairs with \(0\leq m'<m\leq80\), both individual valuations for every
pair, and the resulting exact rational valuation. A separate modular
recurrence replay covers 208 adversarial distances (416 subtraction
orientations), including large powers of two and far base indices, and
checks the lifting identity independently.

## 5. Quotient, edge case, and arbitrary blocks

For distinct indices, (1) gives

\[
\begin{aligned}
 H(m)\equiv H(m')\pmod{2^s}
 &\iff 1+v_2(m-m')\geq s\\
 &\iff m\equiv m'\pmod{2^{s-1}}.                     \tag{12}
\end{aligned}
\]

Equality of indices is handled separately and trivially. Equation (12)
both makes the map on the quotient well-defined and makes it injective.
Every \(H(m)\) is odd by (5) and \(F(0)=0\). The source and the odd target
each have \(2^{s-1}\) elements, so the map is bijective.

When \(s=1\), the source is \(\mathbb Z/1\mathbb Z\) and the target is the
single residue \(1\bmod2\), so there is no concealed \(s\geq2\) hypothesis.
Since every consecutive block of \(2^{s-1}\) integers contains one
representative of each source class, the “any complete block” consequence
is also exact. The independent replay tests two widely separated complete
blocks at every \(1\leq s\leq10\), explicitly tests quotient periodicity,
and includes the singleton edge.

## 6. The diagonal conclusion is correctly negative

At the complete precision \(s=54m\), the period supplied by (2) is

\[
                         2^{54m-1}.                  \tag{13}
\]

The selected depth contributes only the one value indexed by \(m\); it
does not provide a period-length block at that moving precision. Fixed-level
bijection therefore supplies no bound on the Archimedean representative
\(w_{2m}/2^{54m}\), and it cannot locate that value in a colored decimal
cell.

The frozen high-dyadic separator is a valid countermodel to any attempted
deduction using only this dyadic information: it preserves the complete
selected dyadic coordinate while its eventual centered states have zero
carries and only the all-nine endpoint color for each fixed decimal period.
Accordingly, the addendum's statement that a mixed odd--dyadic--
Archimedean estimate is still required is justified.

## 7. Independent replay and status boundary

Run from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_independent_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_independent_check.py

Retained output:

    status: PASS
    finite_claim_label: experiment
    audited_theorem_claim_label: proof sketch
    maximum_F_isometry_precision: 9
    maximum_H_mixing_precision: 10
    fixed_level_blocks_per_precision: 2
    maximum_exact_even_index_m: 80
    f_zero_checks: 64
    reflected_coefficient_checks: 544
    four_pole_coefficient_checks: 1121
    rational_identity_checks: 1121
    f_fixed_level_bijection_checks: 1022
    f_isometry_pair_checks: 174251
    h_parity_checks: 2046
    fixed_level_bijection_checks: 2046
    fixed_level_pair_checks: 348502
    quotient_periodicity_checks: 1023
    s_one_edge_checks: 3
    endpoint_unit_checks: 162
    exact_two_term_decomposition_checks: 3240
    exact_valuation_gap_checks: 6480
    exact_scaled_isometry_checks: 3240
    exact_selected_complete_coordinate_checks: 80
    complete_coordinate_recurrence_checks: 20
    adversarial_scaled_isometry_checks: 416
    adversarial_two_adic_lifting_checks: 208
    full_diagonal_period_at_even_depth_m: 2^(54*m-1)
    asserts_diagonal_mixing: false
    asserts_colored_return: false
    asserts_v1: false

The supplied checker also compiles and returns PASS against the frozen
inputs, including its 698,027 finite pair tests. No declaration was added to
the verified Lean track, so no axiom-audit registration or formal-code check
is claimed.

This addendum makes no novelty claim. Its literature and mathlib boundaries
are inherited from the pinned reports; the only added arithmetic lemma is
proved elementarily above. The audit treats those searches as provenance,
not as evidence for the missing diagonal theorem.

This audit used the descendant-area watch
watch:local:pi-digits:independent-high-dyadic-audit-20260813 on
local:pi-digits for agent codex-independent-high-dyadic-audit. The final
poll was empty at cursor and delivered sequence 56,970, so there was no event
to acknowledge. Observation events are coordination signals only and were
not used as mathematical evidence.

## Sharp handoff

The even-depth theorem is a correct, exact strengthening of fixed-level
mixing for the actual selected dyadic coordinate. Its proof needs only the
frozen analytic identities for \(F\), the elementary lifting calculation,
and ordinary valuation algebra. It remains strictly a fixed-level result.
The moving \(54m\)-bit Archimedean location, colored return, and V1 are still
unproved.
