# BBP dyadic moving diagonal: an exact decimal recurrence and seven modular phases

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is Marcel's local, human-authored question and has no
external source URL; none is invented here.

Frozen inputs:

- [bbp_all_stratum_dyadic_mixing_20260813.md](bbp_all_stratum_dyadic_mixing_20260813.md),
  SHA-256
  `5089d63f83de1978731c50964c7fce45e7a4cc88e989a29acd99e08b8a9c8360`;
- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  `d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`:

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists r\geq0\ \forall i<m:\quad d_{r+i}(\pi)=w_i.       \tag{1}
\]

Occurrence is contiguous, leading zeroes are allowed, and the empty word is
vacuous.  No occurrence is proved here.

The coefficient-specific moving-diagonal attack does produce two exact
results, both with status `proof sketch` because they use the frozen
two-adic identity for (F).

1.  The normalized **complete** selected dyadic coordinate satisfies the
    nonautonomous decimal recurrence

    \[
                 \boxed{X_{n+1}=\{10X_n+\Gamma_n\}.}          \tag{2}
    \]

    The factor ten is not an analogy: the old state is shifted by 28 binary
    places while the moving modulus grows by 27 places.
2.  The forcing (Gamma_n) has an exact seven-phase formula.  It is
    exponentially close on the circle to a sum of seven modular-power
    residues, each having a denominator of size (O(n^4)):

    \[
      \Gamma_n=\left\{\sum_{j=1}^7{h_{n,j}\over d_{n,j}}
                     +\varepsilon_n\right\},\qquad
      0<\varepsilon_n\ll {1\over n^2}
                   \left({5\over2^{27}}\right)^{n+1}.         \tag{3}
    \]

This is a useful sharpening of the diagonal gap.  The functional equation
does not leave an opaque analytic forcing: it reduces it to seven explicit
varying-modulus exponential residues.  But no discrepancy, density, or
target-hitting estimate for those residues is obtained.  Standard fixed-level
two-adic permutation, ergodic, Mahler/automatic, and exponential-sum results
do not bridge the remaining quantifier and scale mismatch.

There is one small unconditional complexity consequence within the frozen
framework: the rational state sequence (X_n) takes infinitely many values
and is not eventually periodic.  This does not imply that even one prescribed
interval is hit.

The companion finite replay is an `experiment`.  The bounded source search
below is `literature-checked`.  Nothing here is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Exact state and seven-step functional equation

Use the audited coefficient

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}                         \tag{4}
\]

and the frozen restricted two-adic function

\[
 F(X)=\sum_{j\geq0}16^j a(X-1-j),\qquad
 F(X+1)=16F(X)+a(X).                                \tag{5}
\]

Put

\[
 \begin{aligned}
  Z_n&=5^nF(7n+1),& K_n&=27n,\\
  G_n&=\sum_{j=1}^7 16^{7-j}a(7n+j),&
  b_n&=5^{n+1}G_n.
 \end{aligned}                                                   \tag{6}
\]

Seven iterations of (5) give

\[
 F(7n+8)=2^{28}F(7n+1)+G_n,
\]

and hence the exact rational recurrence

\[
                 \boxed{Z_{n+1}=5\,2^{28}Z_n+b_n.}            \tag{7}
\]

For a two-integral rational (u), write
([u]_{2^K}\in\{0,\ldots,2^K-1\}) for its canonical residue.
Define

\[
 X_n={[Z_n]_{2^{K_n}}\over2^{K_n}},\qquad
 \Gamma_n={[b_n]_{2^{K_{n+1}}}\over2^{K_{n+1}}}.             \tag{8}
\]

The frozen valuation identity gives

\[
 r_n=v_2(Z_n)=v_2(7n+1),\qquad
 \kappa_n=K_n-r_n.                                  \tag{9}
\]

Thus, for the complete reduced coordinate (w_n) in the frozen report,

\[
 [Z_n]_{2^{K_n}}=2^{r_n}w_n,qquad
                  X_n={w_n\over2^{\kappa_n}}.                  \tag{10}
\]

So (X_n) is exactly the normalized complete coordinate asked about in this
branch, not a truncated substitute.

If (Z_n) is changed by a multiple of (2^{K_n}), the first term of (7)
changes by a multiple of (2^{K_n+28}), one power of two beyond the next
modulus (2^{K_n+27}).  Therefore (7)--(8) imply

\[
\begin{aligned}
 [Z_{n+1}]_{2^{K_{n+1}}}
 &=[5\,2^{28}[Z_n]_{2^{K_n}}+[b_n]_{2^{K_{n+1}}}]
      _{2^{K_{n+1}}},\\
 X_{n+1}&=\{10X_n+\Gamma_n\},
\end{aligned}                                                   \tag{11}
\]

which proves (2).  This is the exact coefficient-specific diagonal
recurrence missing from the earlier fixed-level statement.

## 2. The forcing is seven explicit varying-modulus phases

For (1\leq j\leq7), set

\[
 \begin{aligned}
  k_{n,j}&=7n+j,\\
  d_{n,j}&=(2k_{n,j}+1)(4k_{n,j}+3)
            (8k_{n,j}+1)(8k_{n,j}+5),\\
  p_{n,j}&=5^{n+1}16^{7-j}
            (120k_{n,j}^2+151k_{n,j}+47),\\
  M_n&=2^{27(n+1)}.
 \end{aligned}                                                   \tag{12}
\]

Every (d_{n,j}) is odd and

\[
                         b_n=\sum_{j=1}^7{p_{n,j}\over d_{n,j}}. \tag{13}
\]

Let

\[
 \rho_{n,j}\equiv p_{n,j}d_{n,j}^{-1}\pmod {M_n},qquad
 0\leq\rho_{n,j}<M_n,                                  \tag{14}
\]

and define the exact lift

\[
                         h_{n,j}={d_{n,j}\rho_{n,j}-p_{n,j}\over M_n}. \tag{15}
\]

For every (n\geq1), (0<p_{n,j}<M_n).  One elementary bound is

\[
 p_{n,j}<2^{3(n+1)+38}(n+1)^2<2^{27(n+1)}.             \tag{16}
\]

The last inequality holds at (n=1), and its right-to-left ratio grows by
at least (2^{24}/(3/2)^2) at each next index.  Equations (14)--(16) show

\[
                         0\leq h_{n,j}<d_{n,j},qquad
 h_{n,j}\equiv-p_{n,j}M_n^{-1}\pmod {d_{n,j}}.          \tag{17}
\]

More explicitly, the second congruence is a varying-modulus power phase:

\[
 h_{n,j}\equiv-
 (120k_{n,j}^2+151k_{n,j}+47)2^{4(7-j)}
 \left(5\,2^{-27}\right)^{n+1}pmod {d_{n,j}}.          \tag{18}
\]

Dividing (15) by (d_{n,j}M_n), summing, and reducing modulo one gives the
exact formula

\[
 \boxed{
 \Gamma_n=\left\{\Theta_n+\varepsilon_n\right\},\qquad
 \Theta_n=\sum_{j=1}^7{h_{n,j}\over d_{n,j}},\qquad
 \varepsilon_n={b_n\over M_n}.}                    \tag{19}
\]

The denominators are only quartic in the moving index.  Indeed

\[
 d_{n,j}\leq15\cdot31\cdot57\cdot61\,(n+1)^4.          \tag{20}
\]

Also, for (k\geq1), positivity and the elementary estimates

\[
 0<a(k)\leq {318k^2\over512k^4}<{1\over k^2}
\]

give

\[
 \boxed{
 0<\varepsilon_n\leq
 {16^7-1\over15(7n+1)^2}
 \left({5\over2^{27}}\right)^{n+1}.}                \tag{21}
\]

Thus the real-small part of the forcing is completely negligible, but the
modular term (Theta_n\bmod1) is not.  For example, the exact replay has
(Gamma_{12}>0.98) while (\varepsilon_{12}<10^{-90}).  Treating the
ordinary size of (b_n/M_n) as the size of the two-adic forcing discards
the dominant modular quotient.

Equation (18) is the sharp new endpoint.  A diagonal distribution theorem
would have to control a sum of seven residues of an exponentially growing
power modulo the changing quartic integers (d_{n,j}).  Neither the
isometry nor (5) estimates those least residues.

## 3. What fixed-level two-adic dynamics does and does not give

The frozen theorem says

\[
 v_2(Z(n)-Z(m))=v_2(n-m).                              \tag{22}
\]

Consequently (Z) permutes every fixed residue ring.  In particular, for
every (s\geq1) and (2^s\nmid h),

\[
 \sum_{n=0}^{2^s-1}
 \exp\left(2\pi i h{[Z(n)]_{2^s}\over2^s}\right)=0.   \tag{23}
\]

This is perfect complete-sum cancellation at a **fixed** level.  It is not
a discrepancy estimate for (X_n).  Membership of (X_n) in a leading
dyadic cell of width (2^{-u}) reads bits of (Z(n)) in positions
(27n-u,\ldots,27n-1), whereas (22) controls the low fixed positions.
The exact first counterexample is already

\[
 \left\lfloor4X_1\right\rfloor
 =\left\lfloor4X_2\right\rfloor=1.                   \tag{24}
\]

So the first two diagonal values lie in the same quarter even though
(Z(0),Z(1)) permute residues modulo two.

There is a second exact obstruction to invoking ergodicity of the selected
map.  Its reduction modulo four is

\[
                         (Z(0),Z(1),Z(2),Z(3))=(1,0,3,2). \tag{25}
\]

Thus it has two cycles modulo four, and the inverse image of
({0,1}\subset\mathbb Z/4\mathbb Z) is a nontrivial invariant set.
The map is Haar-measure preserving because it is an isometry, but it is not
ergodic on all of (\mathbb Z_2).  More importantly, the diagonal samples
the images (Z(n)), not an orbit (Z^{\circ n}(x)), and reads moving high
bits rather than a fixed two-adic cylinder.  P-adic pointwise or shrinking-
target theorems therefore do not address (2).

## 4. Van der Corput, Mahler, and automatic boundaries

Van der Corput differencing at a fixed modulus can use

\[
 Z(n+h)-Z(n)=h\,U_h(n),\qquad U_h(n)\in\mathbb Z_2^\times, \tag{26}
\]

which is another form of (22).  But the valuation of each difference only
says that its additive character has large order; it does not bound the
sum of those characters.  For the first (N) diagonal points, a common
denominator representation is

\[
 X_n={2^{27(N-n)}[Z(n)]_{2^{27n}}\over2^{27N}}.       \tag{27}
\]

The numerator in (27) is a depth-dependent truncation, not the value of one
fixed analytic phase modulo (2^{27N}).  In addition, the sample length is
(N\asymp\log(2^{27N})), far shorter than the power-scale ranges in which
available prime-power exponential-sum estimates provide cancellation.

The word *Mahler* creates another possible false shortcut.  A Mahler-basis
expansion of a continuous two-adic function is a binomial interpolation in
its **input**.  It does not turn the sequence of coefficients on the moving
bit diagonal (27n) into an automatic sequence.  Likewise (5) is an
additive difference equation, not an algebraic finite-field generating
series to which Christol-type automaticity criteria directly apply.
Equation (18) makes the obstruction concrete: its modulus changes with
(n), so no finite kernel or fixed-modulus transducer has been established.

No negative automaticity theorem is claimed.  The point is only that the
available hypotheses do not meet the premises of the standard theorems.

## 5. A limited exact digit-complexity consequence

From (9)--(10), (X_n) is in lowest terms with denominator
(2^{\kappa_n}).  Since

\[
 \kappa_n=27n-v_2(7n+1)\longrightarrow\infty,         \tag{28}
\]

the state sequence takes infinitely many distinct rational values.

It is also not eventually periodic.  Suppose a period (t\geq1) existed.
Equality (X_{n+t}=X_n) would force
(kappa_{n+t}=\kappa_n) for every sufficiently large (n).

- If (t) is even, take a large even (n).  Both valuations in (9) are
  zero, so (kappa_{n+t}-\kappa_n=27t\ne0).
- If (t) is odd, choose a large (n\equiv3-t\pmod4).  Then (n) is even,
  (v_2(7n+1)=0), and (n+t\equiv3\pmod4), so
  (v_2(7(n+t)+1)=1).  Hence
  (kappa_{n+t}-\kappa_n=27t-1\ne0).

This proves nonperiodicity, but not nonperiodicity of any chosen leading-bit
projection, positive entropy, discrepancy decay, or target hitting.

## 6. Exact replay and falsification data

The companion
[bbp_dyadic_diagonal_functional_recurrence_20260813_check.py](bbp_dyadic_diagonal_functional_recurrence_20260813_check.py),
SHA-256
`c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651`,
reconstructs the coefficient directly.  It checks fixed-level permutations,
direct evaluations of (F), (7), (11), all seven identities (14)--(21), and
the exact valuation.  It then computes bounded leading-cell and discrepancy
statistics.  Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py
```

Retained output:

```text
status: PASS
finite_claim_label: experiment
theorem_claim_label: proof sketch
maximum_fixed_precision: 10
maximum_direct_depth: 80
maximum_diagonal_depth: 2048
fixed_level_permutation_checks: 2046
direct_functional_identity_checks: 80
diagonal_recurrence_checks: 2047
seven_phase_lift_checks: 14329
phase_decomposition_checks: 164
phase_error_bound_checks: 164
exact_valuation_checks: 2048
quartic_denominator_bound_checks: 14329
selected_map_mod_four: [1, 0, 3, 2]
first_two_two_bit_cells: [1, 1]
prefix_coverage: {1: 2, 2: 4, 8: 256, 9: 505, 10: 880, 11: 1302}
prefix_missing_first[9]: [57, 85, 291, 301, 366]
longest_leading_bit_run: {bit: 1, length: 10, start_n: 611}
diagonal_star_discrepancy: 0.0234170538950785345099412101652
forcing_star_discrepancy: 0.0259477616552624931663733396411
minimum_distance_to_boundary: 0.000667981303506625065634214447458
twelfth_forcing_phase_above_0_98: true
twelfth_real_correction_below_1e_minus_90: true
asserts_diagonal_equidistribution: false
asserts_target_hitting: false
asserts_decimal_word_occurrence: false
asserts_v1: false
```

The bounded data look broadly mixing at coarse scales, but they also falsify
the natural exact-uniformity inference: at depth 2 both states occupy one
quarter, and after 2,048 samples only 505 of 512 nine-bit leading cells have
appeared.  These are `experiment` observations only.  They neither refute
eventual equidistribution nor support a proof of it.

## 7. Literature, mathlib, and coordination boundary

Status: bounded `literature-checked` search on **2026-08-13 UTC**.

| primary source | checked relevance and boundary |
|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | Supplies the exact four-pole series used in (4).  It gives hexadecimal digit extraction, not (moving) two-adic diagonal distribution. |
| Anashin, [*Ergodic Transformations of the Space of p-adic Integers*](https://doi.org/10.1063/1.2193107) | Characterizes ergodicity of compatible maps through single cycles at every fixed residue level.  Equation (25) fails that condition already modulo four; in any case our diagonal is not an iterated orbit. |
| Milićević, [*Sub-Weyl subconvexity for Dirichlet L-functions to prime power moduli*](https://doi.org/10.1112/S0010437X15007381), Sections 3--5 | Develops van der Corput/exponent-pair bounds for short sums with a fixed p-adically analytic phase modulo a prime power.  Equation (27) is a changing truncation and has only logarithmic sample length relative to its modulus. |

Searches covered `p-adic analytic exponential sums prime power short
interval`, `p-adic ergodic 1-Lipschitz growing cylinders`, `automatic
sequence diagonal p-adic analytic`, and `powers modulo varying polynomial
modulus`.  No primary theorem found in this bounded search proves
discrepancy or target hitting for the seven varying-modulus phases (18).

The mathlib search found
`Mathlib/NumberTheory/Padics/MahlerBasis.lean`, which formalizes Mahler's
binomial basis and the continuous-function expansion, but no p-adic
ergodic, shrinking-target, discrepancy, or prime-power exponential-sum
theorem that supplies the missing estimate.  No Lean declaration is added:
formalizing a finite replay would not promote the frozen analytic
`proof sketch`, and there is no V1-supporting target-hitting theorem to
register in the axiom audit.

This branch registered the descendant-area watch
`watch:local:pi-digits:dyadic-diagonal-attack-20260813` on
`local:pi-digits` for agent `codex-dyadic-diagonal-attack`.  Its latest poll
was empty at cursor and delivered sequence 57,121, so no event was
acknowledged.  Observation events were not used as mathematical evidence.

## Sharp handoff

The moving diagonal is no longer merely described as “fixed-level mixing at
the wrong quantifier.”  Equations (11) and (19) give its exact dynamics:

\[
 X_{n+1}=\left\{10X_n+
 \sum_{j=1}^7{h_{n,j}\over d_{n,j}}+\varepsilon_n\right\},
\]

where every (d_{n,j}=O(n^4)), every (h_{n,j}) is the explicit modular
power (18), and (\varepsilon_n) is exponentially negligible.

That is a real reduction, but not a return theorem.  The remaining sharp
problem is a discrepancy or target-hitting estimate for the simultaneous
varying-modulus phase vector

\[
 \left(
 {h_{n,1}\over d_{n,1}},\ldots,{h_{n,7}\over d_{n,7}}
 \right),
\]

strong enough to survive the expanding decimal recurrence.  Fixed-level
isometry, full-space p-adic ergodicity, generic Mahler/automatic machinery,
and currently located p-adic exponent-sum results do not provide it.  No
such estimate is proved here, so V1 remains a `conjecture`.
