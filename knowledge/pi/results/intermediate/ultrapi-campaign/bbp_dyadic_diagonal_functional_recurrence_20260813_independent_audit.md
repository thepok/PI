# Independent audit: BBP dyadic diagonal functional recurrence

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's local, human-authored question and has no external
source URL; none is invented here.

Audited artifacts:

- [bbp_dyadic_diagonal_functional_recurrence_20260813.md](bbp_dyadic_diagonal_functional_recurrence_20260813.md),
  SHA-256
  `8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba`;
- [bbp_dyadic_diagonal_functional_recurrence_20260813_check.py](bbp_dyadic_diagonal_functional_recurrence_20260813_check.py),
  SHA-256
  `c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651`;
- [bbp_all_stratum_dyadic_mixing_20260813.md](bbp_all_stratum_dyadic_mixing_20260813.md),
  SHA-256
  `5089d63f83de1978731c50964c7fce45e7a4cc88e989a29acd99e08b8a9c8360`;
- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  `d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`.

Independent checker:
[bbp_dyadic_diagonal_functional_recurrence_20260813_independent_check.py](bbp_dyadic_diagonal_functional_recurrence_20260813_independent_check.py),
SHA-256
`d97c1026884fb9f2a4110a5e1045b578114b3929cda5713373faa4c88f83eb1c`.
It imports no code from the primary checker.

## Verdict and claim boundary

**Independent audit verdict: PASS**, with the nonfatal domain qualification
recorded below: the elementary proof of $p_{n,j}<M_n$ starts at $n=1$.
This does not change the mathematical result at its stated $n\geq1$ domain.

The following claims survive independent derivation, conditional only on the
frozen two-adic identity for $F$, and therefore retain status `proof sketch`:

1. the complete normalized dyadic state obeys
   
   \[
        X_{n+1}=\{10X_n+\Gamma_n\};
   \]
2. for $n\geq1$, the forcing has the exact seven-phase decomposition
   
   \[
       \Gamma_n=
       \left\{\sum_{j=1}^7\frac{h_{n,j}}{d_{n,j}}+
       \frac{b_n}{2^{27(n+1)}}\right\},
   \]
   with $0\leq h_{n,j}<d_{n,j}=O(n^4)$, the stated modular-power
   formula for $h_{n,j}$, and the stated exponentially small real
   correction;
3. the compatible selected map is measure-preserving but not ergodic on
   $\mathbb Z_2$, since its reduction modulo four has two cycles;
4. the rational state sequence is infinite and not eventually periodic.

The exact replay is an `experiment`.  The bounded source audit below is
`literature-checked`.  No target-hitting or discrepancy theorem is obtained.
In particular, this audit does **not** prove that a prescribed decimal word
occurs in pi and does **not** prove canonical V1.  V1 remains a `conjecture`.

## 1. Independent algebraic derivation

### 1.1 BBP coefficient and seven-step indices

Starting from the four poles in BBP Theorem 1,

\[
 a(k)=\frac4{8k+1}-\frac2{8k+4}-\frac1{8k+5}-\frac1{8k+6},
\]

ordinary common-denominator expansion gives

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}.
\]

The denominator is odd for every integral $k$.  Reindexing the defining
series directly gives

\[
 F(X+1)=16F(X)+a(X).
\]

Starting at $X=7n+1$, seven applications introduce exactly the indices
$7n+1,\ldots,7n+7$, with weights $16^6,\ldots,16^0$:

\[
 F(7n+8)=16^7F(7n+1)+
 \sum_{j=1}^7 16^{7-j}a(7n+j).
\]

Thus, with $Z_n=5^nF(7n+1)$,

\[
 Z_{n+1}=5\,16^7Z_n+5^{n+1}G_n
        =5\,2^{28}Z_n+b_n.
\]

This independently confirms the index range, the positive signs, the power
$2^{28}$, and the exponent $5^{n+1}$.  Exact rational arithmetic checked
this identity for $0\leq n\leq32$; this check does not substitute for the
displayed algebra.

### 1.2 Why the normalized multiplier is exactly ten

Let $K_n=27n$, $M_n=2^{K_n}$, and

\[
 x_n=[Z_n]_{M_n},\qquad X_n=\frac{x_n}{M_n}.
\]

Replacing $Z_n$ by $x_n+qM_n$ changes the homogeneous term by

\[
 5\,2^{28}qM_n,
\]

which is divisible by $2^{K_n+27}=M_{n+1}$.  Therefore no discarded bit
can affect the next residue.  After division by the new modulus,

\[
 \frac{5\,2^{28}x_n}{2^{K_n+27}}=10X_n.
\]

This proves the exact circle recurrence, rather than an approximate or
heuristic decimal analogy.  The independent checker compared both the raw
and normalized identities against direct two-adic series evaluations for
$0\leq n\leq128$.

### 1.3 Complete reduced coordinate

The frozen valuation identity is

\[
 v_2(Z_n)=r_n:=v_2(7n+1).
\]

For $n\geq1$, $r_n<27n$.  Hence the canonical residue $x_n$ has exact
valuation $r_n$, and

\[
 x_n=2^{r_n}w_n,qquad
 X_n=\frac{w_n}{2^{27n-r_n}},qquad w_n\text{ odd}.
\]

Thus the recurrence acts on the complete selected dyadic coordinate; it is
not a fixed-prefix truncation.

## 2. Independent phase-lift derivation

For $k=7n+j$, put

\[
 \begin{aligned}
 d_{n,j}&=(2k+1)(4k+3)(8k+1)(8k+5),\\
 p_{n,j}&=5^{n+1}16^{7-j}(120k^2+151k+47),\\
 M_n&=2^{27(n+1)}.
 \end{aligned}
\]

Let $\rho_{n,j}$ be the canonical residue of
$p_{n,j}d_{n,j}^{-1}$ modulo $M_n$, and define

\[
 h_{n,j}=\frac{d_{n,j}\rho_{n,j}-p_{n,j}}{M_n}.
\]

The numerator is an integer multiple of $M_n$.  For $n\geq1$, the
report's bound $0<p_{n,j}<M_n$, together with
$0\leq\rho_{n,j}<M_n$, forces

\[
 0\leq h_{n,j}<d_{n,j}.
\]

Reducing its defining equality modulo $d_{n,j}$ gives

\[
 h_{n,j}\equiv-p_{n,j}M_n^{-1}\pmod {d_{n,j}},
\]

and substituting the definitions gives exactly

\[
 h_{n,j}\equiv-
 (120k^2+151k+47)2^{4(7-j)}
 (5\,2^{-27})^{n+1}\pmod {d_{n,j}}.
\]

There is no sign or exponent reversal here.  Finally,

\[
 \frac{\rho_{n,j}}{M_n}
 =\frac{h_{n,j}}{d_{n,j}}+
  \frac{p_{n,j}}{d_{n,j}M_n}.
\]

Summation and reduction modulo one prove the exact seven-phase formula.
The modular term is not bounded by the ordinary size of $b_n/M_n$.

### 2.1 Bounds

For $1\leq j\leq7$, $k\leq7(n+1)$.  Consequently

\[
 120k^2+151k+47
 \leq(5880+1057+47)(n+1)^2<2^{13}(n+1)^2.
\]

Together with $5^{n+1}<2^{3(n+1)}$ and
$16^{7-j}\leq2^{24}$, this even gives the stronger bound

\[
 p_{n,j}<2^{3(n+1)+37}(n+1)^2,
\]

so the report's exponent $38$ is safe.  At $n=1$ its right side is
below $2^{54}=M_1$, and the ratio improves by at least
$2^{24}/(3/2)^2$ at every subsequent step.

The four factors of $d_{n,j}$ are bounded respectively by
$15(n+1),31(n+1),57(n+1),61(n+1)$, proving the quartic bound.
For $k\geq1$,

\[
 0<a(k)<\frac1{k^2},
\]

because its numerator is at most $318k^2$ and its denominator exceeds
$512k^4$.  The geometric sum of the seven weights then proves

\[
 0<\frac{b_n}{M_n}\leq
 \frac{16^7-1}{15(7n+1)^2}
 \left(\frac5{2^{27}}\right)^{n+1}.
\]

## 3. Fixed-level dynamics and the mod-four obstruction

The frozen isometry

\[
 v_2(Z(n)-Z(m))=v_2(n-m)
\]

makes $n\mapsto Z(n)$ a compatible permutation at every fixed binary
precision.  Passing through the inverse system therefore defines a
measure-preserving compatible map $T:\mathbb Z_2\to\mathbb Z_2$.
Independent reconstruction gives

\[
 (T(0),T(1),T(2),T(3))\bmod4=(1,0,3,2).
\]

Thus the reduction of $T$ modulo four has the two cycles
$(0\ 1)$ and $(2\ 3)$.  The clopen
set

\[
 S=\{x\in\mathbb Z_2:x\bmod4\in\{0,1\}\}
\]

has Haar measure $1/2$ and satisfies $T^{-1}(S)=S$.  This directly
proves nonergodicity; it also agrees with Anashin's single-cycle criterion.
The diagonal sequence is $T(n)$, not an iterated orbit $T^{\circ n}(x)$,
so even an ergodicity theorem for an unrelated map would not establish the
moving-high-bit statement.

Fixed-level permutation also gives the complete additive-character
cancellation stated in the report.  It does not control the bits in positions
$27n-u,\ldots,27n-1$.  The exact first counterexample is confirmed:

\[
 \lfloor4X_1\rfloor=\lfloor4X_2\rfloor=1.
\]

## 4. Infinite range and nonperiodicity

Since $w_n$ is odd, $X_n$ is in lowest terms with denominator
$2^{\kappa_n}$, where

\[
 \kappa_n=27n-v_2(7n+1)\longrightarrow\infty.
\]

This proves infinite range.  If an eventual period $t\geq1$ existed,
equal rational values would have equal reduced denominators.

- For even $t$, take a sufficiently large even $n$.  Both valuations
  are zero, so $\kappa_{n+t}-\kappa_n=27t$.
- For odd $t$, take a sufficiently large
  $n\equiv3-t\pmod4$.  Then $n$ is even and
  $v_2(7n+1)=0$, while $n+t\equiv3\pmod4$ and
  $v_2(7(n+t)+1)=1$.  Hence
  $\kappa_{n+t}-\kappa_n=27t-1$.

Both differences are nonzero, so the nonperiodicity proof is correct.  It
does not imply density, positive entropy, or a hit of any prescribed cell.

## 5. Edge and artifact findings

### 5.1 The $n=0$ edge

The proof of $p_{n,j}<M_n$ is explicitly stated only for $n\geq1$, and
that restriction is necessary: three of the seven numerators at $n=0$
are at least $2^{27}$.  The exact recurrence itself remains valid at
$n=0$.  Direct exact computation also finds all seven $n=0$ heights
canonical despite the failure of this sufficient bound.  No result used for
the moving states $n\geq1$ is affected.  The report preserves the
$n\geq1$ qualifier when it states the canonical-height proof.

### 5.2 Resolved presentation finding

The first audited draft contained three vertical-tab bytes and three missing
TeX backslashes.  The primary author corrected only those presentation
defects.  The final primary artifact pinned at the top of this audit has no
unexpected control byte and no remaining malformed `left` or `mathbb` token.
The independent checker was repinned and rerun against that final hash.

### 5.3 Branch scope

A discrepancy theorem for the seven phases would address the dyadic
moving-diagonal subproblem.  It would not by itself couple the odd
coordinates and the Archimedean carry/color data needed for V1; the frozen
high-dyadic separator already makes that limitation explicit.  The primary
report respects this boundary elsewhere and makes no V1 claim.

## 6. Independent exact replay

The independent checker reconstructs the coefficient from the four original
poles, checks the functional equation on positive and negative inputs,
exhausts selected permutations through 11 bits, verifies the rational and
normalized recurrences, and extends the seven-phase/valuation replay to
depth 3,072.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_independent_check.py
```

Retained output:

```text
status: PASS
finite_claim_label: experiment
audited_theorem_claim_label: proof sketch
coefficient_reconstruction_checks: 513
functional_equation_checks: 640
maximum_fixed_precision: 11
fixed_level_permutation_checks: 4094
isometry_spot_checks: 112
selected_map_mod_four: [1, 0, 3, 2]
mod_four_invariant_subset: [0, 1]
rational_seven_step_recurrence_checks: 33
direct_diagonal_recurrence_checks: 129
normalized_multiplier_ten_checks: 129
maximum_phase_depth: 3072
seven_phase_lift_checks: 21497
varying_modulus_power_checks: 21497
numerator_bound_checks: 21497
quartic_denominator_bound_checks: 21497
circle_decomposition_checks: 104
phase_error_bound_checks: 104
complete_coordinate_valuation_checks: 3072
n_zero_numerator_bound_failures: 3
n_zero_noncanonical_heights: 0
first_two_two_bit_cells: [1, 1]
twelfth_forcing_phase_above_0_98: true
twelfth_real_correction_below_1e_minus_90: true
asserts_diagonal_equidistribution: false
asserts_target_hitting: false
asserts_decimal_word_occurrence: false
asserts_v1: false
```

The primary checker was also compiled and rerun independently; it returned
`status: PASS` with the retained counts printed in the primary report.

## 7. Sources, mathlib, and claim vocabulary

Status: bounded `literature-checked` verification on **2026-08-13 UTC**.

- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9),
  Theorem 1, does state exactly the four-pole base-16 series used here.  It
  supplies digit extraction, not distribution of this moving dyadic
  diagonal.
- Anashin,
  [*Ergodic Transformations of the Space of p-adic Integers*](https://arxiv.org/abs/math/0602083),
  states for compatible maps the single-cycle-at-every-level criterion used
  to characterize ergodicity.  The exact mod-four computation above fails
  that premise.
- Milićević,
  [*Sub-Weyl subconvexity for Dirichlet L-functions to prime power moduli*](https://arxiv.org/abs/1407.4100),
  develops short exponential-sum estimates for fixed prime-power moduli and
  p-adically analytic phases.  The current diagonal instead has a changing
  truncation and only logarithmic length relative to its common modulus;
  the cited paper does not supply the required estimate.
- The local mathlib tree contains
  `Mathlib/NumberTheory/Padics/MahlerBasis.lean` and generic ergodic-theory
  modules, but the bounded search found no theorem proving the required
  p-adic moving-cylinder discrepancy or target hitting.  Mahler expansion
  concerns the input variable and does not make the moving bit diagonal an
  automatic sequence.

The primary report's claim labels are correctly separated: all-index
mathematics remains `proof sketch` because it inherits the frozen analytic
identity; bounded computation is `experiment`; the dated source boundary is
`literature-checked`; and V1 is only a `conjecture`.  Nothing audited here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## Final audit conclusion

The exact recurrence, all indices and signs, the seven modular residues,
their quartic denominators, the exponentially small real correction, the
complete-coordinate valuation, and the mod-four nonergodicity obstruction
all pass independent derivation and replay.  What remains is a genuinely new
uniform distribution/target-hitting estimate at changing moduli, followed by
the still-missing coupling to the odd and Archimedean color coordinates.
No such estimate is proved in the audited branch.  **No V1 proof is present.**
