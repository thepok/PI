# Independent audit: BBP selected-numerator prefix separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen artifact audited:

- [bbp_selected_numerator_prefix_separator_20260813.md](bbp_selected_numerator_prefix_separator_20260813.md),
  SHA-256
  `5edd6bdacb3d0d9a6b12b4265da777891bdc22d2b95a1c75bc102e475280d0f6`;
- primary checker
  [bbp_selected_numerator_prefix_separator_20260813_check.py](bbp_selected_numerator_prefix_separator_20260813_check.py),
  SHA-256
  `017c7d17b68700bea23f89f859df16390de4e1f65f6cb1a6298eb27d04b6171d`.

## Verdict and claim boundary

**PASS.**  Conditional only on the frozen BBP recurrence and exact two-adic
valuation stated as dependencies in the primary report, the separator's
all-index construction is correct.  Its appropriate status remains
`proof sketch`.  Both the primary replay and a disjoint replay passed with
label `experiment`.

Canonical V1 remains a `conjecture`.  The separator neither proves nor
disproves a digit-return statement for pi.  It proves the narrower logical
point claimed in the primary report: the listed proper subset of the exact
selected-numerator data is compatible with an alternative rational phase
having one eventual boundary color and zero centered carries.

Two presentation details need to be made explicit when the separator is
used later, but neither is a mathematical gap:

1. the closest progression member is unique because the target is
   irrational, not merely because a nearest point exists; and
2. the all-nine zero-carry conclusion uses the exact alternative phase
   quotient (b_n^*=9).  Multiplying the centered recurrence alone can hide
   this quotient.

The phrase "exact threshold" at the end of Section 5 is valid as the
threshold delivered by the displayed worst-case nearest-grid estimate.  It
must not be read as a proof that preservation slopes at or above
(log_2 5) are impossible by a more structured selection.

## 1. Independent reconstruction of the selected representative

Put

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 M_n=2^{2n+4}L_{7n}.
\]

Every denominator entering (L_{7n}) is odd.  For (n\geq1),
(2n+4\leq27n), so (M_n\mid D_n).  The integers in the required class form
the nonempty discrete progression

\[
                 V_n+M_n\mathbb Z.
\]

It therefore has at least one member closest to (D_nt_n).  There cannot be
two: a tie would put (D_nt_n) at
(V_n+(j+\tfrac12)M_n), a rational number.  But

\[
 D_nt_n=-D_n10^n(\pi-B_{7n})
\]

is irrational because (B_{7n}) is rational and pi is irrational.  Thus the
rounded integer (S_n^*) exists and is unique.  Its grid error obeys

\[
 \left|{S_n^*\over D_n}-t_n\right|
 \leq {M_n\over2D_n}=2^{3-25n}.
\]

The first omitted BBP summand gives exactly the primary lower bound

\[
 |t_n|>{(5/2^{27})^n\over336(7n+1)^2}.
\]

Indeed the four denominator factors are at most
(3k,7k,9k,13k), while the numerator is at least (120k^2), so
(a(k)>1/(21k^2)).  Dividing the grid bound by this lower bound gives

\[
 { |S_n^*/D_n-t_n|\over|t_n|}
 \leq2688(7n+1)^2(4/5)^n=o(1).
\]

Also (t_n<0) and (t_n\to0); the latter follows directly from the
geometric BBP tail (for example (a(k)<1) for (k\geq1)).  Hence
(-1/2<S_n^*/D_n<0) eventually.  Therefore

\[
                 r_n^*=D_n+S_n^*
\]

is eventually the unique positive representative used by the construction,
with (0<r_n^*<D_n) and phase
(r_n^*/D_n=1+S_n^*/D_n).

## 2. Residues, valuations, reduced denominators, and determinants

Because both (D_n) and (M_n) are multiples of (L_{7n}) and
(2^{2n+4}), respectively,

\[
 r_n^*\equiv S_n^*\equiv V_n\pmod {M_n}.
\]

This proves both congruences claimed in (21), including every prime-power
component of the complete odd (L_{7n}).

The frozen valuation identity is
(v_2(V_n)=v_2(7n+1)).  Since
(7n+1<2^{2n+4}) for (n\geq1), this valuation is below the preserved
dyadic prefix.  The elementary rule

\[
 x\equiv y\pmod {2^a},\quad v_2(y)<a
 \quad\Longrightarrow\quad v_2(x)=v_2(y)
\]

therefore gives (v_2(r_n^*)=v_2(V_n)).  At every odd prime (p), congruence
modulo the full (p)-power in (L_{7n}) gives

\[
 \min(v_p(r_n^*),v_p(D_n))
 =\min(v_p(V_n),v_p(D_n)).
\]

Combining the dyadic and odd components proves

\[
                  \gcd(r_n^*,D_n)=\gcd(V_n,D_n).
\]

For every integer (q\geq1), adding (v_p(q)) before truncation at
(v_p(D_n)) preserves the equality.  Consequently

\[
 \gcd(qr_n^*,D_n)=\gcd(qV_n,D_n),
\]

so the reduced denominators agree for every repunit multiplier, not just
for the finitely checked periods.  Finally the Euclidean gcd identity
(gcd(x-zD,D)=gcd(x,D)) proves, for every (z\in\mathbb Z),

\[
 \gcd(qr_n^*-zD_n,D_n)=\gcd(qV_n,D_n).
\]

The CRT-character assertion follows even more directly: if
(m\mid M_n), then (hr_n^*\equiv hV_n\pmod m) for every integer (h).

## 3. Cross-depth forcing and its size

Let (E_n=S_n^*-V_n).  Then
(2^{2n+4}L_{7n}\mid E_n), and

\[
 K_n^*-K_n=E_{n+1}-10\Lambda_nE_n,
 \qquad \Lambda_n=2^{27}{L_{7n+7}\over L_{7n}}.
\]

The first term is divisible by
(2^{2n+6}L_{7n+7}).  The second is divisible by
(2^{2n+32}L_{7n+7}): multiplication by (10\Lambda_n) contributes
28 dyadic powers and promotes (L_{7n}) to (L_{7n+7}).  Hence

\[
 K_n^*\equiv K_n\pmod {2^{2n+6}L_{7n+7}},
\]

exactly as claimed.

Writing (eta_n=S_n^*/D_n-t_n), direct substitution gives

\[
 {K_n^*\over D_{n+1}}-\delta_n=\eta_{n+1}-10\eta_n.
\]

The two grid bounds yield

\[
 |\eta_{n+1}-10\eta_n|
 \leq(2^{-22}+80)2^{-25n}<81\,2^{-25n}.
\]

The first one of the next seven positive BBP terms gives

\[
 \delta_n>{5\over168(7n+1)^2}(5/2^{27})^n.
\]

Their quotient is (O(n^2(4/5)^n)).  It tends to zero, so the alternative
forcing is positive eventually and has the asserted relative asymptotic.

## 4. Eventual all-nine color and zero carry

Fix (P\geq1) and set (q=10^P-1).  Since
(e_n^*=S_n^*/D_n\to0) from below, eventually

\[
                 -\tfrac12<qe_n^*<0.
\]

Thus the split color of (r_n^*/D_n=1+e_n^*) is exactly

\[
 c_{n,P}^*=\left\lfloor q{r_n^*\over D_n}+\tfrac12\right\rfloor=q.
\]

For clarity, the missing integer quotient is forced exactly, not just
asymptotically.  From the definition of (K_n^*),

\[
\begin{aligned}
 10\Lambda_nr_n^*+K_n^*
 &=10\Lambda_n(D_n+S_n^*)+S_{n+1}^*-10\Lambda_nS_n^*\\
 &=9D_{n+1}+r_{n+1}^*.
\end{aligned}
\]

Since (0<r_{n+1}^*<D_{n+1}), the alternative phase quotient is
(b_n^*=9).  The exact colored carry factorization is therefore

\[
 \gamma_{n,P}^*=qb_n^*+c_{n+1,P}^*-10c_{n,P}^*
 =9q+q-10q=0
\]

at every sufficiently large transition.  This validates both the boundary
color and the zero-carry conclusion for each fixed (P).

## 5. General prefix slope

Let (kappa_n=\lfloor cn\rfloor) with
(0<c<\log_2 5).  Eventually
(kappa_n>v_2(7n+1)), because the latter is (O(\log n)), and
(kappa_n<27n), so the valuation and divisibility arguments still apply.
The nearest-grid estimate becomes

\[
 |\eta_n|\leq2^{-(27-c)n+O(1)},\qquad
 { |\eta_n|\over|t_n|}
 \leq n^{O(1)}(2^c/5)^n=o(1).
\]

Moreover
(kappa_{n+1}-kappa_n\leq3<28).  Thus multiplication by
(10\Lambda_n) supplies all dyadic powers needed at the next depth, and the
forcing congruence holds modulo
(2^{\kappa_{n+1}}L_{7n+7}).  This proves the claimed open range
(c<\log_2 5).  The argument deliberately makes no assertion at equality
or above it.

## 6. Disjoint deterministic replay

The independent checker is
[bbp_selected_numerator_prefix_separator_20260813_independent_check.py](bbp_selected_numerator_prefix_separator_20260813_independent_check.py),
SHA-256
`b40896575c796525b1c3581c00feb1d17bc3c54ec4193f486edf43afce0dd240`.
It imports no code from the primary checker.  Instead it sums the BBP
partials directly as exact `Fraction` values, recovers each raw endpoint
integer from the fraction, and audits depths 110 through 145 against one
common rational tail endpoint at depth 170.

It checks five periods, seven additional multipliers, seven signed
determinants, the exact quotient (b_n^*=9), all forcing identities, and
five rational prefix slopes through (23/10).  The last inequality
(23/10<\log_2 5) is certified without floating point by
(2^{23}<5^{10}).

Commands:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_independent_check.py
```

Retained output:

```text
status: PASS
bounded_replay_label: experiment
audited_construction_label: proof sketch
depth_range: [110, 145]
rational_tail_cutoff: 170
periods_checked: [1, 2, 3, 5, 6]
endpoint_checks: 108
congruence_and_cell_checks: 216
determinant_gcd_checks: 3456
transition_checks: 315
split_color_carry_checks: 535
general_slope_checks: 700
maximum_relative_state_error: 0.004294325776976832
maximum_relative_forcing_error: 0.004294325786681506
asserts_actual_pi_carry_return: false
asserts_v1: false
```

The finite replay is only an `experiment`.  The PASS verdict for the
all-index separator comes from the derivations above, with the frozen BBP
recurrence and valuation identity explicitly retained as dependencies.
