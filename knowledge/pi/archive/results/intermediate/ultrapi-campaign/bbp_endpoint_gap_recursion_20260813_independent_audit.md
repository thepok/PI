# Independent audit: BBP endpoint-gap recursion

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

## Conclusion and claim boundary

The frozen report's algebraic no-go and all bounded calculations survive an
independent adversarial reconstruction.  No fatal defect was found.  In
particular:

1. The exponent-window identities (R6)--(R10) and every displayed offset
   through $e=14$ are exact.
2. The localization argument (R11)--(R17) is valid when (R17) is read, as in
   its frozen source, as a statement about the isolated three-primary
   projection.  It is not a small full-circle defect statement.
3. The directed-cover lemma (R18)--(R20) has the stated direction and constant
   $2\varepsilon$.
4. A disjoint exact computation checks all 41,924 pairs of complete-period
   subwindows.  It recovers the four stated thresholds with strict positive
   margins.
5. The adjacent identities and gap comparisons (R25)--(R28) follow with the
   displayed constants.
6. The rational construction (R29)--(R33) is a valid structural countermodel
   with exactly the narrow scope claimed in the report.  It is not a model of
   the BBP sums or of pi.

The algebraic identities and general elementary implications retain label
`proof sketch`; bounded reconstructions retain label `experiment`.  This
audit makes no new `machine-checked` or `literature-checked` claim and is not
a `candidate resolution` or a `verified resolution`.  The endpoint gap law
(R5) and canonical V1 remain `conjecture`s.

## 1. Frozen objects and independence

| object | SHA-256 |
|---|---|
| canonical local source | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| [three-primary decimation report](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [independent decimation audit](bbp_three_primary_decimation_20260813_independent_audit.md) | `5dc190f913c1eb727e4a1cbc9bef2d8f3373af00b17e1aa50244ae8efceb3371` |
| [full-phase experiment](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [full-phase checker](bbp_three_grid_full_phase_experiment_20260813_check.py) | `502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458` |
| [twisted-sum report](bbp_three_primary_twisted_sum_20260813.md) | `0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12` |
| [independent twisted-sum audit](bbp_three_primary_twisted_sum_20260813_independent_audit.md) | `44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81` |
| [audited endpoint-gap report](bbp_endpoint_gap_recursion_20260813.md) | `6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d` |
| [audited primary checker](bbp_endpoint_gap_recursion_20260813_check.py) | `0c8967858d1023e001cbc3fb011ae525cdd1800d3622e92d7d1fc0dd712cc780` |
| [independent checker](bbp_endpoint_gap_recursion_20260813_independent_check.py) | `d047954e714e5dd89967fbd1f9d6e9fabf128c0726404cb1206925186f0b12bc` |

All nine inputs pinned by the independent checker match.  The independent
checker imports no definition from the primary checker.  It instead forms
the four BBP pole sums directly, generates every rational phase by modular
exponentiation rather than the primary recurrence, and turns all subwindow
distances into integers over the single denominator
$9D_{e-2}D_e$.  This gives a derivation and quantifier traversal disjoint
from the primary Boolean cache.

## 2. Window arithmetic: (R6)--(R10)

The elementary identity

\[
 A_e=9A_{e-2}+1
\]

immediately yields

\[
 M_e^-=9M_{e-2}^-+13,\qquad
 M_e^+=9M_{e-2}^++5.
\]

Writing $\alpha M_{e-2}=U(M_{e-2})+r$, with $0\le r<1$, gives

\[
 U(M_e)=9U(M_{e-2})+\lfloor9r+\alpha s\rfloor.
\]

The exact integer inequalities

\[
 10^{15}<16^{13}<10^{16},\qquad
 10^6<16^5<10^7
\]

give $15\le c_e^-\le24$ and $6\le c_e^+\le15$, including both endpoint
possibilities correctly.  Subtracting lower bounds from upper bounds then
gives

\[
 L_e^\sigma-9L_{e-2}^\sigma=c_e^\sigma-s_\sigma-8.
\]

The independent exact-$10^U$ inequalities reproduce the twelve retained
$(c,\Delta L)$ pairs:

```text
e4:  pre (23, 2),  drop (6,-7)
e6:  pre (15,-6),  drop (7,-6)
e8:  pre (21, 0),  drop (13,0)
e10: pre (21, 0),  drop (14,1)
e12: pre (23, 2),  drop (6,-7)
e14: pre (17,-4),  drop (10,-3)
```

Thus the cardinality obstruction noted at $e=6$ is literal: a row with six
fewer exponents than nine copies of the old row cannot support an injective
nine-new-exponents-for-every-old-exponent assignment.

## 3. Three-localized defect: (R11)--(R17)

Let $b_e=B_{M_e}$, $D_e=9b_e-b_{e-2}$, and write

\[
 b_{e-2}=\frac{P}{3^EC},\qquad 3\nmid C.
\]

The frozen decimation supplies $D_e\in\mathbb Z_{(3)}$.  If
$n\equiv\rho\pmod {3^{E-2}}$, the exact order of ten modulo $3^E$ gives
$3^E\mid10^n-10^\rho$.  Therefore both summands in

\[
 9N_nb_e-N_\rho b_{e-2}
 =N_nD_e+(10^n-10^\rho)b_{e-2}
\]

have denominators prime to three.  This proves (R15).  Reducing the same
identity modulo one gives (R16); it supplies no Archimedean bound.

For (R17), the notation $x_{e,n}$ is imported from the frozen decimation
report.  If the new three-exponent is $E+2$, unit nesting reduces the new
unit to the old unit modulo $3^E$.  Multiplication of the new isolated
coordinate by nine lowers its denominator from $3^{E+1}$ to $3^{E-1}$,
and exponent congruence replaces $n$ by $\rho$.  Hence

\[
 9x_{e,n}=x_{e-2,\rho}\pmod1.
\]

The phrase “this defect is zero” is consequently correct only for this
three-primary projection.  The primary report immediately distinguishes it
from the full-circle defect in (R15)--(R16), so this is a notation
qualification, not a logical defect.

The independent exact fractions reproduce the maximum same-exponent
full-circle defects:

| transition | row | maximum defect |
|:---:|:---:|---:|
| $4\to6$ | pre-drop | 0.499253697955943... |
| $4\to6$ | first-drop | 0.498783217937848... |
| $6\to8$ | pre-drop | 0.499100471113819... |
| $6\to8$ | first-drop | 0.499988950495557... |

Each comparison with $49/100$ is exact.  This remains an `experiment` and
does not assert asymptotic persistence.

## 4. Directed covering lemma: (R18)--(R20)

The map $z\mapsto9z$ sends the complement of $R_9(S)$ onto the complement
of $S$, with every complementary arc split into nine arcs of one ninth the
length.  Hence

\[
 G(R_9(S))=G(S)/9.
\]

For (R20), let $I$ be a $Z$-free complementary arc of length $g$.  If
$g\le2\varepsilon$, the desired bound is immediate.  Otherwise remove an
$\varepsilon$-arc from each end.  A point of $R_9(S)$ in the remaining arc
would be at circle distance greater than $\varepsilon$ from every point of
$Z$, contradicting the directed-cover hypothesis.  The remaining arc has
length $g-2\varepsilon$, so

\[
 g-2\varepsilon\le G(R_9(S))=G(S)/9.
\]

Taking the largest $Z$-free arc proves (R20).  Only the direction “each
ideal child is near some point of $Z$” is needed; extra points of $Z$ can
only reduce its largest gap.

## 5. Exhaustive subwindow quantifiers

For a fixed pair of old and new subwindows define

\[
 W(J_{e-2},J_e)=
 \max_{m\in J_{e-2}}\max_{0\le j<9}
 \min_{\substack{n\in J_e\\n\equiv m\pmod T}}
 d_{\mathbb T}\!\left(\{N_nb_e\},\frac{y_m+j}{9}\right).
\]

There are exactly nine $n$'s in the inner minimum.  Statement (R22) for
every subwindow pair is precisely

\[
 \min_{J_{e-2},J_e}W(J_{e-2},J_e)>\theta_{e,\sigma}.
\]

The independent checker evaluates this min-max-min expression directly.
Every distance is represented by an integer over the common exact
denominator $9D_{e-2}D_e$.  The independently obtained minima are:

| transition | row | pairs | threshold | weakest pair witness | exact-fraction SHA-256 |
|:---:|:---:|---:|---:|---:|---|
| $4\to6$ | pre-drop | 39 | $3/20$ | 0.156181324759245... | `741ea04b7bd9081a8d2178f922f72bb548eec8a73cfa9f43b8e8d11181252189` |
| $4\to6$ | first-drop | 603 | $1/10$ | 0.110610687478028... | `ded06cd1c1ae9fa7c9cdd0896200477457a3a9afc5664609769aa8faffeac6e1` |
| $6\to8$ | pre-drop | 1,417 | $1/4$ | 0.268609097269055... | `41b5ca5d1eaeeb923a2bfa154141b25e117f23a23ab4386ca550a1c99322f8f7` |
| $6\to8$ | first-drop | 39,865 | $1/6$ | 0.176811796598342... | `ea9ab62cceed3787eecc3dc9a97c98151f6cd811a89b569dc9e39f57d2e112dc` |

All four inequalities are strict integer cross-multiplications, not decisions
made from the displayed decimals.  The checker constructs 38,772 distinct
distance entries and traverses all 41,924 subwindow pairs.

The primary scope is exact: this rules out the nine corresponding exponents
inside each primary fibre.  It does not rule out a nearby point belonging to
a different fibre.  No global Hausdorff matching, gap law, fixed return, or
V1 statement follows from this finite calculation.

The four exact largest-gap comparisons also reproduce

\[
 G_e>G_{e-2}/9,\qquad G_e<G_{e-2}/3.
\]

The first inequality falsifies (R0) in those four rows.  The second is only an
`experiment`, exactly as labeled in the primary report.

## 6. Adjacent rows: (R25)--(R28)

Subtracting the definitions of the two cross-epoch defects gives (R25)
without approximation.  For $M=M_e^-$, the adjacent difference is the
single positive BBP term

\[
 t_e=B_{M+1}-B_M=\frac{a(M+1)}{16^{M+1}}.
\]

On a common row exponent $n\le U(M)$, one has
$N_n<10^n\le16^M$, while $a(M+1)<1/(M+1)^2$.  Therefore

\[
 0<N_nt_e<\frac1{16(M+1)^2}<\frac1{15(M+1)^2}.
\]

Applying this once at each epoch and using the triangle inequality proves
(R26).  The independent reconstruction checks the single-term identities and
these strict bounds at $e=4,6,8$.

The exponent intervals have one minus-only lower exponent and either one or
two plus-only upper exponents.  Removing $r$ points merges at most $r+1$
old gaps.  A pointwise circle displacement of at most $\delta$ changes the
largest gap by at most $2\delta$.  Applying these facts to the common labeled
points gives exactly

\[
 G_e^+\le2G_e^-+2\delta_e,\qquad
 G_e^-\le3G_e^++2\delta_e.
\]

This comparison is same-epoch only and cannot be iterated as an
$e-2\to e$ contraction.

## 7. Structural countermodel: (R29)--(R33)

Because $C_e\equiv C_{e-2}\pmod {3^{e-2}}$ and $3\nmid C_2$, every $C_e$
is a three-adic unit.  Direct subtraction gives both localized identities in
(R31).  Inversion preserves the same congruence, so the normalized endpoint
units nest to the required old moduli.

The complete-grid assertion also holds at every depth, not only in the finite
replay.  If two primary points in one period agreed modulo $3^{E-1}$, then
after undoing the unit and multiplying by three one would have
$10^n\equiv10^m\pmod {3^E}$.  The exact order
$\operatorname{ord}_{3^E}(10)=3^{E-2}$ forces $n\equiv m$ within that
period.  Thus all $3^{E-2}$ points are distinct.

For any prescribed $\varepsilon>0$, the congruence class in (R29) contains
arbitrarily large positive $C_e$.  It can therefore be chosen so that

\[
 \frac{10^{U(M_e^+)}-16}{3^{e-1}C_e}<\varepsilon.
\]

This upper-bounds both selected rows.  All their unreduced phases lie in
$(0,\varepsilon)$, so their wraparound gap is greater than
$1-\varepsilon$.  Choosing $C_e$ still larger can simultaneously enforce
any prescribed adjacent-row displacement bound.

The independent finite construction does this through $e=8$ with
$\varepsilon=1/100$ and additionally enforces the concrete bound

\[
 (10^{U(M_e^+)}-16)(\widetilde b_e^+-\widetilde b_e^-)
 <\frac1{15(M_e^-+1)^2}.
\]

It checks 1,092 primary points; the smallest constructed gap is greater than
0.99996, hence certainly greater than $99/100$.

The scope limitation is essential and correctly stated in the primary
report.  The construction does not preserve the four individual T74 pole
identities, the actual reduced BBP numerator, the identity of the adjacent
difference with the actual next BBP term, or a real shadow converging to pi.
It is therefore not a counterexample to (R5) or V1.  It proves only that the
listed three-localized nesting and closeness data, by themselves, cannot
force an Archimedean gap contraction.

## 8. Reproduction and integrity

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py \
  work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_independent_check.py
```

The primary stdout, including its final newline, has independently reproduced
SHA-256
`3490c218eeef3e1d572b5ce198298f214bde4f69592c411db948bd78b8c97f8a`,
matching the frozen report.  The independent stdout has SHA-256
`4aca87279281396a63a69297d198d63a34ac304567f6f53c9bc34639d455863d`.

The independent run also checks all nine input hashes, all eight relative
Markdown links in the primary report, and the absence of forbidden C0 control
bytes.  Both checkers end in `status=PASS`.  Neither checker asserts the
endpoint gap law, a fixed return, or V1.  No formal file, verification gate,
primary artifact, or `ultrapi.md` was changed by this audit.

## Sharp handoff

The report has correctly isolated the present obstruction.  The endpoint
decimation gives exact control after projection to the three-primary factor,
but the complementary phase can remain order one.  Sliding complete-period
subwindows and pairing adjacent pre/drop rows does not remove it, and the
structural countermodel shows that no rearrangement using only those inputs
can prove gap decay.

Meaningful further progress must therefore estimate the actual synchronized
BBP complement—for example its selected Fourier coefficient—or establish a
direct discrepancy bound for the full endpoint rows.  Without such genuinely
pi/BBP-specific Archimedean information, (R5) and canonical V1 remain
`conjecture`s.
