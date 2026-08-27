# Independent audit of the sevenfold BBP high-dyadic separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Audited corrected artifacts:

- [bbp_high_dyadic_archimedean_separator_20260813.md](bbp_high_dyadic_archimedean_separator_20260813.md),
  SHA-256
  `d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`;
- [bbp_high_dyadic_archimedean_separator_20260813_check.py](bbp_high_dyadic_archimedean_separator_20260813_check.py),
  SHA-256
  `69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8`.

Independent replay:

- [bbp_high_dyadic_archimedean_separator_20260813_independent_check.py](bbp_high_dyadic_archimedean_separator_20260813_independent_check.py),
  SHA-256
  `b64e69dec2e19d969d61f41a1ae26873254028c70a8276820ab9c18d1d924f2b`.

## Verdict and correction history

**PASS after one substantive selector repair and three precision
clarifications.** The corrected report is a sound `proof sketch`; the two
finite replays are `experiment` evidence. It proves neither a colored return
for the actual BBP sequence nor canonical V1. V1 remains a `conjecture`.

The originally supplied report/checker pair was:

- report SHA-256
  `46439edaf800bec6fb36fe4a42631921d9db12142436da8bad200e68f477f865`;
- checker SHA-256
  `10b6da87791c9f24b3c860f6e1776981776c0e7a960a09e17d28d2286e299bc2`.

That version does **not** pass as written. Its nearest-grid choice preserved
the dyadic class but did not prove its assertion that the odd selected class
changed. The closest grid point can lie in the original class modulo
(L_{7n}); a finite sample cannot exclude that possibility at all depths.
The final frozen report repairs this by excluding exactly that shift class.
If exclusion forces an adjacent grid point, the error bound becomes
(3/(2L_{7n})), still exponentially smaller than the BBP tail.

The final report also correctly:

1. distinguishes the (kappa_n=27n-r_n) reduced output bits from the
   (27n) raw bits of (F(7n+1)) needed before division by (2^{r_n});
2. records the tail upper bound needed to conclude that the alternative
   centered state tends to zero from below, not merely that it has the same
   sign as the tail; and
3. guarantees that the product-formula integer is nonzero and uses the
   transcendence, rather than mere irrationality, of pi when explaining why
   the small Archimedean error is not an algebraic input to a product formula.

No further mathematical correction was needed.

## 1. Exact rational identity and two-adic isometry

Write

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}.
\]

The frozen all-depth audit supplies a restricted power series

\[
 F(X)=\sum_{j\geq0}16^j a(X-1-j)
\]

with (F(0)=0) and (F(X+1)=16F(X)+a(X)). Iterating at the positive
integers gives in (mathbb Q_2)

\[
 F(N+1)=\sum_{k=0}^N16^{N-k}a(k).
\]

The right side is rational. Injectivity of
(mathbb Q\hookrightarrowmathbb Q_2), followed by the definitions of
(A_N,L_N,B_N), proves the ordinary rational identity

\[
 \boxed{F(N+1)=A_N/L_N=16^NB_N.}
\]

Equivalently, the nominal infinite tail after reversing at (N+1) is
(16^{N+1}F(0)=0); there is no remaining approximation term.

The pairwise isometry used later also follows from the audited ingredients,
although the all-depth report states mainly its one-point specialization.
Coefficientwise (F(X)\equiv X\pmod2), so (F=X+2G) for a restricted
integral power series (G). For (x,y\in\mathbb Z_2), the difference
(G(x)-G(y)) is divisible by (x-y). Hence

\[
 \frac{F(x)-F(y)}{x-y}
 =1+2\frac{G(x)-G(y)}{x-y}
\]

is a two-adic unit when (x\ne y). Therefore

\[
 v_2(F(x)-F(y))=v_2(x-y),
 \qquad v_2(F(x))=v_2(x).
\]

This validates both the valuation and fixed-level permutation steps without
assuming distribution of a diagonal orbit.

## 2. Raw and reduced complete dyadic coordinates

At depth (7n), let

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 r_n=v_2(7n+1),\qquad \kappa_n=27n-r_n.
\]

The identity above and the isometry give
(v_2(V_n)=v_2(A_{7n})=r_n). Since (r_n<27n), cancellation leaves
exactly (2^{\kappa_n}) in the reduced dyadic denominator. In
(mathbb Q_2), the remaining numerator-times-odd-denominator-inverse is

\[
 \frac{V_n/2^{r_n}}{L_{7n}}
 =\frac{5^nF(7n+1)}{2^{r_n}}.
\]

Odd cancellation in an ordinary reduced fraction does not change this
two-adic unit. Thus

\[
 w_n=left[\frac{5^nF(7n+1)}{2^{r_n}}
       \right]_{2^{\kappa_n}}
\]

is exactly the complete reduced dyadic coordinate, not a prefix of it.
Computationally, however, division by (2^{r_n}) means that this value needs
(F(7n+1)\bmod2^{27n}), not merely
(F(7n+1)\bmod2^{\kappa_n}). The corrected report makes this raw/reduced
distinction explicit.

## 3. The exponent (28+r_n) and the diagonal quantifier

Seven iterations of the functional equation give

\[
 F(7n+8)=2^{28}F(7n+1)+G_n,
 \qquad
 G_n=\sum_{j=1}^7 16^{7-j}a(7n+j).
\]

Multiplying by (5^{n+1}) and substituting
(5^nF(7n+1)=2^{r_n}w_n) at the available precision yields

\[
 w_{n+1}=2^{-r_{n+1}}
 \left[
 5^{n+1}G_n+5\,2^{28+r_n}w_n
 \right]_{2^{27(n+1)}}.
\]

The bracket has exact two-adic order (r_{n+1}), because it represents
(5^{n+1}F(7n+8)). Replacing (w_n) by another lift changes the bracket by

\[
 5\,2^{28+r_n+\kappa_n}=5\,2^{27(n+1)+1},
\]

so no missing input bit affects the result. Division then produces the
canonical residue modulo (2^{\kappa_{n+1}}). This checks the exponent
(28+r_n), the bracket precision, and equality rather than a bare
congruence.

For each **fixed** (s), isometry makes (F) a permutation modulo (2^s),
and multiplication of the index by the odd unit (7) shows that
(n\mapsto F(7n+1)\bmod2^s) has one copy of every residue per block of
(2^s) indices. The selected diagonal instead asks for raw level (s=27n)
at index (n). A full fixed-level block there has length (2^{27n}).
The quantifiers are therefore

\[
 \forall s\ \text{(a full block of length (2^s))}
 \quad\text{versus}\quad
 s=27n\ \text{at one moving index (n)}.
\]

The first statement supplies no uniform moving-level estimate. The report
does not silently turn fixed-level bijectivity into diagonal distribution.

## 4. Actual odd denominator growth and the separator scale

Let (mathcal R_N) be the reduced odd denominator of (B_N). Reduction of
(A_N/(16^NL_N)) immediately gives (mathcal R_N\mid L_N). The frozen
actual-odd-quotient report, independently audited at SHA-256
`85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36`,
derives from its surviving prime bands and fixed-modulus PNT/AP that

\[
 \log\mathcal R_N=(6+o(1))N.
\]

Consequently

\[
 \log L_{7n}\geq(42+o(1))n.
\]

This lower bound uses the **actual reduced odd denominator**, not merely the
raw LCM support.

The coefficient satisfies, for (k\geq1),

\[
 \frac1{21k^2}<a(k)<\frac1{k^2}.
\]

For example, after clearing the positive denominator, the lower inequality
has numerator

\[
 2008k^4+2147k^3+275k^2-194k-15>0,
\]

and the upper inequality has numerator
(392k^4+873k^3+665k^2+194k+15>0).
Positivity of the BBP tail then gives, with
(lambda=5/2^{27}),

\[
 \frac{\lambda^n}{336(7n+1)^2}
 \leq |t_n|
 \leq \frac{\lambda^n}{15(7n+1)^2}
 \longrightarrow0.
\]

The first bound uses the first omitted term; the second sums the geometric
majorant. These constants and signs rederive independently.

## 5. Odd-class-avoiding nearest grid and every dyadic bit

Every integer in the preserved raw dyadic class has a unique representation

\[
 S=V_n+2^{27n}j,\qquad j\in\mathbb Z.
\]

Because (2^{27n}) is a unit modulo the odd number (L_{7n}), this point
also preserves the complete odd class exactly when
(j\equiv0\pmod{L_{7n}}). Start with a closest (j) to the real target
(D_nt_n). If it is in the forbidden class, either adjacent integer is
admissible because (L_{7n}>1); choosing the nearer adjacent integer gives

\[
 |S_n^*/D_n-t_n|\leq\frac3{2L_{7n}},
 \qquad
 S_n^*\not\equiv V_n\pmod{L_{7n}}.
\]

This argument handles half-mesh ties as well: an initially chosen forbidden
closest point has an admissible neighbor at distance at most three half
meshes. It is the necessary repair to the first frozen version.

The odd-denominator lower bound and the lower tail bound imply

\[
 \frac{|S_n^*/D_n-t_n|}{|t_n|}
 \leq \exp\!\left[-\bigl(42-\log(2^{27}/5)+o(1)\bigr)n\right]
 n^{O(1)}\longrightarrow0,
\]

where (42-\log(2^{27}/5)=24.895\ldots>0). Together with the tail upper
bound, this proves

\[
 -\tfrac12<e_n^*:=S_n^*/D_n<0
\]

eventually.

The congruence (S_n^*\equiv V_n\pmod{2^{27n}}), with
(v_2(V_n)=r_n<27n), forces

\[
 v_2(S_n^*)=v_2(D_n+S_n^*)=r_n.
\]

After dividing by (2^{r_n}), the unit residues agree modulo
(2^{\kappa_n}); multiplication by the common odd denominator inverse shows
that both raw and reduced complete dyadic coordinates agree. This is stronger
than retention of any fixed linear prefix.

## 6. Next-depth forcing class and all-nine zero carries

Let

\[
 K_n^*=S_{n+1}^*-10\Lambda_nS_n^*,\qquad
 \Lambda_n=2^{27}\frac{L_{7n+7}}{L_{7n}}.
\]

Subtracting the analogous identity for (V_n) proves

\[
 \frac{K_n^*-K_n}{D_{n+1}}=\eta_{n+1}-10\eta_n.
\]

Moreover, (S_{n+1}^*-V_{n+1}) is divisible by (2^{27(n+1)}), while

\[
 10\Lambda_n(S_n^*-V_n)
\]

is divisible by (2^{27(n+1)+1}). Hence

\[
 \boxed{K_n^*\equiv K_n\pmod{2^{27(n+1)}}.}
\]

The error bounds above make
(eta_{n+1}-10eta_n) exponentially smaller than the frozen positive lower
bound

\[
 K_n/D_{n+1}\geq
 \frac5{168(7n+1)^2}\lambda^n.
\]

Thus the alternative forcing is eventually positive and relatively
asymptotic to the actual forcing.

Now fix (P\geq1) and put (q_P=10^P-1). Since (e_n^*\to0) from below,
eventually
(-1/2<q_Pe_n^*<0). For
(r_n^*=D_n+S_n^*), the split color is therefore exactly

\[
 \left\lfloor q_P\frac{r_n^*}{D_n}+\frac12\right\rfloor=q_P,
\]

the all-nine endpoint. The underlying phase quotient is also exact:

\[
 10\Lambda_nr_n^*+K_n^*=9D_{n+1}+r_{n+1}^*.
\]

Consequently the colored carry is

\[
 q_P\cdot9+q_P-10q_P=0.
\]

This holds after a (P)-dependent onset, which is the correct quantifier.
It says nothing about the actual BBP carries because the construction has
explicitly changed the odd class.

## 7. Exact product-formula boundary

Put (Delta_n=S_n^*-V_n). The selector guarantees both

\[
 0\ne\Delta_n=2^{27n}j_n
 \quad\text{and}\quad
 j_n\not\equiv0\pmod{L_{7n}}.
\]

Thus

\[
 |\Delta_n|_\infty\geq2^{27n},\qquad
 |\Delta_n|_2\leq2^{-27n}.
\]

There is no two-adic product-formula contradiction: the same divisibility
that makes the two-adic factor small already forces the ordinary integer
height to be large. Any additional valuation of (j_n) and its incidental
odd prime factors balance exactly in

\[
 |\Delta_n|_\infty\prod_p|\Delta_n|_p=1.
\]

The genuinely small real error is

\[
 D_n\eta_n=S_n^*-D_nt_n.
\]

Because (t_n=-10^n(\pi-B_{7n})), this has a nonzero rational coefficient
of the transcendental number pi and is itself transcendental. It is not the
nonzero rational or algebraic form needed for a product formula. A
missing-word assumption locates decimal tails in a proper infinite survivor
set; it does not by itself convert this quantity into an algebraic form that
is simultaneously small at infinity and highly divisible at enough finite
places. The report's one-place no-go is therefore exact. It does not rule out
a future mixed odd--dyadic--Archimedean construction.

## 8. Independent replay

The independent checker imports no primary checker. It pins the target, all
four frozen parent reports, and the corrected primary report/checker. It
reconstructs the compact coefficient from the four original BBP poles and
then checks:

- (F(k+1)=A_k/L_k) in 673 exact rational rows;
- fixed-level permutation behavior through nine bits;
- 72 complete raw/reduced diagonal states and every (r_n);
- the (28+r_n) recurrence and its input-lift independence;
- divisibility of every sampled actual reduced odd denominator into (L_{7n});
- 2,100 adversarial selector conditions, including forbidden points and
  half-mesh boundaries;
- an independently selected full-dyadic separator at depths 36 through 70;
- the changed odd class, complete dyadic state, next forcing class, forcing
  coboundary, phase quotient nine, and all-nine zero carries; and
- the nonzero integer/height mechanism behind the product-formula no-go.

Replay from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_independent_check.py
```

The retained run was:

```text
status: PASS
finite_claim_label: experiment
audited_report_claim_label: proof sketch
rational_identity_rows: 673
fixed_level_permutation_checks: 1022
complete_diagonal_states: 72
raw_reduced_and_recurrence_checks: 284
actual_odd_denominator_divisibility_checks: 72
adversarial_selector_checks: 2100
separator_state_checks: 280
forcing_and_next_class_checks: 170
all_nine_and_zero_carry_checks: 416
product_formula_no_go_checks: 70
last_log_actual_odd_denominator_over_depth: 5.98550762709175
preserves_complete_raw_and_reduced_dyadic_coordinate: true
preserves_complete_next_dyadic_forcing_class: true
forces_changed_complete_odd_class: true
asserts_actual_bbp_carries_are_zero: false
asserts_v1: false
```

The last finite log ratio is only an `experiment`; the constant (6) comes
from the audited PNT/AP proof sketch, not numerical extrapolation.

## 9. Source and claim boundary

The corrected report accurately limits the BBP, Lagarias, and
Bailey--Crandall source scopes. The BBP source supplies the formula, while the
standard orbit-distribution consequences remain conditional; none supplies
the missing diagonal mixed correlation. This audit preserves the report's
dated bounded `literature-checked` label and makes no novelty claim.

The result is not `machine-checked`, a `candidate resolution`, or a
`verified resolution`. Its valid conclusion is narrower: complete dyadic
data, complete next-depth dyadic forcing data, and BBP-scale Archimedean
asymptotics do not force colored returns after the odd selected coordinate is
allowed to change. A theorem coupling the **actual** odd coordinate to the
dyadic diagonal and Archimedean window is still missing.

## 10. Coordination record

This audit registered the descendant-area watch
`watch:local:pi-digits:independent-high-dyadic-audit-20260813` on
`local:pi-digits` for agent `codex-independent-high-dyadic-audit`. Its initial
cursor was 56,970. The pre-verdict poll was empty at the same delivered
sequence, so there was no event to acknowledge. Observation events were used
only as coordination signals, never as mathematical evidence.
