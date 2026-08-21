# Sevenfold BBP high-dyadic coordinate and the one-place product-formula barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9`;
- [bbp_centered_carry_recurrence_20260813.md](bbp_centered_carry_recurrence_20260813.md),
  SHA-256
  `3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6`;
- [bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
  SHA-256
  `d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`;
- [bbp_short_orbit_return_attack.md](bbp_short_orbit_return_attack.md),
  SHA-256
  `eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d`.

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  This report does not prove that every
finite decimal word occurs in pi.

The positive result, with status `proof sketch`, is an exact description of
the **entire** high-dyadic coordinate which the prefix separator left open.
If

\[
 F(X)=\sum_{j\geq0}16^j a(X-1-j)
\]

is the audited two-adic null function, then its value at every positive
integer is not merely congruent to the BBP numerator: it is the rational
identity

\[
                   \boxed{F(N+1)={A_N\over L_N}=16^NB_N.}       \tag{1}
\]

At sevenfold depth this gives the complete reduced dyadic numerator
coordinate of

\[
             {V_n\over D_n}={5^nA_{7n}\over2^{27n}L_{7n}}.
\]

It also gives an exact seven-step recurrence for that coordinate, including
the carries created when the diagonal precision grows from roughly \(27n\)
to \(27(n+1)\).

This stronger coordinate still does not yield a colored return.  Two sharp
obstructions are proved.

1. The isometry of \(F\) implies perfect permutation behavior at each
   **fixed** binary precision, but the selected coordinate lives at precision
   \(27n-v_2(7n+1)\).  A complete period at that precision has exponential
   length, so fixed-level mixing says nothing about this diagonal sample.
2. A dual separator preserves the **complete dyadic selected-numerator
   coordinate**, not merely a linear prefix, and also preserves the complete
   next-depth dyadic forcing congruence.  Nevertheless it has eventual zero
   carries and only the all-nine color.  It deliberately changes the odd
   coordinates.  Thus even all high dyadic bits plus the real BBP tail scale
   cannot by themselves force V1.

The requested product-formula test is therefore negative in a precise way.
The dyadic agreement supplies smallness at one non-Archimedean place, while
the corresponding integer difference is large at the ordinary absolute
value and is unconstrained at the odd places.  The rational product formula
then balances exactly; there is no contradiction.  To make this route work,
one needs a genuinely mixed estimate coupling a sufficiently large part of
the odd selected numerator with the complete dyadic coordinate and the
Archimedean BBP window.

The companion finite replay is an `experiment`.  The bounded source search
is `literature-checked` on the displayed date.  Nothing here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Normalized target and exact selected state

Canonical V1 is

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists r\geq0\ \forall i<m:\quad d_{r+i}(\pi)=w_i.       \tag{2}
\]

Occurrence is contiguous, leading zeroes are allowed, and the empty word is
vacuous.  This is neither infinite-tail occurrence nor subsequence
occurrence.

Use the four-pole coefficient

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}                          \tag{3}
\]

and write

\[
 \begin{aligned}
 L_N&=\mathop{\rm lcm}(d_0,\ldots,d_N),\\
 A_N&=\sum_{k=0}^N(120k^2+151k+47)16^{N-k}{L_N\over d_k},\\
 B_N&={A_N\over16^NL_N}.
 \end{aligned}                                                   \tag{4}
\]

Here every \(d_k\), hence \(L_N\), is odd.  At sevenfold depth put

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 {V_n\over D_n}=10^nB_{7n}.                         \tag{5}
\]

For later comparison retain

\[
 \begin{aligned}
 R_n&={L_{7n+7}\over L_{7n}},&
 \Lambda_n&=2^{27}R_n,\\
 H_n&=\sum_{j=1}^7(120(7n+j)^2+151(7n+j)+47)
       16^{7-j}{L_{7n+7}\over d_{7n+j}},&
 K_n&=5^{n+1}H_n.
 \end{aligned}                                                   \tag{6}
\]

The exact integer recurrence is

\[
 D_{n+1}=\Lambda_nD_n,\qquad
 V_{n+1}=10\Lambda_nV_n+K_n.                       \tag{7}
\]

## 2. The two-adic function equals the exact selected rational numerator

The all-depth audit defines the restricted two-adic analytic function

\[
 F(X)=\sum_{j\geq0}16^ja(X-1-j),                    \tag{8}
\]

and proves

\[
 F(0)=0,\qquad F(X+1)=16F(X)+a(X).                  \tag{9}
\]

Iterating (9) from \(0\) to \(N+1\) gives an identity in \(\mathbb Q_2\):

\[
 F(N+1)=\sum_{k=0}^N16^{N-k}a(k).                  \tag{10}
\]

Both sides are rational numbers, and the embedding
\(\mathbb Q\hookrightarrow\mathbb Q_2\) is injective.  Hence (10) is an
ordinary rational equality.  Equation (4) now proves (1).

This removes an avoidable \(O(1)\)-bit loss in the earlier tail-congruence
formulation.  It also explains the valuation identity without a limiting
tail:

\[
 v_2(A_N)=v_2(F(N+1))=v_2(N+1),                    \tag{11}
\]

because \(L_N\) is odd and the audited isometry gives
\(v_2(F(x))=v_2(x)\).

Set

\[
 r_n=v_2(7n+1),\qquad \kappa_n=27n-r_n.            \tag{12}
\]

After cancellation of \(2^{r_n}\), the reduced form of (5) has dyadic
denominator \(2^{\kappa_n}\).  For a two-integral rational \(x\), let
\([x]_{2^s}\in\{0,\ldots,2^s-1\}\) denote its canonical residue.  The
complete reduced dyadic coordinate is therefore

\[
 \boxed{
 w_n=\left[\,{5^nF(7n+1)\over2^{r_n}}\,\right]_{2^{\kappa_n}}.} \tag{13}
\]

Equivalently, if the reduced form of \(V_n/D_n\) is
\(P_n/(2^{\kappa_n}Q_n)\) with \(Q_n\) odd, then

\[
                      w_n\equiv P_nQ_n^{-1}\pmod {2^{\kappa_n}}. \tag{14}
\]

Thus (13) contains every retained and previously omitted dyadic bit.

## 3. Exact seven-step diagonal recurrence

Define the rational seven-term block

\[
                    G_n=\sum_{j=1}^7 16^{7-j}a(7n+j).          \tag{15}
\]

Seven iterations of (9) give

\[
                    F(7n+8)=16^7F(7n+1)+G_n.                  \tag{16}
\]

Multiplying by \(5^{n+1}\), and using the definition of \(w_n\), gives the
canonical exact recurrence

\[
 \boxed{
 w_{n+1}=2^{-r_{n+1}}
 \left[
  5^{n+1}G_n+5\,2^{28+r_n}w_n
 \right]_{2^{27(n+1)}}.}                              \tag{17}
\]

The bracket in (17) is divisible by \(2^{r_{n+1}}\).  Indeed it is congruent
to \(5^{n+1}F(7n+8)\), whose valuation is exactly \(r_{n+1}\).  If \(w_n\)
is changed by its modulus \(2^{\kappa_n}\), the second term in the bracket
changes by

\[
 5\,2^{28+r_n+\kappa_n}=5\,2^{27(n+1)+1},           \tag{18}
\]

so the input precision in (13) is sufficient.  After division, (17) lies in
\([0,2^{\kappa_{n+1}})\), making it equality rather than only a congruence.

Equation (17) is genuinely coefficient-specific: its inhomogeneous term is
the exact block of the four BBP poles.  But it is a deterministic evaluator,
not a mixing theorem.  Proving that its normalized real representative hits
every required colored cell remains the open step.

## 4. Fixed-level mixing does not control the diagonal

The all-depth audit proves the isometry

\[
                v_2(F(x)-F(y))=v_2(x-y)\qquad(x,y\in\mathbb Z_2). \tag{19}
\]

Because \(7\) is a unit modulo \(2^s\), the affine map
\(n\mapsto7n+1\) permutes \(\mathbb Z/2^s\mathbb Z\).  Therefore

\[
       n\longmapsto F(7n+1)\pmod {2^s}              \tag{20}
\]

also runs through every residue exactly once in each block of \(2^s\)
consecutive indices.  This is perfect deterministic mixing at every fixed
level.

It does not apply to (13).  The reduced output \(w_n\) has
\(\kappa_n=27n-r_n\) bits, but division by \(2^{r_n}\) means that computing
it from \(F(7n+1)\) requires the raw fixed level \(s=27n\).  A complete
period at that raw precision has length

\[
                     2^{27n}=\exp(27(\log2)n).                 \tag{21}
\]

Only one diagonal index \(n\), not a full block of that length, is available
at depth \(n\).  No implication from the finite-level permutation property
to the diagonal distribution follows.  This is the same quantifier defect as
using equidistribution separately for a growing modulus without a uniform
rate.

## 5. Dual separator preserving every dyadic bit

The exact bounded zero-carry solution for the selected recurrence is

\[
 t_n=-10^n(\pi-B_{7n})<0,\qquad
 t_{n+1}=10t_n+{K_n\over D_{n+1}}.                  \tag{22}
\]

For each \(n\geq1\), first take a closest integer in the full dyadic
progression

\[
                         S\equiv V_n\pmod {2^{27n}}.           \tag{23}
\]

The shifts in (23) form an integer lattice after division by \(2^{27n}\).
Because \(L_{7n}\) is odd, exactly one residue class of those shifts would
also give \(S\equiv V_n\pmod {L_{7n}}\).  If the closest shift lies in that
forbidden class, replace it by the closer of its two adjacent shifts.  At
least one neighbor is admissible because \(L_{7n}>1\).  Call the resulting
integer \(S_n^*\), and put

\[
 e_n^*={S_n^*\over D_n},\qquad
 \eta_n=e_n^*-t_n,\qquad r_n^*=D_n+S_n^*.           \tag{24}
\]

The mesh of (23), after division by \(D_n\), is exactly \(1/L_{7n}\).
The closest shift has error at most half a mesh and an adjacent shift adds at
most one mesh.  Therefore

\[
 \boxed{
 |\eta_n|\leq{3\over2L_{7n}},\qquad
 S_n^*\not\equiv V_n\pmod {L_{7n}}.}                         \tag{25}
\]

Let \(\mathcal R_N\) be the reduced odd denominator of \(B_N\).  The frozen
actual-quotient report proves from explicit moving prime bands and the prime
number theorem in progressions that
\(\log\mathcal R_N=(6+o(1))N\).  Since
\(\mathcal R_N\mid L_N\), this gives

\[
                         \log L_{7n}\geq(42+o(1))n.             \tag{26}
\]

The first omitted positive BBP term gives, with
\(\lambda=5/2^{27}\),

\[
 |t_n|\geq{\lambda^n\over336(7n+1)^2}.              \tag{27}
\]

The standard positive-tail upper bound from the same frozen BBP audit gives
\[
 |t_n|\leq{\lambda^n\over15(7n+1)^2}\longrightarrow0.         \tag{27a}
\]

Because

\[
             42-\log(2^{27}/5)=24.895\ldots>0,                \tag{28}
\]

equations (25)--(27a) imply

\[
                         {|\eta_n|\over|t_n|}\longrightarrow0. \tag{29}
\]

Thus eventually

\[
                         -\tfrac12<e_n^*<0.          \tag{30}
\]

The construction preserves the complete raw and reduced dyadic coordinate:

\[
 \boxed{
 S_n^*\equiv r_n^*\equiv V_n\pmod {2^{27n}},\qquad
 v_2(S_n^*)=v_2(r_n^*)=v_2(V_n)=r_n.}              \tag{31}
\]

Define

\[
                         K_n^*=S_{n+1}^*-10\Lambda_nS_n^*.     \tag{32}
\]

Then

\[
 {K_n^*\over D_{n+1}}={K_n\over D_{n+1}}
                      +\eta_{n+1}-10\eta_n,         \tag{33}
\]

and multiplication of (23) by \(10\Lambda_n\) proves

\[
 \boxed{K_n^*\equiv K_n\pmod {2^{27(n+1)}}.}       \tag{34}
\]

The relative forcing error also tends to zero exponentially.  Indeed the
frozen lower bound for the true forcing is

\[
 {K_n\over D_{n+1}}\geq
 {5\over168(7n+1)^2}\lambda^n,                     \tag{35}
\]

and (25)--(28) apply to the error in (33).

Nevertheless (30) makes the centered carry of (33) zero at every late
transition.  For every fixed \(P\geq1\), put \(q_P=10^P-1\).  Eventually
\(-1/2<q_Pe_n^*<0\), so the \(q_P\)-centered carry is also zero and

\[
 \left\lfloor{q_Pr_n^*\over D_n}+\tfrac12\right\rfloor=q_P.  \tag{36}
\]

Thus only the all-nine endpoint color appears.  This sequence is not the BBP
sequence and is not a counterexample concerning pi: it changes the odd
selected residue modulo \(L_{7n}\).  Its exact consequence is that the full
dyadic coordinate, its exact cross-depth forcing class, and BBP-scale real
asymptotics do not imply a colored return without odd-coordinate input.

## 6. Why the rational product formula gives no contradiction

Let

\[
                         \Delta_n=S_n^*-V_n.         \tag{37}
\]

By (23), \(\Delta_n=2^{27n}h_n\) for an integer \(h_n\).  If it is nonzero,
the normalized rational product formula says

\[
 |\Delta_n|_\infty\prod_p|\Delta_n|_p=1.            \tag{38}
\]

The preserved dyadic coordinate gives

\[
                         |\Delta_n|_2\leq2^{-27n}.  \tag{39}
\]

In this construction (25) makes \(\Delta_n\ne0\), so already
\(|\Delta_n|_\infty\geq2^{27n}\).  This is the elementary integer form of
the compensation in the product formula: one-place divisibility alone makes
the ordinary height large rather than contradictory.

But (22), (24), and (5) give the exact real size

\[
 \Delta_n=D_ne_n^*-V_n
          =D_n(e_n^*-10^nB_{7n}).                  \tag{40}
\]

The two terms in parentheses lie near \(0\) and near \(10^n\pi\),
respectively.  In particular \(|\Delta_n|_\infty\) is of the natural
selected-numerator height, not exponentially small.  At the odd primes the
separator imposes no systematic divisibility; (25) only ensures that the
complete odd congruence is not retained.  Any incidental odd factors remain
uncontrolled.  Consequently the ordinary factor and the odd local factors
exactly compensate (39), as (38) requires.

Replacing \(\Delta_n\) by the small real error
\(D_n(e_n^*-t_n)=D_n\eta_n\) does not help: that quantity is not the
difference of the selected BBP numerator and the separator numerator.  The
identity defining \(t_n\) contains the transcendental number pi with nonzero
rational coefficient, so it is not a rational or algebraic number to which
(38) can be applied.

Now test the proposed proper-subshift hypothesis directly.  If a word \(w\)
were absent from pi, then every \(\{10^m\pi\}\) would lie in the
finite-state survivor set \(K_w\).  BBP tail transfer would place the
corresponding rational phases exponentially close to \(K_w\).  This is a
location constraint, not Archimedean smallness of a nonzero rational or
algebraic form: a proper decimal survivor set is infinite and is not the
zero set of any nonzero one-variable polynomial.  Ordinary decimal
truncation of a point of \(K_w\) gives only the universal denominator-\(10^m\)
error \(10^{-m}\).  The identity (1) adds a dyadic coordinate to the BBP
rational, but it creates no form that is both small at infinity and highly
divisible at the remaining places.  Thus the missing-word assumption plus
the all-depth two-adic identity does not satisfy the premises needed for a
product-formula contradiction.

This identifies the minimum stronger input for a product-formula route.  One
needs a nonzero rational or algebraic form which is simultaneously:

- exponentially small at the Archimedean place because a forbidden decimal
  subshift forces it;
- divisible to total logarithmic order exceeding its global height at \(2\)
  **and at enough odd primes**; and
- linked to the exact four-pole selected numerator, rather than to a freely
  chosen rational shadow.

The prior high-prime rigidity theorem shows the tension: preserving the
actual explicit primes above the depth, together with the full dyadic
coordinate and a BBP-quality Archimedean window, already selects \(B_N\)
uniquely.  It does not estimate that unique point's decimal orbit.  The
missing theorem is therefore a mixed selected odd--dyadic--Archimedean
correlation, not another one-place valuation or the bare product formula.

## 7. Exact replay

The companion
[bbp_high_dyadic_archimedean_separator_20260813_check.py](bbp_high_dyadic_archimedean_separator_20260813_check.py)
uses only integers and `Fraction` arithmetic.  It independently reconstructs
\(L_{7n},A_{7n},D_n,V_n\); evaluates the finite residues of \(F\); verifies
(1), (13), and (17); exhausts the fixed-level permutation through ten bits;
and constructs the full-dyadic separator through fifty exact transitions.

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py
```

Retained output:

```text
status: PASS
finite_claim_label: experiment
report_claim_label: proof sketch
diagonal_depth_range: [1, 110]
separator_depth_range: [50, 100]
rational_tail_cutoff: 130
null_identity_checks: 230
fixed_level_permutation_checks: 2046
complete_diagonal_coordinate_checks: 440
seven_step_recurrence_checks: 327
adversarial_selector_checks: 330
separator_state_checks: 408
separator_transition_checks: 300
color_and_zero_carry_checks: 608
largest_log10_relative_tail_error: -534.0806523682841
largest_log10_relative_forcing_error: -534.0806523667287
preserves_complete_dyadic_selected_coordinate: true
preserves_complete_next_dyadic_forcing_class: true
preserves_odd_selected_coordinate: false
asserts_actual_bbp_carries_are_zero: false
asserts_all_color_return: false
asserts_v1: false
```

Every bounded row has label `experiment`.  The all-index statements are the
rational and two-adic identities, prime-number asymptotics, and elementary
nearest-grid construction above.

## 8. Literature and mathlib boundary

Status: bounded `literature-checked` search on **2026-08-13 UTC**.

| primary source | checked relevance and boundary | local pin |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | Supplies the exact four-pole series.  It gives base-sixteen digit extraction, not diagonal two-adic/decimal mixing. | SHA-256 `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Barsky--Muñoz--Pérez-Marco, [*On the genesis of BBP formulas*](https://doi.org/10.4064/aa200619-28-9), Theorem 5.2 and Proposition 5.3 | Gives the logarithmic generation of BBP formulas and a null formula.  It does not prove a product-formula return for pi. | source scope pinned in the all-depth audit |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2), Theorems 3.1, 3.3, and 4.1 | Places BBP remainders in a dynamical framework; the needed distribution conclusion remains conditional. | SHA-256 `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Bailey--Crandall, [*On the Random Character of Fundamental Constant Expansions*](https://doi.org/10.1080/10586458.2001.10504441), Hypothesis A | The rational-perturbation distribution mechanism is explicitly a hypothesis. | SHA-256 `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` |

Fresh searches covered `BBP pi p-adic analytic product formula digit
distribution`, `p-adic analytic interpolation lacunary orbit normality`,
`adelic product formula missing digits`, and repository searches for a
rational product-formula or moving-precision equidistribution theorem.  The
results concerned general adelic dynamics, BBP formula families, and metric
digit-restricted sets.  No primary theorem found in this bounded search
couples the exact diagonal
\((F(7n+1)/2^{r_n})\bmod2^{\kappa_n}\) with the odd selected coordinates
and the decimal orbit of this fixed pi.

The mathlib search found standard valuation and finite-ring interfaces but no
theorem supplying that mixed correlation.  Since the key positive result is
the elementary rational identity (1), no new formal infrastructure is
justified by this route-closure report.

## 9. Coordination record

This branch registered the descendant-area watch
`ultrapi-high-dyadic-20260813` on `local:pi-digits` for agent
`codex-ultrapi-high-dyadic`.  The initial and final polls were empty at cursor
and delivered sequence 56,947, so there was no event to acknowledge.
Observation events are coordination signals only and were not used as
mathematical evidence.

## Sharp handoff

The exact high-dyadic coordinate is no longer unknown: equations (13) and
(17) calculate all of it from the two-adic BBP function and the four-pole
block.  Fixed-level permutation is also exact.  What fails is the required
uniformity on the exponentially growing diagonal.

The dual separator proves that even this complete coordinate, its
cross-depth forcing class, and exponentially accurate real forcing can
coexist with permanent zero carries and only one color when the odd
coordinate is changed.  The bare product formula cannot rule this out,
because it sees only one forced small local factor and a large ordinary
height.

The next viable target is therefore a genuinely mixed estimate for the
**actual** selected numerator: an exponential sum, determinant, or algebraic
form in which enough odd local data, the diagonal dyadic coordinate, and the
Archimedean BBP window are simultaneously present.  No such estimate is
proved here, so V1 remains a `conjecture`.
