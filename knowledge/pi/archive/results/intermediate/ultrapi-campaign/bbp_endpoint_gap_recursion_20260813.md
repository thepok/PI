# BBP endpoint-gap recursion: exact localization and a primary-compatible no-go

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Frozen inputs:

| artifact | SHA-256 |
|---|---|
| [three-primary decimation report](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [independent decimation audit](bbp_three_primary_decimation_20260813_independent_audit.md) | `5dc190f913c1eb727e4a1cbc9bef2d8f3373af00b17e1aa50244ae8efceb3371` |
| [full-phase experiment](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [full-phase checker](bbp_three_grid_full_phase_experiment_20260813_check.py) | `502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458` |
| [twisted-sum report](bbp_three_primary_twisted_sum_20260813.md) | `0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12` |
| [independent twisted-sum audit](bbp_three_primary_twisted_sum_20260813_independent_audit.md) | `44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81` |

All frozen inputs remained byte-for-byte unchanged.

## Outcome and claim boundary

There is **no unconditional recursion from (G_{e-2}) to (G_e)** in this
report.  In particular, the tempting inequality

\[
                         G_e^\pm\le {G_{e-2}^\pm\over9}                 \tag{R0}
\]

is false in all four transitions for which both rows were reconstructed as
exact rational sets.  The weaker factor-three inequality happens to hold in
those four finite cases, but remains only an `experiment`, not an asymptotic
statement.

The strongest rigorous progress is a no-go with three parts.

1. The decimation gives an exact cross-epoch **three-localized defect** after
   primary-compatible exponent matching.  Its denominator is prime to three,
   but it can be almost maximally large on the real circle.  Localization is
   not an Archimedean estimate.
2. An exact exhaustive `experiment` checks every pair of consecutive complete
   primary-period subwindows at the transitions (4\to6) and (6\to8).  At
   (6\to8), every primary-compatible nine-child refinement misses at least
   one ideal child by more than (1/4) on the pre-drop row and more than
   (1/6) on the drop row.  Optimizing both subwindows does not repair the
   mechanism.
3. An elementary rational `proof sketch` constructs endpoint systems with the
   same valuation pattern, localized decimation, nested units, complete
   primary grids, and arbitrarily close adjacent signs, while their full
   phases have largest gap arbitrarily close to one.  This countermodel is
   deliberately **not** the BBP sequence and does not shadow pi.  It proves
   that those structural inputs alone cannot imply gap decay; pi-specific
   control of the synchronized complement is indispensable.

The exact identities and the countermodel have label `proof sketch`; all
bounded computations have label `experiment`.  This branch adds no formal
declaration and makes no new `machine-checked` or `literature-checked` claim.
It is not a `candidate resolution` or a `verified resolution`.  Canonical V1
remains a `conjecture`.

## 1. Normalized statements and quantifiers

Canonical V1 is the assertion that for every integer (P\ge1) and every
(0\le k<10^P), there exists (n\ge0) such that

\[
                 \left\lfloor10^P\{10^n\pi\}\right\rfloor=k.          \tag{R1}
\]

Leading zeros are retained.  The assertion asks for one contiguous
occurrence of each finite word; it neither quantifies over infinite words nor
asserts infinitely many occurrences.

For the branch problem, let

\[
 B_M=\sum_{j=0}^M {120j^2+151j+47\over
 (2j+1)(4j+3)(8j+1)(8j+5)16^j},\qquad N_n=10^n-16.          \tag{R2}
\]

For even (e\ge2), set

\[
 A_e={3^e-1\over8},\quad M_e^-=5A_e-1,\quad M_e^+=5A_e,
 \quad U(M)=\lfloor\log_{10}(16^M)\rfloor.                 \tag{R3}
\]

The full rational rows and their largest circular gaps are

\[
 X_e^\pm=\bigl\{\{N_nB_{M_e^\pm}\}:M_e^\pm\le n\le U(M_e^\pm)\bigr\},
 \qquad G_e^\pm=G(X_e^\pm).                                \tag{R4}
\]

Here (G(S)) is the largest complementary arc between consecutive distinct
points of a nonempty finite circle set.  Distinctness on the retained rows is
proved in the frozen full-phase report.  “Recursion” below means a uniform
all-sufficiently-large-even-(e) inequality, not a fit to finitely many rows.
“Maps to nine children” means the exponent matching forced by the old primary
period; it does not mean an unconstrained nearest-neighbour matching after
forgetting the primary coordinate.

The exact endpoint-gap conjecture under attack is

\[
 \exists C>0\ \exists e_0\ \forall e\ge e_0\text{ even}\ \forall\sigma\in\{-,+\},
 \qquad G_e^\sigma\le C{\log |X_e^\sigma|\over |X_e^\sigma|}.          \tag{R5}
\]

Nothing in this report proves or refutes (R5).

## 2. Exact exponent-window recursion

Put (alpha=\log_{10}16).  Direct substitution gives

\[
 M_e^-=9M_{e-2}^-+13,\qquad M_e^+=9M_{e-2}^++5.             \tag{R6}
\]

For (sigma\in\{-,+\}), let (s_-=13,s_+=5) and write

\[
 U(M_e^\sigma)=9U(M_{e-2}^\sigma)+c_e^\sigma.              \tag{R7}
\]

If ({x}) denotes fractional part, then exactly

\[
 c_e^\sigma=\left\lfloor9\{\alpha M_{e-2}^\sigma\}
                              +\alpha s_\sigma\right\rfloor.          \tag{R8}
\]

Since (15<13\alpha<16) and (6<5\alpha<7),

\[
 15\le c_e^-\le24,\qquad6\le c_e^+\le15.                  \tag{R9}
\]

Writing (L_e^\sigma=|X_e^\sigma|), (R6)--(R7) give

\[
 L_e^\sigma=9L_{e-2}^\sigma+c_e^\sigma-s_\sigma-8.        \tag{R10}
\]

Thus the new row has approximately, but not exactly, nine times as many
exponents.  The exact offsets through (e=14) are:

| (e) | sign | (c_e^σ) | (L_e^σ-9L_{e-2}^σ) |
|---:|:---:|---:|---:|
| 4 | − | 23 | 2 |
| 4 | + | 6 | −7 |
| 6 | − | 15 | −6 |
| 6 | + | 7 | −6 |
| 8 | − | 21 | 0 |
| 8 | + | 13 | 0 |
| 10 | − | 21 | 0 |
| 10 | + | 14 | 1 |
| 12 | − | 23 | 2 |
| 12 | + | 6 | −7 |
| 14 | − | 17 | −4 |
| 14 | + | 10 | −3 |

These rows have label `experiment`, although (R6)--(R10) are elementary
all-depth identities.  In particular, at (e=6) there are six fewer new
exponents than nine copies of the old row.  A literal injective assignment of
nine distinct new exponents to every old row exponent is already impossible
there by cardinality.

## 3. Exact cross-epoch full-phase defect

Write (b_e^\sigma=B_{M_e^\sigma}) and

\[
                         D_e^\sigma=9b_e^\sigma-b_{e-2}^\sigma.        \tag{R11}
\]

The frozen decimation proves at `proof sketch` level

\[
                              D_e^\sigma\in\mathbb Z_{(3)}.            \tag{R12}
\]

Let (E_{e-2}^-=e-2), (E_{e-2}^+=e-3), and

\[
 T_{e-2}^\sigma=3^{E_{e-2}^\sigma-2}.                                \tag{R13}
\]

For the drop sign this formula is used from (e\ge6), avoiding the already
audited (e=4\to2) boundary exception.  Choose exponents (n,ρ) with

\[
                              n\equiv\rho\pmod {T_{e-2}^\sigma}.        \tag{R14}
\]

The exact order of ten modulo (3^{E_{e-2}^\sigma}) implies
(3^{E_{e-2}^\sigma}\mid10^n-10^\rho).  Therefore

\[
\boxed{
 9N_nb_e^\sigma-N_\rho b_{e-2}^\sigma
 =N_nD_e^\sigma+(N_n-N_\rho)b_{e-2}^\sigma
 \in\mathbb Z_{(3)}.}                                                \tag{R15}
\]

Modulo one, the left side is precisely

\[
 9\{N_nb_e^\sigma\}-\{N_\rho b_{e-2}^\sigma\}.                       \tag{R16}
\]

At the isolated primary coordinate this defect is zero: the endpoint-unit
nesting and (R14) give exactly

\[
                         9x_{e,n}^\sigma=x_{e-2,\rho}^\sigma\pmod1.    \tag{R17}
\]

Equations (R15)--(R17) expose the issue sharply.  Every remaining defect has
denominator prime to three, but no upper bound on its circle distance follows.
The exact checker finds a fixed-exponent defect larger than (49/100) in
each of the four reconstructed transitions:

| transition | sign | maximum checked defect |
|:---:|:---:|---:|
| (4\to6) | − | 0.499253697955943… |
| (4\to6) | + | 0.498783217937848… |
| (6\to8) | − | 0.499100471113819… |
| (6\to8) | + | 0.499988950495557… |

This table is an `experiment`.  It does not prove that the defects stay large
asymptotically, but it rigorously falsifies the premise that three-localization
itself makes them small.

## 4. What a genuine gap recursion would need

For a finite circle set (S), define its complete ninefold inverse image

\[
                 R_9(S)=\left\{{s+j\over9}:s\in S, 0\le j<9\right\}.  \tag{R18}
\]

Then exactly

\[
                              G(R_9(S))={G(S)\over9}.                   \tag{R19}
\]

An elementary directed-Hausdorff argument gives the useful conditional
lemma: if every point of R₉(S) lies within circle distance ε of a point of Z,
then

\[
                              G(Z)\le {G(S)\over9}+2\varepsilon.       \tag{R20}
\]

Indeed, an open Z-free arc shortened by ε at both ends is R₉(S)-free, so its
shortened length is at most (R19). If Z is a subset of the new full row,
adding the remaining row points can only decrease the gap.

Equation (R20) is the desired deterministic recursion template. Its missing
input is not algebraic nesting but a small **full-phase** ε. Moreover, a
complete old primary-period block S is only a subset of the old row. Removing
r points can merge r+1 old gaps, so the general selection-loss bound is far
too costly when r has the same order as the old primary period. A useful
recursion must control this loss or refine the entire old row.

## 5. Exhaustive primary-compatible subwindow no-go

Take any consecutive old subwindow (J_{e-2}) of length
(T=T_{e-2}^\sigma) inside the old row and any consecutive new subwindow
(J_e) of length (9T) inside the new row.  Each old exponent (m\in
J_{e-2}) has exactly nine corresponding exponents (n\in J_e) with

\[
                                 n\equiv m\pmod T.                      \tag{R21}
\]

These are the nine exponents forced by the primary inverse system.  For each
old full phase (y_m=\{N_mb_{e-2}^\sigma\}), its ideal real-circle children
are ((y_m+j)/9), (0\le j<9).

The standalone checker exhausts **every pair** ((J_{e-2},J_e)), using exact
Python rational arithmetic.  In every pair it finds an old (m) and a branch
(j) such that all nine corresponding phases satisfy

\[
 d_{\mathbb T}\!\left(\{N_nb_e^\sigma\},{y_m+j\over9}\right)
                                      >\theta_{e,\sigma}.              \tag{R22}
\]

The exact retained thresholds and search sizes are:

| transition | sign | (θ_{e,σ}) | all subwindow pairs checked |
|:---:|:---:|---:|---:|
| (4\to6) | − | (3/20) | 39 |
| (4\to6) | + | (1/10) | 603 |
| (6\to8) | − | (1/4) | 1,417 |
| (6\to8) | + | (1/6) | 39,865 |

Thus the freedom to slide both complete-period subwindows does not produce a
small primary-compatible refinement at either transition.  At (6\to8), the
best possible mechanism of this exact form still has an order-one missing
child.

The qualification is important.  Equation (R22) does **not** say that the
ideal child is far from every point of the new row; a point from a different
primary fibre could be nearby after complementary cancellation.  It
rigorously falsifies the natural map supplied by (R17), not arbitrary global
matching.  Proving arbitrary global matching would itself require essentially
the full-phase covering information sought in (R5).

The exact largest gaps also give:

| transition | sign | old gap | new gap | conclusion |
|:---:|:---:|---:|---:|:---|
| (4\to6) | − | 0.236173020622015… | 0.043865699325988… | (G_e>G_{e-2}/9) |
| (4\to6) | + | 0.236173595486821… | 0.043865699175123… | (G_e>G_{e-2}/9) |
| (6\to8) | − | 0.043865699325988… | 0.008593524984164… | (G_e>G_{e-2}/9) |
| (6\to8) | + | 0.043865699175123… | 0.008593524984164… | (G_e>G_{e-2}/9) |

Every inequality in this table is checked exactly, not from the displayed
decimals.  All four also satisfy (G_e<G_{e-2}/3), but that is only finite
`experiment` and is not promoted to a conjectural theorem here.

## 6. The adjacent pre/drop identity transports the obstruction

Let

\[
 t_e=b_e^+-b_e^->0.                                                    \tag{R23}
\]

For arbitrary exponents (n,ρ), define the unwrapped cross-epoch defects

\[
 Z_e^\sigma(n,\rho)=9N_nb_e^\sigma-N_\rho b_{e-2}^\sigma.              \tag{R24}
\]

The adjacent-depth identity gives the exact relation

\[
\boxed{Z_e^+(n,\rho)-Z_e^-(n,\rho)=9N_nt_e-N_\rho t_{e-2}.}            \tag{R25}
\]

If (n) belongs to the common part of the two new rows and (ρ) belongs
to the common part of the two old rows, the frozen positive-tail estimate
implies

\[
 |Z_e^+(n,\rho)-Z_e^-(n,\rho)|
 \le {9\over15(M_e^-+1)^2}
      +{1\over15(M_{e-2}^-+1)^2}.                                     \tag{R26}
\]

So the pre/drop defects are extremely close.  This explains why dropping one
three-primary power barely changes the observed full geometry: the
complement compensates in both adjacent rows.  It does not make either defect
small.

There is one genuine, but same-epoch and too-weak, deterministic gap
comparison.  Since (1<\alpha<2), the two row intervals share all but one
lower point and one or two upper points.  Pair the common phases using the
adjacent bound

\[
                         \delta_e={1\over15(M_e^-+1)^2}.                \tag{R27}
\]

Moving a finite circle set pointwise by at most (δ_e) changes its largest
gap by at most (2\delta_e).  Removing one point merges at most two gaps;
removing two merges at most three.  Consequently

\[
 G_e^+\le2G_e^-+2\delta_e,
 \qquad
 G_e^-\le3G_e^++2\delta_e.                                             \tag{R28}
\]

Equation (R28) is a `proof sketch` relation between the adjacent signs.  It
does not connect (e) to (e-2), so it cannot prove (R5).

## 7. Exact structural countermodel

The following elementary construction shows why (R12), (R17), complete
primary periods, and adjacent closeness cannot by themselves force gap
decay.  Fix (C_2=1).  Recursively choose integers

\[
 C_e=C_{e-2}+k_e3^{e-2},\qquad 3\nmid C_e,                              \tag{R29}
\]

with (k_e) as large as desired, and define

\[
 \widetilde b_e^-={1\over3^eC_e},
 \qquad
 \widetilde b_e^+={1\over3^{e-1}C_e}.                                  \tag{R30}
\]

Then the endpoint valuations have exactly the required pattern, and direct
subtraction gives

\[
\begin{aligned}
 9\widetilde b_e^- -\widetilde b_{e-2}^-
   &=-{k_e\over C_eC_{e-2}}\in\mathbb Z_{(3)},\\
 9\widetilde b_e^+ -\widetilde b_{e-2}^+
   &=-{3k_e\over C_eC_{e-2}}\in\mathbb Z_{(3)},\\
 \widetilde b_e^+-\widetilde b_e^-
   &={2\over3^eC_e}.
\end{aligned}                                                          \tag{R31}
\]

The normalized endpoint unit for both signs is (C_e^{-1}) in the relevant
three-adic modulus.  Congruence (R29) therefore gives the same nested unit
system, and every complete primary exponent period is still a complete grid.

Given any ε > 0, choose kₑ so large that

\[
 {10^{U(M_e^+)}-16\over3^{e-1}C_e}<\varepsilon.                        \tag{R32}
\]

Every full phase from both selected rows then lies in the real arc
((0,\varepsilon)), hence

\[
                              \widetilde G_e^\pm>1-\varepsilon.        \tag{R33}
\]

The checker instantiates ε = 1/100 through e = 8, checks all structural
identities exactly, checks 1,092 primary points, and certifies gaps greater
than 99/100.

This is a logical no-go, not a counterexample about pi. The constructed
endpoint values are not BBP partial sums and do not satisfy the real-shadow
estimate toward pi. In particular, they preserve neither T74's four
individual pole-term identities nor the actual reduced BBP numerator; those
properties were never hypotheses of the countermodel. The conclusion is
precisely scoped: a proof of (R5) must use new pi/BBP-specific information
about the complementary phase, not only the explicitly listed valuation,
localized-decimation, unit-nesting, complete-primary-grid, and adjacent-row
properties.

## 8. Reproducible checker

The standalone
[checker](bbp_endpoint_gap_recursion_20260813_check.py), SHA-256
`0c8967858d1023e001cbc3fb011ae525cdd1800d3622e92d7d1fc0dd712cc780`,
imports no branch checker.  It pins all six frozen research artifacts and the
canonical source, reconstructs the four-pole sums through depth 4,100,
performs exact integer/rational circle-distance comparisons, and exhausts
41,924 complete-subwindow pairs. The retained complete stdout, including its
final newline, has SHA-256
`3490c218eeef3e1d572b5ce198298f214bde4f69592c411db948bd78b8c97f8a`.
Reproduce from the repository root with:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py
```

Its retained output ends with:

```text
complete_subwindow_pairs=41924
exact_subwindow_distance_checks=38772
countermodel_checks=33
countermodel_primary_points=1092
countermodel_gap_lower_bound=99/100
countermodel_is_bbp_or_pi=false
asserts_endpoint_gap_law=false
asserts_fixed_return=false
asserts_v1=false
status=PASS
```

The local mathlib search found generic Hausdorff-distance infrastructure in
`Mathlib.Topology.MetricSpace.HausdorffDistance`, but no specialized
largest-circular-gap recursion used here.  No formal file, `AxiomAudit.lean`,
verification gate, primary report, or `ultrapi.md` was edited.  This branch
makes no novelty claim and invokes no new literature theorem beyond the
frozen applicability records.

## 9. Coordination record

This branch registered descendant-area watch
`ultrapi-endpoint-gap-recursion-20260813` on `local:pi-digits` for agent
`codex-ultrapi-endpoint-gap-recursion`. Its initial and final polls were empty
at cursor and delivered sequence 57,342, so there was no event to acknowledge.
Observation events would have been coordination signals only, never
mathematical evidence.

## Sharp handoff

The endpoint nesting is now separated from the gap conjecture as strongly as
the present exact data permit.  It supplies a perfect ninefold inverse system
only after projecting to the three-primary coordinate.  On the full circle,
the residue-matched defect is merely three-localized, the obvious
primary-compatible refinements fail exhaustively at two transitions, and the
adjacent identity transports rather than removes that defect.

The surviving route is therefore not another rearrangement of the same
endpoint congruence.  It requires a genuinely Archimedean estimate on the
actual synchronized complement—such as the selected Fourier coefficient in
the frozen twisted-sum report—or a direct discrepancy estimate for the full
BBP/pi row.  Without that new estimate, the endpoint gap law and canonical V1
remain `conjecture`s.
