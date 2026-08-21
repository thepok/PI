# The selected BBP three-adic limit as an explicit shell series

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Frozen mathematical inputs:

| input | SHA-256 |
|---|---|
| [three-primary decimation](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [Bailey--Borwein--Plouffe paper](../theory/pi-quantitative-block-hitting/library/t4/bbp-1997.pdf) | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |

## Outcome and claim boundary

Canonical V1 remains a `conjecture`.  This branch gives no correlation-decay
estimate, no deterministic escape from the bounded exceptional fibres, and no
occurrence theorem for every finite decimal word in pi.

The mathematical derivation below has label `proof sketch`.  Its substantive
advance is an all-depth, convergent expression for the previously abstract
coherent unit

\[
 U_\infty=\lim_{\substack{e\to\infty\\e\ {\rm even}}}
             3^eB_{M_e}\in\mathbb Z_3^\times.
\]

It is

\[
 \boxed{
 U_\infty=\sum_{s\ge0}3^s
 \left(4\rho(H_{1,s}-H_{3,s})-2H_{2,s}+4H_{4,s}\right),}       \tag{SL1}
\]

where \(\rho\in\mathbb Z_3\) is the unique root
\(\rho^2=-2\), \(\rho\equiv1\pmod3\), and every \(H_{i,s}\) is
an explicit **finite** sum of reciprocals of 3-adic units in one arithmetic
progression.  Sections 2--3 give the exact sets and derive (SL1) directly from
the four BBP poles.

The frozen decimation then identifies every selected prefix with this one
limit:

\[
  U_e\equiv U_\infty\pmod {3^e},\qquad
  a_e\equiv U_\infty10^{M_e}\pmod {3^e}.                       \tag{SL2}
\]

Thus (SL1) determines all two-digit lifts **algorithmically**, through
arbitrary-precision finite progression sums, not just a bounded table.  This
is not a finite closed recurrence.  It does not make their digit sequence
rational, algebraic, automatic, or Mahler; none of those classifications was
obtained.  More importantly, even such a classification would not by itself
control the synchronized complementary weights in the actual BBP correlation.

The bounded replay has label `experiment`.  The applicability search is
`literature-checked`.  There is no `machine-checked`, `candidate resolution`,
or `verified resolution` claim in this branch.

## 1. Normalized statement and quantifiers

Canonical V1 is

\[
 \forall P\ge1\ \forall 0\le k<10^P\ \exists n\ge0:\qquad
 \left\lfloor10^P\{10^n\pi\}\right\rfloor=k,                 \tag{SL3}
\]

where \(k\) is represented by exactly \(P\) decimal digits, including
leading zeroes.  It asks for one contiguous occurrence of each finite word.
It does not assert normality, positive frequency, or infinitely many
occurrences.

Use the exact BBP coefficient

\[
 A(k)={4\over8k+1}-{1\over2(2k+1)}-{1\over8k+5}
      -{1\over2(4k+3)},\qquad
 B_M=\sum_{k=0}^M{A(k)\over16^k}.                              \tag{SL4}
\]

For even \(e\ge2\), set

\[
 M_e={5(3^e-1)\over8}-1={5\cdot3^e-13\over8},
 \qquad U_e=3^eB_{M_e}.                                       \tag{SL5}
\]

The phrase “an explicit description of the selected path” is kept separate
from three stronger claims:

1. (SL1) is an algorithm for every 3-adic digit of \(U_\infty\).
2. A finite automaton would require a finite 3-kernel or an equivalent
   finite-state presentation.  (SL1) does not supply one.
3. Escape from the actual exceptional fibres depends on both the path and
   the complementary weights.  It is not a property of \(U_\infty\) alone.

## 2. Stable pole shells

Write the four pole triples in (SL4) as

\[
 (a_i,b_i,c_i)=(8,1,4),(2,1,-1/2),(8,5,-1),(4,3,-1/2).        \tag{SL6}
\]

For \(s\ge0\), define the following finite sets of positive 3-adic units:

\[
\begin{aligned}
 Q_{1,s}&=\{q: q<5\cdot3^s,\ 3\nmid q,\
                    q\equiv3^s\pmod8\},\\
 Q_{2,s}&=\{q:4q<5\cdot3^s,\ 3\nmid q,\ q\equiv1\pmod2\},\\
 Q_{3,s}&=\{q: q<5\cdot3^s,\ 3\nmid q,\
                    q\equiv5\cdot3^s\pmod8\},\\
 Q_{4,s}&=\{q:2q<5\cdot3^s,\ 3\nmid q,\
                    q\equiv3\cdot3^s\pmod4\},                \tag{SL7}
\end{aligned}
\]

and

\[
                         H_{i,s}=\sum_{q\in Q_{i,s}}q^{-1}
                         \quad\hbox{in }\mathbb Z_3.           \tag{SL8}
\]

These sets arise without an asymptotic density argument.  Fix \(s\), let
even \(e\) tend to infinity, and isolate a pole whose linear denominator has
exact height \(e-s\):

\[
                   a_i k+b_i=q3^{e-s},\qquad3\nmid q.          \tag{SL9}
\]

The four endpoint maxima are

\[
\begin{array}{c|c}
i& a_iM_e+b_i\\ \hline
1&5\cdot3^e-12\\
2&(5\cdot3^e-9)/4\\
3&5\cdot3^e-8\\
4&(5\cdot3^e-7)/2.
\end{array}                                                    \tag{SL10}
\]

After division by \(3^{e-s}\), the strict bounds in (SL7) are therefore
exact for all sufficiently large \(e\) at each fixed \(s\).  Since \(e\)
is even and all \(a_i\) are powers of two, the integrality condition in
(SL9) becomes, respectively,

\[
 q\equiv3^s\pmod8,\qquad q\equiv1\pmod2,\qquad
 q\equiv5\cdot3^s\pmod8,\qquad q\equiv3\cdot3^s\pmod4,     \tag{SL11}
\]

which is precisely (SL7).  No pole of height greater than \(e\) occurs at
this endpoint.  The maxima for poles two and four are below \(3^{e+1}\).
For poles one and three, the only possible height-\(e+1\) unit quotient is
\(q=1\), and it fails their respective integrality congruences modulo eight.

## 3. Derivation and convergence of the limit series

### `proof sketch`

The contribution of a solution (SL9) to \(U_e\) is

\[
 c_i3^sq^{-1}16^{-k},\qquad
 k={q3^{e-s}-b_i\over a_i}.                                   \tag{SL12}
\]

Because \(16\in1+3\mathbb Z_3\) and \(3\nmid a_i\), it has a unique
\(a_i\)-th root in \(1+3\mathbb Z_3\).  Therefore, for fixed \(s,q,i\),

\[
             16^{-k}\longrightarrow16^{b_i/a_i}
             \quad\hbox{in }\mathbb Z_3.                     \tag{SL13}
\]

The four chosen root values simplify completely.  With
\(\rho^2=-2\), \(\rho\equiv1\pmod3\), they are

\[
 16^{1/8}=\rho,qquad16^{1/2}=4,qquad
 16^{5/8}=4\rho,qquad16^{3/4}=-8.                            \tag{SL14}
\]

Multiplying by the four coefficients \(c_i\) gives
\(4\rho,-2,-4\rho,4\).  Hence the fixed shell limit is

\[
 C_s=4\rho(H_{1,s}-H_{3,s})-2H_{2,s}+4H_{4,s}.                \tag{SL15}
\]

Every reciprocal in (SL8) is a 3-adic unit, so \(C_s\in\mathbb Z_3\).
Consequently \(v_3(3^sC_s)\ge s\), which proves convergence of the right
side of (SL1).

To identify the limit, work modulo an arbitrary \(3^R\).  Shells \(s\ge R\)
vanish.  For the finitely many shells \(s<R\), (SL7) is stable once \(e\)
is large, and (SL13) may be taken term by term.  Thus the limit of \(U_e\)
modulo \(3^R\) is the first \(R\) terms of (SL1), proving the identity in
\(\mathbb Z_3\).

The frozen decimation gives

\[
 9B_{M_{e+2}}-B_{M_e}\in\mathbb Z_{(3)}.                     \tag{SL16}
\]

Multiplication by \(3^e\) yields

\[
                         U_{e+2}-U_e\in3^e\mathbb Z_{(3)}.    \tag{SL17}
\]

All later endpoints therefore have the same residue modulo \(3^e\).
Taking the limit in (SL17) proves the first part of (SL2); multiplication by
the 3-adic unit \(10^{M_e}\) proves the second.

## 4. An exact radix-nine refinement, and why it is not yet a finite state

There is an inspectable functional hierarchy behind (SL8).  For example,
put

\[
 b_s=5\cdot3^s-1,qquad
 L_{r,s}=\sum_{\substack{1\le q\le b_s\\q\equiv r\ (8)\\3\nmid q}}q^{-1}.
                                                                    \tag{SL18}
\]

Since \(b_{s+2}=9b_s+8\), write every unit \(q\) uniquely as
\(q=9u+d\), where
\(d\in D=\{1,2,4,5,7,8\}\).  This gives the exact all-depth identity

\[
 L_{r,s+2}=
 \sum_{d\in D}\ 
 \sum_{\substack{0\le u\le b_s\\u+d\equiv r\ (8)}}{1\over9u+d}.  \tag{SL19}
\]

Expanding each unit denominator in \(\mathbb Z_3\) gives

\[
 L_{r,s+2}=
 \sum_{d\in D}\sum_{n\ge0}{(-9)^n\over d^{n+1}}
 \sum_{\substack{0\le u\le b_s\\u+d\equiv r\ (8)}}u^n.          \tag{SL20}
\]

The series in \(n\) converges at least two ternary digits per term.  Its
inner sums are ordinary finite power sums, so (SL20) is an arbitrary-precision
recurrence.  Analogous radix decompositions apply to the other two cutoff
shapes in (SL7).

What (SL20) does **not** show is just as important.  The scalar reciprocal
sum opens into moments of every order.  No finite invariant collection of
moments, finite 3-kernel, algebraic formal-series equation, or Mahler
functional equation was found.  A hidden resummation may exist; finite data
cannot rule it out.  Thus this report neither calls the path automatic nor
claims that it is nonautomatic.

## 5. Why classifying \(U_\infty\) alone cannot close the BBP argument

The exceptional-fibre problem concerns correlations

\[
 S_e(a;W_e)=\sum_{j<3^{e-2}}e_{3^e}(a10^j)W_e(j).             \tag{SL21}
\]

Equation (SL2) now makes the selected \(a=a_e\) completely explicit in
3-adic terms.  But the weight \(W_e\) contains the complementary dyadic and
odd CRT coordinates of the four-pole phase.  Rationality, algebraicity,
automaticity, or a Mahler equation for \(U_\infty\) would not estimate that
joint phase by itself.

There is an exact separator.  For any predetermined coherent path \(a_e\),
choose

\[
                  W_e(j)=\overline{e_{3^e}(a_e10^j)}.          \tag{SL22}
\]

Then \(S_e(a_e;W_e)=3^{e-2}\) at every depth, irrespective of how simple
the digit path is.  This artificial weight is not the actual BBP complement;
it proves the logical point that a theorem about the path alone cannot imply
escape from complement-dependent exceptional fibres.  A positive theorem
must use the actual cross-depth complement, not only (SL1).

## 6. Bounded exact diagnostics

### `experiment`

The disjoint checker evaluates the four rational poles directly through
\(M_{12}=332149\), independently evaluates (SL1), and obtains:

| \(e\) | \(M_e\) | direct \(U_e\bmod3^e\) | shell limit \(\bmod3^e\) |
|---:|---:|---:|---:|
| 2 | 4 | 2 | 2 |
| 4 | 49 | 38 | 38 |
| 6 | 454 | 524 | 524 |
| 8 | 4,099 | 4,898 | 4,898 |
| 10 | 36,904 | 57,386 | 57,386 |
| 12 | 332,149 | 175,484 | 175,484 |

The shell algorithm continues without forming the depth-three-million
partial sum.  At 24 ternary digits it gives

\[
 U_\infty\equiv30006928667\pmod {3^{24}},                     \tag{SL23}
\]

whose least-significant-first base-nine digit pairs are

\[
                  2,4,6,6,8,2,6,0,4,5,8,0.                  \tag{SL24}
\]

The following are deliberately bounded falsifications only.

* No fraction \(a/b\), with \(3\nmid b\),
  \(|a|\le100000\), and \(1\le b\le100000\), agrees with (SL23).
* No monic quadratic \(X^2+AX+B\), with
  \(|A|,|B|\le100000\), vanishes at (SL23) modulo \(3^{24}\).
* The twelve base-nine digits in (SL24) obey no affine recurrence of order
  one, two, or three over \(\mathbb Z/9\mathbb Z\).

None of these finite statements proves irrationality, transcendence,
nonalgebraicity, or nonautomaticity.

## 7. Mathlib and primary-literature applicability

### `literature-checked`

Search and direct-check date: **2026-08-13 UTC**.  Search terms included
`p-adic Lerch transcendent harmonic sums`, `Dwork truncated hypergeometric
congruence`, `p-adic path automaton`, `Christol automatic algebraic series`,
and local mathlib symbol searches for `PadicInt`, `MahlerBasis`, `harmonic`,
and `automatic`.

| source | exact applicability |
|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | Supplies (SL4).  It states no 3-adic endpoint-limit or exceptional-fibre theorem. |
| Young, [*The p-adic Arakawa--Kaneko zeta functions and p-adic Lerch transcendent*](https://doi.org/10.1016/j.jnt.2015.01.022) | Constructs p-adic Lerch-type functions through convergent forward-difference series.  No checked identity identifies Young's function with the moving cutoff (SL5) or with (SL1), and the paper gives no selected-path correlation estimate. |
| Delaygue--Rivoal--Roques, [*On Dwork's p-adic Formal Congruences Theorem and Hypergeometric Mirror Maps*](https://arxiv.org/abs/1309.5902) | Gives Dwork congruences for specified generalized hypergeometric truncations.  No verified transformation places the four moving pole cutoffs (SL5) under those hypotheses. |
| Christol--Kamae--Mendès France--Rauzy, [*Suites algébriques, automates et substitutions*](https://doi.org/10.24033/bsmf.1926), Theorem 1 | Equates algebraicity of a formal power series over a finite field with automaticity of its coefficient sequence.  (SL1) is a characteristic-zero 3-adic scalar; no algebraic digit-generating series has been supplied. |
| Abram--Lagarias, [*p-adic path set fractals and arithmetic*](https://arxiv.org/abs/1210.2478) | Treats paths already given by finite automata and proves closure properties.  It does not manufacture a finite presentation for (SL1). |

The local mathlib files
`Mathlib/NumberTheory/Padics/MahlerBasis.lean` (SHA-256
`e411b105ed7ad06d43278dcb18397a3a509be1e2f9a357a20d6b685e44e92172`)
and `Mathlib/NumberTheory/Padics/AddChar.lean` (SHA-256
`70702d9ebf13663f2b0c4f3de89bccb543e3b99e45eaa48f503dff2e2a3c90f3`)
formalize Mahler bases for continuous 3-adic functions and additive
characters.  “Mahler basis” there is not a Mahler functional equation.
`Mathlib/NumberTheory/Harmonic/Defs.lean` (SHA-256
`7f51e807c25be865d66ff82a292b24c3dcfc51d694f7aa2797e07663c083f83e`)
defines ordinary harmonic numbers, not the progression shells (SL8).  No
local automatic-sequence or Christol recognizer was found.

No inspected source directly states (SL1).  This sentence records search
scope only; it is not a novelty claim.

## 8. Reproduction and frozen record

The standard-library
[checker](bbp_selected_limit_shell_series_20260813_check.py), SHA-256
`2959de8d8952fa2255d4f725f3bba9eea813fdc497d85951ef7a2c655b63c764`,
imports no sibling checker.  Its frozen
[record](bbp_selected_limit_shell_series_20260813_record.json), SHA-256
`3dd091a46e5f363e5c50f289c0c47ab932ab95c376a3287445acc1f23d9f4a8f`,
contains all displayed finite values and explicit negative-claim flags.

Run from the repository root:

```text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_selected_limit_shell_series_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_selected_limit_shell_series_20260813_check.py
```

The retained run took 5.88 seconds and about 15.5 MB maximum resident memory.
It reported:

```text
status=PASS
claim_label=experiment
limit_mod_3pow24=30006928667
base9_digits=2,4,6,6,8,2,6,0,4,5,8,0
direct_shell_matches=e2,e4,e6,e8,e10,e12
small_rational_height_le_100000=false
small_monic_quadratic_height_le_100000=false
affine_recurrence_orders_1_2_3=false
asserts_nonautomaticity=false
asserts_exceptional_path_decay=false
asserts_v1=false
record_sha256=3dd091a46e5f363e5c50f289c0c47ab932ab95c376a3287445acc1f23d9f4a8f
```

## 9. Sharp next theorem and coordination

The path-selection problem is no longer “find the missing 3-adic digits.”
They are exactly (SL1)--(SL2).  The sharp next theorem must couple those
digits to the actual complement.  One sufficient target is

\[
 \forall\eta>0\ \exists e_0\ \forall\hbox{ even }e\ge e_0:
 \quad
 \left|S_e\!\left(U_\infty10^{M_e}\bmod3^e;W_e^{\rm BBP}\right)\right|
 <\eta3^{e-2}.                                                 \tag{SL25}
\]

Any weaker useful theorem still has to exclude the selected residue from the
bounded bad fibres infinitely often using the **actual** cross-depth
complement.  A rational/algebraic/automatic classification of
\(U_\infty\) alone is not sufficient, by (SL22).

This branch registered watch `ultrapi-selected-limit-20260813` on
`local:pi-digits` for agent `codex-ultrapi-selected-limit`.  Its initial poll
was empty at cursor and delivered sequence 57,500, so no event was
acknowledged.  Observation events are coordination signals only and supplied
no mathematical evidence.
