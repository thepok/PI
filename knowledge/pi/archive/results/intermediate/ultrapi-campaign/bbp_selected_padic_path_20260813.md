# Selected coherent three-adic BBP path: exact lift formula and hidden carry

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's immutable local question and has no external source
URL; none is invented here.

Frozen inputs:

| input | SHA-256 |
|---|---|
| [three-primary decimation](bbp_three_primary_decimation_20260813.md) | `29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0` |
| [CF36 Gowers report](bbp_cf36_gowers_cube_persistence_20260813.md) | `3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e` |
| [actual exceptional-path report](bbp_exceptional_path_actual_complement_20260813.md) | `95e3b5d67784adefeda89357b3c652b7dd2b9d2550a26f00dedf2a0f489e01dc` |

## Outcome and claim boundary

Canonical V1 remains a `conjecture`. This branch proves no selected
correlation decay, no deterministic escape from the exceptional fibres, and
no occurrence theorem for arbitrary decimal words.

The exact new conclusions have label `proof sketch`.

1. If \(D_e=9B_{M_{e+2}}-B_{M_e}\), then for every even \(e\ge2\),

   \[
                 \boxed{D_e\equiv1\pmod {9\mathbb Z_{(3)}}}.             \tag{SP1}
   \]

2. This constant is not itself the selected lift digit. The next two
   previously hidden digits of \(U_e10^{M_e}\) contribute a carry
   \(\ell_e\), and the actual two-digit lift is

   \[
                              \boxed{\kappa_e\equiv\ell_e+1\pmod9}.       \tag{SP2}
   \]

3. Consequently the visible coefficient \(a_e\bmod3^e\) is not a
   sufficient Markov state. The exact rows \(e=4,6,8\) have the identical
   visible value \(a_e=29\), but their next lift pairs are \(0,0,4\).

The bounded replay has label `experiment`. The applicability search is
`literature-checked`. This branch adds no formal declaration and makes no
`machine-checked`, `candidate resolution`, or `verified resolution` claim.

## 1. Normalized path and ambiguous quantifiers

For even \(e\ge2\), set

\[
 M_e={5(3^e-1)\over8}-1,\qquad B_e=B_{M_e},\qquad
 U_e=3^eB_e\in\mathbb Z_{(3)}^\times,                              \tag{SP3}
\]

and select the canonical representative

\[
 a_e\equiv U_e10^{M_e}\pmod {3^e},\qquad 0\le a_e<3^e.             \tag{SP4}
\]

The phrase “finite-state description” has two different meanings. The narrow
one asks whether the visible residue \(a_e\) alone determines the next lift;
Section 3 disproves that. The broad one allows an unspecified finite auxiliary
state extracted from the whole BBP construction. Finite data cannot disprove
every such encoding, and no such all-encodings claim is made here.

## 2. Inspectable modulo-nine defect calculation

Write the four poles as

\[
 f_i(k)={c_i\over(a_i k+b_i)16^k},\qquad
 (a_i,b_i,c_i)=(8,1,4),(2,1,-1/2),(8,5,-1),(4,3,-1/2),             \tag{SP5}
\]

and put \(d=(1,4,5,6)\), \(m=(1,4,1,2)\). The frozen exact
decimation is

\[
 9f_i(9r+d_i)-f_i(r)
   =f_i(r)\bigl(16^{-m_i(a_ir+b_i)}-1\bigr).                       \tag{SP6}
\]

Let \(M=M_e\) and \(N=M_{e+2}=9M+13\). The four paired cutoffs at \(N\)
are

\[
                         (M+1,M+1,M,M).                            \tag{SP7}
\]

Thus

\[
\begin{aligned}
D_e={}&f_1(M+1)+f_2(M+1)\\
 &+\sum_{i=1}^4\sum_{r\le Q_i}
       \bigl(9f_i(9r+d_i)-f_i(r)\bigr)
 +\sum_{i=1}^4\sum_{\substack{0\le k\le N\\k\not\equiv d_i\ (9)}}
       9f_i(k),                                                     \tag{SP8}
\end{aligned}
\]

where \(Q=(M+1,M+1,M,M)\).

This expression can be reduced modulo nine without an ellipsis:

- Write \(a_ir+b_i=3^ju\), \(3\nmid u\). From \(16=1+15\), the
  paired error in (SP6) satisfies

  \[
  {9f_i(9r+d_i)-f_i(r)\over3}\equiv c_im_i\pmod3.                  \tag{SP9}
  \]

  Hence one paired term contributes \(3(c_im_i\bmod3)\) modulo nine.
  Since \(M\equiv4\pmod9\), the four pair counts modulo three are
  \(0,0,2,2\).

- A nonpaired term matters modulo nine only when
  \(v_3(a_ik+b_i)=1\). If \(a_ik+b_i=3u\), its contribution is

  \[
                            9f_i(k)\equiv3c_iu^{-1}\pmod9.          \tag{SP10}
  \]

  In every complete block \(k\bmod9\), the two height-one units are
  \(u=1,2\) and cancel modulo three. Since \(N\equiv4\pmod9\), only
  the final residues \(k=0,\ldots,4\) remain.

- The regular boundary terms use \(M+1\equiv5\pmod9\).

The entire pole-by-pole calculation is:

| pole \((a_i,b_i,c_i;m_i)\) | paired errors | nonpaired final residues | regular boundary | total mod \(9\) |
|---|---:|---:|---:|---:|
| \((8,1,4;1)\) | \(0\) | \(6\) | \(2\) | \(8\) |
| \((2,1,-1/2;4)\) | \(0\) | \(3\) | \(5\) | \(8\) |
| \((8,5,-1;1)\) | \(3\) | \(6\) | \(0\) | \(0\) |
| \((4,3,-1/2;2)\) | \(3\) | \(0\) | \(0\) | \(3\) |

The column total is

\[
                               8+8+0+3\equiv1\pmod9,               \tag{SP11}
\]

which proves (SP1). The small boundary \(e=2\) obeys the same residue
calculation; the checker also evaluates the full exact rational values for
\(e=2,4,6\), independently obtaining \(D_e\bmod9=1\) in every case.

Multiplying (SP1) by \(3^e\) gives the equivalent exact shell law

\[
                         U_{e+2}-U_e\equiv3^e\pmod {3^{e+2}}.      \tag{SP12}
\]

## 3. Exact lift formula and the hidden carry

Let \(x_e\) be the canonical residue

\[
 x_e\equiv U_e10^{M_e}\pmod {3^{e+2}},\qquad
 0\le x_e<3^{e+2},                                                 \tag{SP13}
\]

and define

\[
                       \ell_e={x_e-a_e\over3^e}\in\{0,\ldots,8\}.  \tag{SP14}
\]

Since \(M_{e+2}-M_e=5\cdot3^e\), LTE gives

\[
                         10^{M_{e+2}-M_e}\equiv1\pmod {3^{e+2}}.   \tag{SP15}
\]

Combining (SP12)--(SP15), and using \(10^{M_e}\equiv1\pmod9\), gives

\[
\begin{aligned}
 a_{e+2}
 &\equiv U_{e+2}10^{M_{e+2}}\\
 &\equiv x_e+3^eD_e10^{M_e}\\
 &\equiv a_e+3^e(\ell_e+1)\pmod {3^{e+2}}.                         \tag{SP16}
\end{aligned}
\]

Writing \(a_{e+2}=a_e+\kappa_e3^e\) proves (SP2). This resolves the
tempting but false inference “\(D_e\equiv1\pmod9\), hence every lift is
one”: that inference drops \(\ell_e\), precisely the two digits absent from
\(a_e\bmod3^e\).

## 4. Exact bounded path data

### `experiment`

The checker recomputes \(U_e\bmod3^{e+2}\) directly from every four-pole
term:

| \(e\) | \(M_e\) | \(U_e\bmod3^e\) | \(a_e\) | hidden \(\ell_e\) | next lift \(\kappa_e\) |
|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 2 | 2 | 2 | 3 |
| 4 | 49 | 38 | 29 | 8 | 0 |
| 6 | 454 | 524 | 29 | 8 | 0 |
| 8 | 4,099 | 4,898 | 29 | 3 | 4 |
| 10 | 36,904 | 57,386 | 26,273 | 2 | 3 |
| 12 | 332,149 | 175,484 | 203,420 | 2 | 3 |
| 14 | 2,989,354 | 3,364,130 | 1,797,743 | 0 | 1 |

The \(e=14\) row is an exact modular sum through all 2,989,355 terms, not
an FFT or floating calculation. Equations (SP1)--(SP16) then give the exact
prediction

\[
             a_{16}=a_{14}+3^{14}=1,797,743+4,782,969=6,580,712.   \tag{SP17}
\]

The finite word of lift pairs is \(3,0,0,4,3,3,1\). It satisfies no
affine recurrence of order one or two over \(\mathbb Z/9\mathbb Z\), but six
transitions are far too few to support an automaticity conclusion.

The repeated visible state \(a_e=29\) at \(e=4,6,8\), followed by next
lifts \(0,0,4\), is an exact counterexample to the state choice \(a_e\)
alone. It is not a counterexample to every possible finite-state encoding:
one could include \(\ell_e\), a pole-shell state, or arbitrarily much hidden
precision. Proving that no fixed finite augmentation suffices would require
an all-depth complexity theorem not obtained here.

## 5. Reproduction

The standalone
[checker](bbp_selected_padic_path_20260813_check.py) imports no branch
checker. Run from the repository root:

~~~text
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_selected_padic_path_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_selected_padic_path_20260813_check.py
~~~

The final run reported `PASS` in 24.16 seconds and used 17,792 KiB maximum
resident memory. The checker SHA-256 is
`24f8858a1c80a4df6710c21d5aa09d8d7d4e2a402f789c0c41c9e6b95ff74563`;
its exact-record SHA-256 is
`fb3e99511c46f3cbe2d6772dcbae5fc7e33516cde7ef9c1a1ccf2c4035e1d9a0`.
It explicitly prints:

~~~text
visible_state_collision=a29_next_lifts_0_0_4
asserts_finite_state_impossibility_for_all_encodings=false
asserts_exceptional_path_decay=false
asserts_v1=false
~~~

## 6. Mathlib and primary-literature applicability

### `literature-checked`

Search date: **2026-08-13 UTC**.

- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9),
  supplies the four-pole series (SP5), not a selected 3-adic path,
  finite automaton, exceptional-fibre escape, or decimal-distribution theorem.
- Delaygue--Rivoal--Roques,
  [*On Dwork's p-adic Formal Congruences Theorem and Hypergeometric Mirror
  Maps*](https://arxiv.org/abs/1309.5902), proves congruences for specified
  generalized hypergeometric truncations. No verified transformation puts the
  moving four-pole endpoint sum (SP3) under its hypotheses.
- Abram--Lagarias,
  [*p-adic path set fractals and arithmetic*](https://arxiv.org/abs/1210.2478),
  studies sets whose digit paths are already presented by finite automata and
  closure under rational \(p\)-adic arithmetic. It does not prove that the
  BBP path has such a presentation.
- Christol's theorem concerns algebraicity of formal power series over finite
  fields and finite \(p\)-kernels. This object is a characteristic-zero moving
  truncation in \(\mathbb Z_3\); no algebraic formal-series equation or finite
  kernel has been established. Real-base automatic-number transcendence
  theorems likewise cannot infer nonautomaticity of this 3-adic path merely
  from the known transcendence of real \(\pi\).
- A local mathlib search found standard \(p\)-adic valuation and finite-sum
  infrastructure, but no automatic-sequence library, no theorem recognizing
  these BBP endpoint digits, and no declaration that yields exceptional-fibre
  escape.

This is a bounded applicability record, not an exhaustive survey or a novelty
claim.

## 7. Coordination and sharp handoff

This branch registered descendant watch `ultrapi-padic-path-20260813` on
`local:pi-digits` for agent `codex-ultrapi-padic-path`. Its initial poll was
empty at cursor and delivered sequence 57,498, so no event was acknowledged.
Observation events are coordination signals only and supplied no mathematical
evidence.

The selected path is now exact one layer deeper: decimation contributes the
universal pair \(1\), but the true lift appears only after adding the hidden
pair \(\ell_e\). The repeated-\(29\) collision proves that the visible
coefficient is not a Markov state. What remains is an all-depth theorem on the
hidden carries—or, preferably, a direct estimate of the selected relative
correlations. Existing \(p\)-adic congruence, automatic-sequence, and metric
exceptional-path results do not supply either step, so canonical V1 remains a
`conjecture`.
