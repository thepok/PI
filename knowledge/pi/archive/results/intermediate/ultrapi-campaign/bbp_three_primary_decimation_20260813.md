# BBP three-primary decimation and nested endpoint units

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's immutable local question and has no external source
URL; none is invented here.

Frozen parent:
[bbp_three_primary_epoch_20260813.md](bbp_three_primary_epoch_20260813.md),
SHA-256
`5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7`.

## Outcome and claim boundary

This branch proves at `proof sketch` level an exact three-adic decimation
law for the four BBP pole sums.  It explains why the leading three-primary
units at the last pre-drop and first drop depths form two nested inverse
systems as the even epoch grows.

The congruence is stronger than the bounded numerical pattern that exposed
it: it holds at every truncation depth and follows term by term from four
affine identities plus LTE.  At the special endpoints it gives two Cauchy
sequences in \(\mathbb Z_3^\times\), and the complete residual grids form
compatible ninefold refinements.

This does **not** control the other CRT coordinates.  The decimation is a
three-adic congruence, not an equality modulo one in the real circle.  It
therefore proves neither a return of the full BBP phase, a fixed-sixteen
return, nor canonical V1.  V1 remains a `conjecture`.

The companion bounded exact replay has label `experiment`.  The source
search has label `literature-checked`.  The four affine folds, four exponent
folds, and four one-term rational identities are `machine-checked` in T74;
the LTE summation, endpoint nesting, and real-shadow consequences remain a
`proof sketch`.  Nothing here is a `candidate resolution` or a
`verified resolution`.

## 1. Normalized four-pole problem

Write

\[
 B_M=\sum_{k=0}^M\sum_{i=1}^4 f_i(k),\qquad
 f_i(k)={c_i\over(a_ik+b_i)16^k},                         \tag{1}
\]

with

\[
\begin{array}{c|c|c|c}
i&a_i&b_i&c_i\\ \hline
1&8&1&4\\
2&2&1&-1/2\\
3&8&5&-1\\
4&4&3&-1/2.
\end{array}                                                \tag{2}
\]

This is exactly the Bailey--Borwein--Plouffe partial fraction

\[
 {4\over8k+1}-{1\over2(2k+1)}
 -{1\over8k+5}-{1\over2(4k+3)}.                           \tag{3}
\]

Let \(\mathbb Z_{(3)}\) denote the rationals whose denominators are prime
to three.  Congruences below are additive congruences in this localization;
they are not ordinary integer congruences unless explicitly stated.

## 2. Exact ninefold decimation

Define

\[
 d_i={8b_i\over a_i},\qquad m_i={8\over a_i}.
\]

For (2), these are the integer vectors

\[
             (d_1,d_2,d_3,d_4)=(1,4,5,6),\qquad
             (m_1,m_2,m_3,m_4)=(1,4,1,2).          \tag{4}
\]

The two identities

\[
 a_i(9r+d_i)+b_i=9(a_ir+b_i),\qquad
 8r+d_i=m_i(a_ir+b_i)                              \tag{5}
\]

hold for every \(r\ge0\).  Hence

\[
\boxed{
 9f_i(9r+d_i)-f_i(r)
 =f_i(r)\left(16^{-(8r+d_i)}-1\right).}            \tag{6}
\]

### `proof sketch`

Every coefficient \(c_i\), every \(m_i\), and 16 is a three-adic unit.  LTE
gives, for \(q>0\),

\[
                  v_3(16^q-1)=1+v_3(q).            \tag{7}
\]

With \(q=8r+d_i=m_i(a_ir+b_i)\), equations (6)--(7) give the exact
valuation

\[
\boxed{v_3\bigl(9f_i(9r+d_i)-f_i(r)\bigr)=1.}      \tag{8}
\]

On the other hand, if \(k\not\equiv d_i\pmod9\), then
\(9\nmid a_ik+b_i\), so

\[
                         v_3(9f_i(k))\ge1.          \tag{9}
\]

For \(q\in\mathbb Z\), put

\[
 F_i(q)=\begin{cases}\sum_{r=0}^qf_i(r),&q\ge0,\\0,&q<0.
       \end{cases}
\]

Pair the terms \(k\equiv d_i\pmod9\) in \(9F_i(M)\) with (6), and use
(9) on every unpaired term.  This proves, for every \(M\ge0\),

\[
\boxed{
 9B_M-\sum_{i=1}^4F_i\!\left(
       \left\lfloor{M-d_i\over9}\right\rfloor\right)
 \in3\mathbb Z_{(3)}.}                             \tag{10}
\]

No asymptotic argument or cancellation among different poles is used in
(10).  It is a finite termwise decimation identity.

## 3. Nested pre-drop and drop units

For even \(e\ge2\), put

\[
 A_e={3^e-1\over8},\qquad
 M_e^-=5A_e-1,\qquad M_e^+=5A_e.                   \tag{11}
\]

The frozen epoch theorem gives

\[
 v_3(B_{M_e^-})=-e,qquad v_3(B_{M_e^+})=-(e-1).   \tag{12}
\]

For every even \(e\ge4\), elementary substitution in (11) gives

\[
 M_e^-=9M_{e-2}^-+13,qquad
 M_e^+=9M_{e-2}^++5.                               \tag{13}
\]

At the pre-drop endpoint, the four cutoffs in (10) are

\[
 (M_{e-2}^-+1,M_{e-2}^-+1,M_{e-2}^-,M_{e-2}^-).   \tag{14}
\]

The two extra terms are \(f_1(M_{e-2}^+)\) and
\(f_2(M_{e-2}^+)\).  Their linear denominators are prime to three, so both
belong to \(\mathbb Z_{(3)}\).  Thus (10) implies

\[
\boxed{9B_{M_e^-}-B_{M_{e-2}^-}\in\mathbb Z_{(3)}.}         \tag{15}
\]

At the drop endpoint, the four cutoffs are

\[
 (M_{e-2}^+,M_{e-2}^+,M_{e-2}^+,M_{e-2}^+-1).     \tag{16}
\]

The missing term \(f_4(M_{e-2}^+)\) is also three-integral.  Hence

\[
\boxed{9B_{M_e^+}-B_{M_{e-2}^+}\in\mathbb Z_{(3)}.}         \tag{17}
\]

Normalize the endpoint units by

\[
 U_e^-=3^eB_{M_e^-},\qquad U_e^+=3^{e-1}B_{M_e^+}.           \tag{18}
\]

Multiplication of (15)--(17) by the relevant powers of three proves

\[
\boxed{
 U_e^-\equiv U_{e-2}^-\pmod {3^{e-2}\mathbb Z_{(3)}},
 \qquad
 U_e^+\equiv U_{e-2}^+\pmod {3^{e-3}\mathbb Z_{(3)}}.}      \tag{19}
\]

Both sequences are therefore Cauchy in \(\mathbb Z_3^\times\).  The first
six endpoint residues are

\[
\begin{array}{c|r|r|r}
e&M_e^-&U_e^-\bmod3^e&U_e^+\bmod3^{e-1}\\ \hline
2&4&2&2\\
4&49&38&23\\
6&454&524&185\\
8&4099&4898&914\\
10&36904&57386&18410\\
12&332149&175484&175874.
\end{array}                                                \tag{20}
\]

Table (20) is an `experiment`; the all-depth statement is (19).

## 4. Compatible residual grids

The frozen three-primary report writes the isolated residual coordinate as

\[
 x_{e,n}^-={U_e^-g_n\bmod3^{e-1}\over3^{e-1}},qquad
 g_n={10^n-16\over3}.                               \tag{21}
\]

The pre-drop period is \(T_e=3^{e-2}\).  Equation (19) implies, for every
fixed exponent \(n\),

\[
\boxed{9x_{e,n}^-\equiv x_{e-2,n}^-\pmod1.}         \tag{22}
\]

Here the right side is interpreted at its own denominator
\(3^{e-3}\).  Thus the complete \(T_e\)-point coset grid is a ninefold
refinement of the previous complete grid.  The same argument applies to the
drop grids, with periods \(3^{e-3}\) and \(3^{e-5}\).

This inverse-system statement is only about the isolated three-primary
factor.  If \(\chi_{e,n}\) denotes the other CRT coordinates, the actual
phase remains

\[
                         x_{e,n}^-+\chi_{e,n}\pmod1.          \tag{23}
\]

Neither (10) nor (19) relates \(\chi_{e,n}\) at successive epochs.

## 5. Uniform real shadow on a complete period

Although the decimation itself is three-adic, the entire pre-drop period is
well inside the range where the BBP truncation shadows pi.  With
\(T=3^{e-2}\),

\[
 M_e^-={45T-13\over8}\ge5(T-1).                    \tag{24}
\]

The positive BBP tail estimate gives

\[
 0<\pi-B_M\le {16^{-M}\over15(M+1)^2}.             \tag{25}
\]

For \(M=M_e^-\) and every \(M\le n<M+T\), equations (24)--(25) yield

\[
\begin{aligned}
 |(10^n-16)(\pi-B_M)|
 &\le {10^{M+T}16^{-M}\over15(M+1)^2}\\
 &\le { (8/5)^5\over15(M+1)^2}
       \left({31250\over32768}\right)^T.           \tag{26}
\end{aligned}
\]

Thus the full rational BBP phase on one complete three-primary period
uniformly shadows the corresponding actual pi-orbit segment with
exponentially decreasing error.  This makes control of the complement in
(23) sufficient and genuinely relevant.  It does not supply that control.

## 6. Reproducible exact replay

The standalone
[`checker`](bbp_three_primary_decimation_20260813_check.py), SHA-256
`abda4aa38bc575439320ecc60a44d0df8418be042b2bb0558f70f05c1c2dfc71`,
imports no branch checker.  It verifies 1,025 partial fractions, 2,052 exact
affine and termwise decimations, 14,567 nonlift integrality cases, 513
finite-sum congruences, the endpoint algebra through \(e=160\), and the
nested residues through \(e=12\).  Its retained output ends with

```text
asserts_joint_crt_control=false
asserts_fixed_return=false
asserts_v1=false
status=PASS
```

Every bounded row in the replay has label `experiment`; it is not the proof
of (10) or (19).

The algebraic input (5)--(6) is independently represented in
[`T74T74ThreePrimaryDecimation.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean),
SHA-256
`eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727`.
Its twelve theorem declarations are registered in
[`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean).  Direct compilation
with `--trust=0` and the central audit report only `propext`,
`Classical.choice`, and `Quot.sound`.  T74 does not state (7)--(10), the
endpoint epochs, the complementary phase, or V1.

## 7. Dated source and literature check

Search date: **2026-08-13 UTC**.

- Bailey--Borwein--Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9),
  Theorem 1 supplies (1)--(3), not (10), a decimal distribution theorem, or
  V1.  The pinned local PDF has SHA-256
  `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`.
- A bounded search for `BBP p-adic congruence`, `BBP 3-adic decimation`,
  `arctangent partial-sum p-adic congruence`, and `Dwork truncated-sum
  congruence` located general Dwork/hypergeometric frameworks but no theorem
  whose stated hypotheses directly produce (10) or control (23).
  Delaygue--Rivoal--Roques,
  [*On Dwork's p-adic Formal Congruences Theorem and Hypergeometric Mirror
  Maps*](https://arxiv.org/abs/1309.5902), concerns generalized
  hypergeometric series with rational parameters and mirror-map coefficient
  integrality.  No application of that machinery is asserted here; (10) is
  proved directly by (5)--(9).
- A mathlib search found the standard valuation and finite-sum tools but no
  existing declaration of this four-pole decimation.  T74 therefore records
  only the small algebraic core; it does not add an unproved valuation or
  distribution premise.

This is a bounded `literature-checked` applicability record, not a novelty
claim or an exhaustive survey.

## Sharp handoff

The special endpoint units are not unrelated samples: (19) makes them two
coherent three-adic limits, and (22) makes the complete residual grids an
exact inverse system.  Equation (26) simultaneously says that every such
full period is an exponentially accurate real shadow of a genuine pi-orbit
segment.

The missing step is still synchronized and Archimedean: prove that the other
CRT phase in (23) cannot cancel every refining grid, or obtain direct target
hitting for their sum.  Three-adic nesting alone gives no such estimate, so
canonical V1 remains a `conjecture`.
