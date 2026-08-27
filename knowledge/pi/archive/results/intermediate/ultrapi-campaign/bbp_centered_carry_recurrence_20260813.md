# Sevenfold BBP centered carries: exact cross-depth recurrence and the linear-gap barrier

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen parent inputs:

- [bbp_fixed_period_carry_attack_20260813.md](bbp_fixed_period_carry_attack_20260813.md),
  SHA-256
  `bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55`;
- [bbp_fixed_period_carry_attack_20260813_independent_audit.md](bbp_fixed_period_carry_attack_20260813_independent_audit.md),
  SHA-256
  `ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91`;
- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9`;
- [bbp_all_depth_two_adic_independent_audit.md](bbp_all_depth_two_adic_independent_audit.md),
  SHA-256
  `846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007`.

## Outcome and claim boundary

No positive lower density of nonzero centered carries was proved. Therefore
(40bl) and canonical V1 remain a `conjecture`. In particular, this report is
not a proof that every finite decimal word occurs in pi.

The branch gives an exact cross-depth recurrence for the rational carry
stream in (40bk), including its changing odd denominator and its selected
two-adic numerator coordinate. The deductions below have label `proof sketch`.

1. If \(D_n,U_{n,P},z_{n,P},S_{n,P}\) are the exact denominator,
   numerator, nearest integer, and centered numerator at BBP depth \(7n\),
   then one sevenfold block gives

   \[
   D_{n+1}=\Lambda_nD_n,\qquad
   U_{n+1,P}=10\Lambda_nU_{n,P}+J_{n,P},              \tag{1}
   \]

   and

   \[
   S_{n+1,P}=10\Lambda_nS_{n,P}+J_{n,P}
      -\widehat\gamma_{n,P}D_{n+1}.                   \tag{2}
   \]

2. The carry is the exact nearest-integer quotient

   \[
   \widehat\gamma_{n,P}
   =\left\lfloor
      {10\Lambda_nS_{n,P}+J_{n,P}\over D_{n+1}}+{1\over2}
    \right\rfloor .                                   \tag{3}
   \]

   Iteration gives an exact simultaneous integer-interval test for every
   zero-carry block of length \(h\).
3. For every \(P\geq1\) and \(n\geq1\),

   \[
                  \boxed{v_2(S_{n,P})=v_2(7n+1).}     \tag{4}
   \]

   Hence \(S_{n,P}/2^{v_2(7n+1)}\) is the actual selected odd numerator.
4. The carry term in (2) vanishes modulo every divisor of \(D_{n+1}\).
   Both the full two-adic coordinate and all new odd-LCM coordinates are
   therefore carry-blind as congruences. The missing operation is selection
   of the centered Archimedean representative.
5. Combining (4) with the available BBP tail estimate does not improve the
   known linear zero-run bound. The published irrationality measure gives

   \[
   h < {763\over125}n
       +{763\over125}\log_{10}(10^P-1)-\log_{10}2     \tag{5}
   \]

   for every sufficiently late length-\(h\) zero block. This is
   \(h=O_P(n)\), not the uniform or average gap control needed for positive
   carry density.
6. No finite autonomous automaton, periodic clock, or deterministic
   finite-order recurrence using only previous carries can generate the
   eventual stream. Its output would be eventually periodic and would make
   \((10^P-1)\pi\) rational. A transducer receiving an unbounded coefficient
   or index stream is not excluded.

The exact replay has label `experiment`. The dated source audit is
`literature-checked`. Nothing new here is `machine-checked`, a
`candidate resolution`, or a `verified resolution`.

## 1. Normalized target and quantifiers

Canonical V1 asks whether, for every \(m\geq0\) and every decimal word
\((w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\), there is a position
\(r\geq0\) at which the word occurs contiguously in the decimal expansion
of pi. Leading zeroes are allowed and the empty word is vacuous. This is
separate from the false assertion that every infinite sequence occurs as a
suffix and from the weaker subsequence reading.

The frozen adjacent-BBP route reduces its fixed-period noncollapse side to
positive lower density, for every fixed \(P\geq1\), of

\[
\widehat\gamma_{n,P}
 =\widehat z_{n+1,P}-10\widehat z_{n,P},\qquad
\widehat z_{n,P}
 =\left\lfloor(10^P-1)10^nB_{7n}+{1\over2}\right\rfloor .
                                                               \tag{6}
\]

The period \(P\) is fixed before \(n\to\infty\), and its lower-density
constant may depend on \(P\). The desired adjacent-matching argument needs
the property for every \(P\) along the same selected empirical subsequence.
This report fixes one arbitrary \(P\geq1\) in each derivation and does not
exchange those quantifiers.

## 2. Exact four-pole integers at depth \(7n\)

Write the combined BBP coefficient as

\[
a(k)={c_k\over d_k},\qquad
c_k=120k^2+151k+47,\qquad
d_k=(2k+1)(4k+3)(8k+1)(8k+5),                       \tag{7}
\]

and put

\[
L_m=\operatorname{lcm}(d_0,\ldots,d_m),\qquad
A_m=\sum_{k=0}^m c_k16^{m-k}{L_m\over d_k}.          \tag{8}
\]

Every \(d_k\), hence every \(L_m\), is odd, and

\[
                         B_m={A_m\over16^mL_m}.       \tag{9}
\]

For \(q_P=10^P-1\), define

\[
\begin{aligned}
D_n&=2^{27n}L_{7n},&
U_{n,P}&=q_P5^nA_{7n},\\
z_{n,P}&=\left\lfloor{U_{n,P}\over D_n}+{1\over2}\right\rfloor,&
S_{n,P}&=U_{n,P}-D_nz_{n,P}.
\end{aligned}                                       \tag{10}
\]

Then \(U_{n,P}/D_n=q_P10^nB_{7n}\) and

\[
                         -D_n\leq2S_{n,P}<D_n.        \tag{11}
\]

The half-open convention in (11) exactly matches `floor(x+1/2)`.

Now isolate one seven-term increment:

\[
\begin{aligned}
R_n&={L_{7n+7}\over L_{7n}},\\
H_n&=\sum_{j=1}^7
 c_{7n+j}16^{7-j}{L_{7n+7}\over d_{7n+j}},\\
\Lambda_n&=2^{27}R_n,\qquad
J_{n,P}=q_P5^{n+1}H_n.
\end{aligned}                                       \tag{12}
\]

All four quantities are integers and \(R_n\) is odd. Splitting (8) at
\(7n\) gives

\[
                  A_{7n+7}=16^7R_nA_{7n}+H_n.        \tag{13}
\]

Multiplying (13) by \(q_P5^{n+1}\), and using
\(5\cdot16^7=10\cdot2^{27}\), proves (1). Substituting
\(U_{n,P}=D_nz_{n,P}+S_{n,P}\) proves (2), while division by
\(D_{n+1}\) proves (3). In particular,

\[
\boxed{
\widehat\gamma_{n,P}=0
\iff
-D_{n+1}\leq
2(10\Lambda_nS_{n,P}+J_{n,P})<D_{n+1}.}             \tag{14}
\]

The normalized forcing has the exact interpretation

\[
{J_{n,P}\over D_{n+1}}
 =q_P10^{n+1}(B_{7n+7}-B_{7n}).                      \tag{15}
\]

Equations (1)--(3) form a closed rational recurrence. No decimal digit of pi
and no nesting assumption on reduced odd denominators enters it.

## 3. Exact two-adic valuation and fresh odd moduli

The independently audited all-depth BBP calculation proves as a
`proof sketch` that, for every \(m\geq1\), the reduced denominator of
\(B_m\) has two-adic valuation

\[
                         4m-v_2(m+1).                 \tag{16}
\]

Since (9) has odd \(L_m\), this is equivalent to

\[
                         v_2(A_m)=v_2(m+1).           \tag{17}
\]

The multiplier \(q_P5^n\) is odd, so

\[
                         v_2(U_{n,P})=v_2(7n+1).      \tag{18}
\]

For \(n\geq1\), \(v_2(7n+1)<27n=v_2(D_n)\). The two
terms in \(S_{n,P}=U_{n,P}-D_nz_{n,P}\) have unequal valuations, and the
ultrametric equality case proves (4). Equivalently, with
\(r_n=v_2(7n+1)\),

\[
\overline S_{n,P}:={S_{n,P}\over2^{r_n}}\in2\mathbb Z+1. \tag{19}
\]

The selected odd-numerator recurrence is therefore

\[
2^{r_{n+1}}\overline S_{n+1,P}
 =10\Lambda_n2^{r_n}\overline S_{n,P}+J_{n,P}
  -\widehat\gamma_{n,P}2^{27(n+1)}L_{7n+7}.          \tag{20}
\]

Modulo \(2^{27(n+1)}\), modulo \(L_{7n+7}\), or modulo any
prime power dividing \(D_{n+1}\), the carry term in (20) is zero. Thus
the entire congruence class of \(S_{n+1,P}\) modulo \(D_{n+1}\) is
carry-blind. This does not rule out a future argument that combines
odd-prime data with an Archimedean estimate; it rules out reading the carry
from those congruences alone.

The odd increment itself is locally small in a rigorous sense. Since

\[
L_{7n+7}=\operatorname{lcm}
 (L_{7n},d_{7n+1},\ldots,d_{7n+7}),
\]

prime valuations give

\[
R_n\mid\prod_{j=1}^7d_{7n+j}.                        \tag{21}
\]

In particular,

\[
R_n\leq
\bigl((14n+15)(28n+31)(56n+57)(56n+61)\bigr)^7,     \tag{22}
\]

so one fresh odd-LCM increment contains only \(O(\log n)\) bits. The
checker also gives exact bounded counterexamples to two tempting local
rules. At each of the five zero carries \(n=761,\ldots,765\),
\(R_n>1\) and \(\gcd(J_{n,1},R_n)=1\); their bit lengths are respectively
75, 76, 74, 106, and 31. Hence neither a nontrivial fresh odd modulus nor
unit forcing at every fresh factor locally forces a nonzero carry. These
computed rows have label `experiment`; their role is to falsify those
specific universal shortcuts, not to establish asymptotics.

## 4. Exact \(h\)-step recurrence and null-block criterion

For \(h\geq1\), put

\[
\Lambda_{n,h}={D_{n+h}\over D_n}
 =2^{27h}{L_{7(n+h)}\over L_{7n}},                   \tag{23}
\]

and define the integer

\[
J_{n,h,P}=U_{n+h,P}-10^h\Lambda_{n,h}U_{n,P}.        \tag{24}
\]

Equivalently,

\[
J_{n,h,P}=\sum_{t=0}^{h-1}10^{h-1-t}
 {D_{n+h}\over D_{n+t+1}}J_{n+t,P}.                 \tag{25}
\]

The weighted carry is

\[
\Gamma_{n,h,P}=z_{n+h,P}-10^hz_{n,P}
 =\sum_{t=0}^{h-1}10^{h-1-t}\widehat\gamma_{n+t,P}. \tag{26}
\]

Iteration gives

\[
\begin{aligned}
U_{n+h,P}&=10^h\Lambda_{n,h}U_{n,P}+J_{n,h,P},\\
S_{n+h,P}&=10^h\Lambda_{n,h}S_{n,P}+J_{n,h,P}
 -\Gamma_{n,h,P}D_{n+h}.
\end{aligned}                                       \tag{27}
\]

For \(1\leq t\leq h\), set

\[
T_{n,t,P}=10^t\Lambda_{n,t}S_{n,P}+J_{n,t,P}.        \tag{28}
\]

Every prefix aggregate in (26) is zero exactly when its nearest-integer
quotient is zero. Recursively, all individual carries in the block vanish
exactly when all prefix aggregates vanish. Therefore

\[
\boxed{
\widehat\gamma_{n,P}=\cdots=\widehat\gamma_{n+h-1,P}=0
\iff
\forall\,1\leq t\leq h:\quad
-D_{n+t}\leq2T_{n,t,P}<D_{n+t}.}                    \tag{29}
\]

This is an exact criterion, not an asymptotic exclusion of long blocks.

## 5. Why the recurrence does not beat the linear gap bound

Let

\[
\widehat e_{n,P}={S_{n,P}\over D_n}.
\]

If (29) holds, then (27), divided by \(D_{n+h}\), gives

\[
\widehat e_{n+h,P}
 =10^h\widehat e_{n,P}
  +q_P10^{n+h}(B_{7(n+h)}-B_{7n}).                  \tag{30}
\]

Since \(|\widehat e_{n+h,P}|\leq1/2\),

\[
|\widehat e_{n,P}|
 \leq {1\over2\,10^h}
 +q_P10^n(B_{7(n+h)}-B_{7n})
 \leq {1\over2\,10^h}
 +{q_P5^n\over2^{27n}15(7n+1)^2}.                  \tag{31}
\]

Equation (4) supplies only

\[
|\widehat e_{n,P}|
 \geq {2^{v_2(7n+1)}\over2^{27n}L_{7n}}.            \tag{32}
\]

The available upper tail allowance in (31), divided by the grid bound in
(32), is

\[
{q_P5^nL_{7n}\over15(7n+1)^2\,2^{v_2(7n+1)}}
 \geq {9\,5^n\over15(7n+1)^3}.                      \tag{33}
\]

The last expression exceeds one at \(n=8\) and increases thereafter.
Indeed, for \(n\geq2\), \(7n+8\leq11n\), \(7n+1>7n\), and
\(5\cdot7^3>11^3\). Thus (31)--(32) remain compatible even after the
\(10^{-h}\) term is discarded. The exact valuation plus the standard tail
bound imposes no restriction on \(h\) for \(n\geq8\). A stronger result
needs signed Archimedean separation between the selected numerator and the
BBP tail.

The known linear restriction comes from the irrationality measure. The
parent audit uses the published bound \(\mu(\pi)<888/125\). Put
\(M=888/125\). For fixed \(P\), the sevenfold rational carries eventually
equal the true centered carries of \(q_P\pi\). If a sufficiently late
length-\(h\) block vanishes and \(z_{n,P}\) denotes the true nearest
integer, then

\[
\left|\pi-{z_{n,P}\over q_P10^n}\right|
 <{1\over2q_P10^{n+h}}.                              \tag{34}
\]

After another fixed-\(P\) onset, the definition of the published
irrationality-measure bound gives

\[
\left|\pi-{z_{n,P}\over q_P10^n}\right|
 >(q_P10^n)^{-M}.                                    \tag{35}
\]

Comparing (34)--(35) and taking base-ten logarithms proves (5). Its slope is
\(M-1=763/125\). It permits geometric carry gaps and hence only the
already audited logarithmic lower count. Even a merely sublinear pointwise
gap bound would not itself prove positive density; (40bl) needs uniform or
averaged linear-frequency input.

## 6. Finite-state and local-pattern no-go

The true carries give the convergent centered expansion

\[
q_P\pi=z_{0,P}+\sum_{n\geq0}{\gamma_{n,P}\over10^{n+1}}. \tag{36}
\]

The rational carries \(\widehat\gamma_{n,P}\) agree with them after a
finite index. If their eventual stream were produced by a finite autonomous
state machine, its bounded output would be eventually periodic. The sum in
(36) would then be rational, making \(q_P\pi\), hence pi, rational.

The same argument excludes an eventual fixed-order recurrence

\[
\widehat\gamma_n
 =F(\widehat\gamma_{n-r},\ldots,\widehat\gamma_{n-1}) \tag{37}
\]

and a finite periodic dependence on \(n\): include the clock residue in
the finite state. It does not exclude a transducer fed the unbounded
integers \(R_n,H_n\), the digits of \(n\), or another nonperiodic input.

## 7. Exact replay and finite falsification

The companion
[bbp_centered_carry_recurrence_20260813_check.py](bbp_centered_carry_recurrence_20260813_check.py)
has SHA-256 `b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff`.
It uses only integers and `Fraction`
for structural checks. It:

- pins eleven canonical, parent-audit, primary-source, and certified-prefix
  artifacts;
- reconstructs \(L_m,A_m\) through \(m=7000\), verifies that every
  \(R_n\) divides the product of its seven new denominators, and checks
  1,000 exact sevenfold numerator blocks;
- replays 3,000 one-step denominator, numerator, centered-residue, carry,
  and valuation identities for \(P=1,2,4\);
- checks six independent \(h\)-step recurrences and every prefix
  inequality in their null-block criteria;
- exhibits an exact rational \(P=1\) five-zero block at carry positions
  \(761,\ldots,765\), including the five fresh odd-unit witnesses in
  Section 3;
- finds incompatible continuations for identical carry contexts of orders
  one through six; this only corroborates the general eventual-periodicity
  argument on a finite prefix;
- independently reads the certified 1,048,596-digit prefix of pi and checks
  1,048,571 true \(P=1\) carries. The longest observed zero block has
  length six at position 710,099, and 943,633 observed carries are nonzero;
  and
- verifies that the true and rational carry windows agree exactly from
  positions 755 through 771, including the rational five-zero block.

Every bounded value in this list has label `experiment`. In particular,
the observed fraction \(943633/1048571\) and the observed zero runs prove
no asymptotic density or bounded-gap theorem.

Replay from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py
```

The retained run reports `status: PASS` and explicitly reports
`asserts_positive_carry_density: false`,
`asserts_sublinear_zero_run_bound: false`, and `asserts_v1: false`.

## 8. Literature and mathlib applicability audit

Status of this bounded search: `literature-checked` on **2026-08-13 UTC**.

| source | checked use and boundary | local pin |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | Supplies the four-pole series behind (7)--(9), not a centered-carry density theorem. | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Bailey--Crandall, [*On the Random Character of Fundamental Constant Expansions*](https://doi.org/10.1080/10586458.2001.10504441), Hypothesis A and Theorems 2.7--3.1 | Gives the rational-perturbation recurrence and finite-attractor/rationality boundary. Its distribution alternative is explicitly a hypothesis, and its pi conclusion is base 2/16 rather than decimal. | `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2) | Audits the perturbed-radix framework. It has no theorem controlling the selected cross-depth odd numerator in (20). | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Zeilberger--Zudilin, [*The Irrationality Measure of Pi is at Most 7.103205334137...*](https://doi.org/10.2140/moscow.2020.9.407) | Supplies the exponent in (34)--(35), yielding (5) but not positive density. | `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` |
| Local T17 certified decimal prefix | Supplies an independently enclosed prefix for finite true-carry replay only. | digit file `77eeccb0067283e14c460b33dc230de54ef15c2e825fc2a35c984fb6984bf684`; report `f566dd992fa7897797a83022741eec709978bb278c4f247d698d73348999719e` |

Fresh searches covered BBP rational recurrences, centered-digit density,
digit changes inferred from irrationality measures, finite-state
descriptions of BBP orbits, and fixed-number lacunary distribution. They
found metric or algebraic-number digit theorems and the conditional
Bailey--Crandall program, but no primary theorem proving positive density of
these fixed-pi decimal carries. This bounded absence record is not a novelty
claim.

The local mathlib search found real digit/floor infrastructure and the
repository's effective irrationality interfaces, but no theorem converting
(1)--(3) into nonzero-carry density. No Lean declaration was added, so no
new axiom-audit registration or formal gate is claimed.

## Sharp handoff

For every fixed \(P\), the remaining target is the explicit integer process

\[
(D_n,S_{n,P})\longmapsto
\left(
\Lambda_nD_n,
10\Lambda_nS_{n,P}+J_{n,P}
-D_{n+1}\left\lfloor
 {10\Lambda_nS_{n,P}+J_{n,P}\over D_{n+1}}+{1\over2}
\right\rfloor
\right).                                             \tag{38}
\]

Its two-adic valuation is (4), its fresh odd denominator is \(R_n\), and
its zero blocks are exactly (29). Modulo the changing denominator, however,
the carry disappears; the standard tail is too wide to turn (4) into a gap
exclusion; and irrationality measure stops at (5). A viable continuation
must prove Archimedean anti-concentration or signed separation for the
selected odd numerator in (38), averaged over linearly many depths.
Valuation-only, autonomous finite-state, and finite local-pattern arguments
do not close (40bl). No such separation is proved here, so canonical V1
remains a `conjecture`.
