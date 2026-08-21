# BBP character breakthrough attack: scalar monotone forcing and its exact wall

Audit date: **2026-08-13 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Provenance: the immutable local question was created from Marcel's request and
contains no external source URL; none is invented here.

## Normalized statement and quantifier boundary

Canonical V1 asks whether, for every \(m\geq0\) and every word
\((d_1,\ldots,d_m)\in\{0,\ldots,9\}^m\), there is an index \(n\geq0\)
at which those digits occur contiguously in the decimal expansion of pi.
Leading zeroes are allowed and the empty word is vacuous.  The two other
readings recorded in the source remain excluded: the assertion that every
infinite word occurs as a tail is false, while the assertion that every
infinite word occurs as a subsequence amounts to every digit recurring
infinitely often and is also open.

The audited T69/Furstenberg bridge and the parent one-character report reduce
V1 to the fixed return

\[
 \liminf_{n\to\infty}\|(10^n-16)B_n\|_{\mathbb T}=0,             \tag{1}
\]

where \(B_n\) is the rational BBP partial sum below.  This report attacks (1),
not normality, a metric almost-everywhere statement, or a finite digit search.

## Outcome and claim status

No proof of (1) or V1 was obtained.  Canonical V1 remains a `conjecture`.

There is a material coefficient-specific reduction, with status `proof
sketch`:

1. Eliminating the cumulative BBP partial sum from two consecutive forcing
   equations gives, for every \(n\geq0\), one scalar second-order recurrence

   \[
    R_{n+2}-11R_{n+1}+10R_n=h_n,                    \tag{2}
   \]

   with a completely local two-term four-pole forcing \(h_n\).
2. The associated rational quantity

   \[
    C_n=R_{n+1}-10R_n                              \tag{3}
   \]

   is a strictly decreasing upper approximation to \(144\pi\) for every
   \(n\geq2\).  Its error and the total remaining variation are explicitly
   bounded at the BBP scale:

   \[
    0<C_n-144\pi<\frac{(5/8)^{n+1}}{(n+1)^2},
    \qquad
    \sum_{j=N}^{\infty}|h_j|=C_N-144\pi
    \quad(N\geq2).                                  \tag{4}
   \]
3. If \(Z_n=e(R_n)\) and \(W_n=Z_{n+1}/Z_n\), then

   \[
    W_{n+1}=W_n^{10}e(h_n).                         \tag{5}
   \]

   This removes \(B_n\) from the local recurrence.  However, \(W_n\) is
   exponentially close to the unforced derivative orbit
   \(e(9\cdot10^n\pi)\), and the required \(Z_n\)-return is the **partial
   product** return

   \[
       \limsup_n\Re\prod_{j=0}^{n-1}W_j=1.          \tag{6}
   \]

   Thus (5) is an exact scalarization, but not new cancellation.
4. A rational separator preserves strict one-sided monotone forcing,
   summable forcing with exponential base \(5/8\), rational roots of unity,
   and even \(W_n\to1\), while its noninitial partial products stay at least
   \(1/8\) from the
   identity \(1\) in circle phase.  Hence no theorem using only those local properties can
   establish (6).  A successful use of (2)--(5) must exploit more of the
   exact four-pole values than their sign, monotonicity, or summability.

The finite replay is an `experiment`.  The bounded source search is
`literature-checked` on the displayed date.  Nothing here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. BBP definitions and a useful coefficient inequality

For integers \(k,n\geq0\), put

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 b_k=\frac{a(k)}{16^k},\qquad
 B_n=\sum_{k=0}^n b_k,                              \tag{7}
\]

and

\[
 q_n=10^n-16,\qquad R_n=q_nB_n.                    \tag{8}
\]

The parent report proves

\[
 0<\pi-B_n\leq\frac{16^{-n}}{15(n+1)^2}.           \tag{9}
\]

Besides \(0<a(k)<k^{-2}\) for \(k\geq1\), the exact difference

\[
 a(k)-a(k+1)=\frac{3P(k)}
 {(2k+1)(2k+3)(4k+3)(4k+7)
  (8k+1)(8k+5)(8k+9)(8k+13)},                      \tag{10}
\]

where

\[
 P(k)=40960k^5+220672k^4+453632k^3+443480k^2
      +206712k+36903,                              \tag{11}
\]

shows that \(a(k)\) is strictly decreasing for all \(k\geq0\).  In
particular,

\[
                         0<b_{k+1}<\frac{b_k}{16}.  \tag{12}
\]

All signs in what follows ultimately come from this elementary four-pole
identity.

## 2. Elimination of the cumulative partial sum

Since \(q_{n+1}=10q_n+144\) and \(B_{n+1}=B_n+b_{n+1}\),

\[
 \begin{aligned}
 C_n:=R_{n+1}-10R_n
 &=144B_n+q_{n+1}b_{n+1}.                          \tag{13}
 \end{aligned}
\]

Taking one difference eliminates \(B_n\):

\[
\boxed{
 \begin{aligned}
 h_n:=C_{n+1}-C_n
 &=R_{n+2}-11R_{n+1}+10R_n\\
 &=(10^{n+2}-16)b_{n+2}
   +(160-10^{n+1})b_{n+1}.
 \end{aligned}}                                    \tag{14}
\]

This is the direct local four-pole identity sought in this branch.  It has
no unevaluated partial sum and no pi in its definition.

The endpoint signs are not silently extrapolated.  Exact reduction gives

\[
 h_0=\frac{20048317}{16336320}>0,\qquad
 h_1=\frac{258249}{17353600}>0.                    \tag{15}
\]

For every \(n\geq2\), (12) gives

\[
\begin{aligned}
 h_n
 &<\left(\frac{10^{n+2}-16}{16}+160-10^{n+1}\right)b_{n+1}\\
 &=\left(159-\frac38\,10^{n+1}\right)b_{n+1}<0. \tag{16}
\end{aligned}
\]

Thus the sign change occurs exactly between \(h_1\) and \(h_2\), and
\(C_n\) is strictly decreasing from \(n=2\) onward.

## 3. One-sided approximation and exact total variation

Let \(T_n=\pi-B_n\).  From (13),

\[
 C_n-144\pi
 =(10^{n+1}-160)b_{n+1}-144T_{n+1}.                \tag{17}
\]

Monotonicity of \(a(k)\) and the geometric series imply

\[
 0<T_{n+1}
 <a(n+2)\sum_{k=n+2}^{\infty}16^{-k}
 <\frac{b_{n+1}}{15}.                              \tag{18}
\]

Consequently, for \(n\geq2\),

\[
 \left(10^{n+1}-\frac{848}{5}\right)b_{n+1}
 < C_n-144\pi
 <10^{n+1}b_{n+1}
 <\frac{(5/8)^{n+1}}{(n+1)^2}.                    \tag{19}
\]

This proves both the one-sided bound in (4) and \(C_n\to144\pi\).  Combining
that limit with (16), for every \(N\geq2\), gives the exact telescoping
variation identity

\[
 \sum_{n=N}^{\infty}|h_n|
 =\sum_{n=N}^{\infty}(C_n-C_{n+1})
 =C_N-144\pi
 <\frac{(5/8)^{N+1}}{(N+1)^2}.                    \tag{20}
\]

In particular the complete future forcing after depth \(N\) is exactly the
current one-sided approximation error \(C_N-144\pi\), and is smaller than the
displayed BBP-scale bound.  This is stronger than merely asserting
\(h_n\to0\).

## 4. Root-of-unity recurrence and exact comparison with the decimal orbit

Let \(e(x)=\exp(2\pi ix)\), \(Z_n=e(R_n)\), and

\[
 W_n=\frac{Z_{n+1}}{Z_n}=e(R_{n+1}-R_n).           \tag{21}
\]

Every \(Z_n,W_n\) is a root of unity.  Exponentiating (14) yields

\[
 \boxed{W_{n+1}=W_n^{10}e(h_n).}                  \tag{22}
\]

For comparison, put \(X_n=q_n\pi\),

\[
 E_n=X_n-R_n=q_n(\pi-B_n),\qquad
 Y_n=e(X_{n+1}-X_n)=e(9\cdot10^n\pi).             \tag{23}
\]

For \(n\geq2\), (9) gives

\[
 0<E_n\leq\frac{(5/8)^n}{15(n+1)^2}.              \tag{24}
\]

At the level of unwrapped phases,

\[
 \delta_n:=(R_{n+1}-R_n)-9\cdot10^n\pi
 =E_n-E_{n+1},                                    \tag{25}
\]

and hence

\[
 |\delta_n|\leq
 \frac{(5/8)^n}{15(n+1)^2}
 +\frac{(5/8)^{n+1}}{15(n+2)^2}
 \qquad(n\geq2).                                  \tag{26}
\]

Thus \(W_n=Y_ne(\delta_n)\) with exponentially summable error.  Moreover,

\[
 \delta_{n+1}-10\delta_n=h_n,                     \tag{27}
\]

so (22) is exactly the perturbed derivative of the original decimal orbit,
not an independent random recurrence.

The accumulated defect is even more explicit:

\[
 \sum_{j=0}^{n-1}\delta_j=E_0-E_n=47-15\pi-E_n.  \tag{28}
\]

Since \(Z_0=e(-47)=1\),

\[
 Z_n=\prod_{j=0}^{n-1}W_j.                        \tag{29}
\]

Equations (25)--(29) explain the precise wall.  Pointwise control of the
local variables \(W_n\), even convergence of \(W_n\) to \(1\), does not
control the selected partial products.  The unresolved statement is exactly

\[
 \boxed{
   \limsup_{n\to\infty}\Re\prod_{j=0}^{n-1}W_j=1,}
                                                               \tag{30}
\]

which is the parent one-character target in scalar local coordinates.

## 5. Monotone-forcing separator

The following rational model shows that sign, monotonicity, summability, and
local convergence in (22) cannot by themselves prove (30).  Put

\[
 \alpha=\frac19,\qquad \rho=\frac58,
 \qquad
 \varepsilon_n=\frac13\rho^n,                    \tag{31}
\]

and, for \(n\geq0\), define rational shadows

\[
 R_n^*=\frac{10^n-16}{9}-\varepsilon_n,
 \qquad B_n^*=\frac{R_n^*}{10^n-16}.              \tag{32}
\]

Then \(R_0^*=-2\), so \(e(R_0^*)=1\), and \(B_n^*\in\mathbb Q\).
Moreover, for \(n\geq2\),

\[
 B_n^*=\frac19-\frac{\varepsilon_n}{q_n}\uparrow\frac19,
\]

because \(q_n>0\) and
\(\varepsilon_{n+1}/q_{n+1}<\varepsilon_n/q_n\) for \(n\geq2\).
Direct substitution gives

\[
 \begin{aligned}
 C_n^*&:=R_{n+1}^*-10R_n^*=16+\frac{25}{8}\rho^n,\\
 h_n^*&:=C_{n+1}^*-C_n^*=-\frac{75}{64}\rho^n,\\
 W_n^*&:=e(R_{n+1}^*-R_n^*)=e\left(\frac18\rho^n\right)
 \longrightarrow1.
 \end{aligned}                                    \tag{33}
\]

Thus \(C_n^*\downarrow16=144\alpha\), \(h_n^*<0\) is absolutely summable at
the same exponential base \(5/8\), and

\[
 W_{n+1}^*=(W_n^*)^{10}e(h_n^*).                  \tag{34}
\]

Nevertheless \(10^n\equiv1\pmod9\), and for \(n\geq1\),
\(\varepsilon_n\leq\varepsilon_1=5/24\), so

\[
 \|R_n^*\|_{\mathbb T}
 =\frac13-\varepsilon_n\geq\frac18
 \qquad(n\geq1).                                  \tag{35}
\]

The local roots \(W_n^*\) converge to \(1\), while their selected products
never return to \(1\): because \(e(R_0^*)=1\), their products through depth
\(n\) equal \(e(R_n^*)\), whose circle distance has the uniform lower bound
in (35).  This separator is intentionally rational and does
not satisfy the four-pole formula (7).  The parent report's Kempner separator
independently preserves transcendence and irrationality exponent two but not
the strict monotonicity in (33).  Together the two separators locate the
remaining leverage narrowly: neither generic irrationality nor generic
one-sided scalar forcing suffices; a proof must exploit an additional exact
four-pole correlation in the accumulated product (30).

## 6. Exact replay

The companion
[`bbp_character_breakthrough_attack_20260813_check.py`](bbp_character_breakthrough_attack_20260813_check.py),
SHA-256
`34bdc64f14eff57a23346bfc9924ff8f137efd8bdc8b1d87a1bbda5d7b88851f`,
uses `Fraction` arithmetic throughout.  It pins the target, parent report,
and parent independent audit; replays (10)--(16); and checks the separator
identities and the exact \(1/8\) gap.

Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_character_breakthrough_attack_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_character_breakthrough_attack_20260813_check.py \
  --max-depth 240
```

Retained output:

```text
status: PASS
claim_label: experiment
pinned_artifacts: 3
coefficient_checks: 243
partial_sum_checks: 243
scalar_identity_checks: 723
sign_checks: 241
separator_checks: 2163
exact_endpoint_signs: h_0>0,h_1>0,h_n<0_for_checked_n>=2
separator_gap_lower_bound: 1/8
asserts_fixed_return: false
asserts_v1: false
all exact finite checks passed
```

The loop counts are an `experiment`; the all-index proofs are the rational
identities and inequalities above.

## 7. Dated literature and mathlib audit

Status: bounded `literature-checked` search on **2026-08-13 UTC**.

The primary sources checked were:

| source | exact relevance and boundary | local pin |
|---|---|---|
| Bailey--Crandall, [*On the Random Character of Fundamental Constant Expansions*](https://www.davidhbailey.com/dhbpapers/bcrandom.pdf), especially Hypothesis A and Theorems 2.7--2.10 | Gives the classical rational-perturbation dynamical program and explicitly leaves its equidistribution hypothesis unproved.  It does not prove a prescribed return for pi. | SHA-256 `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2), especially Theorems 3.3 and 4.1 | Gives the general BBP shadow mechanism and conditional dichotomy framework; it does not supply cancellation or a fixed return for the selected pi orbit. | SHA-256 `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Chen--Ye--Zheng, [*Distribution modulo one of linear recurrent sequences*](https://arxiv.org/abs/2604.14036v1), Theorem 1.3 | The parent audit verifies infinitude, a limsup dispersion bound, and one residue-slice spread statement for \((10^n-16)\pi\).  None places zero in its limit set. | SHA-256 `a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d` |

Exact web/arXiv queries included
`prescribed point accumulation b^n alpha modulo one fixed irrational`,
`linear recurrence modulo one zero limit point`,
`BBP formula rational partial sums distribution modulo one`, and
`nonautonomous expanding circle map rational perturbation equidistribution`.
They returned metric/generic shrinking-target results, the Bailey--Crandall
hypothesis, BBP computation papers, and general recurrence dispersion, but no
theorem applicable to the fixed pi return (1).

A repository/mathlib search for `Furstenberg`, `equidistribut`, `lacunary`,
`fractional part`, and dense circle orbits found the existing AllMath bridge
and mathlib's additive irrational-rotation/dense-subgroup infrastructure,
not a theorem about the noninvertible expanding orbit
\(x\mapsto10x\pmod1\), the nonautonomous rational recurrence (22), or a
prescribed return for pi.  No new formal infrastructure was invented and no
Lean declaration is claimed here.

## Sharp handoff

The strongest new coefficient-only statement is (14), together with the
one-sided all-depth estimate (19)--(20).  It reduces the two-coordinate
parent recurrence to a scalar perturbed power map whose perturbation has one
sign after the two checked endpoints and whose entire future variation is
known exactly.

The separator proves that those local properties do not control the needed
partial product.  The next valid advance must estimate the accumulated
four-pole phases in (30), for example by ruling out the parent's persistent
low-frequency Fejer bias using an identity that depends on the exact rational
values in (14).  Re-proving \(h_n<0\), \(h_n\to0\), \(W_n\to Y_n\), or
finite small returns cannot close the target.
