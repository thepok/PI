# Independent audit: BBP character scalar monotone forcing

Audit date: **2026-08-13 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question was created from Marcel's request and has no
external source URL; none is invented here.

Corrected primary artifacts:

- [`bbp_character_breakthrough_attack_20260813.md`](bbp_character_breakthrough_attack_20260813.md),
  SHA-256
  `5a0e3027eb2b6c38b48e2b3ae075b4175b586bbd54ec1de68e6621cb0e03c264`;
- [`bbp_character_breakthrough_attack_20260813_check.py`](bbp_character_breakthrough_attack_20260813_check.py),
  SHA-256
  `34bdc64f14eff57a23346bfc9924ff8f137efd8bdc8b1d87a1bbda5d7b88851f`.

Independent replay:

- [`bbp_character_breakthrough_independent_check_20260813.py`](bbp_character_breakthrough_independent_check_20260813.py),
  SHA-256
  `1d4f1b534c55afcc6261bfa9bbf7b75f0a9ebaf37ccf9d3ef7b01cb8b79a92d5`.

## Verdict

**PASS after a substantive separator correction and presentation repairs.**

The corrected coefficient identities, endpoints, all-index inequalities,
second-order scalar recurrence, one-sided approximation, phase identities,
and rational separator all rederive independently.  The bounded primary-source
claims also have the stated scope.  The mathematical conclusions have status
`proof sketch`; the bounded source audit is `literature-checked` on the audit
date; the bounded replays are `experiment` only.  Nothing new is
`machine-checked`.

No fixed-sixteen return and no V1 statement is proved.  Canonical V1 remains a
`conjecture`.  The exact unresolved blocker is still

\[
 \liminf_{n\to\infty}\|(10^n-16)B_n\|_{\mathbb T}=0,
 \qquad
 B_n=\sum_{k=0}^n\frac{a(k)}{16^k},                 \tag{A1}
\]

or, equivalently,

\[
 \limsup_{n\to\infty}\Re\prod_{j=0}^{n-1}W_j=1.   \tag{A2}
\]

The local scalar recurrence does not establish (A2).  Its exact four-pole
forcing still needs an accumulated-phase cancellation or recurrence result
that is absent from the checked literature.

## 1. Corrections made during the audit

The pre-audit primary hashes were

- report:
  `bf8e6ad28cd3766132f1fc5b4dc94861a00b5d453ea8f9f1f5a02fef335b9e3d`;
- checker:
  `b538ac69b9ae97330c834b6c4e02eaddb33af538e8021a12da0830171993aec4`.

The following were genuine defects, so the primary artifacts were corrected in
place while preserving their scope.

1. The original separator used
   \(\varepsilon_n=(8/75)(5/8)^n\).  It correctly kept
   \(e(R_n^*)\) at circle distance at least \(7/24\) for \(n\geq2\), but
   \(R_0^*=-133/75\notin\mathbb Z\).  Therefore

   \[
     \prod_{j=0}^{n-1}W_j^*=e(R_n^*-R_0^*)
   \]

   was not \(e(R_n^*)\), and the report's claimed \(7/24\) lower bound for
   the **partial product** in (A2) did not follow.  In fact that original
   product phase was
   \((8/75)(1-(5/8)^n)\), whose correct eventual separation already begins
   at \(1/25\), so the qualitative separator idea survived but its stated
   anchoring and constant were wrong.
2. The corrected model takes
   \(\varepsilon_n=(1/3)(5/8)^n\).  It has \(R_0^*=-2\), so the partial
   product is exactly \(e(R_n^*)\), and it has the clean uniform lower bound
   \(1/8\) for every \(n\geq1\).  The primary checker was changed to replay
   this anchored model independently of floating-point arithmetic.
3. A literal U+000B vertical tab had corrupted `\varepsilon_n`; the displayed
   sign bound also contained a comma where multiplication
   \(\frac38\,10^{n+1}\) was intended.  The control byte, malformed formula,
   and broken inline-math delimiters were repaired.  A full C0 scan is now in
   the independent checker.
4. The prose saying future variation was *smaller* than the current
   approximation error was corrected: it is **equal** to
   \(C_N-144\pi\), and smaller than the displayed BBP-scale upper bound.
   Index domains and the elementary monotonicity explanation for the
   separator shadow were also made explicit.

These corrections do not prove (A1), do not change the branch's `proof sketch`
status, and do not strengthen the canonical claim.

## 2. Normalization and exact dependency on the fixed return

Canonical V1 says that every finite word over \(\{0,\ldots,9\}\), including
words with leading zeroes and the empty word, occurs contiguously in the
decimal expansion of pi.  The assertion that every infinite word occurs as a
tail is false.  The assertion that every infinite word occurs as a subsequence
is equivalent to every digit recurring infinitely often and remains open.
The primary report does not exchange these quantifiers.

The checked T69 dependency is

\[
 \operatorname{Dense}\{10^s16^t\pi\bmod1:s,t\in\mathbb N\}
 \Longrightarrow
 \bigl(\mathrm{V1}\leftrightarrow\mathrm{R16}\bigr),            \tag{A3}
\]

where R16 is

\[
 16\pi\bmod1\in
 \overline{\{10^n\pi\bmod1:n\in\mathbb N\}}.
\]

Furstenberg's paper theorem supplies the density premise because the
multiplicative semigroup generated by 10 and 16 is nonlacunary and pi is
irrational.  This paper step is source-audited; it has not been inserted into
Lean as an axiom.  Circle distance rewrites R16 as arbitrarily small values of
\(\|(10^n-16)\pi\|_{\mathbb T}\).  No exact hit occurs because
\(10^n-16\neq0\) and pi is irrational.  Hence arbitrarily accurate hits use
unbounded indices and R16 is exactly

\[
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0.            \tag{A4}
\]

The parent BBP bound gives, for \(n\geq2\),

\[
 0<(10^n-16)(\pi-B_n)
 \leq\frac{(5/8)^n}{15(n+1)^2}\longrightarrow0.                \tag{A5}
\]

The circle norm is 1-Lipschitz, so (A4) is equivalent to (A1).  Finally,
\(1-\Re e(x)=2\sin^2(\pi\|x\|_{\mathbb T})\) makes (A1) equivalent to the
one-character return, and \(R_0=-47\in\mathbb Z\) makes that return exactly
(A2).  Thus the reduction to V1 is correct, but its Furstenberg component is a
source-audited paper theorem rather than a new formal theorem in this branch.

## 3. Coefficient identity and scalar elimination

For \(k,n\geq0\), define

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},\quad
 b_k=\frac{a(k)}{16^k},\quad
 B_n=\sum_{k=0}^n b_k,
\]

and \(q_n=10^n-16\), \(R_n=q_nB_n\).  Independent integer-polynomial
expansion gives

\[
 a(k)-a(k+1)=\frac{3P(k)}{D(k)},
\]

where \(D(k)\) is the eight-factor positive denominator in the primary report
and

\[
 P(k)=40960k^5+220672k^4+453632k^3+443480k^2
      +206712k+36903.
\]

Every coefficient of \(P\) is positive.  Thus \(a(k)>a(k+1)>0\), and
\(b_{k+1}<b_k/16\).  A second symbolic expansion gives

\[
\begin{aligned}
 &(2k+1)(4k+3)(8k+1)(8k+5)\\
 &\qquad-k^2(120k^2+151k+47)\\
 &=392k^4+873k^3+665k^2+194k+15>0,
\end{aligned}
\]

which independently confirms \(a(k)<k^{-2}\) for \(k\geq1\).

Using \(q_{n+1}=10q_n+144\) and \(B_{n+1}=B_n+b_{n+1}\) gives exactly

\[
 C_n:=R_{n+1}-10R_n=144B_n+q_{n+1}b_{n+1}.         \tag{A6}
\]

One difference cancels the cumulative partial sum:

\[
\begin{aligned}
 h_n:=C_{n+1}-C_n
 &=R_{n+2}-11R_{n+1}+10R_n\\
 &=(10^{n+2}-16)b_{n+2}+(160-10^{n+1})b_{n+1}.
                                                               \tag{A7}
\end{aligned}
\]

The two exceptional endpoints independently reduce to

\[
 h_0=\frac{20048317}{16336320}>0,
 \qquad
 h_1=\frac{258249}{17353600}>0.
\]

For every \(n\geq2\), the strict coefficient decrease gives

\[
 h_n<\left(159-\frac38\,10^{n+1}\right)b_{n+1}<0,
\]

because the final bracket is already negative at \(n=2\) and decreases
thereafter.  There is no missed endpoint: the sign switches exactly after
\(h_1\), and \(C_n\) is strictly decreasing from \(C_2\) onward.

## 4. One-sided approximation and total variation

Let \(T_n=\pi-B_n\).  The BBP series and coefficient monotonicity give

\[
 0<T_{n+1}
 <a(n+2)\sum_{k=n+2}^{\infty}16^{-k}
 <\frac{b_{n+1}}{15}.                              \tag{A8}
\]

Equation (A6) then yields

\[
 C_n-144\pi=(10^{n+1}-160)b_{n+1}-144T_{n+1}.
\]

For \(n\geq2\), therefore,

\[
 \left(10^{n+1}-\frac{848}{5}\right)b_{n+1}
 <C_n-144\pi
 <10^{n+1}b_{n+1}
 <\frac{(5/8)^{n+1}}{(n+1)^2}.                    \tag{A9}
\]

The left coefficient is positive already at \(n=2\).  Thus \(C_n>144\pi\)
and \(C_n\to144\pi\).  Since every \(h_n<0\) from \(n=2\), telescoping is
legitimate and gives, for every \(N\geq2\),

\[
 \sum_{n=N}^{\infty}|h_n|=C_N-144\pi
 <\frac{(5/8)^{N+1}}{(N+1)^2}.                    \tag{A10}
\]

This confirms the one-sided approximation and exact total-variation claim.

## 5. Root-of-unity recurrence and the accumulated phase

Set \(e(x)=\exp(2\pi ix)\), \(Z_n=e(R_n)\), and
\(W_n=e(R_{n+1}-R_n)\).  Every phase is rational, so these are roots of
unity.  Equation (A7) gives

\[
 W_{n+1}=W_n^{10}e(h_n).                           \tag{A11}
\]

For \(X_n=q_n\pi\) and \(E_n=X_n-R_n\), direct subtraction gives

\[
 \delta_n:=(R_{n+1}-R_n)-9\cdot10^n\pi=E_n-E_{n+1}.             \tag{A12}
\]

The endpoint is

\[
 E_0=-15\pi+47=47-15\pi;
\]

it is not positive, and the primary report correctly restricts positivity of
\(E_n\) to \(n\geq2\).  Applying one more difference to (A12) gives

\[
 \delta_{n+1}-10\delta_n=h_n,
\]

while telescoping gives

\[
 \sum_{j=0}^{n-1}\delta_j=E_0-E_n=47-15\pi-E_n.                 \tag{A13}
\]

Finally \(Z_0=e(-47)=1\), so

\[
 Z_n=\prod_{j=0}^{n-1}W_j.                         \tag{A14}
\]

These calculations confirm that the scalarization is exact.  They also show
its limitation: \(W_n\) is exponentially close to
\(e(9\cdot10^n\pi)\), so (A11) is an asymptotic restatement of the derivative
decimal orbit, not an independent source of randomness or cancellation.

## 6. Corrected rational separator

Let \(\rho=5/8\), \(\varepsilon_n=\rho^n/3\), and

\[
 R_n^*=\frac{10^n-16}{9}-\varepsilon_n,
 \qquad B_n^*=\frac{R_n^*}{10^n-16}.
\]

All these quantities are rational.  Since \(R_0^*=-2\), the associated
partial products have the required anchor.  Exact substitution gives

\[
\begin{aligned}
 C_n^*&=16+\frac{25}{8}\rho^n,\\
 h_n^*&=-\frac{75}{64}\rho^n,\\
 W_n^*&=e\left(\frac18\rho^n\right),\\
 W_{n+1}^*&=(W_n^*)^{10}e(h_n^*).
\end{aligned}                                                   \tag{A15}
\]

Thus the forcing is strictly one-sided, monotone, and summable with
exponential base \(5/8\), while \(W_n^*\to1\).  For \(n\geq2\),

\[
 B_n^*=\frac19-\frac{\varepsilon_n}{q_n}\uparrow\frac19,
\]

because \(q_n>0\) and \(\rho q_n<q_{n+1}\).  On the other hand,
\(10^n\equiv1\pmod9\), so for every \(n\geq1\),

\[
 \left\|R_n^*\right\|_{\mathbb T}
 =\frac13-\frac13\rho^n\geq\frac18.              \tag{A16}
\]

Because \(R_0^*\) is integral,

\[
 \prod_{j=0}^{n-1}W_j^*=e(R_n^*-R_0^*)=e(R_n^*),
\]

and (A16) is genuinely a partial-product obstruction of the same form as
(A2).  The separator deliberately does not satisfy the BBP four-pole formula.
It therefore proves only that sign, monotonicity, summability, roots of unity,
and local convergence are insufficient in isolation.  It does not refute a
coefficient-specific theorem and does not imply anything negative about V1.

## 7. Sources, search boundary, and formal status

The following pinned primary sources were inspected independently.

| source | independent scope check | SHA-256 |
|---|---|---|
| Furstenberg, *Disjointness in ergodic theory, minimal sets, and a problem in Diophantine approximation* | Theorem IV.1 supplies density of the orbit of an irrational point under a nonlacunary integer semigroup; the 10-and-16 application used by T69 matches its hypotheses. | `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` |
| Bailey--Borwein--Plouffe, *On the Rapid Computation of Various Polylogarithmic Constants* | Supplies the exact BBP series used to define \(a(k)\) and \(B_n\); it does not supply the required decimal return. | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Bailey--Crandall, *On the Random Character of Fundamental Constant Expansions* | Hypothesis A is explicitly a conjectural rational-perturbation dichotomy.  Theorems 2.7--2.10 concern infinite orbit values and finite/periodic attractors; they do not prove equidistribution or a prescribed return for pi. | `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` |
| Lagarias, *On the Normality of Arithmetical Constants*, arXiv:math/0101055v2 | Theorem 3.3 is a rationality criterion for perturbed base expansions, and Theorem 4.1 derives digit density/normality only under weak/strong dichotomy hypotheses.  No fixed pi return follows. | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Chen--Ye--Zheng, *Distribution modulo one of linear recurrent sequences*, arXiv:2604.14036v1 | Theorem 1.3 gives infinitude, a limsup dispersion bound, and a residue-slice spread conclusion under the parent audit's checked hypothesis.  These are in the wrong direction for the liminf-zero return. | `a17f776537f415e4f0b0508024cf95389b1ed4da05a347efda6b149bb2e4924d` |
| Shallit, *Simple Continued Fractions for Some Irrational Numbers* | Theorems 3 and 8--9 give irrationality and bounded partial quotients for the decimal Fredholm--Kempner specialization used by the parent separator; bounded partial quotients imply irrationality exponent two. | `592a08ecf6df04414fe7bf5083d56898139b5d553679b244296833a1e2f1f981` |
| Kempner, *On Transcendental Numbers* | The cited specialization supplies transcendence of the decimal Fredholm--Kempner number used only in the parent separator. | `99c4bf8d04d2dbdc63e8d274266f212072d4c248fcbc659e60ca7fa9350eb014` |

The primary report's dated query list is consistent with these sources.  A
fresh repository/mathlib symbol search found the existing AllMath decimal
orbit and fixed-sixteen bridge modules and generic irrational-rotation,
floor, and density infrastructure, but no theorem about this prescribed
return for a fixed pi orbit.  The bounded search therefore supports the
primary report's `literature-checked` label and no stronger one.

No formal code was changed.  No declaration, axiom, `sorry`, `admit`,
`native_decide`, or compiler-trusting shortcut was added.  There is no new
claim to register in `audit/AxiomAudit.lean`, and this branch does not warrant
the labels `candidate resolution` or `verified resolution`.

## 8. Independent replay

The independent checker does not import the primary checker.  It pins all
primary, parent, T69, and literature artifacts; verifies the coefficient
identities by integer-polynomial expansion; replays the rational recurrences,
endpoints, affine-in-pi identities, and corrected separator; and scans all
scoped text artifacts for C0 controls.

Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_character_breakthrough_independent_check_20260813.py
.venv/bin/python \
  work/ultrapi-resume/bbp_character_breakthrough_independent_check_20260813.py \
  --max-depth 180
```

Retained final output was:

```text
status: PASS
claim_label: experiment
pinned_artifacts: 17
c0_scanned_text_artifacts: 12
symbolic_polynomial_checks: 2
coefficient_checks: 735
scalar_checks: 728
affine_pi_identity_checks: 906
separator_checks: 1622
corrected_separator_initial_phase: R_star_0=-2
corrected_separator_gap_lower_bound: 1/8
asserts_fixed_return: false
asserts_v1: false
all independent exact finite checks passed
```

Loop output is an `experiment`, not an infinite proof.

## Sharp handoff

The corrected branch has isolated a valid coefficient-specific scalar
identity and a sharp logical wall.  The only route to (A2) that this reduction
leaves open is to use the **exact values**

\[
 h_n=(10^{n+2}-16)b_{n+2}+(160-10^{n+1})b_{n+1}
\]

to control their accumulated phases.  Reusing only \(h_n<0\), exponential
summability, \(W_n\to e(9\cdot10^n\pi)\), or root-of-unity structure cannot
close the target.  A next valid advance must rule out the parent's persistent
low-frequency Fejer-bias alternative by a genuinely four-pole correlation,
or supply another theorem that directly forces (A1).
