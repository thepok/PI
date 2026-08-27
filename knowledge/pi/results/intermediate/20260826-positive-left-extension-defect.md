# Positive left-extension defect for the primitive boundary score

Status: `proof sketch`; independently algebra-audited against T130, T132,
T139, T142, and T156. No fixed-pi signed estimate is proved.

Date: 2026-08-26 UTC

This note records a new exact scale-transport law proposed by ChatGPT Pro and
checked independently by the operator and three local audit passes. It is a
useful structural bridge, not the missing source of target-signed information
for the actual decimal orbit of pi. Under the signed-bridge operator rule it
must remain unformalized until a genuine fixed-pi input feeds it.

## Statement

Write

\[
 Z^\pi_{q,A}(N)=\operatorname{primitiveBoundaryFourierSum}(q,A,N),
 \qquad
 \alpha_q(h)=\operatorname{positiveBoundaryCoefficient}(q,h),
\]

and put `A_d=A+dq` for `0 <= d < 10`. Thus `A_d` is the decimal
left-extension `dA`. For `q >= 1000` and `1 <= h <= 2q-1`, define

\[
 D_q(h)=10\alpha_{10q}(10h)-\alpha_q(h).
\]

The audited coefficient calculation gives

\[
 \boxed{D_q(h)>0.} \tag{1}
\]

Let `rho(h)=h/10^{nu_10(h)}` and

\[
 R^\pi_{q,A}(N)=\sum_{h=1}^{2q-1}
 D_q(h)e(-h(A+1/2)/q)S^\pi_{\rho(h)}(N).
\]

Digit-character orthogonality then yields the exact zero-sector identity

\[
 \boxed{
 \sum_{d=0}^{9}Z^\pi_{10q,A+dq}(N)
 =Z^\pi_{q,A}(N)+R^\pi_{q,A}(N).} \tag{2}
\]

No primitive ray or endpoint is discarded here. Expanding the T139 fibre sum
recovers the positive frequencies `1 <= h <= 2q-1`; summing the ten child
phases selects exactly the frequencies divisible by ten.

## Exact defect mass

Set

\[
 a_q=1-\cos(\pi/q),\qquad
 \delta_q=100a_{10q}-a_q.
\]

The exact positive mass is

\[
 \Delta_q=\sum_{h=1}^{2q-1}D_q(h)
 =\delta_q\frac{(q-1)(3q^2+q+1)}{6q}
  +\frac{33a_{10q}}{2q}. \tag{3}
\]

For `q >= 1000`,

\[
 0<\Delta_q<\frac{25}{12q^2}+\frac{33}{40q^3}
 <\frac{21}{10q^2}. \tag{4}
\]

Consequently,

\[
 |R^\pi_{q,A}(N)|\le N\Delta_q,
\]

and taking real parts in (2) gives the signed propagation inequality

\[
 \boxed{
 \max_{0\le d<10}\Re Z^\pi_{10q,A+dq}(N)
 \ge \frac{\Re Z^\pi_{q,A}(N)-N\Delta_q}{10}.} \tag{5}
\]

At `N=10q`, (4) and the checked T156 threshold imply

\[
 \Re Z^\pi_{q,A}(10q)\ge-\frac{8589}{1000}
 \Longrightarrow
 \text{some left-extension }dA\text{ is hit by time }10q. \tag{6}
\]

Equivalently, if all ten `dA` cylinders are missed at that horizon, then the
parent score is strictly below `-8589/1000`.

## Algebra audit

With `B_q(h)=fejerSquareCoefficient(q,h)`, the checked piecewise formulas give

\[
 \alpha_q(h)=a_qB_q(h)+L_q(h),
\]

where

\[
 L_q(h)=
 \begin{cases}
 (3h-2q)/(2q^2),&1\le h\le q,\\
 (2q-h)/(2q^2),&q\le h\le2q-1.
 \end{cases}
\]

The curvature term scales exactly: `10 L_(10q)(10h)=L_q(h)`. Moreover,

\[
 B_{10q}(10h)-10B_q(h)=
 \begin{cases}
 33(3h-2q)/(20q^2),&1\le h\le q,\\
 33(2q-h)/(20q^2),&q\le h\le2q-1.
 \end{cases}
\]

Hence

\[
 D_q(h)=\delta_qB_q(h)+10a_{10q}
 \bigl(B_{10q}(10h)-10B_q(h)\bigr). \tag{7}
\]

Only the low-frequency branch can be negative in the second term. There the
exact comparison

\[
 6q^2B_q(h)-(2q-3h)(2q^2+1)
 =3h\bigl((h-q)^2+q^2\bigr)>0
\]

and elementary cosine bounds prove (1). Independent summation checked

\[
 \sum_{h=1}^{2q-1}B_q(h)
 =\frac{(q-1)(3q^2+q+1)}{6q},
\]

and

\[
 \sum_{h=1}^{2q-1}
 \bigl(B_{10q}(10h)-10B_q(h)\bigr)=\frac{33}{20q},
\]

which prove (3). High-precision evaluation at `q=1000` gives
`q^2 Delta_q = 2.0085367021418...`, consistent with (4).

## Exact claim boundary

The target factor survives in every term, and the full child vector can be
recovered through its ten digit-DFT sectors. Nevertheless, this theorem is
generic coefficient transport. The `pi` used to prove `D_q(h)>0` is the
geometric constant inside the boundary kernel, not arithmetic information
that selects the actual decimal orbit of pi.

The nine nonzero child-character sectors remain uncontrolled. Equation (5)
therefore selects only some leading digit. More importantly, it assumes a
one-sided parent score; it does not generate that score. A proposed condition
such as

\[
 \exists N:\quad \Re Z^\pi_{q,A}(N)\ge N\Delta_q
\]

is a strengthened restatement of the open signed summit, not an atomic source
lemma. It must not be counted as progress merely because it composes with
(5).

The shortest legitimate next research rung must instead prove a genuinely
fixed-pi one-sided estimate for either the parent score or a named nonzero
predecessor-digit character sector, with an explicit arithmetic source for
the sign. Until such a rung survives, no Lean declarations from this note
should be added.

## Trust-boundary corrections

- Full-support positivity of `positiveBoundaryCoefficient` is checked in
  T142, not T138.
- The natural-horizon consequence (6) composes directly with T156 and is
  sound. The memo's separate arbitrary-horizon `Re Z >= 0` wording is not a
  single named checked theorem; the required scalar comparison is currently
  recorded only as a `proof sketch`.
