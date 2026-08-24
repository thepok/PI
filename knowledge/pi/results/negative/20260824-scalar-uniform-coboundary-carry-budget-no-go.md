# Scalar uniform coboundaries cannot meet the carry budget

Status: `proof sketch`

Date: 2026-08-24 UTC

Source: independently audited from
`workflows/state/chatgpt-pro/20260824-approximate-ray-coboundary/answer.md`.

This is a scoped obstruction for the boundary-kernel carry route. It records
no fixed-π cancellation estimate, digit occurrence, density, normality, or V1.

## Carry observable and live margin

Let \(T(x)=10x\pmod 1\). For a target word \(dv\), write
\(Q=10^{k-1}\ge10\), \(q=10Q\), and use the carry-flow observable

\[
W_{d\mid v}(x)=H_Q(y_v(x))\mathbf 1_{\{\eta_v(x)=d\}},
\qquad H_Q(y)=K_{10Q}(y/10).
\]

The exact carry identity from the carry-flow note is

\[
K_q(x-c_{dv})=W_{d\mid v}(x)+E_{d\mid v}(x),
\qquad
-\frac{C_{\rm off}}{Q^2}\le E_{d\mid v}(x)\le0,
\]

where

\[
C_{\rm off}=\frac1{50\sin^2(\pi/20)}.
\]

The error is zero on the matching incoming branch. Consequently a lower
bound

\[
\sum_{n<N}W_{d\mid v}(T^n\{\pi\})
>\frac{C_{\rm off}}{Q^2}N
\]

would force the target-cylinder sum to be positive.

## Pointwise scalar no-go

Suppose, pointwise on the circle,

\[
W_{d\mid v}=A+G\circ T-G+r,
\]

where \(G\) is finite at every point. Set

\[
\|r^-\|_\infty=\sup_x\max\{-r(x),0\}.
\]

The nine points \(z_j=j/9\), \(0\le j\le8\), are fixed by \(T\). Since the
target cylinder has length \(1/q<1/9\), choose one \(z_j\) outside it. If its
incoming branch matches \(d\), the exact carry identity gives
\(W_{d\mid v}(z_j)=K_q(z_j-c_{dv})\le0\); otherwise the indicator defining
\(W_{d\mid v}\) makes it zero. Evaluating the decomposition at this fixed
point therefore gives

\[
r(z_j)=W_{d\mid v}(z_j)-A\le-A,
\qquad
\boxed{A-\|r^-\|_\infty\le0}.
\]

For \(A\le0\) the boxed inequality is immediate; for \(A>0\), the displayed
fixed-point value gives \(\|r^-\|_\infty\ge A\).
Thus no pointwise scalar decomposition can supply the strictly positive
uniform margin required by the carry criterion, regardless of how well its
endpoint term telescopes.

For an integrable mean-normalized decomposition, set \(A=\lambda_{d\mid v}\),
where

\[
\lambda_{d\mid v}=\int_{\mathbb T}W_{d\mid v}(x)\,dx.
\]

Integrating the carry identity and using \(E_{d\mid v}\le0\) gives

\[
\lambda_{d\mid v}\ge\mu_{10Q},
\]

where \(\mu_q\) is the zero Fourier coefficient of \(K_q\). The audited
elementary bounds, valid for \(Q\ge10\), give

\[
\boxed{
\|r^-\|_\infty\ge\lambda_{d\mid v}
\ge\mu_{10Q}>\frac1{5Q}>
\frac{C_{\rm off}}{Q^2}}.
\]

The forced residual therefore has the harmful sign and size \(\Omega(Q^{-1})\),
while the permitted carry leakage is only \(O(Q^{-2})\).

## Exact \(L^2\) ray spreading does not repair this

The obstruction is genuinely about pointwise orbit control, not about the
existence of weak approximate coboundaries. Write the centered finite Fourier
expansion

\[
f_{q,c}(x)=K_q(x-c)-\mu_q=\sum_{h\ne0}b_he(hx).
\]

Write each frequency uniquely as \(h=10^ru\), \(10\nmid u\), let \(R_u\) be
the last occupied level, and put

\[
p_u=\sum_{r=0}^{R_u}b_{10^ru}.
\]

The finite transfer

\[
G_0(x)=\sum_u\sum_{r=0}^{R_u-1}
\left(\sum_{j=r+1}^{R_u}b_{10^ju}\right)e(10^ru x)
\]

satisfies \(f_{q,c}=P+G_0\circ T-G_0\), where
\(P=\sum_up_ue(ux)\). For \(M\ge1\), define

\[
H_M(x)=-\sum_u\frac{p_u}{M}
\sum_{r=0}^{M-2}(M-1-r)e(10^ru x),
\]

\[
R_M(x)=\sum_u\frac{p_u}{M}\sum_{r=0}^{M-1}e(10^ru x).
\]

An exact coefficient calculation gives

\[
f_{q,c}=G_M\circ T-G_M+R_M,
\qquad G_M=G_0+H_M,
\]

and Parseval gives the exact decay

\[
\|R_M\|_2^2=\frac1M\sum_u|p_u|^2.
\]

If

\[
B_0=\sum_u\sum_{r=0}^{R_u-1}
\left|\sum_{j=r+1}^{R_u}b_{10^ju}\right|,
\qquad P_1=\sum_u|p_u|,
\]

then

\[
\|G_M\|_\infty\le B_0+\frac{M-1}{2}P_1.
\]

Hence, on the actual orbit \(x_n=\{10^n\pi\}\), the endpoint is explicitly
bounded by

\[
|G_M(x_N)-G_M(x_0)|\le2B_0+(M-1)P_1.
\]

Combining this decomposition with \(K_q=W_{d\mid v}+E_{d\mid v}\), and
using that the matching branch has Haar measure \(1/10\), yields an explicit
residual \(\widetilde R_M=R_M-E_{d\mid v}\) for \(W_{d\mid v}\), with

\[
\|\widetilde R_M\|_2\le
\left(\frac1M\sum_u|p_u|^2\right)^{1/2}
+\sqrt{\frac9{10}}\frac{C_{\rm off}}{Q^2}.
\]

Choosing

\[
M>\frac{Q^4\sum_u|p_u|^2}
{(1-\sqrt{9/10})^2C_{\rm off}^2}
\]

makes this \(L^2\) residual strictly smaller than \(C_{\rm off}/Q^2\).
This still gives no bound for its sum along the single π orbit. At every
outside fixed point the same residual is at most \(-\mu_q\), so its
pointwise negative norm remains above the carry budget.

## Scope

This no-go concerns pointwise scalar decompositions on the circle and a
literal supremum over all points. It does **not** apply to almost-everywhere
identities measured only in essential \(L^\infty\), because isolated fixed
points may be discarded there. It also says nothing about π-specific
residual averages, vector-valued states retaining incoming-digit characters,
or arithmetic numerator/carry structure. Those remain possible inputs; V1
remains open.
