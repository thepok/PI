# T128 primitive-ray coefficient contraction

Status: `machine-checked` (uniform coefficient-load gap); `proof sketch`
(primitive exponential-sum identity, endpoint bounds, and conditional consumer)

This note records the independently audited, corrected part of
`workflows/state/chatgpt-pro/20260824-open-frontier-creative-c/answer.md`.
The uniform coefficient-load gap is now machine-checked in
[`T138T138PrimitiveRayCoefficientGap.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T138T138PrimitiveRayCoefficientGap.lean).
Generic finite decimal-ray telescoping was already known; the new point is a
uniform, coefficient-specific contraction for the actual T128 coefficients.

## Exact coefficients and orbit sums

Fix `k >= 1`, `q = 10^k`, and a word label `0 <= A < q`. Put

\[
c_{q,A}=\frac{2A+1}{2q},\qquad e(t)=e^{2\pi i t},
\qquad x_n=\{10^n\pi\},
\qquad S_h(N)=\sum_{n=0}^{N-1}e(hx_n).
\]

Let

\[
F_q(t)=\frac1q\left|\sum_{j=0}^{q-1}e(jt)\right|^2,
\qquad \beta_q=\cos(\pi/q),
\qquad K_q(t)=(\cos(2\pi t)-\beta_q)F_q(t)^2.
\]

Write `B_q(-h)=B_q(h)`, set `B_q(h)=0` for `h >= 2q-1`, and for
nonnegative `h` define

\[
B_q(h)=
\begin{cases}
\dfrac{4q^3+2q-6qh^2+3h^3-3h}{6q^2},&0\le h\le q,\\[1ex]
\dfrac{(2q-h-1)(2q-h)(2q-h+1)}{6q^2},&q<h\le2q-2.
\end{cases}
\]

The exact T128 coefficients are

\[
\boxed{\alpha_q(h)=\frac{B_q(h-1)+B_q(h+1)}2-\beta_qB_q(h)}
\qquad(0\le h\le2q-1),
\]

where `B_q(-1)=B_q(1)` at `h=0`. Thus

\[
K_q(t)=\alpha_q(0)+\sum_{h=1}^{2q-1}\alpha_q(h)(e(ht)+e(-ht)),
\]

all positive-frequency coefficients satisfy `alpha_q(h) > 0`, and

\[
\alpha_q(0)=
\frac{2(q^2-1)-(2q^2+1)\cos(\pi/q)}{3q}
>\frac1{3q}+\frac2{3q^3}>0.
\]

Define the positive-frequency load and centered complex obstruction by

\[
\boxed{L_q=\sum_{h=1}^{2q-1}\alpha_q(h)},\qquad
\mathcal F_{q,A}(N)=
\sum_{h=1}^{2q-1}\alpha_q(h)e(-hc_{q,A})S_h(N).
\]

The verified T128 directional defect is

\[
D_{q,A}(N)=-\frac2N\operatorname{Re}\mathcal F_{q,A}(N).
\]

Its endpoint says that `D_{q,A}(N) < alpha_q(0)` forces some `n < N`
with `x_n in [A/q,(A+1)/q)`.

## Exact primitive-ray identity and endpoint budget

Let

\[
\mathcal P_q=\{u:1\le u\le2q-1,\ 10\nmid u\},\qquad
R_u=\max\{r\ge0:10^ru\le2q-1\}.
\]

Every supported positive frequency is uniquely `10^r u` with
`u in P_q` and `0 <= r <= R_u`. Define

\[
b_{u,r}=\alpha_q(10^ru)e(-10^ru c_{q,A}),
\qquad
\boxed{p_{q,A}(u)=\sum_{r=0}^{R_u}b_{u,r}},
\]

and the ray tails

\[
\tau_{q,A}(u,s)=\sum_{r=s}^{R_u}b_{u,r}\qquad(1\le s\le R_u).
\]

Exact telescoping along `x_{n+1}={10x_n}` gives

\[
\boxed{
\mathcal F_{q,A}(N)=
\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)+\mathcal B_{q,A}(N)
}
\]

with the literal initial and terminal orbit phases

\[
\boxed{
\mathcal B_{q,A}(N)=
\sum_{u\in\mathcal P_q}\sum_{s=1}^{R_u}
\tau_{q,A}(u,s)
\bigl(e(ux_{N+s-1})-e(ux_{s-1})\bigr).
}
\]

For the exact endpoint quantities

\[
\boxed{
\mathfrak E_{q,A}=
\sum_{u\in\mathcal P_q}\sum_{s=1}^{R_u}
|\tau_{q,A}(u,s)|,
\qquad
W_q=\sum_{h=1}^{2q-1}\nu_{10}(h)\alpha_q(h),
}
\]

one has

\[
\boxed{
|\mathcal B_{q,A}(N)|\le2\mathfrak E_{q,A},
\qquad
\mathfrak E_{q,A}\le W_q\le kL_q.
}
\]

## Uniform coefficient gap

T138 machine-checks the coefficient-specific gain

\[
\boxed{
\sum_{u\in\mathcal P_q}|p_{q,A}(u)|
<L_q-\Delta_*,
\qquad
\Delta_*=\frac1{3\,000\,000}.
}
\]

This holds uniformly for every `k >= 1` and every label `A`. T138 formalizes
the actual centered T128 terms, their exact primitive power-of-ten fibers, and
both the `q=10` and `q>=100` branches. For `q >= 100`,
pairing the first two coefficients on the odd primitive rays
`u=1,3,...,q/50-1` gives the gap: the exact center phases force a summed
angular loss, while `alpha_q(u), alpha_q(10u) > 1/(3q)`. The case `q=10`
uses the single ray `u=1`, whose `h=1` and `h=10` terms already lose more
than `1/2500`. This is where the result goes beyond the previously known
generic ray telescope.

## Conditional T128 criteria

The exact directional sufficient condition is

\[
\boxed{
-\frac2N\operatorname{Re}
\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)
+\frac{4\mathfrak E_{q,A}}N
<\alpha_q(0).
}
\]

It implies a hit in the cylinder for `A`. Replacing `E` by `W` gives the
target-independent endpoint budget

\[
-\frac2N\operatorname{Re}
\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)
+\frac{4W_q}N
<\alpha_q(0),
\]

and a modulus-only sufficient condition is

\[
\boxed{
\frac2N\sum_{u\in\mathcal P_q}|p_{q,A}(u)|\,|S_u(N)|
+\frac{4W_q}N
<\alpha_q(0).
}
\]

These premises retain the actual π-orbit but require exponential-sum control
only at primitive frequencies `10 not dividing u`.

For an explicit comparison, suppose `|S_u(N)| <= epsilon N` for every
`u in P_q`. Since `L_q < pi^2/4`, the sufficient bound

\[
2\varepsilon(L_q-\Delta_*)+\frac{k\pi^2}{N}<\alpha_q(0)
\]

implies the T128 hit. The corresponding primitive threshold

\[
\varepsilon_{\rm ray}(N)=
\frac{\alpha_q(0)-k\pi^2/N}{2(L_q-\Delta_*)}
\]

is strictly larger than the standard all-supported-frequency numerical
threshold

\[
\varepsilon_{\rm all}=\frac{\alpha_q(0)}{2L_q}
\]

whenever

\[
N>\frac{k\pi^2L_q}{\alpha_q(0)\Delta_*}.
\]

In particular, the explicit sufficient horizon is

\[
\boxed{N>2\,250\,000\,\pi^4kq.}
\]

This is a strict comparison of admissible constants after the stated
large-`N` restriction. It is not an exact logical separator between the two
π-orbit premises.

## Claim boundary

Only the uniform actual-T128 coefficient-load gap is `machine-checked`. The
exact primitive exponential-sum identity, its initial/terminal endpoint bound,
and the resulting conditional T128 consumer remain `proof sketch` and are not
in Lean. No required primitive-frequency cancellation estimate is known for
π. This note proves neither the T124 premise nor V1, and it makes no claim of
an exact logical separation on the π orbit.
