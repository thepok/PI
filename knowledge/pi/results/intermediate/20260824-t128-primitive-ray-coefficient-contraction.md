# T128 primitive-ray coefficient contraction

Status: `machine-checked` (T138 coefficient gap and T139 primitive-ray
identity/consumers); `proof sketch` (sharp endpoint-budget evaluation,
actual-pi two-layer endpoint contraction, and explicit threshold comparisons)

This note records the independently audited, corrected part of
`workflows/state/chatgpt-pro/20260824-open-frontier-creative-c/answer.md`.
The uniform coefficient-load gap is now machine-checked in
[`T138T138PrimitiveRayCoefficientGap.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T138T138PrimitiveRayCoefficientGap.lean).
The exact signed reconstruction, actual-orbit primitive identity, endpoint
bound, and conditional hit consumers are machine-checked in
[`T139T139PrimitiveRayBoundaryConsumer.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T139T139PrimitiveRayBoundaryConsumer.lean).
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

T139 machine-checks the positive/negative conjugate reconstruction

\[
\sum_{0<|h|\le2q-1}\alpha_q(|h|)e(-hc_{q,A})S_h(N)
=\mathcal F_{q,A}(N)+\overline{\mathcal F_{q,A}(N)}
=2\operatorname{Re}\mathcal F_{q,A}(N).
\]

Consequently the verified T128 directional defect is

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

For a positive supported frequency `h`, put

\[
v_h=\nu_{10}(h),\qquad u_h=h/10^{v_h},
\]

and retain both literal endpoint blocks in

\[
R_h(N)=
\sum_{j=0}^{v_h-1}e(u_hx_{N+j})-
\sum_{j=0}^{v_h-1}e(u_hx_j),
\qquad
\mathcal B_{q,A}(N)=
\sum_{h=1}^{2q-1}\alpha_q(h)e(-hc_{q,A})R_h(N).
\]

T139 machine-checks exact telescoping along `x_{n+1}={10x_n}`:

\[
\boxed{
\mathcal F_{q,A}(N)=
\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)+\mathcal B_{q,A}(N)
}
\]

The exact endpoint budget is

\[
\boxed{
\mathfrak E_{q,A}=
\sum_{h=1}^{2q-1}\nu_{10}(h)
\left|\alpha_q(h)e(-hc_{q,A})\right|,
\qquad
W_q=\sum_{h=1}^{2q-1}\nu_{10}(h)\alpha_q(h).
}
\]

Because the positive T128 coefficients are positive,
`mathfrak E_(q,A) = W_q`. T139 machine-checks

\[
\boxed{
|\mathcal B_{q,A}(N)|\le2\mathfrak E_{q,A},
\qquad
D_{q,A}(N)\le
-\frac2N\operatorname{Re}\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)
+\frac{4\mathfrak E_{q,A}}N.
}
\]

The elementary comparison `mathfrak E_(q,A)=W_q <= kL_q` will only be used
below for the separate explicit large-`N` simplification.

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

## Machine-checked conditional T128 criteria

T139 proves the exact strict primitive-only sufficient condition

\[
\boxed{
-\frac2N\operatorname{Re}
\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)
+\frac{4\mathfrak E_{q,A}}N
<\alpha_q(0).
}
\]

for `q>0`, `A<q`, and `N>0`. It implies a hit in the cylinder for `A`; T139
also contains the exact wrapper for every `q=10^k`, `k>=1`.

T139 then combines this consumer with T138's load gap. If `epsilon >= 0` and

\[
|S_u(N)|\le\varepsilon N\quad(u\in\mathcal P_q)
\]

at the actual π orbit, then the machine-checked threshold

\[
\boxed{
2\varepsilon(L_q-\Delta_*)+
\frac{4\mathfrak E_{q,A}}N<\alpha_q(0)
}
\]

forces the same hit. Every retained arithmetic frequency is proved not
divisible by ten. This is the T138-enhanced uniform primitive-cancellation
consumer; it does not establish its cancellation hypothesis for π.

## Proof-sketch sharp endpoint evaluation

Put `delta_q = 1 - cos(pi/q)`. Divisor-grid root-of-unity averaging of the
unshifted T128 kernel gives the exact coefficient-budget formula

\[
\boxed{
\mathfrak E_{q,A}
=\frac{\delta_q q(q-1)}{18}-\frac{k}{2}\alpha_q(0)
}<\frac{\pi^2}{36},
\qquad
\lim_{k\to\infty}\mathfrak E_{10^k,A}=\frac{\pi^2}{36}.
\]

The equality holds separately for every target `A`: positivity of the T128
coefficients and the unit target phase remove all `A`-dependence. Together
with T139's literal initial-and-terminal endpoint estimate, it yields

\[
|\mathcal B_{q,A}(N)|<\frac{\pi^2}{18},
\qquad
\frac{4\mathfrak E_{q,A}}N<\frac{\pi^2}{9N}.
\]

At the natural horizon `N >= q`, the endpoint term therefore leaves the
strictly positive zero-mode margin

\[
\alpha_q(0)-\frac{\pi^2}{9N}
>\frac{41}{36q}.
\]

This evaluates and sharply bounds the existing exact T139 premise; it does
not weaken that premise or prove primitive-frequency cancellation. Averaging
over the target labels itself gives only averaged control and does not yield a
wordwise estimate: the supported frequency `h=q` survives. Hence this remains
an endpoint improvement for every target and the actual literal orbit blocks,
not a proof of T124 or V1.

## Proof-sketch actual-pi two-layer endpoint contraction

For `q=10^k`, split the literal T139 endpoint as `B=T-I`.  Regrouping its
pairs `(h,j)` by `s=v_10(h)-j` gives

\[
 I=\sum_{s=1}^kP_{q,s}(\pi-10^sc_{q,A}),\qquad
 T=\sum_{s=1}^kP_{q,s}(10^N\pi-10^sc_{q,A}),
\]

where

\[
 P_{q,s}(t)=\sum_{10^sm\le2q-1}\alpha_q(10^sm)e(mt),\qquad
 M_{q,s}=\sum_{10^sm\le2q-1}\alpha_q(10^sm)
 =\frac{\delta_q q^2/10^s-\alpha_q(0)}2.
\]

Thus `sum_s M_(q,s)=E_(q,A)`.  Put
`theta_1=pi-10c_(q,A)` and `theta_2=pi-100c_(q,A)`, with all phase
magnitudes below interpreted as circle distances.  The exact relation
`theta_2=10 theta_1-9pi`, together with
`dist(9pi,Z)>13/50`, forces

\[
 \|\theta_1\|\ge\frac7{1000}
 \quad\text{or}\quad
 \|\theta_2\|>\frac{19}{100}.
\]

The sampled coefficient sequences `m -> alpha_q(10^s m)` are nonnegative and
unimodal, with `max_h alpha_q(h)<5/(2q)`.  Abel summation therefore gives

\[
 |P_{q,s}(t)|<\frac5{q|\sin(\pi t)|}.
\]

For `k>=3`, the first alternative saves more than `7/500` from the first
layer mass, and the second saves more than `7/500` from the second.  Hence,
uniformly in `A` and `N`,

\[
 \boxed{|I|<\mathfrak E_{q,A}-\frac7{500}},\qquad
 \boxed{|\mathcal B_{q,A}(N)|<2\mathfrak E_{q,A}-\frac7{500}}.
\]

This is an unconditional actual-pi improvement over the phase-blind T139
endpoint bound.  It yields the strictly weaker non-strict hit premise

\[
 -\frac2N\operatorname{Re}\sum_{u\in\mathcal P_q}p_{q,A}(u)S_u(N)
 +\frac{4\mathfrak E_{q,A}-7/250}{N}\le\alpha_q(0).
\]

At `N>=q`, elementary scalar bounds leave margin greater than
`5413/(4500q)`; at `N=q`, it is enough that the primitive real part is at
least `-5413/9000`.  These are sufficient conditions, not equivalent
reformulations.  The gain is only `7/(250N)` and does not affect endpoint-free
singleton rays or prove the still-open extensive primitive/off-diagonal
estimate.

## Proof-sketch explicit threshold comparison

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

The uniform actual-T128 coefficient-load gap is `machine-checked` in T138.
The exact positive/negative conjugate reconstruction, actual π-orbit primitive
identity with both endpoint blocks, endpoint norm and defect bounds, strict
primitive-only T128 hit consumer, decimal-scale wrapper, and T138-enhanced
uniform primitive-cancellation consumer are `machine-checked` in T139. The
sharp endpoint-budget evaluation and displayed numerical comparisons remain
`proof sketch`.

No required primitive-frequency cancellation estimate is known for π. This
note proves neither the T124 premise nor V1, and it makes no claim of an exact
logical separation on the π orbit.
