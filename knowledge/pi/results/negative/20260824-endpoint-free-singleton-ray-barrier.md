# Endpoint-free singleton rays survive decimal-ray compression

Status: `proof sketch`

Date: 2026-08-24 UTC

This is a narrow obstruction to finishing T139, or its mixed-order T140
variant, by controlling only the colliding decimal rays and then applying
coordinatewise magnitude bounds to the remaining frequencies.

Let $q=10^k$, $1\le r\le q$, and let $C_{q,r}(h)$ be the positive
Fourier coefficient of

\[
(\cos(2\pi t)-\cos(\pi/q))F_q(t)F_r(t).
\]

For $h=q+j$, $1\le j\le r-1$, its exact outer-support formula is

\[
C_{q,r}(q+j)=\frac{r-j}{2qr}
 +(1-\cos(\pi/q))\frac{(r-j)^3-(r-j)}{6qr}>0.
\]

## Singleton belt

Put

\[
J_{q,r}=\{1\le j\le\lfloor r/2\rfloor:10\nmid j\},
\qquad H_{q,r}=\{q+j:j\in J_{q,r}\}.
\]

Every $h\in H_{q,r}$ is indivisible by ten, its decimal primitive ray meets
the positive Fourier support only at $h$, and its T139 initial and terminal
endpoint blocks vanish. Thus its primitive coefficient has modulus exactly
$C_{q,r}(h)$, independently of the target label. If

\[
\Lambda_{q,r}=\sum_{h\in H_{q,r}} C_{q,r}(h),
\]

then direct summation gives the uniform bounds

\[
\Lambda_{q,q}\ge\frac{27}{160},\qquad
\Lambda_{q,4q/5}\ge\frac{27}{200}.
\]

More generally, the mixed kernel's zero coefficient is

\[
\mu_{q,r}=(1-\cos(\pi/q))\frac{3qr-r^2+1}{3q}-\frac1q.
\]

If $\mu_{q,r}>0$, then $r>q/5$, and the same belt satisfies

\[
\Lambda_{q,r}\ge\frac9{400}.
\]

Meanwhile the positive zero-mode margin is $O(1/q)$. Changing the mixed
Fejer order therefore cannot remove a constant amount of endpoint-free
singleton coefficient mass.

## Exact phase-blind limitation

For arbitrary complex coordinates with $|z_h|\le\varepsilon_hN$,

\[
\sup\left(-\frac2N\operatorname{Re}\sum_h p_hz_h\right)
=2\sum_h\varepsilon_h|p_h|.
\]

Hence a proof that controls all colliding rays, leaves the singleton belt at
coordinatewise caps, and finishes by the triangle inequality still needs
normalized singleton caps of order (1/q). This minimax statement is only
phase-blind: the maximizing disk vector need not be realizable by a decimal
orbit, so it is not an actual-orbit logical separator.

## Remaining arithmetic target

For $x_n=\{10^n\pi\}$, target centre
$c_{q,A}=(2A+1)/(2q)$, and

\[
H_{q,r,A}(N)=\sum_{j\in J_{q,r}}
C_{q,r}(q+j)e(-(q+j)c_{q,A})S_{q+j}(N),
\]

the identities $e(-qc_{q,A})=-1$ and
$e(qx_n)=e(x_{n+k})$ give the exact signed correlation

\[
H_{q,r,A}(N)=-\sum_{n=0}^{N-1}e(x_{n+k})
\sum_{j\in J_{q,r}}C_{q,r}(q+j)
e\bigl(j(x_n-c_{q,A})\bigr).
\]

This endpoint-free, lag-$k$, target-dependent correlation is the surviving
π-specific arithmetic object. No estimate for it is proved here. The result
supplies no π cancellation estimate, strict predicate separator, T124, V1,
or literature novelty; it only retires the phase-blind route described above.

## Predecessor channels and a diagonal-$L^2$ no-go

For $k\ge2$, put $Q=q/10$, write $A=aQ+A'$ and
$c'=(2A'+1)/(2Q)$, and let $d_n=\lfloor10x_n\rfloor$.  With
$\omega=e(1/10)$ and

\[
G_{q,s,A'}(y)=e\!\left(\frac{s(y-c')}{10}\right)
 \sum_{\ell=0}^{Q/2-1}C_{q,q}(q+10\ell+s)
 \,e\bigl(\ell(y-c')\bigr),
\qquad 1\le s\le9,
\]

the surviving target has the exact nine-channel form

\[
H_{q,q,A}(N)=-\sum_{n<N}e(x_{n+k})
 \sum_{s=1}^{9}\omega^{s(d_n-a)}G_{q,s,A'}(x_{n+1}).
\]

These are precisely the nine nontrivial predecessor-digit characters: their
mean over a hypothetical uniform predecessor digit is zero, while their mean
square is $\sum_{s=1}^9|G_{q,s,A'}(y)|^2$.  This identity is only a sharper
description of the surviving actual-$\pi$ target, not an estimate for it.

## Exact BBP carry cancellation and tail no-go

Let $y_n$, $\tau_n$, and $f_n$ be the canonical selected BBP orbit, error,
and seven-term rational forcing from T106.  With
$\rho=10/16^7$, they satisfy

\[
y_{n+1}=\{10y_n+f_n\},\qquad
f_n=10\tau_n-\tau_{n+1},\qquad
0\leq\tau_n<\rho^n,
\qquad x_n=\{y_n+\tau_n\}.
\]

Define the exact rational-forcing and tail-wrap carries

\[
b_n=\lfloor10y_n+f_n\rfloor,
\qquad m_n=\lfloor y_n+\tau_n\rfloor.
\]

The actual predecessor digit then obeys the exact identity

\[
d_n=b_n+m_{n+1}-10m_n.
\]

Because every frequency in $G_{q,s,A'}$ is $\ell+s/10$, its
quasi-periodicity is

\[
G_{q,s,A'}(z-m)=\omega^{-sm}G_{q,s,A'}(z)
\qquad(m\in\mathbb Z).
\]

Thus the factor $\omega^{s m_{n+1}}$ contributed by the digit carry cancels
the literal tail wrap in $G$ exactly.  For $k\geq2$, the singleton
correlation consequently has the exact decomposition

\[
H_{q,q,A}(N)=R_{q,A}(N)+\Delta_{q,A}(N),
\]

where

\[
R_{q,A}(N)=-\sum_{n<N}e(y_{n+k})
 \sum_{s=1}^9\omega^{s(b_n-a)}G_{q,s,A'}(y_{n+1})
\]

is a target-labelled rational BBP core.  Term by term, if $j=10\ell+s$,
the residual tail multiplier in $\Delta$ is exactly

\[
e\!\left(\tau_{n+k}+\frac j{10}\tau_{n+1}\right)-1.
\]

Writing

\[
\Lambda_q=\sum_{j\in J_{q,q}}C_{q,q}(q+j),
\qquad
M_q=\sum_{j\in J_{q,q}}jC_{q,q}(q+j),
\]

coefficient-adapted summation gives the uniform-in-$N$ bound

\[
|\Delta_{q,A}(N)|<B_{q,k}:=
\frac{2\pi}{1-\rho}
\left(\rho^k\Lambda_q+\frac{\rho}{10}M_q\right).
\]

Here $B_{q,k}=O(q)$ by a direct moment bound, while saturating
$|e(t)-1|$ by $2$ gives the sharper alternative $B_{q,k}=O(\log q)$; the
minimum of the two estimates is available.  Therefore, for each fixed
$q,A$,

\[
\frac{H_{q,q,A}(N)-R_{q,A}(N)}N\longrightarrow0,
\]

and relative to the unnormalized $N/q$ zero-mode scale the difference
vanishes whenever $N/(qB_{q,k})\to\infty$.  Hence the positive exact BBP
tail cannot itself supply extensive T139 cancellation.  This does not
exclude finite horizons $N\lesssim qB_{q,k}$, and it leaves the sign of
$R_{q,A}$, all other primitive rays, and the literal endpoint completely
open.  The broad tail coboundary was already latent in T107; the new content
here is only this exact target-labelled, carry-cancelled core and its
coefficient-adapted no-go.  No $\pi$ estimate, T139 premise, or V1 follows.

## Full primitive-polynomial tail stability (`proof sketch`)

The same tail no-go extends, without a lag-dependent loss, to all T139
primitive rays at once.  Fix $q=10^k$ with $k\geq1$ and $A<q$, and put

\[
\mathcal P_q=\{\operatorname{prim}_{10}(h):1\leq h\leq2q-1\},\qquad
p_{q,A}(u)=\sum_{\substack{1\leq h\leq2q-1\\
 \operatorname{prim}_{10}(h)=u}}C_{q,q}(h)e(-hc_{q,A}),
\]

\[
P_{q,A}(t)=\sum_{u\in\mathcal P_q}p_{q,A}(u)e(ut),\qquad
Z^x_{q,A}(N)=\sum_{n<N}P_{q,A}(x_n),\qquad
Z^y_{q,A}(N)=\sum_{n<N}P_{q,A}(y_n).
\]

Define

\[
m_q=\min\{m\in\mathbb N:\pi(2q-1)\rho^m\leq1\},
\qquad D_q=5m_q+\frac5{1-\rho}.
\]

The complete primitive coefficient load is less than $5/2$.  Since the
frequencies are integral, $e(ux_n)=e(uy_n)e(u\tau_n)$, and hence

\[
\sum_{n=0}^{\infty}|P_{q,A}(x_n)-P_{q,A}(y_n)|
 <D_q.
\]

Indeed, each summand is at most
$(5/2)\min\{2,2\pi(2q-1)\rho^n\}$; splitting at $m_q$ gives the displayed
bound.  Consequently, uniformly for every $N$,

\[
|Z^x_{q,A}(N)-Z^y_{q,A}(N)|<D_q,
\]

and for $N>0$ the corresponding normalized signed T139 terms differ by

\[
\left|{-\frac2N\operatorname{Re}Z^x_{q,A}(N)}
      +\frac2N\operatorname{Re}Z^y_{q,A}(N)\right|<\frac{2D_q}{N}.
\]

Thus passing from the selected rational orbit to the actual $\pi$ orbit
cannot amplify the positive BBP tail across the omitted primitive rays.  This
is only a stability estimate: it leaves cancellation in the selected rational
numerators, the T139 premise, and V1 open.

There is also a quantitative obstruction to the standard diagonal quadratic
route.  Let $V:\mathbb C^{\mathcal P_q}\to\mathbb C^N$ be the actual-orbit
evaluation operator $(Vz)_n=\sum_u z_u e(ux_n)$, and let $p$ be the full T139
primitive coefficient vector.  Every diagonal majorant

\[
V^*V\preceq D
\]

has $D_{u,u}\ge N$, since every column of $V$ has squared norm $N$.  Hence the
corresponding Cauchy--Schwarz certificate is bounded below, for every $N$, by

\[
2\sqrt{p^*Dp/N}\ge2\lVert p\rVert_2.
\]

The endpoint-free singleton coordinates give

\[
2\lVert p\rVert_2\ge\frac{9\sqrt5}{40\sqrt q}
\quad(q\ge100),
\qquad
\alpha_q(0)<\frac{\pi^2}{3q},
\]

and the remaining decimal scale $q=10$ satisfies the same strict comparison
by direct evaluation.  Thus $2\lVert p\rVert_2\gg q^{-1/2}>\alpha_q(0)
=O(q^{-1})$ at every decimal scale, independently of the horizon.  This rules
out scalar or weighted large-sieve arguments, and more generally any proof
that passes through such a frequency-diagonal Gram majorant.  It does **not**
rule out a direct actual-$\pi$ bound on $V^*\mathbf1$, a $p$-specific signed or
off-diagonal estimate, or a different quadratic argument retaining those
correlations.  No $\pi$ estimate or V1 consequence follows.

## Cofinal fixed-target termwise no-go (`proof sketch`)

At the concrete scale $q=100$, the rational core can be simplified further
without dropping its carries or forcing phase.  Put

\[
\Phi(t)=\sum_{\substack{1\le j\le49\\10\nmid j}}
 C_{100,100}(100+j)e((100+j)t),
\qquad z_n=y_n+\frac{f_n}{10}.
\]

If $r_A(n)$ is the $n$th summand of the carry-cancelled core above, direct
substitution of $y_{n+1}=10y_n+f_n-b_n$ twice gives the exact identity

\[
r_A(n)=e(f_{n+1})\Phi(z_n-c_{100,A}).
\]

A directed rational interval certificate constructs a selector
$\sigma:\mathbb N\to\{0,\ldots,99\}$, depending only on the fractional part
of $100z_n$, for which every $n$ satisfies

\[
\operatorname{Re}r_{\sigma(n)}(n)
 <-\frac{9343}{400000}<-\frac1{50}.
\]

The certificate uses 501 distinct mesh nodes and the exact coefficient
moments

\[
\sum_j C_{100,100}(100+j)<1,
\qquad
\sum_j jC_{100,100}(100+j)<7.
\]

The BBP error coboundary then transfers the same selector to the actual-$\pi$
singleton increment $\eta_A(n)$ with an error below $1/4000000$:

\[
\operatorname{Re}\eta_{\sigma(n)}(n)
 <-\frac{93429}{4000000}<-\frac1{50}.
\]

Since the selector has finite range, the exact, time-independent target

\[
A_*:=\min\{A<100:\{n:\sigma(n)=A\}\text{ is infinite}\}
\]

has both adverse bounds at arbitrarily late times.  Thus a finite transient
cannot produce, for every target, an eventual termwise estimate

\[
\operatorname{Re}\eta_A(n)\ge-\frac C{100}
\]

for any $C\le93429/40000$.  In particular it cannot do so with a constant
compatible with the endpoint-free T139 zero-mode budget, since

\[
C<C_{\mathrm{T139}}:=50\alpha_{100}(0)
=\frac{20001(1-\cos(\pi/100))-3}{6}
=1.144881020833854738\ldots .
\]

Reproduce the inclusive-T112 index checks, the directed interval bounds, and
the deterministic certificate hash with
[`bbp_q100_cofinal_fixed_target_obstruction.py`](../../../../workflows/experiments/bbp_q100_cofinal_fixed_target_obstruction.py).

This is only a cofinal obstruction to eventual **termwise** rehabilitation.
Positive increments at intervening times can still compensate in prefixes,
and the other primitive rays can compensate in the full T139 sum.  It proves
no adverse prefix, T139 failure, target hit, cancellation estimate, or V1.

## Full-primitive fixed-target prefix obstruction (`experiment`)

A separate actual-$\pi$ replay closes the compensation escape in the
preceding paragraph only for the two stronger, horizon-uniform mechanisms
stated here.  Fix $q=100$, $A=96$,
$c=193/200$, and let $\alpha(h)$ be the positive T128 coefficient.  On the
complete primitive support

\[
U=\{1\le u\le199:10\nmid u\},
\]

the exact collapsed coefficient is

\[
p(u)=\alpha(u)e(7u/200)
 +\mathbf1_{u\le19}\alpha(10u)e(7u/20)
 -\mathbf1_{u=1}\alpha(100).
\]

Put $P(t)=\sum_{u\in U}p(u)e(ut)$ and
$Z(N)=\sum_{n<N}P(x_n)$.  A standard-library, 190-digit Machin/Taylor replay
at the fixed horizon $N=107$ gives

\[
\begin{aligned}
\alpha(0)&=0.0228976204166770947639\ldots,\\
\operatorname{Re}P(x_{106})&=-0.2742511550856701156157\ldots,\\
\operatorname{Re}Z(107)&=-1.6785026447206228974210\ldots.
\end{aligned}
\]

The exact T139 endpoint specialization has real part
$0.2622735217394053984665\ldots$, and the direct uncompressed T128 sum agrees
with `Z + endpoint` in the replay.  Hence

\[
-\frac{100}{107}\operatorname{Re}Z(107)
=1.5686940604865634\ldots
>50\alpha(0)=1.1448810208338547\ldots,
\]

while the single complete-ray increment requires

\[
-100\operatorname{Re}P(x_{106})=27.4251155085670\ldots.
\]

Thus neither an all-prefix bound
$\operatorname{Re}Z(N)\ge-CN/100$ for every $N\ge1$ nor a termwise bound
$\operatorname{Re}P(x_n)\ge-C/100$ for every $n\ge0$ can hold with a
T139-compatible constant.  This is genuinely a full-primitive obstruction,
not a singleton calculation.  The first 108 post-decimal digits of $\pi$
contain no `96`, and the exact signed defect is
$0.0264715723921722897\ldots>\alpha(0)$, consistent with T128.

Reproduce the high-precision calculation with
[`t139_full_primitive_q100_A96_N107_replay.py`](../../../../workflows/experiments/t139_full_primitive_q100_A96_N107_replay.py).
This is a high-precision replay, not a formal directed-interval certificate;
the target was selected from finite data and is fixed throughout the witness.
One finite witness refutes the two universal mechanisms above, but it says
nothing about eventual or cofinal estimates, a favorable selected later
horizon, additive transient losses, off-diagonal cancellation, T139, or V1.
