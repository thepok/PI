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
