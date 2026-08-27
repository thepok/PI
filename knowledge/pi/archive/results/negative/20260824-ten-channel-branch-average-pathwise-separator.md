# Ten-channel branch averaging does not imply pathwise carry contraction

Status: `proof sketch`

Date: 2026-08-24 UTC

Source: independently audited from
`workflows/state/chatgpt-pro/20260824-ten-channel-carry-contraction/answer.md`.

This note records a scoped separator for the ten-channel carry-flow route. It
proves no estimate for the orbit of π, no prescribed digit occurrence, and no
V1.

## Exact fixed-path construction

Let \(Q=10^m\) with \(m\ge1\), let \(v=4^m\), and write

\[
r_v=\frac{4(Q-1)}9,
\qquad
c_v=\frac{r_v+1/2}{Q}=\frac49+\frac1{18Q}.
\]

For the decimal map \(T(x)=10x\pmod1\), take the fixed orbit

\[
x_n=\frac49 \qquad(n\ge0).
\]

Relative to the suffix \(v\), its centered successor coordinate and
carry-corrected predecessor class are, at every time,

\[
y_n=x_{n+1}-c_v=-\frac1{18Q}=:y_* ,
\qquad \eta_n=4.
\]

Using the matching observable from the carry-flow note,

\[
H_Q(y)=K_{10Q}(y/10),
\]

the incoming-edge flows therefore satisfy, for every \(N\ge1\),

\[
P_{4\mid v}(N)=N H_Q(y_*),
\qquad
P_{d\mid v}(N)=0 \quad(d\ne4).
\]

Here \(H_Q(y_*)>0\). More strongly, the full boundary-kernel sum is positive
in class \(4\) and strictly negative in every other class:

\[
\Sigma_{4\mid v}(N)=N H_Q(y_*)>0,
\qquad
\Sigma_{d\mid v}(N)
=N K_{10Q}\!\left(\frac{4-d+y_*}{10}\right)<0
\quad(d\ne4).
\]

Let \(\omega=e^{2\pi i/10}\) and define the carry characters

\[
C_j(N)=\sum_{n<N}H_Q(y_n)\omega^{-j\eta_n}.
\]

For every nontrivial character \(1\le j\le9\),

\[
C_j(N)=N H_Q(y_*)\omega^{-4j},
\qquad
|C_j(N)|=N H_Q(y_*).
\]

Thus the true path has no character decay at any horizon. Since the weights
are real, the correct conjugacy is

\[
C_{10-j}(N)=\overline{C_j(N)}.
\]

## The averaged Fejer operator contracts the wrong object

Let \(P(y_*)\) be the circulant Fejér branch-averaging matrix from the
transfer-compatible kernel. Its sharp operator norm on the zero-sum channel
subspace is

\[
\rho_Q=
\sqrt{1-\frac9{25}\sin^2\!\left(\frac{\pi}{18Q}\right)}<1.
\]

The spectral gap has the corrected elementary bounds

\[
\boxed{
\frac1{450Q^2}\le1-\rho_Q\le\frac{\pi^2}{900Q^2}.
}
\]

Indeed, for

\[
u=\frac9{25}\sin^2\!\left(\frac{\pi}{18Q}\right),
\]

one has \(1-\rho_Q=u/(1+\rho_Q)\). The inequalities

\[
\sin\!\left(\frac\pi{18Q}\right)\ge\frac1{9Q},
\qquad
\sin\!\left(\frac\pi{18Q}\right)\le\frac\pi{18Q}
\]

then give the two displayed bounds. Hence iterating the branch-average matrix
suggests a \(Q^{-2}\)-scale loss, while the actual single branch chosen by the
orbit retains every nontrivial character with maximal magnitude.

## Exact scope of the separator

At the same suffix phase \(c_v+y_*\), the ten exact predecessors

\[
x_0^{(a)}=\frac{a+c_v+y_*}{10},
\qquad a=0,\ldots,9,
\]

have the same successor phase, scalar kernel profile, and Fejer
branch-averaging matrix, but their matching carry labels are \(a\). Cyclically
relabeling these ten channels preserves the matrix spectrum, induced norms,
purity, total mass, and the magnitudes of all carry characters, while moving
the unique positive target coordinate. The fixed orbit above supplies the
all-horizon realization for label \(4\).

Consequently, **branch-average spectral contraction and cyclic-label-invariant
summaries alone cannot be transferred to pathwise contraction of a prescribed
carry class**. This is not a claim that every ten-channel argument fails. It
does not exclude label-aware signed estimates, predecessor history,
stopping-time arguments, or arithmetic control special to π. Those are
exactly the routes capable of distinguishing the branch actually selected by
the orbit.
