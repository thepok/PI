# BBP four-pole Fourier overlap: summable erasure and a frequency-ray obstruction

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No unconditional overlap between a decimal empirical limit of pi and its
multiplication-by-16 pushforward was proved.  No Fourier limit, fixed return,
decimal-cylinder hit, or proof that every finite decimal word occurs in pi
was obtained.  Canonical V1 remains a `conjecture`.

The actual four-pole coefficient nevertheless gives two useful exact
conclusions, recorded as a `proof sketch`.

1. Its contribution to the desired Fourier average is **summably erased**.
   For every fixed integer frequency \(q\), the BBP average differs from the
   corresponding average on the actual decimal orbit of pi by at most

   \[
                    {272\pi |q|\over45N}.                       \tag{1}
   \]

   Thus the proposed BBP Fourier target is exactly as hard, at the level of
   Cesaro limits, as the same-time \(\times16\) Fourier target for
   \(\{10^n\pi\}\).  The four poles do not leave a residual main term to
   estimate.
2. The exact recurrence does provide a Fourier telescope, but only between
   frequencies \(q\) and \(10q\).  It never mixes the distinct
   multiplication-by-10 frequency rays containing \(q\) and \(16q\).
   Consequently the desired observable is not a finite trigonometric
   coboundary.  At \(q=1\), evaluation at the fixed point \(1/9\) rules out
   even an arbitrary continuous stationary coboundary, and also rules out a
   natural class of asymptotically stationary nonautonomous coboundaries.

A coefficient-specific, orbit-only nonlinear identity could still exist;
the arguments below do not rule that out.  Finding one would be genuinely
new input.  The mathematical conclusions in this note have claim label
`proof sketch`; the bounded checker output is an `experiment`; and the dated
source search is `literature-checked`.  No new statement in this note is
`machine-checked` (the cited T25 dependency is); nothing is a `candidate
resolution` or a `verified resolution`.

## 1. Exact target and quantifiers

For every integer \(k\ge0\), put

\[
 a(k)={4\over8k+1}-{2\over8k+4}-{1\over8k+5}-{1\over8k+6}
 ={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},                                \tag{2}
\]

and

\[
 B_n=\sum_{k=0}^n{a(k)\over16^k},\qquad
 u_n=\{10^nB_n\},\qquad x_n=\{10^n\pi\}.                    \tag{3}
\]

The coefficient is positive.  The actual BBP tail estimate gives, on the
circle,

\[
 d_{\mathbb T}(u_n,x_n)\le t_n:=10^n(\pi-B_n)
 \le{(5/8)^n\over15(n+1)^2}.                                 \tag{4}
\]

This is exponentially stronger than the \(O(1/n)\) starting estimate.  In
particular,

\[
                         \sum_{n\ge0}t_n\le {8\over45}.        \tag{5}
\]

Write \(e(z)=\exp(2\pi iz)\), and for every \(N\ge1\) and fixed
\(q\in\mathbb Z\) define

\[
 \begin{aligned}
 D_N^u(q)&={1\over N}\sum_{n<N}
       \bigl(e(16qu_n)-e(qu_n)\bigr),\\
 D_N^\pi(q)&={1\over N}\sum_{n<N}
       \bigl(e(16qx_n)-e(qx_n)\bigr).
\end{aligned}                                                \tag{6}
\]

The normalization deliberately requires \(N\ge1\); there is no \(N=0\)
average.  At the boundary frequency \(q=0\), every summand in (6) is zero,
so both defects vanish identically.  All substantive frequency statements
below therefore concern \(q\ne0\), and every subsequence \((N_j)\) is
understood to consist of positive integers with \(N_j\to\infty\).

The proposed equality-of-pushforwards target is

\[
                  D_N^u(q)\longrightarrow0
       \quad\hbox{for every fixed }q\in\mathbb Z.             \tag{7}
\]

Along one subsequence on which the empirical measures converge, (7) for all
fixed \(q\) identifies the limit with its \(\times16\) pushforward.  Equality
is stronger than the non-mutual-singularity hypothesis in T70; failure to
prove (7) does not rule out a weaker direct overlap proof.

## 2. The four-pole contribution disappears at Cesaro scale

The circle character \(z\mapsto e(mz)\) is \(2\pi|m|\)-Lipschitz.  Equations
(4)--(5) therefore give the unconditional estimate

\[
\begin{aligned}
 |D_N^u(q)-D_N^\pi(q)|
 &\le {1\over N}\sum_{n<N}
    \{2\pi|16q|t_n+2\pi|q|t_n\}\\
 &\le {34\pi|q|\over N}\sum_{n\ge0}t_n
 \le {272\pi|q|\over45N}.                                   \tag{8}
\end{aligned}
\]

Hence, for the full sequence or along any common subsequence
\(N_j\to\infty\),

\[
        D_N^u(q)\to0\quad\Longleftrightarrow\quad
        D_N^\pi(q)\to0.                                      \tag{9}
\]

This is the main obstruction found in the present attack.  The exact
four-pole forcing does not merely become small; its entire possible effect
on this average has the explicit \(O_q(N^{-1})\) bound (8).  Any successful
coefficient-specific proof must use an arithmetic identity that controls the
selected value of pi itself, not only the asymptotic size of the forcing.

The finite-surrogate version is completely rational.  Fix \(M\ge1\), replace
pi by \(B_M\), and for \(0\le n\le M\) put

\[
 t_{n,M}=10^n(B_M-B_n).
\]

Then, for \(0\le n<M\),

\[
 \{10^nB_M\}=u_n+t_{n,M}\pmod1,qquad
             10t_{n,M}-t_{n+1,M}=\epsilon_{n+1},              \tag{10}
\]

where

\[
 \epsilon_{n+1}=a(n+1)(5/8)^{n+1}.                            \tag{11}
\]

The checker replays (10) with exact fractions; no stored decimal digits of
pi enter it.

## 3. The one exact Fourier telescope stays on power-of-ten rays

Let

\[
                         Z_n(m)=e(mu_n).
\]

The exact BBP recurrence is

\[
 u_{n+1}=\{10u_n+\epsilon_{n+1}\},
\]

and hence

\[
                   Z_{n+1}(m)=e(m\epsilon_{n+1})Z_n(10m).      \tag{12}
\]

Solving (12) for \(Z_n(10m)\) and summing gives, for every \(N\ge0\), the
genuine endpoint telescope

\[
\begin{aligned}
 \sum_{n<N}\{Z_n(10m)-Z_n(m)\}
 &=Z_N(m)-Z_0(m)\\
 &\quad+\sum_{n<N}
   \bigl(e(-m\epsilon_{n+1})-1\bigr)Z_{n+1}(m).               \tag{13}
\end{aligned}
\]

For \(n\ge1\), direct expansion gives

\[
 {1\over n^2}-a(n)
 ={392n^4+873n^3+665n^2+194n+15\over
   n^2(2n+1)(4n+3)(8n+1)(8n+5)}>0.                           \tag{14}
\]

Thus \(\sum_n\epsilon_n<\infty\).  The second line of (13) converges
absolutely, and division by \(N\) proves the known \(\times10\)-invariance
of every empirical limit.  This is the only direct averaged recurrence
provided by (12).

The coefficient sequence is indeed special: \(\epsilon_n\) is
hypergeometric, and its exact first-order rational quotient is checked at
1,199 consecutive indices.  But that quotient appears in the scalar factor
\(e(m\epsilon_{n+1})\); it does not change the frequency map

\[
                              m\longmapsto10m.                 \tag{15}
\]

The frequencies \(q\) and \(16q\) lie on distinct rays under (15) for every
nonzero integer \(q\), since \(16\) is not an integral power of 10.

## 4. Exact coboundary no-go results

### 4.1 No finite Fourier coboundary

For a nonzero integer \(m\), call two frequencies equivalent when one is
obtained from the other by multiplying by an integral power of 10 in either
direction while staying integral.  If

\[
                         \psi(x)=\sum_m c_me(mx)
\]

is a trigonometric polynomial, then every term of

\[
                         \psi(10x)-\psi(x)                    \tag{16}
\]

contributes \(+c_m\) and \(-c_m\) on the same frequency ray.  Consequently
the sum of Fourier coefficients on each ray is zero.

For

\[
                         \phi_q(x)=e(16qx)-e(qx),              \tag{17}
\]

the ray containing \(16q\) has coefficient sum \(+1\), while the distinct
ray containing \(q\) has sum \(-1\).  Therefore

\[
             \phi_q\ne\psi\circ T_{10}-\psi                  \tag{18}
\]

for every trigonometric polynomial \(\psi\) and every \(q\ne0\).  The
checker implements this ray signature with exact integers.

### 4.2 No continuous stationary coboundary at the needed first frequency

The point \(z=1/9\) is fixed by \(T_{10}\).  Any continuous coboundary
\(\psi\circ T_{10}-\psi\) vanishes at \(z\).  But

\[
 \phi_q(1/9)=0
 \quad\Longleftrightarrow\quad {15q\over9}\in\mathbb Z
 \quad\Longleftrightarrow\quad3\mid q.                        \tag{19}
\]

In particular \(\phi_1(1/9)\ne0\), so no continuous stationary transfer
function telescopes the \(q=1\) target.  Since (7) requires \(q=1\), this
already closes the stationary continuous-coboundary route.

### 4.3 No uniformly asymptotically stationary universal coboundary

Put \(F_n(x)=10x+\epsilon_{n+1}\pmod1\).  Suppose continuous functions
\(\psi_n\) converge uniformly to \(\psi\), continuous residuals \(r_n\)
converge uniformly to zero, and the universal identity

\[
 \phi_1(x)=\psi_{n+1}(F_nx)-\psi_n(x)+r_n(x)                  \tag{20}
\]

holds for every circle point \(x\).  Since \(F_n\to T_{10}\) uniformly,
uniform convergence and uniform continuity let \(n\to\infty\) in (20),
giving

\[
                         \phi_1=\psi\circ T_{10}-\psi,
\]

contrary to (19).  Thus a time-dependent universal telescope must fail at
least one of the natural stability properties in (20).  An identity only
along the actual BBP orbit is not excluded.

### 4.4 No rational scalar BBP telescope

A different temptation is to telescope the four-pole scalar series before
exponentiating.  If a rational function \(R(k)\), with no poles on the
nonnegative integers, satisfied

\[
 {a(k)\over16^k}={R(k)\over16^k}-{R(k+1)\over16^{k+1}},       \tag{21}
\]

then the right boundary would tend to zero and the BBP identity would give
\(\pi=R(0)\in\mathbb Q\), contradicting the irrationality of pi.  The same
argument rules out a Gosper-style hypergeometric antidifference equal to a
rational multiple of the summand.  The exact hypergeometric recurrence is
therefore not a hidden rational tail formula.

Equations (18)--(21) rigorously falsify broad, explicitly stated telescope
classes.  They do not prove that no highly orbit-specific nonlinear
cancellation exists.

## 5. Fixed-lag averaged recurrences do not cross the rays

Iteration of (12)'s phase recurrence gives, for every fixed \(h\ge1\),

\[
 u_{n+h}=\left\{10^hu_n+E_{n,h}\right\},\qquad
 E_{n,h}=\sum_{j=1}^h10^{h-j}\epsilon_{n+j}.                  \tag{22}
\]

Using (14),

\[
 0<E_{n,h}\le{(5/8)^n\over(n+1)^2}
       \sum_{j=1}^h10^{h-j}(5/8)^j.                           \tag{23}
\]

Thus every fixed-lag single-character transfer stays on a
multiplication-by-10 frequency ray.  More specifically, expanding a
positive-lag pair correlation of the two-character observable (17) produces
the four frequency differences

\[
 16q10^h-16q,\quad16q10^h-q,\quad q10^h-16q,\quad q10^h-q,
\]

none of which is zero for \(q\ne0\) and \(h\ge1\); the only tempting equality
would be \(10^h=16\).  This does not rule out a van-der-Corput proof using new
estimates for those nonzero-frequency averages.  It does show that the BBP
recurrence supplies no zero-frequency base case: it closes on two separate
frequency rays.

## 6. Cesaro selection and asymptotic stationarity

For \(N\ge1\), compactness always gives a convergent subsequence of the
empirical measures

\[
                         \eta_N={1\over N}\sum_{n<N}\delta_{u_n}.
\]

If \(\eta_{N_j}\Rightarrow\mu\), continuity gives
\((T_{16})_*\eta_{N_j}\Rightarrow(T_{16})_*\mu\).  It gives no shared
component between the two limits.  Equation (8) shows that replacing
\(u_n\) by the actual pi orbit does not improve this selection step.

There is a standard way to manufacture asymptotic \(T_{16}\)-stationarity.
For any probability \(\mu\), let \(S=(T_{16})_*\), fix \(M\ge1\), and

\[
                        \bar\mu_M={1\over M}\sum_{t<M}S^t\mu.
\]

Then, as signed measures,

\[
                 S\bar\mu_M-\bar\mu_M={S^M\mu-\mu\over M}.   \tag{24}
\]

Every weak limit of \(\bar\mu_M\) is \(S\)-invariant.  If \(\mu\) is
\(T_{10}\)-invariant, so is the average because the maps commute.  But the
average is supported on a union of pushed slices, not necessarily on the
original decimal orbit closure, and (24) says nothing about nonsingularity of
the adjacent pair \(\mu,S\mu\).

The exact three-cycle

\[
          \delta_{1/9}\mathop{\longmapsto}^{S}\delta_{7/9}
          \mathop{\longmapsto}^{S}\delta_{4/9}
          \mathop{\longmapsto}^{S}\delta_{1/9}                \tag{25}
\]

already demonstrates the logical gap.  All three probabilities are
\(T_{10}\)-invariant and pairwise mutually singular.  Their slice Cesaro
average is exactly stationary whenever \(3\mid M\), and (24) makes it
asymptotically stationary for arbitrary \(M\to\infty\).  The previously audited
[fixed-return dynamics separator](fixed_return_dynamics_attack.md) is
stronger: it gives nonatomic ergodic positive-entropy probabilities
\(S^t\mu_9\) which are pairwise mutually singular even though their Cesaro
averages converge to Lebesgue measure.  The separator and its independent
audit have respective SHA-256 pins
`147969553dbb57d9678b9351953d2142f3d4984af4ff5ffa752362a6dd7839e7`
and
`9cf83b4db60886d0d4488d0e93ff31c410748681309fc95e677778d5a81c7d32`.

Irrationality of the seed does not repair compactness alone.  Define a
decimal \(\beta\) whose digits are 0 at positions \(2^j\) and 1 elsewhere.
The digit sequence is not eventually periodic, so \(\beta\) is irrational.
For any fixed window length \(L\), at most
\(L(1+\lfloor\log_2(N+L)\rfloor)\) of the first \(N\) suffixes see a zero in
their first \(L\) positions: each relevant power of two excludes at most
\(L\) starts.  All other suffixes lie within \(10^{-L}/9\) of \(1/9\).
First let \(N\to\infty\), then \(L\to\infty\); the decimal empirical
measures converge to \(\delta_{1/9}\), whose pushforward is the singular
measure \(\delta_{7/9}\).

These examples do not preserve the actual four-pole coefficient.  Their
precise role is to prove that subsequence selection, asymptotic stationarity,
irrationality, and even much stronger generic measure data cannot supply
overlap without a coefficient-specific selector.

## 7. Exact replay and bounded computation

The companion
[`bbp_four_pole_overlap_check.py`](bbp_four_pole_overlap_check.py):

- pins the canonical question, the preceding empirical audit, the prior
  fixed-return report and independent audit, T25, and the three primary
  BBP/Lagarias sources;
- reconstructs \(u_n\) with exact fractions through depth 1,200;
- checks 1,199 exact hypergeometric forcing quotients, 180 rational
  finite-tail coboundaries, and 9,600 exact frequency-transfer identities;
- verifies the frequency-ray signature and fixed-point obstruction with
  exact integer/rational arithmetic;
- replays the exact power-of-ten telescope, the singular Dirac cycle, the
  slice-Cesaro endpoint bound, and the sparse-digit density estimate; and
- prints finite Fourier magnitudes at six depths, explicitly as an
  `experiment`.

Its SHA-256 is
`418191b0e515a724c9bb51fb3c0853e27884fa0b155f68487831aa703168e750`.
Replay from the repository root with

```bash
python work/ultrapi-resume/bbp_four_pole_overlap_check.py
```

At \(N=1200\), for example, the normalized \(\times10\) defect magnitudes
for \(q=1,\ldots,8\) lie between about 0.0011 and 0.0026, as forced by the
bounded telescope.  The requested \(\times16\) diagnostics range from about
0.0024 to 0.0811.  Their irregular finite behavior proves neither
convergence nor nonconvergence.

Expected status fields are:

```text
status: PASS
claim_label: experiment
asserts_overlap: false
asserts_fourier_limit: false
asserts_v1: false
```

## 8. Primary literature and mathlib search

Search date: **2026-08-12 UTC**.

- Bailey, Borwein, and Plouffe,
  [*On the Rapid Computation of Various Polylogarithmic Constants*,
  Math. Comp. 66 (1997)](https://doi.org/10.1090/S0025-5718-97-00856-9),
  supplies the exact four-pole identity (2).  Local official PDF SHA-256:
  `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`.
- Bailey and Crandall,
  [*On the Random Character of Fundamental Constant Expansions*,
  Experimental Mathematics 10 (2001)](https://doi.org/10.1080/10586458.2001.10504441),
  writes the combined coefficient \(a(n-1)\) exactly in its equation (3),
  but labels the equidistribution conclusion **Hypothesis A**.  It does not
  prove (7) or a cross-base overlap statement.  Local PDF SHA-256:
  `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8`.
- Lagarias,
  [*On the Normality of Arithmetical Constants*, Experimental Mathematics
  10 (2001), Theorem 3.1 and Remarks](https://arxiv.org/abs/math/0101055v2),
  proves the general perturbed-radix shadow relation and stresses that every
  real number admits such a perturbation representation, while the proposed
  dichotomy is false in that generality.  This directly supports the
  coefficient-erasure boundary above.  Local PDF SHA-256:
  `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9`.
- The local mathlib search found general measure pushforwards, mutual
  singularity, Fourier analysis on the additive circle, and Cesaro-limit
  lemmas, but no ready theorem that converts an asymptotically stationary
  nonautonomous orbit into nonsingularity with a commuting pushforward.
  The repository's
  [`T25T25PowerTenFrequencyShift.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T25T25PowerTenFrequencyShift.lean)
  already machine-checks the exact \(10^t\)-frequency boundary identity;
  its SHA-256 is
  `8fcef4b46de5f2589390327e4f0c9dc929855920120eede74692621416cabf80`.

Fresh searches covered BBP Hypothesis A, BBP normality, exponential sums for
named lacunary orbits, expanding-map coboundaries, and empirical
pushforwards.  No primary source located in this bounded search proves (7),
non-mutual-singularity for a decimal empirical limit of pi, or a theorem
that bypasses the named-point issue.  Absence from this search is not a
novelty claim.

## 9. Handoff

The attempted route did not prove the T70 overlap premise.  It did isolate
why the most natural BBP attack cannot do so:

\[
 \boxed{
 \text{four-pole forcing}
 \xrightarrow[\text{Fourier defect}]{O_q(1/N)}
 \text{actual decimal orbit},
 \qquad q\not\sim_{\times10}16q.}
\]

Future work should not retry asymptotic stationarity in the universal-uniform
or Cesaro-only forms excluded here, finite Fourier coboundaries, rational
Gosper telescoping, or Cesaro averaging of pushed slices.  A viable
continuation must exploit a genuinely orbit-specific
arithmetic feature of the exact selected four-pole sum that survives (8),
or attack non-mutual-singularity directly by a method weaker than equality of
all Fourier coefficients.  Until then, T70 remains conditional and V1
remains unproved.
