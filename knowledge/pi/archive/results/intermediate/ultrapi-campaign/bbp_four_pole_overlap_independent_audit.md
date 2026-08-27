# Independent audit of the BBP four-pole Fourier-overlap obstruction

Audit date: **2026-08-12 UTC**

Target: [`bbp_four_pole_overlap_attack.md`](bbp_four_pole_overlap_attack.md)

Target SHA-256:
`9d9ff606cf0de438061e2a9245d0f0d3fc1cbfb784b1ca6be6aac76195a13545`

Primary checker SHA-256:
`418191b0e515a724c9bb51fb3c0853e27884fa0b155f68487831aa703168e750`

Self-audit SHA-256:
`e38fb9568e1665082dd15575f2359e6dab5c680527944fa37c5d60d15e81a5cb`

Self-audit checker SHA-256:
`9b2dde3acb182cd5e31282aa3673ea45a7e09c6028a7fe3e2a4a21924479ab9c`

Independent checker SHA-256:
`42a522f8b7c0c34df2a597bb0b303fd28e5d00fa10ac6c73ee74e9ce87e2f6e7`

Canonical question SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict and claim status

**PASS, with no further correction required.**  I independently rederived
the coefficient, the tail bound and its indices, the exact constant
$272\pi|q|/(45N)$, the diagonal recurrence, the Fourier telescope, every
frequency-ray assertion, the fixed-point obstruction, the fixed-lag
calculation, and the measure-theoretic separators.  I also replayed both
earlier checkers and wrote a third checker without importing either one.

The result remains a `proof sketch`.  The three checker outputs are
`experiment`; the dated literature search in the target is
`literature-checked`; and the separately cited T25 theorem is
`machine-checked`.  This audit proves no empirical-limit overlap, no Fourier
limit, no fixed return, and no decimal-cylinder hit.  In particular, V1
remains a `conjecture`; nothing audited here is a `candidate resolution` or a
`verified resolution`.

## 1. Independent derivation of the erasure bound

Writing the four BBP poles over a common denominator gives, exactly,

\[
a(k)=\frac{120k^2+151k+47}
{(2k+1)(4k+3)(8k+1)(8k+5)}>0.
\]

For $k\ge1$, direct subtraction gives

\[
\frac1{k^2}-a(k)=
\frac{392k^4+873k^3+665k^2+194k+15}
{k^2(2k+1)(4k+3)(8k+1)(8k+5)}>0.
\]

The first omitted index of the inclusive partial sum $B_n$ is $k=n+1$.
Consequently, including the boundary case $n=0$,

\[
\begin{aligned}
t_n
 &=10^n\sum_{k=n+1}^{\infty}\frac{a(k)}{16^k}\\
 &\le \frac{10^n}{(n+1)^2}
          \sum_{k=n+1}^{\infty}16^{-k}
  =\frac{(5/8)^n}{15(n+1)^2}.
\end{aligned}
\]

Dropping only $(n+1)^{-2}\le1$ yields

\[
             \sum_{n\ge0}t_n\le
             \frac1{15}\sum_{n\ge0}(5/8)^n=\frac8{45}.
\]

The two character differences have Lipschitz constants
$2\pi|16q|$ and $2\pi|q|$.  Thus their combined multiplier is
$2\pi(16+1)|q|=34\pi|q|$, and for every integer $q$ and positive integer
$N$,

\[
 |D_N^u(q)-D_N^\pi(q)|
 \le \frac{34\pi|q|}{N}\frac8{45}
 =\frac{272\pi|q|}{45N}.
\]

This also verifies the often error-prone factor of two: the constant is not
$136/45$, because the chord estimate for $e(mx)$ contains $2\pi|m|$.
For $q=0$, both defects and the right side are zero.  For $q<0$, the
absolute value is essential.  The normalized defect is undefined at $N=0$,
although the later unnormalized empty-sum telescope is valid there.

The implication is exactly the one stated in the target.  For each fixed
$q$, along the full sequence or a common subsequence tending to infinity,

\[
 D_N^u(q)\to0\quad\Longleftrightarrow\quad D_N^\pi(q)\to0.
\]

It does not supply either limit.

## 2. Recurrence, finite-tail indexing, and Fourier telescope

The inclusive definition of $B_n$ gives

\[
10^{n+1}B_{n+1}
=10(10^nB_n)+a(n+1)(5/8)^{n+1}.
\]

With

\[
\epsilon_{n+1}=a(n+1)(5/8)^{n+1},
\]

this proves

\[
u_{n+1}=\{10u_n+\epsilon_{n+1}\}.
\]

There is no shift error at $n=0$: $u_0=\{B_0\}$, and the first forcing
is $a(1)(5/8)$.  For the finite surrogate $B_M$, the identity

\[
t_{n,M}=10^n(B_M-B_n),\qquad
10t_{n,M}-t_{n+1,M}=\epsilon_{n+1}
\]

is valid exactly when $0\le n<M$.  At $n=M$, $t_{M,M}=0$, but
$t_{M+1,M}$ is outside the defined surrogate range; the corrected target
does not use that nonexistent boundary term.

For $Z_n(m)=e(mu_n)$, the recurrence gives

\[
Z_{n+1}(m)=e(m\epsilon_{n+1})Z_n(10m),
\]

so

\[
Z_n(10m)-Z_n(m)
=Z_{n+1}(m)-Z_n(m)
 +(e(-m\epsilon_{n+1})-1)Z_{n+1}(m).
\]

Summing proves the target's endpoint formula with the displayed sign.  Since
$\sum_n\epsilon_n<\infty$, its error series is absolutely convergent by

\[
|e(-m\epsilon)-1|\le2\pi|m|\epsilon.
\]

The telescope therefore bounds the unnormalized $10m$-versus-$m$ sum,
but contains no $16m$-versus-$m$ term.

## 3. Exact scope of the coboundary obstructions

The target keeps four logically different statements separate.  The
separation is necessary and is correct.

### Finite trigonometric transfer

For a nonzero integer $m$, remove every factor of $10$ to obtain its
signed ray core.  In

\[
\psi(10x)-\psi(x),
\]

each Fourier monomial contributes $+c_m$ at $10m$ and $-c_m$ at $m$,
so the coefficient sum on every ray is zero.  For nonzero $q$, the two
rays containing $q$ and $16q$ are distinct: equality would imply
$16=10^j$ for some integer $j$.  The target
$e(16qx)-e(qx)$ has signatures $+1$ and $-1$ on those two rays.
Therefore it is not a trigonometric-polynomial coboundary for any $q\ne0$.
This invariant says nothing by itself about an infinite Fourier series.

### Stationary continuous transfer

The point $1/9$ is fixed by multiplication by $10$, and

\[
e(16q/9)=e(q/9)\quad\Longleftrightarrow\quad3\mid q.
\]

Hence this particular fixed point excludes a continuous stationary
coboundary exactly when $3\nmid q$.  It supplies no obstruction for
$3\mid q$.  The proposed all-frequency overlap target includes $q=1$,
so the narrower fixed-point result is sufficient to close that proposed
stationary route; the report does not inflate it into an all-$q$ theorem.

### Uniformly asymptotically stationary transfer

If the identity in the target holds for every circle point,
$\psi_n\to\psi$ uniformly, and $r_n\to0$ uniformly, then
$F_n\to T_{10}$ uniformly and uniform continuity of $\psi$ gives

\[
\psi_{n+1}\circ F_n-\psi_n+r_n
 \longrightarrow \psi\circ T_{10}-\psi
\]

uniformly.  The $q=1$ fixed-point contradiction follows.  This proof does
not apply to pointwise-only convergence, unbounded or unstable transfer
functions, identities defined merely on the selected orbit, or nonlinear
orbit-specific cancellation.  All of those limitations are explicit in the
target.

### Rational scalar transfer

Under equation (21), summation through $K$ gives

\[
\sum_{k=0}^{K}\frac{a(k)}{16^k}
=R(0)-\frac{R(K+1)}{16^{K+1}}.
\]

A rational function grows at most polynomially, so the boundary tends to
zero.  The BBP identity would then give $\pi=R(0)\in\mathbb Q$, a
contradiction.  This excludes the stated rational/Gosper class, not an
arbitrary nonlinear or orbit-only identity.

## 4. Fixed-lag and measure-theoretic checks

Induction gives, for $h\ge1$,

\[
E_{n,h}=\sum_{j=1}^h10^{h-j}\epsilon_{n+j},\qquad
u_{n+h}=\{10^hu_n+E_{n,h}\}.
\]

Using $a(n+j)<(n+j)^{-2}\le(n+1)^{-2}$ proves the target's bound on
$E_{n,h}$.  Expanding the positive-lag correlation produces exactly the
four listed frequency differences.  None vanishes for $q\ne0,h\ge1$: the
only nontrivial candidate is $10^h=16$.  This shows that the recurrence
does not hand over a zero-frequency base case.  It does not rule out a
van-der-Corput argument equipped with genuinely new nonzero-frequency
estimates, and the target says so.

For slice averaging, the signed-measure identity

\[
S\bar\mu_M-\bar\mu_M=(S^M\mu-\mu)/M
\]

is exact for $M\ge1$.  The atoms $1/9,7/9,4/9$ are fixed by $T_{10}$,
are cyclically permuted by $T_{16}$, and are pairwise distinct.  Their
length-$M$ slice average is exactly $S$-stationary if and only if
$3\mid M$, while its stationarity defect has total-variation norm at most
$2/M$ for every $M$.  Thus asymptotic stationarity alone cannot imply
adjacent overlap.

Finally, the sparse-digit example is sound.  For digits zero at powers of
two and one elsewhere, a length-$L$ window is exceptional only if it
contains a power of two.  At most

\[
L\bigl(1+\lfloor\log_2(N+L)\rfloor\bigr)
\]

of the first $N$ starts are exceptional.  Every other suffix is within
$10^{-L}/9$ of $1/9$.  The digit string is not eventually periodic, so
the represented number is irrational, yet its decimal empirical measures
converge to $\delta_{1/9}$, whose $T_{16}$-pushforward is the mutually
singular atom $\delta_{7/9}$.

## 5. Checker and source audit

Both supplied checkers replayed successfully and reported

```text
status: PASS
asserts_overlap: false
asserts_fourier_limit: false
asserts_v1: false
```

The primary checker uses floating point only for explicitly labeled finite
Fourier diagnostics and for a redundant numerical replay of the character
telescope.  Its structural recurrence, finite surrogate, pin, and ray checks
use exact rational or integer arithmetic.  The self-audit checker improves
this by replaying the telescope in the exact group ring of rational circle
phases.  I found no inference from the finite diagnostics to convergence.

The independent companion
[`bbp_four_pole_overlap_independent_check.py`](bbp_four_pole_overlap_independent_check.py)
does not import either supplied checker.  It performs symbolic polynomial
expansion and 40,042 exact bounded checks, including:

- all signs and indices in the diagonal recurrence and exact group-ring
  telescope, including the empty telescope;
- 1,000 randomized finite-surrogate identities;
- positive, negative, and zero frequencies and the $N=0$ domain guard;
- 11,001 ray/coboundary checks and 20,001 fixed-point divisibility checks;
- 6,400 fixed-lag recurrence, bound, and nonzero-frequency checks;
- exact stationarity behavior through 300 lengths of the Dirac cycle; and
- 500 independently generated sparse-window counts.

The local source pins all match.  Direct text inspection confirms that
Bailey--Crandall presents the relevant conclusion under **Hypothesis A**,
not as a theorem, and that Lagarias explicitly states both the general
shadow relation and the failure of Hypothesis A for arbitrary perturbation
representations.  Those source statements support the report's restraint;
they do not prove the missing cross-ray estimate.

## 6. Final audit boundary

The strongest verified informal conclusion is precisely

\[
\boxed{
 |D_N^u(q)-D_N^\pi(q)|\le\frac{272\pi|q|}{45N},
 \qquad q\not\sim_{\times10}16q\ (q\ne0).}
\]

The first statement erases the summable BBP forcing at Cesaro scale; the
second blocks the named direct telescopes.  Neither bridges the two
frequency rays.  The target therefore passes this independent audit exactly
as a negative route diagnosis, with no overlap, Fourier-limit, or V1
overclaim.
