# Independent audit: BBP adjacent-shift matching

Audit date: **2026-08-13 UTC**

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt). The
immutable target is a local, human-authored question with no external source
URL; none is invented here.

Primary artifact:
[`bbp_adjacent_shift_matching_attack.md`](bbp_adjacent_shift_matching_attack.md)

Primary checker:
[`bbp_adjacent_shift_matching_check.py`](bbp_adjacent_shift_matching_check.py)

Independent checker:
[`bbp_adjacent_shift_matching_independent_check.py`](bbp_adjacent_shift_matching_independent_check.py)

## Verdict and claim boundary

**PASS after two narrow precision corrections.** The BBP coefficient and
endpoint \(1/30\), both tail estimates, both empirical coupling constants,
the recurrences and coefficient-difference formula, Proposition 3.1 with its
quantifier order, the weak-limit argument, measure domination,
nonatomicity, support propagation, Furstenberg application, and the
all-Fourier-frequency-to-\(C=1\)-matching implication all rederive.

The infinite argument remains a `proof sketch`; the bounded source audit is
`literature-checked` on the audit date; and both checkers produce only an
`experiment`. Neither checker treats finite data as proof.

The two exact unresolved mathematical obligations are:

1. prove one fixed \(C\), one sequence \(N_j\to\infty\), density-one sets
   \(G_j\), maps \(\sigma_j\) of congestion at most \(C\), and
   \(\delta_j\downarrow0\) satisfying the adjacent-row matching (18)--(19);
2. on that same sequence, prove
   \(\lim_{\rho\downarrow0}\limsup_j{\cal C}_{N_j}(\rho)=0\).

Neither is established. Equation (25), which would imply the first with
\(C=1\), is also unproved and would not by itself establish the second. Thus
no fixed-sixteen return and no instance of canonical V1 has been proved.
Canonical V1 remains a `conjecture`; this work is not a `candidate resolution`
or a `verified resolution`.

## Corrections recorded

The live pre-correction primary report had SHA-256
`f3dd35b0a41bba03d0268d8ac367c158c3a77b0040b979e56d28824369253f83`.
The final hash is recorded below. The primary checker required no edit.

1. Proposition 3.1 now calls \(N_j\) positive integers and \(\delta_j\)
   nonnegative reals. The previous wording was recoverable from the later
   conditions for all sufficiently large \(j\), but the corrected wording
   makes every \(I_{N_j}\), maximum, and modulus of continuity defined with
   no implicit finite-prefix convention.
2. The paragraph after (25) now quantifies \(q\in\mathbb Z\), first proves
   that the Prokhorov distance between \((T_{16})_*\eta_{N_j}\) and
   \(\eta_{N_j}\) tends to zero, and then explicitly invokes (12) to replace
   the first row by the required shifted row \(\xi_{N_j}\). Without naming
   this second step, the old phrase “the two empirical rows” was ambiguous:
   a matching of \(T_{16}u_n\) to \(u_m\) does not literally satisfy (19),
   whose left entries are \(v_n\). The \(O(1/N_j)\) coupling in (12) closes
   the step.

A coordinating reviewer also reported a duplicate sentence after (28).
The live snapshot available at the start of this independent audit already
contained the sentence exactly once, so no second deletion was made. The
independent checker freezes the final count at one.

## Frozen artifact and source pins

| file | SHA-256 |
|---|---|
| problems/local/pi-digits.txt | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| bbp_adjacent_shift_matching_attack.md | `2764624665fcb2bd4f7a7f8d4a1c4d1094e9459297e018cb095e0a76ff0feba6` |
| bbp_adjacent_shift_matching_check.py | `a800bf01ac2149d646481d600500e0b9db4e49d6cb1786c279cfc3406e3c543d` |
| bbp_adjacent_shift_matching_independent_check.py | `6560c5f9c90b2950a584f05be47fd39ab946c63c3da587d394078ff18518f56d` |
| BBP 1997 local PDF | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias arXiv v2 local PDF | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Furstenberg 1967 local PDF | `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` |
| T69T69FixedSixteenReturn.lean | `fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9` |
| T70T70EmpiricalRigidityBridge.lean | `f8ecbfd2d9f8a13216e75d5ebb3732b98f7844147776b30de7f2666fc7ddec55` |

The independent checker pins every entry in this table except itself. Its
hash above freezes the checked bytes without a self-referential pin.

## 1. Coefficient, endpoint, tails, and constants

Putting the four BBP poles over a common denominator gives exactly

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)}.
\]

All factors are positive for \(k\ge0\). For \(k\ge1\), direct subtraction
gives

\[
 \frac1{k^2}-a(k)=
 \frac{392k^4+873k^3+665k^2+194k+15}
 {k^2(2k+1)(4k+3)(8k+1)(8k+5)}>0.              \tag{I1}
\]

Thus the inclusive partial sum \(B_n\) has first omitted index \(n+1\), and

\[
\begin{aligned}
0<10^n(\pi-B_n)
&<\frac{10^n}{(n+1)^2}\sum_{k=n+1}^{\infty}16^{-k}\\
&=\frac{(5/8)^n}{15(n+1)^2}.
\end{aligned}                                                   \tag{I2}
\]

The weak inequality in (5) is therefore safe.

At the endpoint,

\[
 a(0)=\frac{47}{15},\qquad
 16a(0)-\frac1{30}=\frac{501}{10}.
\]

Consequently

\[
 \widetilde B_n=\frac1{30}+16(B_{n+1}-a(0)),\qquad
 \widetilde B_\infty=16\pi-\frac{501}{10}.
\]

For \(n\ge1\), \(501\,10^{n-1}\) is an integer, which is exactly why the
endpoint statement begins at \(n=1\). Splitting \(B_{n+1}\) after \(B_n\)
then gives on the circle

\[
 v_n=T_{16}u_n+a(n+1)(5/8)^n.                         \tag{I3}
\]

The shifted tail begins at \(k=n+1\). Since
\(a(k+1)<1/(k+1)^2\le1/(n+2)^2\),

\[
 0<10^n(\widetilde B_\infty-\widetilde B_n)
 <\frac{(5/8)^n}{15(n+2)^2}.                         \tag{I4}
\]

The report again states only the safe weak inequality.

Pairing the indices in (I3) and using \(a(n+1)<1\) gives

\[
 W_1(\xi_N,(T_{16})_*\eta_N)
 \le\frac1N\sum_{n=1}^Na(n+1)(5/8)^n
 <\frac1N\sum_{n=1}^{\infty}(5/8)^n
 =\frac5{3N}.                                        \tag{I5}
\]

Similarly, (I4) gives the claimed comparison with the actual shifted orbit:

\[
 \frac1N\sum_{n=1}^N
 \frac{(5/8)^n}{15(n+2)^2}
 <\frac1{15N}\sum_{n=1}^{\infty}(5/8)^n
 =\frac1{9N}.                                        \tag{I6}
\]

Both constants are deliberately loose but correct. They tend to zero
synchronously on every subsequence, so
\(\eta_{N_j}\Rightarrow\mu\) indeed implies
\(\xi_{N_j}\Rightarrow(T_{16})_*\mu\).

## 2. Recurrences and coefficient difference

Using the inclusive last term of \(B_{n+1}\) gives

\[
u_{n+1}=T_{10}u_n+a(n+1)(5/8)^{n+1}.
\]

The corresponding new term of \(\widetilde B_{n+1}\) is
\(a(n+2)16^{-(n+1)}\), giving

\[
v_{n+1}=T_{10}v_n+a(n+2)(5/8)^{n+1}.
\]

Direct rational subtraction gives exactly

\[
a(k+1)-a(k)=
\frac{-3(40960k^5+220672k^4+453632k^3+443480k^2+206712k+36903)}
{(2k+1)(2k+3)(4k+3)(4k+7)(8k+1)(8k+5)(8k+9)(8k+13)}.
\]

Every denominator factor and every numerator coefficient is positive for
\(k\ge0\), so the difference is negative. Its leading-degree ratio is
\(-15/(32k^3)\), which verifies the stated \(O(k^{-3})\). Multiplication by
\((5/8)^{n+1}\) makes the forcing difference summable, but the expanding map
does not turn this into control of different initial conditions.

## 3. Proposition 3.1 and quantifier order

The corrected proposition has the order

\[
\exists C\ge1\ \exists(N_j,G_j,\sigma_j,\delta_j)_{j\ge1}
\quad N_j\to\infty,\quad\delta_j\to0,
\]

with \(C\) independent of \(j\), followed by

\[
       \lim_{\rho\downarrow0}\limsup_{j\to\infty}
       {\cal C}_{N_j}(\rho)=0.                         \tag{I7}
\]

The \(j\)-limit is correctly inside the \(\rho\)-limit. Reversing them would
only detect exact collisions in each finite row; for a finite row of
distinct points the small-radius energy is \(1/N_j\), which vanishes as
\(j\to\infty\) without proving asymptotic anti-concentration.

Let \(x_n=T_{10}^n\alpha\). Equation (I2) gives
\(d(u_n,x_n)\le t_n\), with \(\sum_nt_n<\infty\). Hence the empirical
measures of \(u_1,\ldots,u_N\) and \(x_1,\ldots,x_N\) have Wasserstein
distance \(O(1/N)\). The exact endpoint telescope

\[
 \frac1N\sum_{n=1}^N(f(T_{10}x_n)-f(x_n))
 =\frac{f(x_{N+1})-f(x_1)}N
\]

shows that every weak limit \(\mu\) is \(T_{10}\)-invariant. Since every
\(x_n\) lies in the closed set \(K_\pi\), the same comparison and
Portmanteau show \(\operatorname{supp}\mu\subseteq K_\pi\). This verifies
the weak-limit invariance and support claim, including the use of the same
subsequence as (14).

For continuous \(f\ge0\), the matching gives

\[
\begin{aligned}
\int f\,d\xi_{N_j}
&\le \frac1{N_j}\sum_{n\in G_j}f(u_{\sigma_j(n)})
   +\omega_f(\delta_j)
   +\lVert f\rVert_\infty\frac{|I_{N_j}\setminus G_j|}{N_j}\\
&\le C\int f\,d\eta_{N_j}+o(1).
\end{aligned}
\]

Passing to the limits identified above proves
\((T_{16})_*\mu\le C\mu\). The congestion bound is used in the correct
direction; neither injectivity nor surjectivity is smuggled into this step.

To audit nonatomicity, suppose \(\mu\{x\}=p>0\). For any \(\rho>0\), choose
\(0<r<\rho/2\) such that \(\mu(\partial B(x,r))=0\). Such an \(r\) exists
because distinct metric spheres about \(x\) are disjoint and only countably
many can have positive mass. Weak convergence on this continuity set gives
\(\eta_{N_j}(B(x,r))\to\mu(B(x,r))\ge p\). All ordered pairs of points in
the ball have distance below \(\rho\), so

\[
 \liminf_j{\cal C}_{N_j}(\rho)\ge p^2/4.
\]

This holds for every \(\rho>0\), contradicting (I7). The proof therefore
uses the exact required order of limits and establishes nonatomicity.

## 4. Support dynamics and Furstenberg

For a continuous map \(F\) on a compact space and a finite Borel measure,

\[
          \operatorname{supp}(F_*\mu)=F(\operatorname{supp}\mu). \tag{I8}
\]

The forward inclusion follows by pulling neighborhoods back to
neighborhoods of support points. For the reverse inclusion,
\(F(\operatorname{supp}\mu)\) is compact and therefore closed; a point
outside it has an open neighborhood whose inverse image misses the support
and has measure zero. Compactness is the needed hypothesis, and it is
present here.

Measure domination gives
\(\operatorname{supp}((T_{16})_*\mu)\subseteq\operatorname{supp}\mu\).
Together with (I8), this is exactly

\[
T_{16}(\operatorname{supp}\mu)\subseteq\operatorname{supp}\mu.
\]

\(T_{10}\)-invariance gives the analogous forward invariance under
\(T_{10}\). A probability on the second-countable circle gives full mass
to its support. Since \(\mu\) is nonatomic, the countable rational points
have mass zero, so the support contains an irrational \(z\).

The semigroup \(\{10^a16^b:a,b\ge0\}\) is non-lacunary in Furstenberg's
sense. If 10 and 16 were powers of one integer, their prime valuations
would be proportional, contradicted by the prime 5. Theorem IV.1 therefore
makes the joint forward orbit of \(z\) dense. Forward invariance puts that
entire orbit in the closed support, forcing

\[
\operatorname{supp}\mu=\mathbb T\subseteq K_\pi.
\]

Thus Proposition 3.1 is a valid sufficient criterion. The theorem is not
being applied to a rational point, a two-circle joining, or a merely
measure-one nonclosed set.

## 5. Why all Fourier frequencies imply \(C=1\) matching

Put \(\lambda_j=(T_{16})_*\eta_{N_j}\). Equation (25), for every fixed
\(q\in\mathbb Z\), says that the \(q\)-th Fourier coefficient difference of
\(\lambda_j\) and \(\eta_{N_j}\) tends to zero. If their Prokhorov distance
did not tend to zero, compactness of the probability measures on the circle
would give a further subsequence with
\(\eta_{N_j}\Rightarrow\lambda\) while the distances stay positive. On
that subsequence, all Fourier coefficients of \((T_{16})_*\lambda\) and
\(\lambda\) agree. Trigonometric-polynomial density makes the measures
equal, contradicting the positive limiting distance. Hence

\[
 d_{\rm P}(\lambda_j,\eta_{N_j})\to0.
\]

Equation (I5) also gives
\(d_{\rm P}(\xi_{N_j},\lambda_j)\to0\), so the triangle inequality yields

\[
             d_{\rm P}(\xi_{N_j},\eta_{N_j})\to0.      \tag{I9}
\]

Choose \(\varepsilon_j\downarrow0\) strictly above the last distance.
Strassen--Dudley gives a coupling of the two empirical probabilities with
mass at least \(1-\varepsilon_j\) on pairs at distance at most
\(\varepsilon_j\). Duplicate atom locations cause no problem: split each
coupling mass uniformly among the corresponding indexed copies to obtain an
\(N_j\times N_j\) nonnegative matrix with every row and column sum
\(1/N_j\).

Form the bipartite graph of nearby indexed pairs. If a vertex cover has
\(r\) vertices, all nearby coupling mass is incident to it and is at most
\(r/N_j\), even allowing double counting. Thus every cover has at least
\((1-\varepsilon_j)N_j\) vertices. König's theorem supplies a matching of
at least that size. Its left endpoints give \(G_j\), and the right endpoints
give an injective \(\sigma_j\). Therefore (18)--(19) hold with \(C=1\) and
\(\delta_j=\varepsilon_j\). This proves the advertised implication, but
does not assert (25) for the BBP rows and does not imply (20).

## 6. Generic separators

For

\[
                    \beta=\sum_{r\ge1}10^{-2^r},
\]

the decimal digits equal one exactly at positions \(2^r\). This stream is
not eventually periodic: for any proposed positive period \(p\), take
\(2^r>p\) beyond the alleged preperiod; then
\(2^r<2^r+p<2^{r+1}\), so periodicity would put a one at a non-power of two.
Thus \(\beta\) is irrational.

Among the first \(N\) suffixes, each power of two can contaminate at most
\(L\) length-\(L\) prefixes, giving the safe bound

\[
 L(1+\lfloor\log_2(N+L)\rfloor).
\]

Every other suffix is at most \(10^{-L}/9\). For fixed \(L\) the bad
proportion tends to zero as \(N\to\infty\), and then \(L\to\infty\) proves
empirical convergence to \(\delta_0\). The same estimate shows that for
each fixed \(\rho>0\), a density-one set of points lies in a ball of radius
below \(\rho/2\), so the close-pair energy tends to one. This exactly
separates irrationality and common empirical invariance from (20).

The second separator is also exact: both \(\beta\) and \(1/9\) satisfy the
unforced recurrence \(z_{n+1}=T_{10}z_n\), while their empirical limits are
\(\delta_0\) and \(\delta_{1/9}\). Hence even identical forcing cannot
control two expanding trajectories with different initial phases. The
report correctly limits both examples to generic deductions and does not
claim that they preserve the four-pole BBP coefficient.

## 7. Source and search audit

The local hashes in the primary report all match. Direct PDF-text inspection
found the exact advertised locators:

- Bailey--Borwein--Plouffe, Theorem 1, contains the four-pole base-16
  identity for pi; it contains no empirical-distribution theorem.
- Lagarias, Theorem 3.1, gives the perturbed-radix shadow relation, and
  Theorem 3.3 gives the finite-limit-set rationality criterion. Neither
  establishes either premise of Proposition 3.1.
- Furstenberg, Definition IV.1 and Theorem IV.1, define non-lacunary integer
  semigroups and give density at every irrational circle point, exactly as
  used above.

Dudley's 1968 article metadata and the Prokhorov coupling statement were
rechecked, as were Cameron's Theorems 2.1 and 2.2 for Hall's theorem and the
König matching/vertex-cover equality. These two contextual references are
still accurately disclosed as external and not locally pinned; neither is
used inside Proposition 3.1.

Fresh repetitions of the four quoted searches produced no relevant primary
result proving adjacent BBP matching or close-pair anti-concentration for
pi. This supports only the report's dated bounded-search statement. It is
not an exhaustive absence claim and supplies no novelty status.

The local mathlib names also exist at the recorded locations:
`Measure.support_mono`,
`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, and
`Measure.absolutelyContinuous_of_le_smul`. They are plausible
ingredients for a future formalization; their existence is not itself a
formalization of Proposition 3.1.

## 8. Replay and hygiene

The independent checker does not import the primary checker. It pins the
primary artifacts and local sources, independently reconstructs the rational
states through depth 160 with a depth-240 finite surrogate, and performs:

- 482 coefficient-bound and 484 coefficient-difference checks;
- 320 recurrence and 320 adjacent-state checks;
- 640 finite-tail-majorant checks;
- exact checks of \(1/30\), \(501/10\), \(5/3\), and \(1/9\);
- sparse-window and finite periodicity-separator checks;
- source-marker, UTF-8, C0-byte, claim-boundary, and duplicate-line checks;
  and
- a subprocess replay of the unchanged primary checker.

Both scripts return `PASS` with every fixed-return, matching-hypothesis,
anti-concentration, and V1 assertion flag set to false. Python compilation,
`git diff --check`, and a direct line-length scan also pass. The installed
`ruff` command is a generic auto-venv shim with no underlying ruff module in
this repository, so it could not provide an additional lint result; no tool
was silently substituted.

These checks can catch algebraic, indexing, pin, and hygiene regressions.
They do not turn finite verification into a proof of either remaining
asymptotic obligation.
