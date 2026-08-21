# BBP adjacent-shift matching: a one-sided empirical route to the fixed return

Audit date: **2026-08-13 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable local question has no external source URL; none is invented.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained. Canonical V1 remains a `conjecture`.

This branch gives one exact coefficient-specific normal form and one new
sufficient criterion, both recorded as a `proof sketch`.

1. Multiplication by \(16\) is exactly an **adjacent shift of the actual BBP
   coefficient**, after the single endpoint correction \(1/30\). If \(u_n\)
   is the usual diagonal BBP state and \(v_n\) is the corrected shifted state,
   then for every \(n\geq1\)

   \[
       v_n=16u_n+a(n+1)(5/8)^n\pmod1.                 \tag{A}
   \]

   Their empirical measures differ by \(O(1/N)\) from the actual
   multiplication-by-\(16\) pushforward, synchronously along every
   subsequence. This is unconditional and uses the four-pole coefficient,
   not merely its denominator.
2. Full Fourier equality is stronger than necessary. It would suffice to
   match all but \(o(N_j)\) shifted states \(v_n\) within \(o(1)\) of original
   states \(u_m\), with one fixed bound on the number matched to any \(u_m\),
   and simultaneously prove a vanishing close-pair energy for the original
   row. The matching gives one-sided measure domination, hence forward
   \(\times16\)-invariance of a support; the collision estimate makes the
   limiting measure nonatomic. Furstenberg then makes that support the whole
   circle. No ergodicity, equality of measures, or all-frequency Weyl limit
   is required.
3. Neither finite target has been proved for the BBP rows. Exact computation
   below is only an `experiment`. Two generic examples show that summably
   close forcing and even a common invariant empirical limit do not supply
   the missing matching-plus-anti-concentration estimates.

## 1. Normalized target and quantifiers

Write \(T_bx=bx\pmod1\), \(\alpha=\pi\pmod1\), and

\[
 K_\pi=\overline{\{T_{10}^n\alpha:n\geq0\}}.
\]

Canonical V1 is

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists n\geq0\ \forall i<m:\ d_{n+i}(\pi)=w_i.       \tag{1}
\]

The decimal expansion is unambiguous because pi is irrational. The audited
T69/Furstenberg reduction is

\[
 \mathrm{V1}\iff K_\pi=\mathbb T
 \iff T_{16}\alpha\in K_\pi
 \iff \liminf_n\|(10^n-16)\pi\|_{\mathbb T}=0.          \tag{2}
\]

Every limit in the criterion below has the order

\[
 \exists C\ \exists(N_j,G_j,\sigma_j,\delta_j)_j\
 \quad N_j\to\infty,\quad \delta_j\to0,
\]

followed by a close-pair limit in which \(j\to\infty\) is taken before
\(\rho\downarrow0\). Reversing those quantifiers would turn a finite
separation fact into a false asymptotic claim.

## 2. The corrected adjacent BBP shift

For the standard four-pole coefficient put

\[
 a(k)={4\over8k+1}-{2\over8k+4}-{1\over8k+5}-{1\over8k+6}
 ={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)}                             \tag{3}
\]

and

\[
 B_n=\sum_{k=0}^n{a(k)\over16^k},\qquad
 u_n=\{10^nB_n\}.                                      \tag{4}
\]

The BBP identity says \(B_n\to\pi\). As in the preceding empirical audit,
\(a(k)>0\), \(a(k)<k^{-2}\) for \(k\geq1\), and

\[
 0<t_n:=10^n(\pi-B_n)
 \leq{(5/8)^n\over15(n+1)^2}.                          \tag{5}
\]

Now shift the **coefficient**, not the time index, and correct its endpoint:

\[
 \widetilde B_n={1\over30}+\sum_{k=0}^n{a(k+1)\over16^k},
 \qquad v_n=\{10^n\widetilde B_n\}.                    \tag{6}
\]

Since \(a(0)=47/15\),

\[
 \widetilde B_n={1\over30}+16(B_{n+1}-a(0)),\qquad
 16a(0)-{1\over30}={501\over10}.                       \tag{7}
\]

Therefore the limiting constant is

\[
 \widetilde B_\infty=16\pi-{501\over10},               \tag{8}
\]

and for every \(n\geq1\)

\[
 \{10^n\widetilde B_\infty\}=\{16\,10^n\pi\},          \tag{9}
\]

because \(501\,10^{n-1}\) is an integer. Splitting the last term of
\(B_{n+1}\) in (7) gives the exact finite relation

\[
 \boxed{v_n=T_{16}u_n+d_n,\qquad
 d_n=a(n+1)(5/8)^n}\quad(n\geq1).                      \tag{10}
\]

This is the promised adjacent-shift normal form. If

\[
 \eta_N={1\over N}\sum_{n=1}^N\delta_{u_n},\qquad
 \xi_N={1\over N}\sum_{n=1}^N\delta_{v_n},             \tag{11}
\]

then pairing equal indices in (10) and using (3) gives

\[
 W_1\bigl(\xi_N,(T_{16})_*\eta_N\bigr)
 \leq {1\over N}\sum_{n=1}^Nd_n
 <{5\over3N}.                                          \tag{12}
\]

There is also a direct shifted-tail bound. From (8),

\[
 0<10^n(\widetilde B_\infty-\widetilde B_n)
 \leq{(5/8)^n\over15(n+2)^2},                          \tag{13}
\]

so \(\xi_N\) is within \(1/(9N)\) of the empirical measure of the actual
states \(T_{16}T_{10}^n\alpha\), \(1\leq n\leq N\).
Consequently, synchronously for every subsequence,

\[
             \eta_{N_j}\Rightarrow\mu
 \quad\Longrightarrow\quad
             \xi_{N_j}\Rightarrow(T_{16})_*\mu.        \tag{14}
\]

The original and shifted recurrences are

\[
\begin{aligned}
 u_{n+1}&=T_{10}u_n+a(n+1)(5/8)^{n+1},\\
 v_{n+1}&=T_{10}v_n+a(n+2)(5/8)^{n+1}.
\end{aligned}                                          \tag{15}
\]

Their forcing difference is exponentially summable and even has an extra
inverse power of \(n\). Indeed

\[
 a(k+1)-a(k)=
 {-3(40960k^5+220672k^4+453632k^3+443480k^2+206712k+36903)
  \over
 (2k+1)(2k+3)(4k+3)(4k+7)(8k+1)(8k+5)(8k+9)(8k+13)},  \tag{16}
\]

so it is negative and \(O(k^{-3})\). Equation (16) is useful structure, but
expansion by ten means that summable forcing difference does not control the
two initial conditions.

## 3. Bounded-congestion matching criterion

For \(N\geq1\) let \(I_N=\{1,\ldots,N\}\), and define the close-pair energy

\[
 {\cal C}_N(\rho)={1\over N^2}
 \#\{(m,n)\in I_N^2:\operatorname{dist}(u_m,u_n)<\rho\}. \tag{17}
\]

**Proposition 3.1 (`proof sketch`).** Suppose there are a fixed integer
\(C\geq1\), positive integers \(N_j\to\infty\), sets
\(G_j\subseteq I_{N_j}\), maps \(\sigma_j:G_j\to I_{N_j}\), and nonnegative
reals \(\delta_j\to0\) such that

\[
 {\lvert G_j\rvert\over N_j}\to1,\qquad
 \max_{m\in I_{N_j}}\lvert\sigma_j^{-1}(m)\rvert\leq C, \tag{18}
\]

\[
 \max_{n\in G_j}\operatorname{dist}
       (v_n,u_{\sigma_j(n)})\leq\delta_j,              \tag{19}
\]

and

\[
 \lim_{\rho\downarrow0}\ \limsup_{j\to\infty}
                 {\cal C}_{N_j}(\rho)=0.              \tag{20}
\]

Then \(K_\pi=\mathbb T\), and hence V1 holds.

**Proof.** By compactness of the probability measures, pass to a further
subsequence with \(\eta_{N_j}\Rightarrow\mu\). Equations (5) and (11) show
that \(\mu\) is a \(T_{10}\)-invariant probability supported on \(K_\pi\).
Equation (14) gives

\[
                         \xi_{N_j}\Rightarrow(T_{16})_*\mu. \tag{21}
\]

For any continuous \(f\geq0\), uniform continuity, (18), and (19) give

\[
 {1\over N_j}\sum_{n=1}^{N_j}f(v_n)
 \leq C{1\over N_j}\sum_{m=1}^{N_j}f(u_m)
      +\omega_f(\delta_j)
      +\|f\|_\infty{\lvert I_{N_j}\setminus G_j\rvert\over N_j}. \tag{22}
\]

Taking limits and using the Riesz order characterization for finite Borel
measures proves the measure inequality

\[
                         (T_{16})_*\mu\leq C\mu.       \tag{23}
\]

Condition (20) makes \(\mu\) nonatomic. To see the required quantifiers,
suppose instead that \(\mu\{x\}=p>0\), and fix \(\rho>0\). The spheres
\(\{y:\operatorname{dist}(x,y)=r\}\), \(r>0\), are pairwise disjoint, so only
countably many have positive \(\mu\)-measure. Choose
\(0<r<\rho/2\) outside that exceptional set and put \(U=B(x,r)\). Then
\(\mu(\partial U)=0\), so weak convergence on this continuity set gives

\[
 \eta_{N_j}(U)\longrightarrow\mu(U)\geq p.             \tag{23a}
\]

Thus \(\eta_{N_j}(U)\geq p/2\) eventually. Every two points of \(U\) have
distance \(<2r<\rho\), so

\[
 \liminf_{j\to\infty}{\cal C}_{N_j}(\rho)\geq p^2/4.  \tag{23b}
\]

This holds for every \(\rho>0\), contradicting (20). Hence \(\mu\) is
nonatomic.

For a continuous map of a compact space,

\[
 \operatorname{supp}((T_{16})_*\mu)
       =T_{16}(\operatorname{supp}\mu).                \tag{24}
\]

The domination (23) therefore makes \(\operatorname{supp}\mu\) forward
invariant under \(T_{16}\); \(T_{10}\)-invariance of \(\mu\) gives the other
generator. The complement of the support is \(\mu\)-null, and nonatomicity
makes the countable rational points \(\mu\)-null, so there is an irrational
\(z\in\operatorname{supp}\mu\). Furstenberg's Theorem IV.1 makes
\(\{10^a16^bz:a,b\geq0\}\) dense. This whole orbit lies in the closed
support, so

\[
 \operatorname{supp}\mu=\mathbb T\subseteq K_\pi.
\]

Thus \(K_\pi=\mathbb T\), and the audited decimal-cylinder bridge gives
V1. \(\square\)

The criterion is deliberately one-sided. A bijection with vanishing
bottleneck distance would give \(C=1\), but neither surjectivity nor equality
of the limiting measures is needed. In particular, (18)--(19) ask for a
bounded-congestion transport of the adjacent coefficient row, which is
strictly less information than the all-frequency equality

\[
 {1\over N_j}\sum_{n\leq N_j}
       (e(16qu_n)-e(qu_n))\longrightarrow0
 \quad\text{for every fixed }q\in\mathbb Z.           \tag{25}
\]

Here is the precise finite implication, included only to justify the
comparison.  If the Prokhorov distance between \((T_{16})_*\eta_{N_j}\) and
\(\eta_{N_j}\) did not tend to zero, compactness would give a further
subsequence on which \(\eta_{N_j}\Rightarrow\lambda\) while those distances
stay bounded away from zero.  Equation (25) makes every Fourier coefficient
of \((T_{16})_*\lambda\) and \(\lambda\) equal, a contradiction.  Thus that
Prokhorov distance tends to zero.  Equation (12) also makes the Prokhorov
distance between \(\xi_{N_j}\) and \((T_{16})_*\eta_{N_j}\) tend to zero, so
the Prokhorov distance between the actual two empirical rows \(\xi_{N_j}\)
and \(\eta_{N_j}\) tends to zero. Choose
\(\varepsilon_j\to0\) strictly above that distance. The
Strassen--Dudley theorem supplies a coupling with mass at least
\(1-\varepsilon_j\) on pairs at distance at most \(\varepsilon_j\). Lift it
to an \(N_j\times N_j\) coupling matrix on the indexed atoms, whose row and
column sums are \(1/N_j\), and form the bipartite graph of those nearby
pairs. Every vertex cover catches the nearby coupling mass but has coupling
capacity at most its cardinality divided by \(N_j\). Thus every vertex cover
has at least \((1-\varepsilon_j)N_j\) vertices. König's theorem gives a
matching of the same minimum size. Its left endpoints form \(G_j\), its
matched right endpoints define an injective \(\sigma_j\), and (18)--(19)
hold with \(C=1\) and \(\delta_j=\varepsilon_j\). Hence (25) really does
imply the matching premise. Neither theorem is used in the proof of
Proposition 3.1 itself.

The converse at the measure level is false: domination by a fixed \(C>1\)
permits unequal probabilities. For example
\(\nu=(3\delta_0+\delta_{1/9})/4\leq
2(\delta_0+\delta_{1/9})/2=2\mu\), although \(\nu\ne\mu\); both are
\(T_{10}\)-invariant.

The separate condition (20) is essential; the next section gives an exact
counterexample if it is omitted.

## 4. Quantifier and generic-counterexample audit

### Common empirical invariance does not see an irrational seed

Let

\[
                     \beta=\sum_{r\geq1}10^{-2^r}.    \tag{26}
\]

Its decimal stream has a \(1\) at positions \(2^r\) and zero elsewhere, so it
is not eventually periodic and \(\beta\) is irrational. For a fixed window
length \(L\), at most

\[
              L\bigl(1+\lfloor\log_2(N+L)\rfloor\bigr) \tag{27}
\]

of the first \(N\) suffixes see a \(1\) in their first \(L\) digits. Every
other suffix is at most \(10^{-L}/9\). First let \(N\to\infty\), then
\(L\to\infty\): the empirical measures of \(T_{10}^n\beta\) converge to
\(\delta_0\). Hence

\[
             (T_{16})_*\delta_0=\delta_0              \tag{28}
\]

and even exact common empirical invariance holds, while the decimal orbit of
\(\beta\) omits every digit \(2,\ldots,9\). Its close-pair energy tends to
one for every fixed \(\rho>0\), so (20) fails exactly where required.

This also shows why “the seed is irrational” cannot replace “the limiting
support contains an irrational point.” A density-one empirical limit may
forget all sparse information responsible for irrationality.

### Summably close forcing does not control empirical measures

The exact orbits of \(\beta\) and \(1/9\) both obey the same unforced
recurrence \(z_{n+1}=T_{10}z_n\), yet their empirical limits are respectively
\(\delta_0\) and \(\delta_{1/9}\). Thus even **identical** forcing does not
force overlap between two expanding trajectories with different initial
conditions. The \(O((5/8)^n n^{-3})\) difference in (15)--(16) cannot by
itself prove (18)--(19).

Neither example preserves the four-pole coefficient (3). They refute only
generic deductions that discard its selected initial phase; they are not
counterexamples to the BBP matching target for pi.

## 5. Exact replay and finite diagnostics

The companion
[`bbp_adjacent_shift_matching_check.py`](bbp_adjacent_shift_matching_check.py)
has SHA-256
`a800bf01ac2149d646481d600500e0b9db4e49d6cb1786c279cfc3406e3c543d`.

- pins the canonical question, the three primary sources, T69, T70, and the
  preceding BBP empirical/Fourier reports;
- reconstructs both rational recurrences and checks (3), (7), (10), (15),
  and (16) with exact rational arithmetic;
- checks the direct partial-sum and shifted-tail identities;
- checks the stated universal coupling sums;
- replays the sparse-digit bound (27); and
- prints finite cyclic-order bottleneck matchings and close-pair energies,
  explicitly labeled `experiment`.

At \(N=40,80,160,320\), the minimum bottleneck among cyclic
order-preserving bijections in the replay is approximately
\(0.1246,0.0728,0.0617,0.0404\). The values are compatible with a diffuse
finite sample, but they prove neither (18)--(20) nor any infinite statement.

## 6. Primary-source and applicability audit

Status of this bounded source check: `literature-checked` on
**2026-08-13 UTC**.

| source | exact use | local SHA-256 |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*, Theorem 1](https://doi.org/10.1090/S0025-5718-97-00856-9) | the exact series (3)--(5), not an empirical-distribution theorem | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias, [*On the Normality of Arithmetical Constants*, Theorems 3.1 and 3.3](https://arxiv.org/abs/math/0101055v2) | perturbed-radix shadowing and the finite-limit-set rationality criterion; neither excludes an atomic empirical limit with an infinite omega-limit set | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Furstenberg, [*Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation*, Theorem IV.1](https://doi.org/10.1007/BF01692494) | density of the joint \(\times10,\times16\) orbit of an irrational support point | `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358` |
| Dudley, [*Distances of Probability Measures and Random Variables*](https://doi.org/10.1214/aoms/1177698137), pp. 1563--1572 | the Prokhorov/nearby-variable coupling theorem used only for the contextual implication after (25) | external primary-source page checked 2026-08-13; not pinned locally |
| Hall--König matching theorem; [Cameron, Theorems 2.1 and 2.2](https://doi.org/10.1112/jlms.70378) | the finite vertex-cover-to-matching step used only for the contextual implication after (25) | external source page checked 2026-08-13; not pinned locally |

Fresh searches for `BBP adjacent coefficient empirical measure`,
`perturbed radix bounded congestion matching`, `G-function atomic empirical
limit`, and `times 10 times 16 quasi-invariant support` located no primary
theorem establishing either (18)--(19) or (20) for pi. This is a dated,
bounded applicability search, not an exhaustive absence or novelty claim.
A local mathlib search located `Measure.support_mono`, the open-set
Portmanteau liminf theorem, and
`absolutelyContinuous_of_le_smul`; those cover the measure-theoretic core if
Proposition 3.1 is later formalized, so no parallel support infrastructure is
needed.

## Bottom line

The exact four-pole formula converts the previously opaque
\(\times16\)-pushforward into the corrected adjacent coefficient stream (6).
That is a genuinely coefficient-specific normalization. Proposition 3.1
then replaces T70's ergodicity-plus-nonsingularity route and the stronger
Fourier-equality route by two finite rational targets: bounded-congestion
matching and collision anti-concentration. Both remain unproved. The
canonical fixed return (2), and therefore V1, remain unproved.
