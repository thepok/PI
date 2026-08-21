# BBP fibre matching: exact endpoint and a coefficient-preserving separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

## Outcome and claim boundary

No bounded-congestion matching for the actual pi rows is established, and no
fixed-sixteen return is established.  Thus canonical V1 remains a
`conjecture`.

The useful outcome is a sharper endpoint and a stronger no-go, both recorded
as a `proof sketch`.

1. For two convergent empirical rows on a compact metric space, a
   positive-mass, vanishing-distance matching with any fixed congestion is
   **equivalent** to non-mutual-singularity of the two limiting measures.
   Density-one bounded-congestion matching is equivalent to domination of the
   first limit by a fixed multiple of the second.  These converses use only
   fine continuity-set partitions and finite matchings inside their atoms.
2. Consequently, if the BBP empirical limit is \(T_{10}\)-ergodic, the
   positive-mass target (40bc) is equivalent to
   \((T_{16})_*\mu=\mu\).  It is a finite realization of the full missing
   common-invariance statement, not a logically weaker limit-measure
   hypothesis.  Density-one matching is equivalent to the same statement in
   this ergodic setting.
3. The exact identity \(T_5v_n=T_8u_{n+1}\) contains no cancellation
   information: after passage to a \(T_{10}\)-invariant limit it is the
   tautology \(T_5(T_{16})_*\mu=T_8\mu\).  An explicit Bernoulli separator can
   be lifted through the **same four-pole BBP forcing**.  It has an ergodic,
   nonatomic, positive-entropy limit, satisfies every fixed-period noncollapse
   condition, and satisfies all adjacent and fibre identities, while its two
   limiting measures are mutually singular.  Hence it admits no positive-mass
   bounded-congestion matching.

The separator does not retain rationality of every finite BBP truncation.
That is important: it rules out deductions using only the recurrence,
four-pole forcing, fibre identity, ergodicity, entropy, and noncollapse, but
does not rule out a genuinely pi-specific argument using the selected
rational phase or its odd numerators.

## 1. Exact target and retained BBP notation

Canonical V1 is

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists n\geq0\ \forall i<m:\quad d_{n+i}(\pi)=w_i.       \tag{1}
\]

Leading zeroes are allowed, occurrence is contiguous, and the empty word is
vacuous.  The two other readings recorded in the canonical source are not
substituted for (1).

Put

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},                              \tag{2}
\]

and, as in the independently audited adjacent-row reduction,

\[
 u_n=\{10^nB_n\},\qquad
 v_n=\left\{10^n\left({1\over30}+
                   \sum_{k=0}^n{a(k+1)\over16^k}\right)\right\}. \tag{3}
\]

For \(n\geq1\), on the circle,

\[
\begin{aligned}
 v_n&=T_{16}u_n+d_n,&d_n&=a(n+1)(5/8)^n,\\
 u_{n+1}&=T_{10}u_n+\epsilon_{n+1},
   &\epsilon_{n+1}&=a(n+1)(5/8)^{n+1},\\
 v_{n+1}&=T_{10}v_n+a(n+2)(5/8)^{n+1},&&\\
 T_5v_n&=T_8u_{n+1}.&&                                  \tag{4}
\end{aligned}
\]

The last equality follows from \(5d_n=8\epsilon_{n+1}\).  It is exact, not
an asymptotic tail comparison.

## 2. What finite matching means at the limiting measure

Let \(X\) be a compact metric space, let \(x_n,y_n\in X\), and suppose along
one sequence \(N_j\to\infty\)

\[
 {1\over N_j}\sum_{n\leq N_j}\delta_{x_n}\Rightarrow\mu,
 \qquad
 {1\over N_j}\sum_{n\leq N_j}\delta_{y_n}\Rightarrow\nu. \tag{5}
\]

### Proposition 2.1 (positive mass; `proof sketch`)

The following are equivalent.

* The measures \(\mu\) and \(\nu\) are not mutually singular.
* After passing to a further subsequence, there are a fixed integer
  \(C\geq1\), a number \(\gamma>0\), sets
  \(G_j\subseteq\{1,\ldots,N_j\}\), maps
  \(\sigma_j:G_j\to\{1,\ldots,N_j\}\), and \(\delta_j\downarrow0\) such that

  \[
   {|G_j|\over N_j}\geq\gamma,
   \quad\max_m|\sigma_j^{-1}(m)|\leq C,
   \quad\max_{n\in G_j}d(y_n,x_{\sigma_j(n)})\leq\delta_j. \tag{6}
  \]

Moreover, the reverse implication can always be realized with \(C=1\).

For the forward direction from (6), put mass \(1/N_j\) on every matched
pair.  A weak limit \(\Lambda\) is nonzero, is supported on the diagonal,
and its two marginals coincide with a nonzero measure \(\rho\) satisfying

\[
                       \rho\leq\nu,\qquad \rho\leq C\mu. \tag{7}
\]

Thus mutual singularity is impossible.

Conversely, non-mutual-singularity supplies a nonzero common submeasure
\(\rho\leq\mu,\nu\).  For example, relative to \(\lambda=\mu+\nu\), take
the density

\[
 {d\rho\over d\lambda}=
 \min\left\{{d\mu\over d\lambda},{d\nu\over d\lambda}\right\}. \tag{8}
\]

For each \(r>0\), compactness gives a finite Borel partition into sets of
diameter below \(r\) whose boundaries are null for both measures.  Weak
convergence makes all atom counts converge.  Match, injectively and within
each atom, the smaller of the two counts.  The matched proportion tends to

\[
       \sum_A\min\{\mu(A),\nu(A)\}\geq\sum_A\rho(A)=\rho(X)>0. \tag{9}
\]

A diagonal choice \(r\downarrow0\) gives (6) with \(C=1\).

### Proposition 2.2 (density one; `proof sketch`)

With (5) fixed, the following quantified statements are equivalent:

* there are an integer \(C\geq1\), a further subsequence, sets and maps as in
  (6), and \(\delta_j\downarrow0\), with \(|G_j|/N_j\to1\); and
* there is an integer \(C\geq1\) such that

\[
                              \nu\leq C\mu.             \tag{10}
\]

The same \(C\) may be used in both statements.  A finite initial segment is
irrelevant.  If domination is first known with a nonintegral finite constant,
replace it by its ceiling.

The implication from matching is the nonnegative-continuous-function
argument already used in (40ak).  Conversely, use the same fine
continuity-set partitions.  In each atom, give every \(x\)-index \(C\)
slots.  Equation (10) says the limiting \(y\)-count never exceeds the total
slot count; the sum of the finitely many rounding deficits is \(o(N_j)\).
Matching inside atoms gives distance at most their diameter and leaves only
\(o(N_j)\) \(y\)-indices unmatched.

These propositions identify exactly what the finite combinatorics can and
cannot add.  They do not establish (7) or (10) for the actual rows.

## 3. Ergodicity collapses both matching targets to invariance

For the BBP rows, (4) and the summable tail comparison give

\[
 \eta_{N_j}\Rightarrow\mu
 \quad\Longrightarrow\quad
 \xi_{N_j}\Rightarrow\nu=(T_{16})_*\mu.               \tag{11}
\]

Every such \(\mu\) is \(T_{10}\)-invariant.  If it is also
\(T_{10}\)-ergodic, then \(\nu\) is \(T_{10}\)-invariant and ergodic because
\(T_{10}\) and \(T_{16}\) commute.  Two distinct ergodic invariant
probabilities for the same map are mutually singular.  Propositions 2.1 and
2.2 therefore give the exact equivalences

\[
\begin{aligned}
 &\text{positive-mass bounded-congestion matching}\\
 &\qquad\Longleftrightarrow\quad \mu\not\perp\nu
 \quad\Longleftrightarrow\quad \boxed{(T_{16})_*\mu=\mu}, \tag{12}\\
 &\text{density-one bounded-congestion matching}
 \quad\Longleftrightarrow\quad \boxed{(T_{16})_*\mu=\mu}. \tag{13}
\end{aligned}
\]

When the right side holds, the partition proof even gives a density-one
injective matching.  Thus (40bc) is a useful finite formulation, but under
its stated ergodicity hypothesis it is not a weaker measure-theoretic
endpoint than common invariance.

There is a still weaker sufficient hypothesis for the Furstenberg support
step, namely

\[
                   T_{16}(\operatorname{supp}\mu)
                   \subseteq\operatorname{supp}\mu.   \tag{14}
\]

Equations (6) and (10) imply (14), but (14) does not supply matching or
absolute continuity.  For an infinite support, however, (14) already gives
the full circle by the audited topological rigidity argument.  Proving (14)
for a pi empirical limit is therefore essentially the unresolved
fixed-sixteen support return, not an automatic consequence of fibre
algebra.

## 4. Fibre and carry audit: why cancellation is invalid

Let \(\bar u_n,\bar u_{n+1},\bar v_n\in[0,1)\) be the standard
representatives and define the two integer carries

\[
\begin{aligned}
 r_n&=10\bar u_n+\epsilon_{n+1}-\bar u_{n+1},\\
 s_n&=16\bar u_n+d_n-\bar v_n.                         \tag{15}
\end{aligned}
\]

Then the exact fibre identity refines to

\[
                    5\bar v_n-8\bar u_{n+1}
                         =8r_n-5s_n\in\mathbb Z.       \tag{16}
\]

Thus (4) remembers only a common image together with a finite carry/fibre
label.  Multiplication by 5 has five inverse branches and multiplication by
8 has eight; equality of their images does not select equal lifts.

At the measure level, (11) gives

\[
 (T_5)_*\nu=(T_{80})_*\mu
            =(T_8)_*(T_{10})_*\mu=(T_8)_*\mu.         \tag{17}
\]

Equation (17) follows from \(T_{10}\)-invariance alone.  It cannot imply
non-mutual-singularity without cancelling noninvertible maps.  On the
canonical same-index limiting joining
\((T_{16}x,T_{10}x)_*\mu\), diagonal mass can occur only where
\(16x=10x\pmod1\), a finite six-torsion set.  For a nonatomic \(\mu\) that
particular joining has zero diagonal mass.  An arbitrary reindexing
matching would need genuinely new recurrence information.

The elementary atomic example already makes cancellation fail:

\[
 \mu=\delta_{1/9},\qquad \nu=\delta_{7/9}=(T_{16})_*\mu. \tag{18}
\]

Both measures are \(T_{10}\)-invariant and
\((T_5)_*\nu=(T_8)_*\mu=\delta_{8/9}\), yet their supports are disjoint.
The next section gives a substantially stronger separator.

## 5. Same-forcing ergodic separator

Define the exact four-pole tail independently of its total value by

\[
 \tau_n=\sum_{k=n+1}^{\infty}{a(k)10^n\over16^k}.       \tag{19}
\]

The series is positive and exponentially small, and

\[
             \tau_{n+1}=10\tau_n-\epsilon_{n+1}.       \tag{20}
\]

For an arbitrary phase \(\alpha\in\mathbb T\), put

\[
 x_n=T_{10}^n\alpha,\qquad
 u_n^{\alpha}=x_n-\tau_n,\qquad
 v_n^{\alpha}=T_{16}u_n^{\alpha}+d_n.                 \tag{21}
\]

All equalities are on the circle.  Equations (20)--(21) give every identity
in (4), with exactly the same rational forcing coefficients as the actual
BBP row.  Also

\[
 d(u_n^{\alpha},x_n)\leq\tau_n\to0,
 \qquad
 d(v_n^{\alpha},T_{16}x_n)\leq16\tau_n+d_n\to0.       \tag{22}
\]

When \(\alpha=\pi\), the BBP identity makes \(u_n^\alpha\) exactly the
actual row for every \(n\), and makes \(v_n^\alpha\) exactly the actual
shifted row for every \(n\geq1\).  The excluded \(v_0\) is the
already-audited endpoint correction and has no empirical effect.

Now let \(\beta\) be the fair Bernoulli probability on
\(\{0,1\}^{\mathbb N}\), let

\[
 q(\omega)=\sum_{j\geq1}\omega_j10^{-j},
 \qquad \mu=q_*\beta,                                 \tag{23}
\]

and choose a \(\mu\)-generic phase \(\alpha\).  Such phases exist by the
pointwise ergodic theorem.  The coding is injective on digits \(0,1\): the
alternative expansion of a terminating decimal uses a tail of 9s, which is
outside this alphabet (and the all-zero sequence is the sole allowed
representative of the circle point zero).  Thus there is no rational
double-expansion ambiguity in this model.  Consequently \(\mu\) is
nonatomic, \(T_{10}\)-ergodic, has entropy \(\log2\), and has the
infinite support

\[
                  A=\{0.d_1d_2\ldots:d_j\in\{0,1\}\}. \tag{24}
\]

By (22), the empirical measures of (21) converge to

\[
                 \mu,\qquad \nu=(T_{16})_*\mu.         \tag{25}
\]

The measures in (25) are distinct.  Indeed \(A\subseteq[0,1/9]\), so
\(\mu([3/5,7/9])=0\).  Conditional on the first digit being 1, which has
probability \(1/2\), one has \(x\in[1/10,1/9]\) and

\[
                  T_{16}x=16x-1\in[3/5,7/9].          \tag{26}
\]

The first digit 0 gives no mass in that interval, so the \(\nu\)-mass there
is exactly \(1/2\).  Both measures are \(T_{10}\)-ergodic; hence

\[
                              \mu\perp\nu.              \tag{27}
\]

Nevertheless every fixed-period noncollapse test holds.  For each \(P\geq1\),

\[
 D_P(\mu)=\int\|(10^P-1)x\|_{\mathbb T}^2\,d\mu(x)>0, \tag{28}
\]

because equality to zero would confine the nonatomic \(\mu\) to the finite
set \(\operatorname{Fix}(T_{10}^P)\).  Thus this phase-parametrized BBP row
has all of the following simultaneously:

* the exact four-pole recurrence and adjacent coefficient shift;
* the exact identity \(T_5v_n=T_8u_{n+1}\);
* a \(T_{10}\)-ergodic, nonatomic, positive-entropy empirical limit;
* (40az), equivalently the fixed-lag noncollapse, for every \(P\); and
* no positive-mass bounded-congestion matching, by (27) and Proposition 2.1.

This is not a counterexample about pi.  It is a counterexample to any proof
that discards the selected BBP phase and relies only on the listed dynamical
and fibre data.  In (21), rationality of all \(u_n^\alpha\) occurs only after
the pi phase cancels the transcendental total tail.  The remaining viable
matching attack must use that phase-sensitive arithmetic (for example exact
odd numerator correlations), or introduce a genuinely new theorem specific
to pi.

## 6. Exact replay and bounded diagnostics

The companion
[bbp_fiber_matching_no_go_check.py](bbp_fiber_matching_no_go_check.py)
has SHA-256
`6ee7b3b88c8dcfaaa5df1d565d8ac968b6732f833f1b6f9da4f6628767bb0c2b`.

* pins the canonical question, the prior adjacent audit, the BBP source, and
  the two relevant primary literature sources;
* checks (2), (4), (16), and finite truncations of (19)--(22) by exact
  rational arithmetic;
* enumerates finite Bernoulli cylinders and checks the support-separation
  calculation (26) exactly;
* checks positive finite periodic defects for those discrete cylinder
  approximants; and
* computes finite actual-row matching and carry histograms, explicitly
  labeled `experiment`.

Finite matching radii, histograms, and positive finite defect values are not
asymptotic evidence and prove none of (6), (10), (12), or V1.

The disjoint implementation
[bbp_fiber_matching_no_go_independent_check.py](bbp_fiber_matching_no_go_independent_check.py)
has SHA-256
`abd825b76c0f09c48b2554b780f51d4b65e4cf105b75c962693c9b39c59938af`.
It imports no code from the companion checker, reconstructs the rows from
direct partial sums, checks 64 exact first-difference separation bounds for
the binary coding, and exhausts 784 positive-overlap and 2,352 bounded-
domination finite count-vector cases.  Both checkers report `PASS` and
explicitly report `asserts_v1: false`.

## 7. Literature and mathlib applicability

Status of this bounded search: `literature-checked` on **2026-08-13 UTC**.

| source | exact use and limitation | local SHA-256 |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://doi.org/10.1090/S0025-5718-97-00856-9), Theorem 1 | supplies the series behind (2)--(4); states no empirical matching theorem | `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Blanchard--Host--Maass, [*Representation par automate de fonctions continues de tore*](https://doi.org/10.5802/jtnb.165), Theorem 3.3 and Corollaries 3.4--3.5 | confirms that integer multiplication has a finite transducer representation in base ten; finite-state realizability does not preserve an arbitrary invariant input measure and supplies no matching | `c69b437a2c963d856f4f0026c1716434329b916f961a07da07d2421118d984fa` |
| Badea--Grivaux, [*Around Furstenberg's times p, times q conjecture*](https://arxiv.org/abs/2303.01089v3), Theorem 1.5 | shows that even generic continuous \(T_p\)-invariant measures can have large Fourier coefficients along \(q^n\); it does not specialize to the fixed pi phase or prove overlap with one \(T_q\)-pushforward | `6275f964abab16b16394523367709fa5b7c9ddec5b72ee29dbcc6292284430b1` |
| Prior adjacent-row independent audit | supplies the checked definitions and exact identities used here | `32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93` |

Fresh bounded searches for `times p invariant measure pushforward mutually
singular`, `circle multiplication centralizer invariant measure`, `finite
state transducer multiplication invariant measure`, and `BBP adjacent
coefficient empirical matching` located no primary theorem proving
non-mutual-singularity, domination, or support inclusion for the fixed pi
limit.  This is a dated applicability search, not an exhaustive absence or
novelty claim.

The local mathlib search located
`Measure.exists_positive_of_not_mutuallySingular`, the Lebesgue decomposition
and Radon--Nikodym infrastructure, Portmanteau open-set inequalities, and
finite Hall matching in `Combinatorics.SimpleGraph.Hall`.  Those are enough
to formalize Propositions 2.1--2.2 without new axioms, but no formalization is
claimed in this artifact.

## Bottom line

Under the ergodicity route, both proposed finite matchings are exact avatars
of the missing equality

\[
                              (T_{16})_*\mu=\mu.
\]

The five/eight identity is only equality after two noninvertible fibre maps,
and the same-forcing separator shows that even ergodicity, positive entropy,
nonatomicity, and all fixed-period noncollapse conditions cannot recover the
lost lift information.  A successful continuation must exploit arithmetic
that singles out the rational pi truncations; the existing fibre/carry
algebra alone cannot close V1.
