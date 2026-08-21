# π decimal disjunctivity: does every finite word occur?

Status: `conjecture`

Last audited: 2026-08-13 UTC

## Executive finding

In a bounded search conducted on 2026-08-10, no proof was located that every
finite decimal word occurs in the decimal expansion of \(\pi\). A 2024
exposition explicitly says that this disjunctivity question is unknown, and
the repository's
[`RESEARCH_SUMMARY_20260809.md`](work/review-handoffs/pi/RESEARCH_SUMMARY_20260809.md)
reports no fixed-\(\pi\) proof. No result found here is a
`candidate resolution` or a `verified resolution`.

A fresh primary-source and mathlib audit, extended through 2026-08-13,
reached the same conclusion.  The broad dated search, source pins, and
applicability checks are in
[`literature_report.md`](work/ultrapi-resume/literature_report.md).  The
2025--2026 results located there concern weak factor-complexity bounds,
empirical digit statistics, fixed-prime averages, or related S-unit and
power-orbit problems; none proves a prescribed decimal word for the single
fixed orbit of \(\pi\).

There is, however, a genuine reduction breakthrough relative to the previous
verified repository frontier.  A new `machine-checked` order-\(q\) Jackson
certificate reduces the required Fourier cutoff from \(128\cdot10^k\) to
\(2\cdot10^k\), while increasing the permitted normalized-sum threshold from
\(1/(16388\cdot10^k)\) to

\[
\frac1{24\cdot10^k}+\frac1{12\cdot10^{3k}}.
\]

The fixed-\(\pi\) estimate at that scale remains a `conjecture`, so this is not
a proof of V1.  It is a strictly weaker, target-aligned sufficient condition,
with the strict separation itself `machine-checked`.

There is now also an unconditional fixed-\(\pi\) spectral advance.  New
`machine-checked` path-energy identities prove that, at every fixed nonzero
integer frequency, the absolute gap between the trivial bound \(N\) and the
corresponding exponential-sum norm eventually exceeds every fixed threshold.
This is the first result in this audit that proves nontrivial cancellation for
the actual \(\pi\) orbit without a conjectural arithmetic premise.  Its gap is
simultaneous on every fixed finite frequency window, and an exact shift
identity controls multiplication of the frequency by powers of ten.  The gap
is only additive and may be \(o(N)\), so it still does not supply V1's required
relative cancellation.  A separate first-occurrence theorem does prove a
fixed relative saving after retaining only one orbit point for each distinct
length-\(m\) factor; that saving is lost when the uncontrolled intervening
visits are restored to the full prefix.  A many-frequency strengthening now
shows that at least one sixteenth of the natural frequencies
\(1,\ldots,10^m\) detect a quadratic factor-complexity defect in the full
canonical prefix.  The defect is absolute rather than relative to the square
of that prefix length.  Two further `machine-checked` steps convert the same
positive-proportion selected-energy bound into an additive full-prefix gap
that survives all intervening visits, then move it from the artificial
sum-of-first-occurrences cutoff to the least positive orbit prefix containing
every first-occurrence start.  At that minimal cutoff \(L_m\), at least one
sixteenth of the frequencies \(1,\ldots,10^m\) have gap at least
\(p_\pi(m)/32\ge(m+1)/32\).  The ratio \(p_\pi(m)/L_m\) is still uncontrolled,
so this remains additive rather than the relative cancellation needed for V1.

There is also a new unconditional recurrent-language advance.  At every
length \(m\ge0\), some recurrent decimal block of \(\pi\) has two distinct
one-digit right extensions which both recur arbitrarily late.  Equivalently,
the recurrent factor complexity increases strictly at every step,
\(p^{\mathrm{rec}}_\pi(m+1)\ge p^{\mathrm{rec}}_\pi(m)+1\), and hence
\(p^{\mathrm{rec}}_\pi(m)\ge m+1\).  This is `machine-checked`: deletion of
the last digit maps recurrent factors onto recurrent factors; injectivity at
even one length would make a sufficiently late tail's ordinary complexity
flat and force eventual periodicity.  The branches and their appended digits
remain unspecified, so this does not prove that any prescribed block occurs
and does not prove V1.  A separate `machine-checked` decimal spike model now
attains equality at every positive length and has a unique recurrent
right-special factor at every length.  Shallit's bounded-continued-fraction
theorem gives the represented leading-zero Kempner shift irrationality
exponent (2), while Adamczewski's Mahler-method theorem gives transcendence;
so generic aperiodicity, transcendence, and even optimal scalar Diophantine
approximation cannot strengthen this recurrent-language route.

The latest exact arithmetic package is T63--T68.  T64 and T65 use the parity
of every Hutton Taylor exponent and an exact four-term residue to force, with
multiplicity one, every eligible prime in
\((4K+3)/5<p\le4K+3\), outside the fixed exceptions 17 and 10889.  The
independently audited general local law then gives at `proof sketch` level
\(\log\operatorname{rad}(\operatorname{den}H_K)=4K+3+o(K)\): essentially
all available prime mass has been extracted.  T63 proves the exact five-adic
denominator exponent, and T66 proves the reduced denominator is odd, so this
is the complete base-ten preperiod.  The global CRT coordinate and its
prime-character proxy still retain a correlated complementary phase; the
only proved localization after the mandatory shift lasts logarithmically,
not for the linear transferable digit window.  This is substantive joint
denominator/numerator structure, not a decimal-cylinder hit and not V1.

T67 independently machine-checks the exact obstruction in the
\(1/2+1/3\) shadow: its decimal preperiod is \(4K+1\), and at the first
post-transient shift the bracket width already exceeds \(1/10\).  Thus a
complete-period argument on that denominator cannot transfer even a
one-digit cylinder to \(\pi\).  The selected dyadic transient remains
uncontrolled, so this closes a route rather than proving V1.

T68 adds an infinite simultaneous-primary theorem.  For every \(a\ge2\), at
\(R_a=3^a7^{a+1}\) and \(K_a=(R_a-3)/4\), it machine-checks

\[
 v_3(\operatorname{den}H_{K_a})=R_a+a,\qquad
 v_7(\operatorname{den}H_{K_a})=R_a+a+1.
\]

Its general dominant-layer lemma and all 42 proposition declarations passed
independent adversarial review and the full axiom gate.  The growing-precision
leading units and high-prime completion remain `proof sketch`; even the exact
large primary factors do not select a decimal phase, so T68 is not V1.

Two independently audited follow-up attacks now make that obstruction
sharper.  Across the exact \(5^b\)-member blocks sharing one Hutton decimal
transient, the full exponential phases collapse to one point throughout a
linear transferable window; the complementary CRT coordinate conjugates the
selected coordinate back to the same fixed-π phase.  Separately, recursive
Machin-angle splitting gives arbitrarily thin rational brackets even at fixed
Taylor depth while preserving logarithmic decimal preperiod, but nested
brackets only resolve the cell already occupied by \(\pi\).  Thus neither more
indices nor faster rational approximation supplies the missing prescribed-
cell steering theorem.

T69 now machine-checks the sharp topological endpoint of all these arithmetic
routes.  Assuming exactly the published Furstenberg density conclusion for
the joint \(\times10,\times16\) orbit of \(\pi\), canonical V1 is equivalent
to the single fixed return

\[
 16\{\pi\}\in\overline{\{10^n\pi\pmod1:n\ge0\}}.
\]

Independent review removed an initially over-strong source interface, checked
all eight theorem declarations, and replayed the full gate.  The density
statement is retained as an explicit literature premise rather than a new
axiom; T69 does not prove the fixed return and therefore does not prove V1.

Three further independently audited route closures clarify what cannot supply
that return.  First, integer-Chebyshev optimization on a forbidden-word
survivor is limited to exponential-in-degree smallness by positive logarithmic
capacity, far above the cost of known logarithm measures.  Second,
depth-varying signed Machin tails can cancel strongly in the real metric, but
Yu's \(p\)-adic bound plus \(\mu(\pi)<8\) excludes every synchronized family
with one fixed prime surviving linearly; an exact exponent-2059 cancellation
also prevents an unjustified all-depth endpoint claim.  Third, Iyer's
decimal-0/1 denominators attain the right \(O(N^{-2})\) phase scale, but
Schleischitz's Cantor-distance theorem forces every divisor synchronized with
\(10^N-16\) to have cofactor
\(k=\Omega(N^{\log_2 10})\), hence \(k/N^2\to\infty\).  Exceptionally smaller
fixed-\(\pi\) phases remain possible in principle; none is proved.  A new
independent audit confines any such aligned survivor to
\(d/(10^N-16)^{125/888}\to\infty\) and
\(k/(10^N-16)^{763/888}\to0\), and proves that each fixed denominator is
impossible.  Separately, a reflected 2-adic null identity proves the formerly
experimental all-depth BBP formula
\(v_2(\operatorname{den}A_N)=4N-v_2(N+1)\), closing every exact BBP
denominator anchor for the fixed multiplier 16.  Both are independently
audited `proof sketch` advances; neither controls the surviving nonzero real
phase.  A corrected Padé audit supplies an instructive exact alignment:
the depth-six Euler--Gauss shadow has reduced denominator
\(246612571\mid10^{684842}-16\), but its rational-approximation transfer
error exceeds \(10^{684834}\).  Independent review also caught that a
printed \(0.9058\ldots\) asymptotic for the classical reduced qualities is
incompatible with the checked later-depth trend and is unsupported by a
derivation in its source.  The family-wide closure was therefore withdrawn;
only the finite result and a conditional quality-below-one lemma are retained.

An independently audited Chebotarev argument now closes exact denominator
alignment for the natural all-depth sampled Machin family as well.  There is
a density-(1/256) class of primes for which (10) is a sixteenth power
but (16) is not; consequently none divides any (10^m-16).  T48 forces
one such prime, with multiplicity one, into the reduced denominator of every
sufficiently deep sampled Machin truncation.  Thus no member far enough down
that family has reduced denominator dividing any (10^m-16), for any
(m).  The finite witness is (p=5521) at sampled depth 460.  This is an
unconditional exact-anchor obstruction, not a lower bound on the surviving
nonzero real phase, so it proves no fixed return and no V1.

Three newly audited refinements make the remaining fixed-return obstruction
more exact, without proving it.  First, for the classical Gauss--Lambert
convergents \(A_n=4P_n/Q_n\), the analytic error rate and a canonical common
divisor are now explicit.  With

\[
 H_n=2^{\lfloor n/2\rfloor}
      \operatorname{odd}\!\left({n!\over\operatorname{lcm}(1,\ldots,n)}\right),
 \qquad
 E_n={\gcd(4P_n,Q_n)\over H_n},
\]

the printed constant \(0.7911979206687\ldots\) is rigorously a one-sided
lower bound on reduced approximation quality, not a proved limit.  The actual
limit at that value is equivalent to \(\log E_n=o(n)\); even the weaker
bound

\[
 \limsup_{n\to\infty}{\log E_n\over n}
 <0.4652000032604\ldots
\]

would close this exact-divisibility Padé transfer.  A prime-shift congruence
shows why the bound is genuinely arithmetic: for odd \(p\) and \(0\le s<p\),
\(Q_{p+s}\equiv0\) and \(P_{p+s}\equiv P_pQ_s\pmod p\), so large shifted
prime divisors of earlier continuants enter \(E_n\).  No proof of this bound was
found.  A subsequent independently audited reduction now isolates that
arithmetic much more sharply.  For every odd prime \(\ell\) and \(n\ge2\),

\[
 v_\ell(E_n)\le
 \lfloor\log_\ell n\rfloor+
 \lfloor\log_\ell(n-1)\rfloor-v_\ell(n).
\]

Thus primes at most \(\sqrt n\) have total logarithmic contribution \(o(n)\),
and each larger prime has exceptional exponent at most two.  If
\(n=a\ell+s\), \(\sqrt n<\ell<n\), then the exact remaining criterion is

\[
 v_\ell(E_n)\ge1
 \quad\Longleftrightarrow\quad U_sV_a\equiv0\pmod\ell,
 \qquad U_j=Q_j/j!,\quad V_j=P_j/j!.
\]

A cutoff argument proves that the whole \(V_a\)-branch is already \(o(n)\).
Consequently the only possible linear odd-prime mass is
\(\sum_{\sqrt n<\ell<n,\ \ell\mid U_{n\bmod\ell}}\log\ell\).  The Lucas
product used in this reduction is explicitly credited to Noe's 2006
generalized-central-trinomial congruence.  The separate two-primary edge is
now closed at `proof sketch` level by an independently audited exact formula:
\(v_2(Q_n)-\lfloor n/2\rfloor\) is \(0,0,1,v_2(n+1)\) in the four residue
classes modulo four.  Hence \(v_2(E_n)=O(\log n)\).  The varying odd-prime
zero-density bound remains unproved.

An independently audited follow-up now removes two apparent sources of
slack from that last odd-prime problem.  The natural Gaussian
norm/resultant is exactly \(A_t^2\), so it gives no independent small-height
integer.  Signed reflection instead rewrites every selected prime as a large
prime divisor of one fixed integer \(A_t\), constrained by one of two exact
affine selectors.  Both endpoint tails are sublinear: with
\(B=T=\lfloor n^{1/3}\rfloor\), the unresolved sum \(W_n\) differs by only
\(O(n^{2/3})\) from the compact core
\(a\le n^{1/3}<t\), \(p\mid A_t\), satisfying one selector.  This is a
sharper `proof sketch` reduction, not the missing \(W_n=o(n)\) estimate and
not V1.

The 2026-08-13 independent audit removes the remaining affine selector up to
an unconditional sublinear error.  For

\[
 M_n=\sum_{\substack{\sqrt n<p<n\\p\text{ odd prime}\\p\mid A_n}}\log p
\]

over odd primes, one has

\[
 0\le M_n-W_n\le
 \vartheta\!\left({n\over B+1}\right)
 +{\log5\over2}B(B+1),
\]

and hence \(M_n=W_n+O(n^{2/3})\) at
\(B=\lfloor n^{1/3}\rfloor\).  Equivalently, the desired little-o estimate
holds exactly when every fixed prime band has sublinear logarithmic weight.
Already the first band is the unproved pointwise statement

\[
 \sum_{\substack{n/2<p<n\\p\text{ odd prime}\\p\mid A_n}}\log p=o(n).
\]

This is a `literature-checked` `proof sketch`, not a largest-prime-factor
theorem, an averaged estimate, or V1.  Independent review corrected a false
journal attribution for Wagner's 2012 preprint but found the mathematical
reduction sound.

A further independent audit now localizes that first band exactly.  If
\(t=n-p\) and \(r=\min(t,p-1-t)\), every selected prime occurs on one of the
two rays

\[
 p=n-r\quad\hbox{or}\quad p={n+1+r\over2},
 \qquad 1\le r\le{n-1\over3},\qquad p\mid A_r.
\]

The only overlap is the explicit merger
\(r=(n-1)/3\), \(p=(2n+1)/3\).  Prime-number-theorem endpoint estimates show
that the desired little-o bound is equivalent, for every fixed
\(0<\delta<1/6\), to the same two-ray weight on
\(\delta n\le r\le(1/3-\delta)n\) being \(o(n)\).  Equivalently, the number
of selected first-band primes must be \(o(n/\log n)\).  An exact CRT package
encodes their product as one gcd, but its ambient primorial still has linear
logarithmic size.  Finally, an explicit abstract construction has one minimal
zero per prime, exact reflection, and no consecutive zeros while retaining
\((1/20+o(1))n\) selected weight along infinitely many depths.  Therefore
fixed-prime zero counts, reflection, and spacing alone cannot prove the
estimate; the remaining input must correlate zero locations across different
prime characteristics.  This remains a `literature-checked` `proof sketch`,
not the missing correlation theorem or V1.

A prefix-\(\gcd\) variant was then settled exactly at `proof sketch` level.
After removing prime powers and primes at least \(n\), the common divisor of
\(A_n\) with \(\prod_{r\le(n-1)/3}A_r\) has exactly the same odd-prime
support below \(n\) as \(A_n\) itself.  Its logarithm differs from \(M_n\)
by at most \(\vartheta(\sqrt n)=o(n)\), so its desired little-o bound is
equivalent to the already open medium-prime estimate.  Keeping the full gcd
  adds uncontrolled large common primes and multiplicities.  Independent audit
  passed and corrected a source title; this closes a proposed shortcut, not V1.

On the BBP side, the independently audited carry reduction
(40bi)--(40bm) makes every fixed-period defect exact: it is equivalent to
positive lower density of nonzero centered digits of \((10^P-1)\pi\), and
sevenfold BBP oversampling computes that stream rationally after a finite
fixed-\(P\) onset.  The best published irrationality exponent forces only
\(\Omega(\log N)\) such digits, versus the \(\Omega(N)\) needed; the
Kempner--Fredholm separator shows the logarithmic scale is sharp under finite
irrationality measure and density-one matching alone.

The rational stream now has an exact audited cross-depth recurrence.  Its
denominator, numerator, centered remainder, carry quotient, every finite
zero-carry block, and the selected two-adic numerator valuation are explicit;
one fresh odd-LCM increment has only \(O(\log n)\) bits.  The decisive negative
fact is equally exact: reducing the recurrence modulo any part of the new
denominator deletes the carry term.  Fresh odd factors, all two-adic bits, and
any fixed finite carry memory therefore do not select the Archimedean centered
representative.  The generic one-step integer algebra is now formalized in
T71; the BBP formulas and the missing positive-density estimate remain
`proof sketch` rather than a theorem about V1.

The independently audited odd-LCM continuation also corrects the target
geometry.  V1 itself forces, for every fixed decimal period, arbitrarily late
zero-carry blocks of every prescribed finite length.  Hence bounded carry gaps
would contradict V1, not prove it.  The maximal zero-run is exactly a
restricted repunit-denominator approximation statistic; the published
irrationality measure controls it only linearly in the depth.  Even a new
logarithmic bound would yield only a sublinear-density carry count.  Thus the
needed statement is genuinely an average fixed-pi distribution theorem, not
a fresh-prime valuation or a worst-gap estimate.

A separate matching audit identifies the other proposed endpoint exactly.
For convergent empirical rows, positive-mass vanishing-distance matching with
fixed congestion is equivalent to the two limit measures not being mutually
singular, while density-one matching is equivalent to finite measure
domination.  Under the proposed ergodicity hypothesis, both collapse to the
full missing equality \((T_{16})_*\mu=\mu\).  A same-four-pole Bernoulli
separator retains ergodicity, positive entropy, every fixed-period defect,
and all adjacent fibre identities while making the two limits mutually
singular.  It deliberately does not retain rationality of the finite BBP
truncations, leaving only that selected rational phase as viable leverage.

The target itself now has a second exact formal form.  T72 proves that V1 is
equivalent to arbitrarily late approximation of every point
\(k/(10^P-1)\) by the real decimal orbit of pi, at every requested
precision.  The corresponding centered-carry `proof sketch` sharpens this to
arbitrarily long zero-carry blocks in every residue color.  A common
\(P\)-independent rational BBP phase computes all those colors and carries,
but each fixed color modulus is eventually absorbed into the raw denominator;
the surviving color is an Archimedean cell, not a fixed congruence.

The BBP denominator now has an exact all-depth three-primary description at
`proof sketch` level.  Every even 3-adic epoch contains a forced one-level
denominator drop, while the isolated residual coordinate has exact period
\(3^{E_M-2}\) and traverses a complete residue-one coset on infinitely many
proportional rows.  T73 `machine-checked` the universal modular core: ten has
order \(3^e\) modulo \(3^{e+2}\), the residual quotients
\((10^n-16)/3\) in one period are distinct modulo \(3^{e+1}\), and all reduce
to one modulo three.  This is a genuine complete grid in one coordinate, not
a hit by the synchronized full CRT phase.

T74 now `machine-checked` the four exact one-term ninefold decimations behind
those epochs.  LTE then gives, at independently audited `proof sketch` level,
two nested three-adic endpoint-unit systems and exponentially accurate real
shadows on every complete pre-drop period.  A separate independent Fourier
audit proves that the isolated primary phase has support on one frequency
class modulo nine, with every nonzero coefficient of size \(3\sqrt T\), and
that the full row is exactly one selected Fourier coefficient of its
complement.  This is a substantial sharpening: the obstruction is no longer
generic “CRT dependence,” but one explicit coefficient of the actual growing
BBP complement.  No bound for that coefficient is known, and orthogonality
alone can saturate it.

The complete endpoint phases have now also been measured and independently
reconstructed on fourteen genuine rows through \(5{,}491{,}685\) points.  Their largest
circular gaps all satisfy \(0.899<LG/\log L<1.084\), while the first two
Fourier modes decrease and the coarse ternary correlation stays at
square-root scale.  This is an `experiment`, not an asymptotic theorem.  Its
independent audit also corrects an important logical shorthand: a return to
the single circle target zero does not invoke T72, which requires every
repunit color.  A largest-gap law is nevertheless directly sufficient because
it covers every shifted color, with color zero approached from the positive
side.

The dyadic forcing was also corrected from a tempting but nonmaximal
26-linear-plus-one-quadratic split to an exact 28-odd-linear split.  For a
prime affine modulus, each selected residue is one distinguished root of a
fixed degree-14, -28, or -56 binomial; for composite moduli its local equation
depends on the complementary cofactor.  The inspected distribution theorems
average all roots or all moduli and do not isolate these 28 correlated roots.
Four affine forms have fixed divisor seven, the other 24 have a modulo-three
simultaneous-primality obstruction, and even scalar forcing density does not
propagate through the expanding state recurrence.  The exact selected-root
correlation therefore remains open.

An independently audited rational-phase separator then shows why even much
more accurate local information is insufficient.  One zero-carry model has
the exact reduced BBP denominator and exact two-adic numerator order at every
depth while its forcing is exponentially relatively close to the BBP forcing.
A different coherent zero-carry model uses the exact BBP forcing off only
\(O(\log N)\) reset transitions below \(N\), with exponentially small
relative error even at the resets.  These are two distinct construction
packages; neither preserves the exact selected numerator at every depth.
Consequently that cross-depth numerator correlation, rather than denominator
height, finite asymptotics, or density-one local agreement, is now the
load-bearing arithmetic datum.

Second, the full BBP short orbit has been put in exact reduced CRT
coordinates.  If \(B_M=P_M/(2^{K_M}R_M)\) is the reduced BBP partial sum,
\(D_M=2^{K_M-4}\), and \(A_n=(10^n-16)/16\), then the relevant phase is

\[
 (10^n-16)B_M
 =A_n\left({w_M\over D_M}+{c_M\over R_M}\right),
\]

where the reflected two-adic null identity determines \(w_M\) and eight
additional bits, while \(c_M/R_M\) is the complementary Archimedean quotient.
The minimum of these phases for
\(5\le n\le\lfloor M\log_{10}16\rfloor\) tends to zero if and only if the
fixed-\(16\) return, hence V1, holds.  An explicit separator preserves the
complete actual reduced denominators, the complete two-adic congruence, and
better-than-BBP approximation to a fixed transcendental number while keeping
that whole short orbit a positive distance from zero.  It does not preserve
the four-pole BBP coefficient recurrence, which is therefore the only
remaining selector in this route.  The actual four-pole recurrence has now
been used to expose almost all of the complementary quotient as well.  Its
dyadic coordinate obeys a closed carry recurrence; every odd prime above
\(O(M/\log M)\) has an explicit nonzero localized CRT coordinate; and, after
removing their product, the single residual cofactor \(C_M\) satisfies

\[
 P^+(C_M)=O(M/\log M),\qquad \log C_M=o(M),\qquad
 \log R_M=(6+o(1))M.
\]

Independent review corrected the domain on which a localized coordinate
exists and sharpened the rational-height bound from \(O(L\log L)\) to
\(O(L)\).  This still leaves a synchronized, weighted \(O(M)\)-term power
orbit; subexponential modulus size alone gives no cancellation or hit.

Third, generic dynamics cannot promote Furstenberg's dense union of
\(\times16\)-slices to one fixed slice.  For every infinite
\(\times10\)-minimal compact set \(M\), the sets \(16^tM\) are pairwise
disjoint but have dense union, while preserving Hausdorff dimension and
topological entropy.  There is also an explicit dimension-
\(\log9/\log10>19/20\), entropy-\(\log9\) family of pairwise mutually
singular pushed measures whose Cesaro mean converges to Lebesgue measure.
These independently audited `proof sketch` separators show that density,
large dimension, positive entropy, intersecting supports, and averaged
equidistribution still do not yield the named fixed-\(\pi\) return.

A fourth independently audited refinement identifies the weakest useful
one-measure bridge currently visible in BBP.  If
\(u_n=\{10^nB_n\}\), \(x_n=\{10^n\pi\}\), and
\(t_n=10^n(\pi-B_n)\), then

\[
 x_n=u_n+t_n,\qquad
 W_1\!\left({1\over N}\sum_{n<N}\delta_{u_n},
             {1\over N}\sum_{n<N}\delta_{x_n}\right)
 \le {8\over45N},
\]

and the BBP recurrence is exactly conjugate to \(\times10\) by the moving
translation \(z\mapsto z+t_n\).  Thus its decimal empirical measures have
exactly the same limit set as the actual decimal orbit; BBP does not create
an independent random process.  Nevertheless, V1 would follow if one such
limit \(\mu\) were \(T_{10}\)-ergodic, nonatomic, and not mutually singular
with \((T_{16})_*\mu\).  Ergodicity would force the two measures to be equal,
and Furstenberg would then force full support.  Equivalently, along one
convergent subsequence it would suffice to prove, for every fixed integer
\(q\),

\[
 {1\over N}\sum_{n<N}
 \bigl(e(16qu_n)-e(qu_n)\bigr)\longrightarrow0.
\]

No telescoping identity or BBP estimate proves this same-time \(\times16\)
comparison.  Schmidt's theorem supplies a sharp missing-digit separator in
which the analogous decimal measure is ergodic, nonatomic, and has positive
entropy, while its \(\times16\) pushforward is singular.  The remaining
overlap hypothesis is therefore substantive, not a formal consequence of
empirical invariance.  T70 now `machine-checked` the entropy-free implication
in its clean topological form: probability, \(T_{10}\)-ergodicity, support in
\(K_\pi\), nonsingularity with the \(T_{16}\)-pushforward, and one supplied
support point with dense joint orbit imply \(K_\pi=\mathbb T\) and V1.  Those
π-specific premises remain unproved.

The actual four-pole forcing has now been audited against that Fourier
target.  Its contribution is summably erased:

\[
 |D_N^u(q)-D_N^\pi(q)|\le {272\pi|q|\over45N},
 \qquad N\ge1.
\]

The exact recurrence telescopes only between frequencies \(q\) and \(10q\).
Since \(q\) and \(16q\) lie on distinct multiplication-by-ten rays, the
desired observable is neither a finite Fourier coboundary nor, at \(q=1\),
a stationary continuous coboundary; a natural uniformly asymptotically
stationary universal version is also impossible.  Independent review
rederived the constant and scopes.  Orbit-specific nonlinear cancellation
and direct nonsingularity remain open, so this is a method boundary, not V1.

At proportional BBP depth, the still-unresolved weighted CRT product also
collapses exactly to the corresponding decimal Weyl block of \(\pi\), with
normalized error at most \(2\pi|h|/(15(M+1)^2)\).  Finite differencing merely
multiplies the frequency by odd factors \(10^r-1\).  Independent audit further
shows that the entire actual odd quotient and exact reduced denominator are
insufficient without the selected dyadic carry: changing only that carry
admits rows whose normalized mean tends to a unit.  The separator violates
the actual four-pole recurrence, so it is a proof-method boundary, not a
counterexample.  No weighted cancellation, fixed return, normality, or V1
follows.

Two final 2026-08-13 BBP reductions replace those broad cancellation targets
by narrower coefficient-specific ones.  First, with
\(R_n=(10^n-16)B_n\) and \(Z_n=e(R_n)\), the exact rational recurrence
satisfies

\[
 \mathrm{V1}\iff\liminf_n\|R_n\|_{\mathbb T}=0
 \iff\limsup_n\Re Z_n=1
\]

at `proof sketch` level through the audited T69/Furstenberg bridge.  A 2026
linear-recurrence theorem proves an infinite limit set and dispersion away
from zero, but not the required return to zero; failure of the return would
force a persistent negative low Fourier mode that remains unexcluded.
Second, shifting the actual BBP coefficient by one place gives exactly
\(v_n=16u_n+a(n+1)(5/8)^n\pmod1\).  V1 would follow from an
almost-everywhere bounded-congestion matching of \(v_n\) back to \(u_m\),
together with noncollapse at every fixed decimal period on the same rows.
This strictly improves the earlier vanishing-close-pair-energy criterion:
atoms are allowed, provided the limiting support is infinite.  Under an
additional ergodicity hypothesis even a fixed positive matched proportion
replaces almost-everywhere matching.  All sufficient conditions survived
independent audit; none of the required asymptotic hypotheses has been
proved.  They are sharper endpoints, not a complete proof.

The useful progress is therefore narrower than a resolution but inspectable:

1. the intended statement and its misleading variants are now separated;
2. several exact reductions identify estimates that would suffice;
3. the exact natural-scale Fourier obstruction above gives the strongest local
   verified finite target and strictly supersedes the earlier T6/T18 targets;
4. an elementary sparse collision-energy certificate is valid, but an exact
   audit shows that unrestricted existential sampling merely recovers factor
   complexity; the new constrained first-occurrence theorem obtains relative
   cancellation on one representative per factor, and its many-frequency
   form gives a positive proportion of natural-scale defect witnesses; its
   linear-gap refinement survives uncontrolled repeated visits, and its
   minimal-prefix form isolates the remaining loss exactly in the unknown
   ratio \(p_\pi(m)/L_m\);
5. a fixed-\(\pi\) digit-change/path-energy bridge, simultaneous finite-window
   additive divergence, and the exact power-of-ten frequency-shift identity
   are `machine-checked`, while an explicit sparse-digit separator proves that
   these still fall short of relative cancellation;
6. a `proof sketch` using an unconditional irrationality-measure bound derives
   logarithmically many digit changes, while a dated Diophantine audit shows
   that even scalar exponent \(2\) would not control factor coverage;
7. an exact-integer finite replay exactly verifies all words through length
   five, while current external finite data reports coverage through length
   thirteen. Both are only `experiment`;
8. at every length \(m\ge0\), the recurrent decimal language of \(\pi\)
   contains a right-special block with two recurrent continuations, and its
   complexity grows by at least one at the next length, `machine-checked`;
   an exact `machine-checked` Kempner-shift separator shows this is the sharp
   generic conclusion even alongside `literature-checked` transcendence and
   exponent \(2\);
9. maximal decimal factor entropy is now `machine-checked` to be exactly
   equivalent to V1; an explicit BBP rational recurrence has the same
   omega-limit set as the decimal \(\pi\) orbit, and a fresh 2026 theorem
   gives an unconditional all-arithmetic-scales \(1/10\) spread property;
   exact dyadic and 5-adic denominator calculations and explicit
   periodic/Sturmian separators show why these results still do not establish
   ×16 invariance or the entropy premise; and
10. T34 machine-checks the precise factor-two recurrent-cell transfer for a
   one-sided rational shadow, while T35 proves that sevenfold oversampling
   removes the floor-boundary loss under an exponent-eight premise.  T36 then
   replaces the unformalized BBP tail with explicit rational Machin sums:
   \(M_K\le\pi\), \(\pi-M_K<625^{-K}\), and \(M_{3N}\) eventually has
   exactly \(\pi\)'s matching arithmetic floor code at every fixed length,
   conditional only on the published \(\mu(\pi)<8\) proposition.  T37 closes
   the representation gap exactly: that floor code is the canonical
   `piCylinderCode`, and its value is the contiguous `blockAt piDigit` word
   value, including length zero.  T38 then machine-checks the exact positive
   rational forced recurrence for \(\{10^NM_{3N}\}\), its summable geometric
   error, a uniform-in-prefix Fourier transfer, and equivalence of Weyl
   cancellation with the original decimal \(\pi\) orbit.  Thus the recurrence
   is an exact coordinate model, not an independent source of distribution.
   T39 then transfers recurrent values exactly under the eventual symbolic
   equality: the Machin and \(\pi\)-cylinder streams have identical recurrent
   sets and counts, giving the full \(m+1\) lower bound without T34's
   factor-two loss, but not all \(10^m\) cells.  T40 machine-checks the exact
   local 6+6-term forcing window, its decomposition into positive adjacent
   pairs, and the twice-an-odd cleared numerator for every pair.  T41 finally
   proves the exact target equivalence: V1 is all-cell recurrence of the
   canonical \(\pi\)-cylinder streams, and, under the same explicit source
   premise, equivalently all-cell recurrence of the rational Machin codes.
   T42 machine-checks the odd-denominator and two-adic foundations for each
   three-pair block. T44 now closes the combined calculation: the reduced
   denominator is odd and the reduced numerator has exact two-adic exponent
   \(N+4\), `machine-checked`. T43 independently remains a decisive separator:
   positive, summable geometric forcing with the same exact \(2^{N+4}\)
   numerator profile can drive a base-ten orbit to \(1/3\) while it avoids a
   decimal cell.  A stronger product-grid separator, presently a
   `proof sketch`, also matches the nested 5/239/product grids, the moving
   residue recurrence, and one exact 3-adic cancellation.  Thus those coarse
   arithmetic invariants do not establish either side of T41. T45 goes beyond
   those coarse invariants for the actual twelve-term numerator: every
   admissible interior prime \(p>12\), \(p\ne239\), survives with
   \(v_p(\Delta_N)=-1\), `machine-checked`. This creates long exact geometric
   prime projections, but a fixed-denominator CRT separator shows that a prime
   projection alone still cannot select an archimedean decimal cell. Only an
   estimate using the complete initial numerator/cofactor phase, or an
   independent fixed-\(\pi\) distribution theorem, remains viable.
   T46 machine-checks the corrected dynamical reduction: every finite segment
   is a power-of-ten orbit of one fixed initial rational plus an exact
   nonnegative error telescope, with the pulse-scale bound
   \(10\rho(100\rho)^N\). It proves neither cancellation nor coverage. T47
   closes both endpoint slots, treats the exceptional Machin-base prime 239,
   and routes all four prime residue classes modulo 12: every prime \(p>12\)
   divides the reduced denominator of at least one actual forcing increment,
   `machine-checked`. This universal non-archimedean richness still does not
   control the selected archimedean numerator phase. T48 proves the distinct
   full-seed statement needed by the fixed-modulus analysis: every eligible
   prime in the upper half of the seed's odd-denominator range has valuation
   exactly \(-1\), and hence exact multiplicity one in the reduced seed
   denominator, `machine-checked`. T49 then closes the previously omitted
   endpoint-to-endpoint pulse in the class 5 modulo 12: for the prime
   `p = 12*N+17` outside 317, the actual fixed seed has valuation -1
   throughout the exact sample window from `N+2` through `3*N+3`. T50 proves
   the complementary full-seed two-band law for `d = 12*N+15`: subject only
   to its explicit finite arithmetic exceptions, every
   prime `d/5 < p <= d` occurs with exact multiplicity one in the reduced
   seed denominator. T51 extends this one band farther:
   \(d/7<p\le d/5\), with exact \(p,3p,5p\) coefficient exceptions and its
   \(d+2=7p\) endpoint discharged, is now `machine-checked`. These results
   repair the four-class bookkeeping, but still leave the selected
   complementary numerator phase uncontrolled. T52 now proves the exact
   persistent three-primary part: if \(3^a\le12j+3<3^{a+1}\), then
   \(v_3(10^jM_{3j})=1-a\) and the reduced denominator contains exactly
   \(3^{a-1}\), `machine-checked`. T53 then machine-checks the two-level
   Euclidean split and carry recurrence: the fine CRT carry is known, but the
   next decimal digit is exactly the remaining coarse carry. Thus this
   obstruction is now a verified arithmetic identity, not merely an analogy.
   T54 proves that the complete three-primary factor stays fixed or triples;
   T55 proves the exact coarse selector; T56 proves the generic inverse-three
   residual lift; and T57 proves generic phase recombination and fixed-depth
   multiplication-by-ten transport. These are `machine-checked` identities,
   not a phase estimate. A subsequent actual-Machin `proof sketch` finds a
   shared upper-prime factor of logarithm \(6j+o(j)\) lasting
   \(j/2+O(1)\) steps, with an exact multiplicative residual recurrence on
   that factor. Its complementary CRT coordinate still reconstructs the one
   uncontrolled linked \(q_j10^j\pi\) phase, so no cylinder hit follows.
   A
   growing-band `proof sketch` now captures logarithmic prime mass
   \(d-o(d)\), leaving only \(\exp(o(j))\) complementary quotient choices.
   Exact quotient reciprocity identifies that quotient with the actual
   archimedean cell index. Cross-index consistency does not select it: a
   persistent 3-primary subgroup of size \(\Theta(j)\) preserves the current
   high-prime/base components and exact forcing while alternative members
   realize any prescribed fixed finite itinerary. This is a separator for the
   present information, not a statement about the actual numerator; and
11. T58--T60 machine-check the sharper Hutton rational bracket, its exact
   cylinder certificate from supplied containment witnesses, and its positive
   adjacent increment. T61 now proves that every upper-half prime \(p>7\),
   except 17, survives exactly once in the reduced Hutton denominator; T62
   combines the whole band, T64 enlarges it from \(R/2<p\le R\) to
   \(R/3<p\le R\), and T65 machine-checks the next band down to \(R/5\)
   outside 10889.  T63 and T66 jointly determine the exact base-ten
   denominator transient.  The general fixed-prefix law gives
   \(\log\operatorname{rad}(\operatorname{den}H_K)=R+o(R)\) at independently
   audited `proof sketch` level.  This prime mass grows exponentially in
   \(K\), but the bracket controls
   only \(\Theta(K)=\Theta(\log q_K)\) decimal states.  A direct short-prefix
   audit proves that numerator-uniform denominator/order bounds cannot bridge
   that gap.  Independently, the omitted-word automaton yields the genuinely
   small integer-polynomial value (35), yet an exact exponent ledger shows
   that every available Padé/Lindemann comparison still loses.  The
   Furstenberg--BBP audit reduces the cross-base route to the single return
   \(16\pi\in K_{10}(\pi)\), which is already equivalent to V1.  These are
   meaningful obstructions and reductions, not a proof of V1; and
12. T73--T74 now isolate an exact recurring three-primary BBP skeleton.
   T73 machine-checks the complete power-of-ten orbit, while T74
   machine-checks the four one-term ninefold decimations.  The independently
   audited `proof sketch` sums those identities by LTE and proves nested
   three-adic endpoint units.  A second independent audit finds the exact
   Fourier transform of one complete primary period: it is supported on one
   class modulo nine and has nonzero magnitude \(3\sqrt T\).  Hence the
   complete phase is one selected Fourier coefficient of the synchronized
   CRT complement.  This is a sharper, coefficient-specific target, not
   cancellation: the complement is uncontrolled and can saturate the bound.
   A finite full-phase experiment on fourteen endpoint rows through
   \(5{,}491{,}685\) points has largest circular gap consistently at scale
   \(\log L/L\), motivating the directly sufficient endpoint-gap
   `conjecture`.  At epoch 16 its independently reproduced strict gap bound
   also certifies every one of the 100,000 five-digit words in the inspected
   pi prefix, with minimum multiplicity 23.  This is finite evidence and does
   not prove the asymptotic law or V1.
13. T75 now `machine-checked` the corrected abstract endgame: eventual
   uniform coverage by late finite shadow rows, together with uniform
   vanishing error from a fixed shift of the decimal orbit, implies all T72
   repunit colors and hence V1.  Its separate positive-interior treatment of
   color zero closes the wraparound issue.  T75 proves none of those analytic
   premises for the BBP endpoint rows, so it is a verified bridge rather than
   a proof of V1; and
14. a fresh `literature-checked` comparison identifies the exact metric
   analogue: Peres--Yang (2026) prove
   \(NG_N/\log N\to1\) for almost every starting point of every integer
   divisibility chain, hence for \(10^n\).  Their measure and independent
   mixed-radix inputs do not include the named point pi or the changing
   rational BBP endpoints.  Separately, an independently audited Gowers
   attack proves that only \(O_\eta(1)\) primary coefficients per depth can
   correlate macroscopically with any unit complement, but an artificial
   conjugate complement can keep the selected coherent coefficient fully
   resonant despite vanishing every fixed-order marginal Gowers norm.  The
   remaining target is therefore a deterministic BBP-numerator-specific
   no-hit estimate, not another generic mixing assertion; and
15. the coherent-path continuation and its independent audit make that
   exceptional-set geometry exact.  At every even epoch the exceptional
   coefficients are complete nine-lift fibres.  For any predetermined weight
   sequence their cylinder measures are summable, so Haar-almost every
   coherent three-adic path has vanishing normalized correlation.  T76
   `machine-checked` the corresponding abstract countable-cover theorem and
   the exact geometric budget (1/(4\eta^2)); all 15 declarations pass the
   full axiom gate.  The actual BBP complements, however, change by the deep
   nonconstant twist (40fl), and a full-measure theorem cannot select the one
   computable BBP path.  This is a verified reduction in the size of the
   obstruction, not a proof of V1; and
16. the selected three-adic path now has a sharper independently audited
   `proof sketch`: the normalized endpoint defect is always one modulo nine,
   and the next two ternary digits obey the exact hidden-carry law (40fq).
   Exact rows through epoch 14 predict \(a_{16}=6{,}580{,}712\).  The
   repeated visible value 29 followed by lifts 0, 0, and 4 disproves only the
   bare-integer, epoch-independent state choice.  It neither rules out all
   finite augmentations nor estimates the synchronized complementary phase,
   so no deterministic exceptional-path escape or V1 follows.  T77 now
   `machine-checked` the exact rational nine-block shell and every entry of
   its \((8,8,0,3)\) residue ledger; the remaining uniform
   \(\mathbb Z_{(3)}\)-transport is explicitly not yet machine-checked.

## Provenance

- Erdős Problems URL: none; this is a local research question, not a numbered
  Erdős problem.
- Original external source URL: none was supplied. This absence is preserved
  rather than replaced by a later exposition.
- Canonical local source:
  [`problems/local/pi-digits.txt`](problems/local/pi-digits.txt), SHA-256
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Root created from Marcel's 2026-07-21 question: “does any integer sequence
  occur at some point in the extension of PI?”
- Current research request: 2026-08-10.
- Prize: none recorded.

Working-tree caveat: `ultrapi.md`, the cited Lean modules (including the
quantitative T18--T33 modules), the cited T99 audit files, and the active
theory-program trees are currently untracked; `TheoryLib.lean` and
`audit/AxiomAudit.lean` are modified. These paths describe the present
checkout, not a committed canonical snapshot. The immutable local source and
its SHA-256 above remain the statement authority.

This note begins from the headings and verification intent of
[`problems/TEMPLATE.md`](problems/TEMPLATE.md).

## Exact statement

The immutable local source asks:

> Does every finite sequence of decimal digits occur as a contiguous block
> somewhere in the decimal expansion of pi?

Equivalently, is \(\pi\) disjunctive (or rich) in base 10?

## Normalized statement

Use the unique nonterminating decimal expansion

\[
\pi=3+\sum_{n\ge1}d_n10^{-n},\qquad d_n\in\{0,1,\ldots,9\}.
\]

The canonical proposition V1 is

\[
\forall m\ge1\;\forall (w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\;
\exists n\ge1\;\forall 0\le j<m:\ d_{n+j}=w_j. \tag{V1}
\]

Words may begin with zero, starts are not required to be aligned, and an
occurrence must be contiguous. Let \(p_\pi(m)\) be the number of distinct
length-\(m\) factors in the infinite fractional digit word. Then

\[
\text{V1}\quad\Longleftrightarrow\quad p_\pi(m)=10^m
\text{ for every }m\ge1. \tag{1}
\]

There is also an exact dynamical reformulation:

\[
\text{V1}\quad\Longleftrightarrow\quad
\bigl\{\{10^n\pi\}:n\ge0\bigr\}\text{ is dense in }[0,1). \tag{2}
\]

Equidistribution of this orbit is base-10 normality and is stronger than the
density required in (2).

For a disjunctive one-sided word, “occurs once” already implies “occurs
arbitrarily late.” Given a word \(w\) and a position bound \(K\), apply V1 to
the longer word \(0^K w\); the copy of \(w\) in that occurrence begins after
position \(K\). Thus V1 would make every finite word occur infinitely often.

## Ambiguities

- **Finite versus infinite.** V1 concerns finite words. The assertion that
  every infinite decimal stream is literally a tail of \(\pi\) is false:
  \(\pi\) has countably many tails but there are uncountably many streams.
- **Substring versus subsequence.** The sibling V3 asks whether every infinite
  stream embeds noncontiguously. It is equivalent to every digit
  \(0,\ldots,9\) occurring arbitrarily late. That specialization to \(\pi\)
  remains a `conjecture` and is much weaker than V1.
- **Base.** The target is base 10 only. Normality or disjunctivity in base 2
  or 16 does not in general transfer to base 10.
- **Which digits.** Only the fractional digits \(d_1,d_2,\ldots\) are used;
  the integer digit `3` is excluded from canonical indexing.
- **Leading zeroes.** They are allowed, so the target is stronger than asking
  only for ordinary decimal representations of positive integers.
- **Contiguity and alignment.** The digits must be consecutive, but the start
  may be any position.
- **Frequency.** V1 asks for existence, not the limiting frequency
  \(10^{-m}\) required by normality.

## Known results

| Label | Result | What it actually proves |
|---|---|---|
| `machine-checked` | V2 has an explicit diagonal counterexample in [`T8PiDigitsV2Diagonal.lean`](TheoryLib/PiDigits/T8PiDigitsV2Diagonal.lean). | Resolves only the false infinite-tail reading, not V1. |
| `machine-checked` | V3 is equivalent to every digit occurring arbitrarily late in [`T9PiDigitsV3Reduction.lean`](TheoryLib/PiDigits/T9PiDigitsV3Reduction.lean). | The equivalence is exact; its premise for \(\pi\) remains a `conjecture`. |
| `machine-checked` | Irrationality and Morse–Hedlund give \(p_\pi(m)\ge m+1\) in [`T11PiDigitFactorComplexity.lean`](TheoryLib/PiDigits/T11PiDigitFactorComplexity.lean). | V1 needs \(10^m\), an exponential rather than linear bound. |
| `machine-checked` | At least two unspecified decimal digits occur arbitrarily late in [`T13PiDigitsTwoRecurrentDigits.lean`](TheoryLib/PiDigits/T13PiDigitsTwoRecurrentDigits.lean). | It does not identify the digits or establish recurrence of all ten. |
| `machine-checked` | Conditional finite-alphabet counting in [`T18FiniteAlphabetSubsequentialCounting.lean`](TheoryLib/PiDigits/T18FiniteAlphabetSubsequentialCounting.lean) extracts one fixed unequal directed bigram and its two endpoint digits with logarithmic counts along unbounded prefixes. | The specialization to \(\pi\) retains the T14 digit-change premise and is therefore only a `proof sketch`. |
| `machine-checked` | V1 is equivalent to the orbit-density statement (2) in [`T20BaseTenOrbitDensity.lean`](TheoryLib/PiDigits/T20BaseTenOrbitDensity.lean). | An exact reduction; density at the fixed point \(\pi\) remains a `conjecture`. |
| `machine-checked` | V1 implies V3, while the converse fails for generic decimal streams, in [`T21PiDigitsV1V3Relationship.lean`](TheoryLib/PiDigits/T21PiDigitsV1V3Relationship.lean). | Prevents a silent swap to the weaker subsequence problem. |
| `machine-checked` | Weyl cancellation for every nonzero frequency implies V1 in [`T26WeylCancellationV1.lean`](TheoryLib/PiDigits/T26WeylCancellationV1.lean). | The required fixed-\(\pi\) cancellation is unknown. |
| `machine-checked` | Exact order-\(q\) interval localization in [`T19T19ExactNaturalScaleResonance.lean`](TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean) proves the cutoff \(2q\) and threshold \(1/(24q)+1/(12q^3)\), its direct hitting contrapositive, and its conditional implication to V1. | This is a strictly weaker sufficient condition than the earlier verified T18 target, but its fixed-\(\pi\) premise remains a `conjecture`; no quantitative bound on the witnessing \(N\) is proved. |
| `machine-checked` | The path-energy identity in [`T20T20DigitChangeFourierDefect.lean`](TheoryLib/PiQuantitativeBlockHitting/T20T20DigitChangeFourierDefect.lean) proves \(N\sin^2(\pi/100)\operatorname{Chg}_\pi(N)\le N^2-|S_N(1)|^2\). | This is unconditional and genuinely concerns the fixed \(\pi\) orbit, but it controls only the first frequency through the number of adjacent digit changes. |
| `machine-checked` | [`T21T21UnboundedFourierGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T21T21UnboundedFourierGap.lean) and [`T22T22AllFixedFrequencyGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T22T22AllFixedFrequencyGap.lean) prove that for every fixed \(h\ne0\), \(N-|S_N(h)|\) eventually exceeds every real threshold. | The quantifier order is \(\forall h\,\forall A\,\exists N_0\,\forall N\ge N_0\); it gives no rate uniform in \(h\), and does not show \(|S_N(h)|/N\to0\). |
| `machine-checked` | [`T23T23MorseHedlundFrequencyDefect.lean`](TheoryLib/PiQuantitativeBlockHitting/T23T23MorseHedlundFrequencyDefect.lean) proves fixed relative cancellation on the sample containing one first occurrence of every distinct length-\(m\) factor, and transfers its pair energy into the full canonical first-occurrence prefix. | The sample bound is genuinely relative, but intervening repeated visits can swamp it in the full prefix. Its bare existential full-prefix corollary is already implied qualitatively by T21; the new content is the canonical support/cutoff structure and natural frequency range. |
| `machine-checked` | [`T26T26ManyFrequencyFirstOccurrenceDefect.lean`](TheoryLib/PiQuantitativeBlockHitting/T26T26ManyFrequencyFirstOccurrenceDefect.lean) proves that at least \(10^m/16\) natural frequencies have full-prefix squared defect at least \(p_\pi(m)(p_\pi(m)-3)/4\) at T23's canonical cutoff. | This is a genuine many-frequency strengthening, but after normalization its saving is only of order \((p_\pi(m)/N_m)^2\); no bound on that ratio is known. |
| `machine-checked` | [`T27T27ManyFrequencyLinearGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T27T27ManyFrequencyLinearGap.lean) converts the same selected-energy set into \(N_m-|S_{N_m}(h)|\ge p_\pi(m)/32\) for at least \(10^m/16\) frequencies. | The triangle-inequality transfer survives arbitrary intervening visits and improves the normalized loss from quadratic to linear in \(p_\pi(m)/N_m\), but that ratio remains uncontrolled. |
| `machine-checked` | [`T28T28LastFirstOccurrenceLinearGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T28T28LastFirstOccurrenceLinearGap.lean) proves the T27 count and gap at \(L_m=1+\max_w n(w)\), the least positive orbit prefix containing every first-occurrence start, and proves \(L_m\le N_m\). | This removes T23's artificial sum cutoff. It does not bound \(L_m/p_\pi(m)\), and \(L_m\) concerns representative starts rather than the extra \(m-1\) digits needed to contain the final block in a finite digit prefix. |
| `machine-checked` | [`T29T29AppearanceRatioRelativeGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean) proves that the explicit premise \(L_m\le C\,p_\pi(m)\) turns T28's additive gap into \(|S_{L_m}(h)|/L_m\le1-1/(32C)\) on the same \(10^m/16\) frequencies. | The appearance-ratio premise is unproved for \(\pi\); even a uniform \(C\) gives only a fixed saving on a moving subset, not T19's all-frequency near-zero bound. |
| `machine-checked` | [`T30T30MaximalEntropyEquivalence.lean`](TheoryLib/PiQuantitativeBlockHitting/T30T30MaximalEntropyEquivalence.lean) proves \(h_{10}(\pi)=\log10\iff\mathrm{V1}\), as well as the generic decimal-stream equivalence and universal entropy upper bound. | This is the exact full-entropy target; it proves no maximal-entropy premise for \(\pi\) and therefore no V1 status change. |
| `machine-checked` | [`T31T31RecurrentFactorComplexity.lean`](TheoryLib/PiQuantitativeBlockHitting/T31T31RecurrentFactorComplexity.lean) proves that at least \(m+1\) distinct length-\(m\) decimal blocks recur arbitrarily late in \(\pi\), for every \(m\ge1\). | This strengthens the two-recurrent-digit baseline, but remains linear rather than the \(10^m\) prescribed-block coverage required by V1. |
| `machine-checked` | [`T32T32RecurrentRightSpecial.lean`](TheoryLib/PiQuantitativeBlockHitting/T32T32RecurrentRightSpecial.lean) proves \(p^{\mathrm{rec}}_\pi(m+1)\ge p^{\mathrm{rec}}_\pi(m)+1\) for every \(m\ge0\), and produces a recurrent length-\(m\) block with two distinct recurrent one-digit right extensions. | This strengthens T31 structurally at every length, but neither the block nor either extension digit is prescribed; the increment is still far below full \(10^m\) coverage. |
| `machine-checked` | [`T33T33RecurrentSharpnessSeparator.lean`](TheoryLib/PiQuantitativeBlockHitting/T33T33RecurrentSharpnessSeparator.lean) proves that the decimal powers-of-two spike stream has exactly \(m+1\) recurrent length-\(m\) factors for every \(m>0\), classifies them exactly as the zero and singleton-one blocks, and proves that the all-zero block is its unique recurrent right-special factor at every length. | This is a sharpness separator, not a theorem about \(\pi\). Together with the `literature-checked` bounded continued fraction and transcendence of the corresponding Kempner number, it blocks any generic upgrade based only on aperiodicity, transcendence, or ordinary irrationality exponent (2). |
| `machine-checked` | [`T34T34RecurrentCellTransfer.lean`](TheoryLib/PiQuantitativeBlockHitting/T34T34RecurrentCellTransfer.lean) embeds recurrent values of any eventually two-lift shadow into the target recurrent values times a bit, proving that at most a factor of two is lost. Its decimal-cylinder specialization gives a conditional target lower bound \((m+2)/2\) for \(m\ge1\). | The abstract transfer and the exact \(\pi\)-factor injection are unconditional, but the intended diagonal-BBP cell-shadow relation remains an explicit premise; T34 does not assert that the rational BBP stream satisfies it. |
| `machine-checked` | [`T35T35OversampledBBPGridStability.lean`](TheoryLib/PiQuantitativeBlockHitting/T35T35OversampledBBPGridStability.lean) proves an abstract decimal-grid lemma: under `PowerTenDiophantine x 8 A`, any one-sided approximants with error \(<16^{-K}\), sampled at \(K=7N\), have exactly the same fixed-length arithmetic floor code at position \(N\) as \(x\), eventually. It also checks the quantifier conversion from the source-level \(\mu(\pi)<8\) proposition. | The theorem's `a` is arbitrary. For the intended BBP application, identifying `a` with the BBP truncations and proving its displayed `hbelow` and `htail` obligations remain external and unformalized. T37 now supplies the separate exact floor-to-symbolic bridge, but no BBP tail proof or density follows. |
| `machine-checked` | [`T36T36MachinGridStability.lean`](TheoryLib/PiQuantitativeBlockHitting/T36T36MachinGridStability.lean) constructs explicit finite rational Machin approximants \(M_K\), proves their exact step recurrence, \(M_K\le\pi\), and \(0\le\pi-M_K<625^{-K}\). Conditional only on the explicit source-level \(\mu(\pi)<8\) proposition, it proves that \(M_{3N}\) and \(\pi\) eventually have the same length-\(m\) arithmetic floor code at position \(N\), for each fixed \(m\). | The arctangent series, Machin identity, rationality, error, and transfer are checked; the published irrationality theorem itself remains an explicit literature premise. The theorem concerns a varying rational approximant and proves neither orbit density nor V1; the symbolic digit-code bridge is handled separately. |
| `machine-checked` | [`T37T37FloorSymbolicBridge.lean`](TheoryLib/PiQuantitativeBlockHitting/T37T37FloorSymbolicBridge.lean) proves for every real \(x\) that the arithmetic length-\(m\) block code at start \(N\) is \(\lfloor10^m\{10^Nx\}\rfloor\), packages it in `Fin (10^m)`, and identifies the \(x=\pi\) code exactly with both `piCylinderCode m N` and the word value of `blockAt piDigit m N`. It then upgrades T36 to eventual equality of the rational Machin `Fin`-code stream and the symbolic \(\pi\)-cylinder stream. | Negative inputs, half-open rational endpoints, zero-based indexing, and \(m=0\) are covered. The eventual Machin theorem retains the explicit source-level \(\mu(\pi)<8\) premise and proves representation equality, not coverage, density, normality, or V1. |
| `machine-checked` | [`T38T38MachinForcedOrbit.lean`](TheoryLib/PiQuantitativeBlockHitting/T38T38MachinForcedOrbit.lean) proves that the sampled rational orbit \(v_N=\{10^NM_{3N}\}\) obeys \(v_{N+1}=\{10v_N+\Delta_N\}\) with positive rational forcing; for \(s_N=10^N(\pi-M_{3N})\), it proves \(\Delta_N=10s_N-s_{N+1}\), \(0\le s_N<(10/625^3)^N\), a uniform \(O_h(1)\) difference between fixed-frequency Weyl sums, and exact equivalence of real Weyl cancellation for \((v_N)\) and the decimal \(\pi\) orbit. | This is an unconditional recurrence/transfer theorem and an exact obstruction: the forcing is a summable coboundary encoding the original orbit. It supplies no cancellation estimate, cylinder hit, density, normality, or V1. |
| `machine-checked` | [`T39T39EventualRecurrentTransfer.lean`](TheoryLib/PiQuantitativeBlockHitting/T39T39EventualRecurrentTransfer.lean) proves generically that eventually equal finite-alphabet streams have identical recurrent-value sets and counts. Under T37's explicit source-level \(\mu(\pi)<8\) premise, it identifies the recurrent values/count of `machinBlockCode m` exactly with those of `piCylinderCode m`, and for \(m>0\) transfers the full lower bound \(m+1\le p^{\mathrm{rec}}\) to the rational stream with no factor-two loss. | It proves that all \(10^m\) cells recur in one stream iff they recur in the other, but proves neither side. The source premise remains explicit, and no density, normality, or V1 follows. |
| `machine-checked` | [`T40T40MachinLocalForcing.lean`](TheoryLib/PiQuantitativeBlockHitting/T40T40MachinLocalForcing.lean) expands each sampled Machin forcing increment into its exact six-term window from each arctangent series, rewrites the real increment as three positive adjacent pairs from each base, clears each pair denominator explicitly, and proves that the cleared pair numerator is twice an odd integer for bases 5 and 239. | These are local arithmetic identities. They do not determine cancellation among all six pairs, the reduced denominator of the total forcing, its moving residue, any cylinder hit, or V1. |
| `machine-checked` | [`T41T41MachinV1Equivalence.lean`](TheoryLib/PiQuantitativeBlockHitting/T41T41MachinV1Equivalence.lean) proves exactly that canonical V1 is equivalent to recurrence of every value of every `piCylinderCode m`; under the explicit source-level \(\mu(\pi)<8\) premise, it is also equivalent to recurrence of every value of every rational `machinBlockCode m`. | The equivalence preserves leading-zero words and \(m=0\), but neither side is proved. It is an exact reformulation, not a distribution theorem or a resolution. |
| `machine-checked` | [`T42T42MachinTwoAdicForcing.lean`](TheoryLib/PiQuantitativeBlockHitting/T42T42MachinTwoAdicForcing.lean) proves odd-denominator presentations and exact two-adic order one for each base-5 and base-239 sum of three positive adjacent pairs, together with exact even/odd six-term regroupings. | T42 itself deliberately stops before the combined valuation; T44 now proves the exact global reduced-numerator statement. |
| `machine-checked` | [`T43T43TwoAdicForcingSeparator.lean`](TheoryLib/PiQuantitativeBlockHitting/T43T43TwoAdicForcingSeparator.lean) constructs positive summable geometric forcing with an exact twice-odd certificate \(2^{N+4}15258789/5^{11(N+1)}\), whose forced base-ten orbit converges to \(1/3\) and eventually avoids \([0,1/10)\). | This is an artificial separator, not a statement about \(\pi\). It proves that positivity, geometric decay, summability, and the exact two-adic numerator profile do not imply even one-cell recurrence. |
| `machine-checked` | [`T44T44MachinTotalTwoAdicForcing.lean`](TheoryLib/PiQuantitativeBlockHitting/T44T44MachinTotalTwoAdicForcing.lean) proves \(v_2(\Delta_N)=N+4\) for the actual rational forcing, proves its reduced denominator odd, and states literally that its reduced numerator has exact two-adic exponent \(N+4\). | This closes the former T42 formal API gap. T43 proves that even this exact profile has no generic implication to a decimal-cell hit. |
| `machine-checked` | [`T45T45MachinPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T45T45MachinPrimeSurvival.lean) combines the two singular terms at an admissible interior prime \(p=12N+5+2k\), \(k\in\{1,3,4\}\), reduces their numerator modulo \(p\) to the nonzero residue \(951=3\cdot317\), and proves \(v_p(\Delta_N)=-1\) for every prime \(p>12\), \(p\ne239\), in those slots. | This is exact arithmetic of the actual signed twelve-term numerator. It controls one non-archimedean component, not the full ordered residue or any decimal cell. |
| `machine-checked` | [`T46T46MachinFixedModulusTelescoping.lean`](TheoryLib/PiQuantitativeBlockHitting/T46T46MachinFixedModulusTelescoping.lean) proves the exact rational iterate, its fixed-initial-denominator representation, the identity between the accumulated forcing and \(10^ts_n-s_{n+t}\), and the uniform pulse bound \(<10\rho(100\rho)^N\) for \(t\le2N+1\). | “Fixed denominator” describes the main representation from the initial sample; it does not assert unchanged later reduced denominators. No exponential-sum saving or cylinder hit follows. |
| `machine-checked` | [`T47T47MachinAllPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T47T47MachinAllPrimeSurvival.lean) proves the two endpoint valuations, proves \(v_{239}(\Delta_{19})=-245\), routes every prime \(p>12\) through its residue class modulo 12, and concludes that \(p\) divides the reduced denominator of some actual sampled Machin forcing. | The conclusion is existential in the forcing index and purely non-archimedean. Even survival of every prime supplies no ordering, density, Fourier cancellation, prescribed decimal cell, or V1. |
| `machine-checked` | [`T48T48MachinSeedUpperHalfPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T48T48MachinSeedUpperHalfPrimeSurvival.lean) expands the complete fixed seed \(10^{N+1}M_{3(N+1)}\), isolates its unique singular pair for every prime \((12N+15)/2<p\le12N+15\), excludes the extra endpoint \(12N+17\), and proves valuation \(-1\) and reduced-denominator multiplicity one outside \(p=239,317\). | This validates the route-specific exponential-cofactor premise in the same-denominator separator. It still leaves the actual numerator residue modulo that cofactor completely uncontrolled. |
| `machine-checked` | [`T49T49MachinEndpointPulse.lean`](TheoryLib/PiQuantitativeBlockHitting/T49T49MachinEndpointPulse.lean) combines the right base-239 endpoint in forcing `N` with the next left base-5 endpoint. For prime `p = 12*N+17 > 12`, outside 239 and 317, it proves the exact localized core, its nonzero residue proportional to `4*951/(5*239)`, and valuation -1 for `sampledMachinValueRat (N+2+t)` at every `t <= 2*N+1`. | This is the missing class-5-modulo-12 long pulse. The first omitted forcing contains exponent `3*p`, so the cutoff is exact for the integrality argument. It is local p-adic information, not a cylinder hit. |
| `machine-checked` | [`T50T50MachinSeedLowerBandPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T50T50MachinSeedLowerBandPrimeSurvival.lean) treats the fixed seed with `d = 12*N+15`. In `d/5 < p <= d/3`, it combines the singular exponents `p,3*p`, proves the full coefficient `5359397032/1706489875`, and obtains valuation -1 outside the explicit fixed exceptions. In `d/3 < p <= d`, it proves the unique-term law. It also classifies and discharges the apparent endpoint case `p | d+2`; the closed union theorem gives exact reduced-denominator multiplicity one across `d/5 < p <= d` subject only to `5,239,317,11,19,233,13757`. | This machine-checks the arithmetic input behind the repaired two-band cofactor estimate. It neither proves the PNT/Jacobsthal asymptotic layer nor locates the actual reduced numerator in an archimedean interval. |
| `machine-checked` | [`T51T51MachinSeedThirdBandPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean) treats \(5p\le12N+15<7p\), isolates the seed exponents \(p,3p,5p\), and proves valuation \(-1\) plus exact reduced-denominator multiplicity one outside \(239,19,37,79,48049,3586217\). If the extra endpoint is singular, Lean proves \(12N+17=7p\), hence \(p\equiv11\pmod {12}\), and rules out every prime factor of the adjusted coefficient. | This machine-checks the third fixed prime band with no endpoint hypothesis. It is local denominator arithmetic and supplies no archimedean residue, cylinder hit, or V1. |
| `machine-checked` | [`T52T52MachinSeedThreePrimaryPersistence.lean`](TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean) proves that for every \(j\ge1\), if \(3^a\le12j+3<3^{a+1}\), then \(v_3(10^jM_{3j})=1-a\), and the reduced denominator has exact three-primary multiplicity \(a-1\). | The proof isolates the unique least-valuation odd exponent \(3^a\), proves the Machin cancellation factor has exact 3-adic order one, and controls the full regular remainder. It is persistent denominator structure, not numerator distribution or a word hit. |
| `machine-checked` | [`T53T53MachinQuotientCarry.lean`](TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean) proves the exact split \(b=Fc+r\), the rational identity \(b/(FD)=c/D+r/(FD)\), and the full base-ten recurrence for the fine remainder, fine carry, coarse quotient, decimal carry, and next numerator. | For canonical states the decimal digit is exactly \((10c+\lfloor10r/F\rfloor)/D\). This formally identifies the uncontrolled complementary quotient with the digit-generating state; it does not control that state. |
| `machine-checked` | [`T54T54ThreePrimaryNestedSchedule.lean`](TheoryLib/PiQuantitativeBlockHitting/T54T54ThreePrimaryNestedSchedule.lean) proves that adjacent exponent windows for \(12j+3\) differ by zero or one. Hence the exact T52 factor \(3^{a-1}\) stays fixed or triples, always divides the next factor, and has adjacent quotient exactly one or three. | This closes the former divisibility defect in the cross-index resonance bookkeeping. It supplies no cancellation for the inherited actual alias and no numerator-phase distribution. |
| `machine-checked` | [`T55T55ThreePrimaryCoarseSelector.lean`](TheoryLib/PiQuantitativeBlockHitting/T55T55ThreePrimaryCoarseSelector.lean) proves in \(\operatorname{ZMod}(D)\) that the reduced full remainder casts to the original numerator, \(Fc=A-r\), and, when \(F\) is a unit, \(c=AF^{-1}-rF^{-1}\). | This formally validates the generic selector in (11bg). It also makes the obstruction literal: the leading residue does not determine the coarse class unless the complementary fine phase is controlled. It proves no such control and no V1. |
| `machine-checked` | [`T56T56ThreePrimaryResidualLift.lean`](TheoryLib/PiQuantitativeBlockHitting/T56T56ThreePrimaryResidualLift.lean) proves the exact lifted residual-numerator identity, derives \(3R'=R+F(u-v)\) after cancellation of the old selector modulus, and concludes \(R'=3^{-1}R\) in \(\operatorname{ZMod}(F)\) when three is a unit. | This formalizes the generic algebra underlying (11bj); the Machin-specific instantiation there remains a `proof sketch`. The update is a permutation of fine residue classes, not magnitude decay, alias averaging, a cylinder hit, or V1. |
| `machine-checked` | [`T57T57ThreePrimaryPhaseRecombination.lean`](TheoryLib/PiQuantitativeBlockHitting/T57T57ThreePrimaryPhaseRecombination.lean) proves the exact rational recombination \(b/(Fd)=t+L/d+R/F\), the fixed-depth residual carry identity, and \(R'\equiv10R\pmod F\). | These are generic identities under explicit split, divisibility, and carry hypotheses. T57 does not instantiate the canonical Machin variables or carry ranges; multiplication by ten is transport, not necessarily a permutation, cancellation, a cylinder hit, or V1. |
| `machine-checked` | [`T58T58HuttonRationalShadow.lean`](TheoryLib/PiQuantitativeBlockHitting/T58T58HuttonRationalShadow.lean) defines rational Hutton lower and upper Taylor sums, proves \(H_K\le\pi\le U_K^H\), and proves their exact positive width \(8/((4K+5)3^{4K+5})+4/((4K+5)7^{4K+5})\). | This is an unconditional sharper rational bracket, not a theorem that its decimal orbit hits any prescribed cell. The comparison with the Machin bracket and affine-coupling analysis remain `proof sketch`. |
| `machine-checked` | [`T59T59HuttonCylinderCertificate.lean`](TheoryLib/PiQuantitativeBlockHitting/T59T59HuttonCylinderCertificate.lean) proves that a scaled bracket wholly contained in one translated decimal cylinder fixes the arithmetic block code, then specializes T58 and identifies the canonical symbolic `piCylinderCode` value. | This certifies one supplied finite hit. It does not prove the existential bracket-containment premise for any prescribed word, let alone uniformly for all words, so it is not V1. |
| `machine-checked` | [`T60T60HuttonAdjacentIncrement.lean`](TheoryLib/PiQuantitativeBlockHitting/T60T60HuttonAdjacentIncrement.lean) expands each adjacent Hutton lower-shadow increment into its four exact Taylor terms, proves the closed positive rational formula, and proves strict increase. | This formalizes the arithmetic input to the neighboring-denominator analysis. It proves no valuation, period localization, decimal-cylinder hit, or V1. |
| `machine-checked` | [`T61T61HuttonUpperHalfPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean) proves that if \(p>7\) is prime, \(p\ne17\), and \(4K+3<2p\le2(4K+3)\), then \(v_p(H_K)=-1\); equivalently, \(p\) occurs exactly once in the reduced denominator of the lower Hutton shadow. | This is unconditional actual-numerator denominator structure. It neither combines the eligible primes into an asymptotic product theorem nor estimates the short decimal orbit of the selected numerator, so it proves no cylinder hit or V1. |
| `machine-checked` | [`T62T62HuttonEligiblePrimeProduct.lean`](TheoryLib/PiQuantitativeBlockHitting/T62T62HuttonEligiblePrimeProduct.lean) defines the exact finite set of T61-eligible primes, proves its members are pairwise coprime and each has denominator multiplicity one, and proves their whole squarefree product divides \(\operatorname{den}(H_K)\). | This is the joint finite divisor theorem formerly left implicit. It contains no PNT/asymptotic lower bound, selected-numerator estimate, short-orbit distribution, cylinder hit, or V1. |
| `machine-checked` | [`T64T64HuttonOneThirdPrimeProduct.lean`](TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean) proves that if \(p>7\) is prime, \(p\ne17\), and \(4K+3<3p\) with \(p\le4K+3\), then \(v_p(H_K)=-1\) and the reduced denominator has exact multiplicity one; it then proves that the squarefree product of every such prime divides \(\operatorname{den}(H_K)\). | The extension is exact because the only positive multiples of \(p\) below \(3p\) are \(p,2p\), while every Hutton exponent is odd. It strengthens the finite forced band to \(((4K+3)/3,4K+3]\), but contains no product asymptotic, selected-numerator estimate, cylinder hit, or V1. |
| `machine-checked` | [`T63T63HuttonFiveAdicTransient.lean`](TheoryLib/PiQuantitativeBlockHitting/T63T63HuttonFiveAdicTransient.lean) proves, including \(K=0\), that \(5^e\le4K+3<5^{e+1}\) implies \(v_5(H_K)=-e\) and exact reduced-denominator multiplicity \(e\). | This proves the exact five-primary exponent used in the post-transient CRT reduction. It does not by itself determine a full base-10 preperiod, which may also depend on the two-primary denominator, and it gives no phase distribution or V1. |
| `machine-checked` | [`T65T65HuttonOneFifthPrimeProduct.lean`](TheoryLib/PiQuantitativeBlockHitting/T65T65HuttonOneFifthPrimeProduct.lean) treats \((4K+3)/5<p\le(4K+3)/3\): the only singular odd exponents are \(p,3p\); their four terms reduce to the fixed residue \(21778=2\cdot10889\). Outside the genuine new exception \(10889\), Lean proves valuation \(-1\), denominator multiplicity one, and divisibility by the whole squarefree band product. | Together with T64 this forces the finite band \(((4K+3)/5,4K+3]\) outside two fixed exceptions. It proves no PNT asymptotic, selected-numerator or complementary-phase estimate, cylinder hit, or V1. |
| `machine-checked` | [`T66T66HuttonDecimalTransient.lean`](TheoryLib/PiQuantitativeBlockHitting/T66T66HuttonDecimalTransient.lean) proves every paired Hutton summand has exact two-adic valuation two, the nonzero full lower shadow has valuation at least two, and its reduced denominator is odd. Combined with T63, \(5^e\le4K+3<5^{e+1}\) gives \(\max(v_2(\operatorname{den}H_K),v_5(\operatorname{den}H_K))=e\). | This closes the exact base-ten denominator preperiod used by the CRT reduction. It gives no control of the post-transient numerator phase, no cylinder hit, and no V1. |
| `machine-checked` | [`T67T67TwoThreeArctanShadow.lean`](TheoryLib/PiQuantitativeBlockHitting/T67T67TwoThreeArctanShadow.lean) proves the exact \(1/2+1/3\) rational bracket, \(v_2(E_K)=-(4K+1)\), \(v_2(\operatorname{den}E_K)=4K+1\), \(v_5(\operatorname{den}E_K)\le4K+1\), and hence exact decimal preperiod \(4K+1\). It also proves \(10^{4K+1}W_K>1/10\). | At the first post-transient position the uncertainty is already wider than every nonempty decimal cylinder. This machine-checks a complete-period obstruction; it does not control the selected dyadic-transient numerator, hit a cylinder, or prove V1. |
| `machine-checked` | [`T68T68HuttonSimultaneousPrimary.lean`](TheoryLib/PiQuantitativeBlockHitting/T68T68HuttonSimultaneousPrimary.lean) proves a general odd-prime dominant-layer score lemma and, for every \(a\ge2\), exact simultaneous valuations \(v_3(H_{K_a})=-(R_a+a)\), \(v_7(H_{K_a})=-(R_a+a+1)\), hence reduced-denominator multiplicities \(R_a+a\) and \(R_a+a+1\), where \(R_a=3^a7^{a+1}=4K_a+3\). | All 42 proposition declarations passed independent checks and the full gate. The theorem does not formalize the leading units, CRT/high-prime completion, short-orbit cancellation, a cylinder hit, or V1. |
| `machine-checked` | [`T69T69FixedSixteenReturn.lean`](TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean) proves the metric form of \(16\{\pi\}\in\overline{\{10^n\pi\}}\), derives \(\times16\)-invariance and containment of the joint \(10^s16^t\) orbit, proves that full decimal-orbit closure implies exact list-valued V1, and proves V1 implies the fixed return. Under exactly the explicit density of the joint orbit, it proves V1 iff the fixed return. | The density premise is Furstenberg's published consequence for irrational \(\pi\), but is not formalized as a kernel theorem or new axiom. Independent audit narrowed the premise to its minimal form and the corrected full gate passed. T69 proves neither the fixed return nor V1. |
| `machine-checked` | [`T70T70EmpiricalRigidityBridge.lean`](TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean) proves support transport under invariant or absolutely-continuous pushforwards and, conditional on the explicit T77 `FurstenbergSourcePremise`, proves that every infinite compact set forward invariant under \(\times10\) and \(\times16\) is the whole circle. Its ergodic-nonsingular and nonergodic absolute-continuity interfaces then imply full pi-orbit closure and exact V1. | All 15 supporting declarations are registered and the full allowlist gate passes. T70 constructs no Furstenberg premise and proves no infinite-support, matching, absolute-continuity, ergodicity, or nonsingularity statement for the fixed pi orbit; it is a conditional bridge, not V1. |
| `machine-checked` | [`T71T71CenteredCarryRecurrence.lean`](TheoryLib/PiQuantitativeBlockHitting/T71T71CenteredCarryRecurrence.lean) proves uniqueness of half-open centered integer representatives, the exact one-step remainder recurrence under a changing denominator, the advanced-old-quotient identity, and the equivalence between zero carry and the uncorrected numerator lying in the new centered interval. | All four declarations are registered exactly once and passed independent type, boundary, 36,912-row integer, kernel, exploit, and axiom-allowlist checks. T71 is generic algebra: it neither instantiates the BBP coefficient identities nor proves nonzero-carry density, a gap bound, a word hit, or V1. |
| `machine-checked` | [`T72T72ColoredRepunitReturn.lean`](TheoryLib/PiQuantitativeBlockHitting/T72T72ColoredRepunitReturn.lean) proves that canonical V1 is exactly equivalent to arbitrarily late, arbitrarily accurate real returns of the pi decimal orbit to every repunit-grid color \(k/(10^P-1)\). | All ten supporting declarations are registered exactly once and the full kernel, exploit, and axiom-allowlist gate passes. An independent formal audit recompiled the module, checked every quantifier and boundary cylinder, replayed the full 8,493-job gate, and found only the permitted dependencies. Ordinary real distance makes color zero endpoint-safe; the reverse proof uses \((10a+5)/(10^{m+1}-1)\), strictly inside every word cylinder including leading-zero and all-nine words. T72 proves only an equivalence, not that pi has the return property. |
| `machine-checked` | [`T73T73ThreePrimaryOrbit.lean`](TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean) proves that ten has exact order \(3^e\) modulo \(3^{e+2}\), its first \(3^e\) powers have no repeats, and the first \(3^e\) quotients \((10^n-16)/3\) are distinct modulo \(3^{e+1}\) while all reduce to one modulo three. | Nine theorem declarations are registered in the axiom audit. These are the generic finite-orbit ingredients for the isolated BBP three-primary coordinate; T73 does not formalize the BBP denominator epoch formula or identify the full coset as a set, and it gives no control of any synchronized complementary CRT coordinate, decimal-cylinder hit, or V1. |
| `machine-checked` | [`T74T74ThreePrimaryDecimation.lean`](TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean) proves four affine folds, four exponent folds, and the four exact rational identities \(9f_i(9r+d_i)-f_i(r)=f_i(r)(16^{-(8r+d_i)}-1)\) for the BBP pole offsets \(d=(1,4,5,6)\). | All twelve declarations are registered exactly once and passed direct `--trust=0`, barrel, central-audit, forbidden-construct, and full 8,493-job checks. T74 deliberately does not formalize LTE, the summed decimation, endpoint epochs, the synchronized complement, a decimal hit, or V1. |
| `machine-checked` | [`T75T75UniformShadowCover.lean`](TheoryLib/PiQuantitativeBlockHitting/T75T75UniformShadowCover.lean) proves that eventual uniform circle coverage by finite shadow rows, lateness of every attached exponent, and uniformly vanishing shifted-shadow error imply arbitrarily late circle density, every endpoint-safe colored repunit return, and therefore canonical V1 for pi. | Four claim-supporting declarations are registered and passed the complete 8,493-job exact-allowlist gate. The color-zero proof targets a small positive interior point. T75 asserts none of the three analytic premises for the actual BBP rows; in particular it does not prove the endpoint-gap `conjecture` or V1. |
| `machine-checked` | [`T76T76ExceptionalPathCylinderCover.lean`](TheoryLib/PiQuantitativeBlockHitting/T76T76ExceptionalPathCylinderCover.lean) proves that uniformly bounded bad prefix families in a \(p\)-ary tree have an infinitely-often set admitting countable cylinder covers of arbitrarily small total Bernoulli weight; it also proves the exact even-epoch series \(\sum_{r\ge0}2/(\eta^2 3^{2+2r})=1/(4\eta^2)\). | All 15 declarations are registered and the full gate passes. T76 is an abstract outer-cover theorem: it does not formalize the BBP coefficient bound, select the actual computable BBP path, relate the changing complements across epochs, or prove V1. |
| `machine-checked` | [`T77T77SelectedPadicDefectShell.lean`](TheoryLib/PiQuantitativeBlockHitting/T77T77SelectedPadicDefectShell.lean) proves the exact all-\(M\) rational nine-block/five-tail decomposition of \(9B_{9M+13}-B_M\), the even-epoch depth residue, all pair-count, complete-block, tail, boundary, and pole-residue tables, and total residue one in \(\mathbb Z/9\mathbb Z\). | All 26 declarations are registered and the full 8,493-job gate passes. T77 does not yet connect arbitrary rational pole shells through \(\mathbb Z_{(3)}\) to its finite residue ledger, so it does not machine-check the all-depth congruence (40fp), path escape, or V1. |
| `proof sketch` | Independent derivations give the all-depth finite-sum ninefold decimation, nested pre-drop and drop endpoint units, and the exact sparse Fourier transform of the isolated three-primary phase. | The pre-drop grids refine nine-to-one for even \(e\ge4\); the drop transition \(e=4\to2\) is three-to-one and only later transitions are nine-to-one. The complete BBP sum remains one selected coefficient of an uncontrolled complementary CRT weight, so these results do not imply full-phase cancellation or V1. |
| `proof sketch` | Exact nine-block orthogonality expresses the selected complementary Fourier energy as a sum of nine-point twisted block squares. Even ideal ordinary off-diagonal mixing leaves asymptotic energy share \(1/9\) and gives only the constant Cauchy bound \(1/3+o(1)\). | Every block correlation also retains linear dyadic precision and exponential high-prime modulus. This is a phase-sensitive no-go for support/energy-only and one-step-differencing arguments, not a cancellation theorem. |
| `proof sketch` | The isolated three-primary character has vanishing normalized \(U^s\)-norm for every fixed \(s\), yet its artificial conjugate complement has the same small norm and saturates the selected correlation. Exact unit averaging gives \(\#\{a:|S_a(W)|\ge\eta T\}\le12/\eta^2\). | Only constantly many unit coefficients can be exceptional per depth, but the actual BBP coefficient follows one coherent three-adic lift path and is not a fresh sample. Second and selected third differences retain exponential high-prime and dyadic moduli. Independent audit confirms the algebra but no selected-coefficient decay or V1. |
| `proof sketch` | The exceptional coefficients at each even epoch are exact nine-lift fibres. For any predetermined changing weight sequence, their Haar cylinder measures are summable, so almost every coherent 3-adic path has normalized correlation tending to zero. The actual complement obeys the exact twisted ninth-power transition (40fl), with unbounded dyadic depth (40fm). | “Almost every” cannot select the one computable BBP path, and the weight changes between epochs. Independent audit confirms the fibre, Borel--Cantelli, transition, and denominator algebra while retaining the endpoint nesting as a `proof sketch`; no deterministic path exclusion or V1 follows. |
| `proof sketch` | For every even \(e\ge2\), the selected BBP endpoint defect satisfies \(9B_{M_{e+2}}-B_{M_e}\equiv1\pmod{9\mathbb Z_{(3)}}\), and the next lift obeys \(\kappa_e\equiv\ell_e+1\pmod9\). | A disjoint audit rederives every paired cutoff, nonlift residue, boundary term, and the lift law. The hidden carry prevents a closed transition from the displayed residue alone; the result gives no complementary-phase estimate, exceptional-path escape, or V1. |
| `experiment` | Fourteen genuine pre-drop and first-drop full-phase rows for even \(e=4,\ldots,16\), with \(11\le L\le5{,}491{,}685\), satisfy \(0.899<LG/\log L<1.084\), where \(G\) is their largest circular gap. At \(e=16\), \(G<2.736782005204\cdot10^{-6}\) for each exact BBP row and the corresponding actual-pi gap is strictly below \(2.736782005019\cdot10^{-6}<10^{-5}\). | Two independent directed-prefix implementations reproduce the epoch-16 rows. The second directly finds all 100,000 five-digit words in each inspected pi window, minimum multiplicity 23. This bounded result motivates \(G_e^\pm=O(\log L_e^\pm/L_e^\pm)\), a directly sufficient `conjecture`; it proves neither length-six coverage, the asymptotic law, nor V1. |
| `experiment` | Exact rational rows falsify \(G_e^\pm\le G_{e-2}^\pm/9\) in all four reconstructed transitions, and exhaustive testing of 41,924 complete-primary-period subwindow pairs rejects the natural primary-compatible ideal-child refinement at fixed positive thresholds. | This rules out the obvious recursion mechanism only. A different global matching remains possible, and no all-depth lower or upper gap law follows from the finite checks. |
| `machine-checked` | [`T24T24FiniteWindowAdditiveDivergence.lean`](TheoryLib/PiQuantitativeBlockHitting/T24T24FiniteWindowAdditiveDivergence.lean) gives one eventual cutoff for every frequency in any fixed finite window and any fixed additive threshold. | This is the valid finite quantifier upgrade of T22. The cutoff may depend arbitrarily on both the window and threshold, so it still gives no relative cancellation. |
| `machine-checked` | [`T25T25PowerTenFrequencyShift.lean`](TheoryLib/PiQuantitativeBlockHitting/T25T25PowerTenFrequencyShift.lean) proves the exact boundary identity relating frequencies \(h\) and \(10^t h\), and \(|G_N(10^t h)-G_N(h)|\le2t\) for \(G_N(h)=N-|S_N(h)|\). | Power-of-ten frequency transport changes the additive gap by only a boundary term; it does not multiply a weak gap into the T19 relative bound. |
| `machine-checked` | Long-lag equal-block collision decay implies every finite word occurs in [`T3T3CollisionDecayImpliesDisjunctive.lean`](TheoryLib/PiLongLagBlockCollisionDecay/T3T3CollisionDecayImpliesDisjunctive.lean). | The long-lag estimate for \(\pi\) is the unproved premise. |
| `literature-checked` | Zeilberger–Zudilin give \(\mu(\pi)\le7.103205334137\ldots<7.104\). | Combined with the separate local periodic-window argument, this is the numerical input to the `proof sketch` below. |
| `literature-checked` | Bugeaud--Kim give \(p_{10}(\pi,m)+p_{16}(\pi,m)-2m\to\infty\). | The bases are multiplicatively independent, but the theorem does not determine which base contributes the excess; BBP does not transfer it to decimal complexity. |
| `literature-checked` | Fischler--Rivoal (Math. Ann. 394, 2026) give effective \(c,d>0\) with \(|\pi-a/b|\ge\exp(-cb^d)\), by viewing \(\pi\) as a real irrational simple zero of the rational-coefficient E-function \(\sin z\). | At \(b=10^N\) this is \(\exp(-c10^{dN})\), far below the ordinary \(10^{-N}\) truncation scale and insensitive to whether the numerator avoids a word. It gives no cylinder escape or V1. |
| `literature-checked` | Peres--Yang (arXiv:2606.28860v1, 2026) prove \(NG_N(x)/\log N\to1\) for Lebesgue-almost every \(x\) when \((a_n)\) is an integer divisibility chain, in particular \(a_n=10^n\). Their block survivor bounds quantify the probability that an interval of length \(\asymp\log N/N\) is missed. | The proof uses Lebesgue measure and, for the sharp lower bound, independent mixed-radix digits. It does not include the fixed point \(\pi\) or the triangular array of selected rational BBP numerators. It identifies the right scale and a deterministic no-hit analogue to seek, not a specialization proving V1. |
| `experiment` | Every word of length at most 13 appears in a known finite prefix. | No finite prefix establishes V1 or any asymptotic digit law. |

The `machine-checked` labels above follow the accepted-module status recorded
in the repository's 2026-08-09 review brief. During this audit, each theorem
used by this note was also registered explicitly in the currently modified
`audit/AxiomAudit.lean`. The full gate reported only `propext`,
`Classical.choice`, and `Quot.sound` for those declarations.

Irrationality and transcendence are nowhere near enough. Irrationality rules
out eventual periodicity, while explicit transcendental Liouville numbers can
have decimal expansions using only the digits 0 and 1.

## A weak fixed-π proof sketch

Status: `proof sketch`, with the numerical input `literature-checked` and the
generic periodic-window inequality `machine-checked`.

Let

\[
\operatorname{Chg}_\pi(N)=
\#\{1\le j<N:d_j\ne d_{j+1}\}.
\]

Here and in (3), `log` is the natural logarithm.

The current T99 audit presents a proof sketch combining the
irrationality-exponent bound \(\mu(\pi)<888/125=7.104\) with the checked
periodic-window inequality to derive

\[
\liminf_{N\to\infty}
\frac{\operatorname{Chg}_\pi(N)}{\log N}
\ge \frac1{\log(888/125)}
=0.5100328548\ldots. \tag{3}
\]

The proof sketch argues as follows. A constant run is a period-one decimal
window. The effective irrationality bound limits a sufficiently late run
beginning at zero-based position \(a\) to length at most

\[
\frac{763}{125}a+\frac{888}{125}+1.
\]

Consequently successive run starts grow by at most a factor \(888/125\), up
to an additive constant. Iterating and inverting that recurrence gives (3).
The source-pinned derivation is
[`T99_DELTA_AUDIT.md`](work/theory/pi-positive-decimal-factor-entropy/library/t99/T99_DELTA_AUDIT.md).

If the assembled derivation is correct, (3) would be an unconditional
fixed-\(\pi\) consequence because its published numerical input is
unconditional rather than a digit-randomness conjecture. It retains the
repository label `proof sketch` pending independent checking. Even then it is
not close to V1: a word may have logarithmically many changes and still omit
almost every decimal block. The same audit claims a repetition-exponent bound,
but that bound would not improve the Morse–Hedlund complexity baseline.

## Meaningful working stone 1: sparse collision energy

Status: `proof sketch`. No novelty claim is made; the sparse-witness idea was
already recorded in
[`notes/gpt-speculative-directions-2026-07-23.md`](notes/gpt-speculative-directions-2026-07-23.md).

Let \(S\) be a finite nonempty set of starting positions, let \(B_i^{(m)}\)
be the length-\(m\) block at \(i\), and put

\[
c_v=\#\{i\in S:B_i^{(m)}=v\},\qquad
D=\#\{v:c_v>0\},\qquad
E=\sum_v c_v^2.
\]

Thus \(E\) is the number of ordered equal-block pairs in \(S^2\). Since
\(\sum_vc_v=|S|\), Cauchy–Schwarz gives the exact finite inequality

\[
|S|^2\le D E,\qquad\text{hence}\qquad D\ge\frac{|S|^2}{E}. \tag{4}
\]

For a fixed length-\(k\) word \(u\), let \(L_u(m)\) be the number of
length-\(m\) decimal words that avoid \(u\), and define

\[
U_k(m)=\max_{u\in\{0,\ldots,9\}^k}L_u(m).
\]

For \(m\ge k\), the following certificate is sufficient:

\[
\boxed{\quad \frac{|S|^2}{E}>U_k(m)
\quad\Longrightarrow\quad
\text{every length-}k\text{ word occurs in }\pi.\quad} \tag{5}
\]

Indeed, if some \(u\) were globally missing, every sampled \(m\)-block would
avoid \(u\), so \(D\le L_u(m)\le U_k(m)\), contradicting (4) and (5).
The finite number \(U_k(m)\) is exactly computable with a KMP/de Bruijn
avoidance automaton.

At the endpoint \(m=k\), \(U_k(k)=10^k-1\). Therefore the especially simple
certificate

\[
E<\frac{|S|^2}{10^k-1} \tag{6}
\]

forces all \(10^k\) length-\(k\) words to occur among the sampled starts.
Still at \(m=k\), if a word is missing from the sampled starts and
\(q=10^k\), the corresponding necessary energy gap is

\[
\frac{E}{|S|^2}-\frac1q\ge\frac1{q(q-1)}. \tag{7}
\]

There is an instructive calibration. For \(N\) independent uniform draws from
\(q\) words,

\[
\mathbb E E=N+\frac{N(N-1)}q.
\]

This expectation passes the crude full-energy threshold (6) exactly when
\(N>(q-1)^2\). Thus a diagonal-inclusive energy certificate typically needs
quadratic sample size, much more than the coupon-collector scale. This
explains why the diagonal term obstructs naive energy estimates.

There is also an exact no-go result for the unrestricted sparse idea. Let
\(p_x(m)\) be the number of distinct length-\(m\) factors of any fixed
infinite word \(x\). For every nonempty finite \(S\), (4) gives

\[
\frac{|S|^2}{E}\le D\le p_x(m).
\]

Conversely, choose one occurrence of each distinct length-\(m\) factor. For
that finite \(S\), every nonzero occupancy is one, so
\(E=|S|=p_x(m)\) and equality holds. Therefore

\[
\boxed{\sup_{\varnothing\ne S\subset\mathbb N\text{ finite}}
       \frac{|S|^2}{E_{x,S}(m)}=p_x(m).} \tag{7a}
\]

This `proof sketch` shows that merely asserting the existence of a favorable
sparse sample is exactly a repackaging of factor complexity; quantified over
all target lengths, it is equivalent to V1 rather than a weaker route to V1.
Sparse collision estimates retain content only when \(S\) is prescribed or
restricted independently of the observed blocks, or when a quantitative
location bound is required. The earlier suggestion to search over arbitrary
\(S\) is therefore retired.

## Machine-checked breakthrough: exact natural-scale Fourier certificate

Status: the finite theorem, comparison implications, strictness witness, and
conditional implication to V1 are `machine-checked`. The fixed-\(\pi\)
cancellation premise is still a `conjecture`.

Put

\[
x_j=\{10^j\pi\},\qquad
S_N(h)=\sum_{j=0}^{N-1}e^{2\pi i h x_j}.
\]

Write \(q=10^k\). The former T6 theorem said that omission of a particular
length-\(k\) word before \(N\) forces some integer \(h\) with

\[
0<|h|\le128q,
\qquad
\frac{|S_N(h)|}{N}\ge\frac1{16388q}. \tag{8}
\]

The new progression is:

| Verified module | Frequencies required | Resonance forced by an empty interval of length \(1/q\) |
|---|---:|---:|
| [T6](TheoryLib/PiQuantitativeBlockHitting/T6PiNaturalScaleResonanceObstruction.lean) | \(0<|h|\le128q\) | \(|S_N(h)|/N\ge1/(16388q)\) |
| [T18](TheoryLib/PiQuantitativeBlockHitting/T18T18SharperNaturalScaleResonance.lean) | \(0<|h|\le4q\) | \(|S_N(h)|/N\ge1/(40q)\) |
| [T19](TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean) | \(0<|h|\le2q\) | \(|S_N(h)|/N\ge1/(24q)+1/(12q^3)\) |

T19 first proves a generic finite statement. If \(x_0,\ldots,x_{N-1}\) lie
in \([0,1)\) and avoid an interval \([a,a+1/q)\), then some nonzero integer
\(h\) satisfies

\[
|h|\le2q,
\qquad
\frac1{24q}+\frac1{12q^3}
\le \frac1N\left|\sum_{j<N}e^{2\pi i h x_j}\right|.
\]

Its direct contrapositive is an interval-hit theorem. Specializing the
intervals to decimal cylinders and \(x_j=\{10^j\pi\}\) yields the new
finite target:

\[
\boxed{
\left(N\ge1\ \land\quad
\forall h\in\mathbb Z,\ 0<|h|\le2\cdot10^k:\quad
\frac{|S_N(h)|}{N}<
\frac1{24\cdot10^k}+\frac1{12\cdot10^{3k}}\right)
\Longrightarrow
\forall w\in\{0,\ldots,9\}^k\ \exists j<N\ \forall 0\le r<k:\quad
d_{j+1+r}=w_r.} \tag{9}
\]

The conclusion bounds the start, not the final digit: every certified block is
fully contained in the first \(N+k-1\) fractional digits.

The proof uses the existing Jackson/Fejér minorant at order \(q\). An
injective triangular family of zero-frequency quadruples has the exact
cardinality identity

\[
3\,|I_q|=2q^3+q.
\]

This is a lower-bound family, not an enumeration of every zero mode. Combined
with the exact unaggregated coefficient mass \(4\), it gives constant
coefficient at least \(1/(3q)+2/(3q^3)\); the finite Fourier extraction
lemma then divides by twice the mass and produces the threshold in (9).

Lean proves the logical chain

\[
\text{T6 cancellation}\Longrightarrow
\text{T18 cancellation}\Longrightarrow
\text{T19 exact cancellation}\Longrightarrow\text{V1}.
\]

The generic implication is the theorem
`sharp_finite_frequency_hypothesis_implies_exact`; its nonconverse is
`exact_finite_frequency_hypothesis_strict_vs_sharp`. The latter uses an
explicit uniform three-point grid that cancels frequencies \(1\) and \(2\)
but resonates at \(3\), so it satisfies the T19 premise for \(q=1\) and
fails the T18 premise. This separator is not evidence about \(\pi\); together
the two theorems verify that the new finite sufficient condition is genuinely
weaker, not merely restated.

The importance of (9) is quantitative: it asks only for frequencies on the
natural cylinder scale and improves both the cutoff and allowed error. It
does not prove the displayed cancellation, nor any upper bound on the
witnessing \(N=N(k)\). Establishing the premise for every \(k\) remains the
unresolved, genuinely \(\pi\)-specific step.

The method is `literature-checked` as classical, not claimed novel or
literature-optimal. Erdős--Turán already used squared-Fejér/Jackson interval
localization in 1948, and Selberg--Vaaler extremal minorants are standard
related machinery. The contribution here is an explicit, audited
specialization that strictly improves the local formal frontier. A bounded
search dated 2026-08-10 did not locate this exact normalization and numerical
pair; that negative search is not a novelty claim.

## Current principal routes and their walls

| Route | Exact target | Status and obstruction |
|---|---|---|
| Natural-scale Fourier hitting | Prove the strict bound in (9) for each \(k\) and a suitable \(N\). | Directly target-aligned; no such fixed-\(\pi\) estimate is present in the repository or was located in the bounded 2026-08-10 search. |
| Prescribed sparse collision witness | Fix a schedule or location budget independently of the observed blocks, then prove (5). | Arbitrary existential \(S\) is exactly factor complexity by (7a) and is retired; only constrained sampling can be a genuinely different route. |
| Appearance ratio or prefix collision energy | Bound \(L_m/p_\pi(m)\), the maximal block multiplicity, or \(E_\pi(m,L_m)/L_m\). | T29 gives the exact conditional relative-gap transfer, but no such \(\pi\)-specific bound is known; the Fibonacci separator below proves that even a uniform bound plus positive-density relative saving does not imply V1. |
| Long-lag collisions | Bound \(R_\pi(m,N)\le C_s(N+N^2 10^{-sm})\) for every \(s\in(0,1)\). | A `machine-checked` chain reaches V1; the all-scale fixed-\(\pi\) square-function estimate remains a `conjecture`. |
| Factor entropy | Prove \(h_{10}(\pi)=\log10\). | T30 proves this is exactly V1; any merely positive lower bound would beat Morse–Hedlund but remains strictly weaker. |
| Near-return sparsity | Control close pairs in \(\{10^j\pi\}\). | Could imply superlinear factor complexity, not full word occurrence. |
| BBP/Bailey–Crandall dynamics | Put \(16\pi\) in the decimal orbit closure, equivalently prove the BBP rational diagonal limit (11c). | This is exactly V1 by Furstenberg; BBP tail control leaves an uncontrolled moving rational residue, and base-16 normality would not transfer. |

The 2026-08-09 repository review identifies the shared wall: a new arithmetic
property of \(\pi\) must produce cancellation at exponentially growing decimal
frequencies, uniformly over coupled lengths, lags, starts, and frequencies.
Generic almost-everywhere lacunary theorems do not specialize to the single
point \(\pi\). Multiplier-10 identities merely shift orbit windows, and
ordinary irrationality measures are far too weak at these scales.

## Current repository delta after the 2026-08-09 review

The automated program files still record no V1 claim-status upgrade. The local
verified track now contains both a material conditional-reduction upgrade and
an unconditional fixed-orbit spectral advance:

- Quantitative T18 and T19 replace the T6 cutoff/threshold by the strict
  progression displayed above. T19, its dependencies, and its strictness
  witness are imported by `TheoryLib.lean`, registered in
  `audit/AxiomAudit.lean`, and passed the full gate. The fixed-\(\pi\)
  premise remains a `conjecture`, so V1 itself is not promoted.

- Quantitative T20--T29 prove (18)--(24), (26), and (28), are imported and
  axiom-registered,
  and pass direct compilation plus the full repository gate. They
  establish first-occurrence support cancellation, simultaneous finite-window
  additive Fourier-gap divergence, the exact power-of-ten boundary law, and a
  positive proportion of natural-scale full-prefix defect witnesses for the
  actual \(\pi\) orbit, a multiplicity-robust linear additive gap, and its
  exact minimal-first-start-prefix form. T29 records the conditional relative
  saving supplied by an appearance-ratio bound, while proving no such bound.
  There is still no all-frequency relative cancellation and hence no V1
  status change.

- Quantitative T30 proves the exact generic equivalence between maximal
  decimal factor entropy and disjunctivity, then identifies it with canonical
  V1 for `piDigit`. It is imported and axiom-registered and has passed direct
  compilation plus an independent automated audit. No theorem establishes
  its maximal-entropy side for \(\pi\).

- Long-lag goal G10 remains unresolved, with its mathematical premise a
  `conjecture`. Program-local T99 is a bounded
  `literature-checked` negative map and explicitly supplies no fixed-\(\pi\)
  estimate:
  [`T99_DIRECTION_DISCOVERY_AUDIT.md`](work/theory/pi-long-lag-block-collision-decay/library/t99/T99_DIRECTION_DISCOVERY_AUDIT.md).
- T100–T103 were rejected for substantive issues including a proposition
  mismatch, circular or unproved premises, and the absence of a quantitative
  saving. They are failed routes, not partial proofs.
- T104 is `machine-checked` only for almost every phase and explicitly does
  not specialize to \(\pi\):
  [`T104T104ProbabilityClosure.lean`](TheoryLib/PiLongLagBlockCollisionDecay/T104T104ProbabilityClosure.lean).
- The near-return program subsequently reached the literal conditional
  transport in T108 and the source-audited related-model scouts T131--T135.
  None discharges a fixed-\(\pi\) premise. T131's balanced cycle flow reduces
  to prior global-\(L^2\) or offline balancing; T132's profile-majorization
  gain requires the unproved `PI-MEET`; T133's exact valuation transducer
  remains at orbit length comparable only to \(\log q\); T134's zero-cylinder
  sources do not yield occupancy at growing depth; and T135's Renyi-2
  projection mechanisms require independence or transfer essentially absent
  from the fixed orbit. Their source-pinned reports are under
  [`library/`](work/theory/pi-lacunary-near-return-sparsity/library/).
- At the latest 2026-08-12 state recheck, T136 and T137 are accepted workflow
  records. T136 closes its bounded literature delta with no survivor; T137
  retains only a related finite tensor-profile model and explicitly leaves
  its fixed-\(\pi\) transfer conjectural. Neither is evidence for a fixed-\(\pi\),
  C1, C2, or V1 claim. Observation and workflow state are not promoted into
  this audit. T138 presently has a `revise` verdict for falsely classifying a
  source already audited in T104 as novel; it is not a trusted finding.
- The near-return program's C1/C2 claims remain `conjecture`, and the
  positive-entropy program's G14 has no supporting fixed-\(\pi\) claim. See
  the current
  [near-return](work/theory/pi-lacunary-near-return-sparsity/program.json),
  [positive-entropy](work/theory/pi-positive-decimal-factor-entropy/program.json),
  and [long-lag](work/theory/pi-long-lag-block-collision-decay/program.json)
  state files.

## Literature search log

This is a bounded `literature-checked` status audit dated 2026-08-10 and
refreshed through 2026-08-13, not an exhaustive novelty review. The broad
source pins and theorem-by-theorem applicability audit are retained in
[`literature_report.md`](work/ultrapi-resume/literature_report.md); the latest
route-specific audits are linked at (40am)--(40ao),
(40ap)--(40bg), and (40ah)--(40ck).

| Date | Database/query or source | Finding |
|---|---|---|
| 2026-08-13 | Generalized-central-trinomial prime-factor search | [Noe (2006)](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf) supplies the Lucas/Schur congruences used in (40am), while [Wagner, arXiv:1205.5402v3](https://arxiv.org/abs/1205.5402v3) controls coefficient size rather than the moving prime window. [Mikić, arXiv:2311.14623v1](https://arxiv.org/abs/2311.14623v1) assumes a coprimality condition that fails for (T_n(2,2)) and treats a fixed parameter, not primes (p\asymp n). No located theorem proves the first-band little-o estimate. The audit also corrected Wagner's false prior JIS attribution. |
| 2026-08-13 | First-band affine-correlation and finite-field coefficient search | [Noe (2006)](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf) supports the Lucas and reflected-zero identities behind (40ap). [Kohen, arXiv:2411.03681v2](https://arxiv.org/abs/2411.03681v2), [Mattarei, arXiv:math/0512239v2](https://arxiv.org/abs/math/0512239v2), and [Sun, arXiv:1008.3887v13](https://arxiv.org/abs/1008.3887v13) provide fixed-characteristic symmetry, polynomial-weight, and congruence information, but none controls the pointwise cross-prime alignment in (40ap).  The exact countermodel (40at) proves why per-prime zero sparsity alone cannot close that gap; it is not an actual generalized-central-trinomial zero set. |
| 2026-08-13 | Prefix-gcd and generalized-central-trinomial support search | [Noe (2006)](https://cs.uwaterloo.ca/journals/JIS/VOL9/Noe/noe35.pdf) supplies the Lucas and reflection laws proving (40be). [Rowland--Yassawi, arXiv:1310.8635v2](https://arxiv.org/abs/1310.8635v2) treats fixed-characteristic automatic congruences, not a prime moving with the index. [Xiao, arXiv:2110.01751v2](https://arxiv.org/abs/2110.01751v2) concerns constant-coefficient linear recurrences and does not cover this P-recursive sequence or a growing prefix product. Independent audit corrected Xiaos exact title to “polynomials in almost units.” The truncated gcd is provably equivalent to the existing medium-prime target; no applicable little-o theorem was located. |
| 2026-08-13 | BBP one-character and linear-recurrence limit sets | [Chen--Ye--Zheng, arXiv:2604.14036v1](https://arxiv.org/abs/2604.14036v1) applies to ((10^n-16)\pi) and proves an infinite limit set, a (1/22) limsup bound, and residue-class spread at scale (1/10). None is a liminf-zero return. The BBP, Furstenberg, Kempner, and Shallit pins and exact applicability checks are recorded in the one-character independent audit. |
| 2026-08-13 | Scalar BBP monotone-forcing search | [Bailey--Crandall](https://www.davidhbailey.com/dhbpapers/bcrandom.pdf) and [Lagarias](https://arxiv.org/abs/math/0101055v2) provide the conditional perturbed-radix program, not a prescribed return for the fixed \(\pi\) orbit.  No searched recurrence or shrinking-target theorem converts the exact one-sided forcing (40au)--(40av) into return of the accumulated product (40aw).  The independently corrected rational model (40ay) proves that sign, monotonicity, summability, and \(W_n\to1\) alone cannot do so. |
| 2026-08-13 | BBP adjacent-shift matching search | The BBP coefficient identity gives the exact adjacent shift (40aj), while standard coupling, bounded-congestion matching, and Furstenberg support arguments prove only the conditional implication (40ak)--(40al). No located optimal-transport, empirical-measure, or lacunary-orbit theorem establishes both hypotheses for the fixed BBP rows. |
| 2026-08-13 | BBP fixed-period noncollapse and weakened matching search | Furstenberg's Lemma IV.2 and Theorem IV.1 imply that an infinite closed circle set forward invariant under both \(\times10\) and \(\times16\) is the whole circle.  [Lagarias, arXiv:math/0101055v2](https://arxiv.org/abs/math/0101055v2) rules out a finite topological limit set for irrational \(\pi\), but not a finite-support Cesaro limit; [Chen--Ye--Zheng, arXiv:2604.14036v1](https://arxiv.org/abs/2604.14036v1) gives topological progression-slice dispersion, not the positive-density defect (40az).  Metric lacunary pair-correlation theorems such as [Technau--Rudnick, arXiv:2001.08820v1](https://arxiv.org/abs/2001.08820v1) do not specialize to fixed \(\pi\).  No located theorem proves the matching or fixed-period noncollapse required in (40az)--(40bc). |
| 2026-08-13 | BBP centered-carry density and rational oversampling search | [Zeilberger--Zudilin](https://doi.org/10.2140/moscow.2020.9.407) supplies \(\mu(\pi)<7.103205334137\ldots\), which yields only the logarithmic lower bounds (40bm); it supplies no positive carry density. [Kempner](https://doi.org/10.1090/S0002-9947-1916-1501054-4) and [Shallit](https://cs.uwaterloo.ca/~shallit/Papers/scf.pdf) support the transcendental badly-approximable separator showing logarithmic order is generically sharp. [Lagarias, arXiv:math/0101055v2](https://arxiv.org/abs/math/0101055v2) and the local machine-checked T35 corroborate perturbed-radix/sevenfold-grid stability, but neither proves linear nonzero-carry density for the fixed pi row. No searched digit-complexity or metric lacunary theorem closes (40bl). |
| 2026-08-13 | Fixed-pi centered carries and empirical support | [Chen--Ye--Zheng, arXiv:2604.14036v1](https://arxiv.org/abs/2604.14036v1), Theorem 1.3 and Corollary 3.4, apply to \((10^P-1)\pi10^n\): the omega-limit set is infinite, the orbit has limsup distance at least \(1/11\) from the integers, and one slice of every progression has spread at least \(1/10\).  This proves arbitrarily late fixed-amplitude excursions and hence infinitely many nonzero centered carries, but gives no count, Cesaro mass, or infinite-support empirical limit.  A factorial-time dense-grid separator makes that exact topological/frequency gap explicit. |
| 2026-08-13 | Irrational-multiple all-word theorem | [Mahler (1973), Theorem 2](https://doi.org/10.1017/S000497270004243X) proves that for every irrational \(\alpha\) and word length \(m\), some integer \(X_m\) makes \(X_m\alpha\) contain every length-\(m\) word infinitely often; his printed base-ten construction permits \(X_m<10^{2\cdot10^m+2m-1}\).  [Berend--Boshernitzan (1994), Theorem 1.1](https://doi.org/10.4064/aa-66-4-315-322) improves the multiplier for one length-\(k\) block to \(X<2\cdot10^{k+1}\), optimal in order.  Applying it to a linearized decimal de-Bruijn word improves the common all-length-\(m\)-word bound to \(X_m<2\cdot10^{10^m+m}\), still dependent on \(m\), not forced to be 1 or a repunit, and far too large for a reverse finite-carry transfer to the digit language of \(\pi\). |
| 2026-08-13 | BBP fibre matching and nonsingularity search | Fine continuity-set partitions show that positive-mass fixed-congestion matching is exactly non-mutual-singularity of the two empirical limits, and density-one matching is exactly finite domination.  In the ergodic BBP setting both are equivalent to the missing equality \((T_{16})_*\mu=\mu\).  [Blanchard--Host--Maass](https://doi.org/10.5802/jtnb.165) supplies finite transducer context but no invariant-measure lift, and [Badea--Grivaux, arXiv:2303.01089v3](https://arxiv.org/abs/2303.01089v3) does not specialize to the fixed pi phase.  No source found establishes the required overlap, domination, or support inclusion. |
| 2026-08-13 | Fresh BBP-normality status check | The primary [Barsky--Muñoz--Pérez-Marco paper](https://doi.org/10.4064/aa200619-28-9) derives and classifies BBP formulas but says the normality program still depends on Bailey--Crandall's unproved Hypothesis A; it contains no fixed-pi return theorem.  The 2026 [Chen--Ye--Zheng paper](https://arxiv.org/abs/2604.14036) proves infinite limit sets and amplitude/spread bounds for applicable linear recurrent sequences, not density of the decimal pi orbit.  No source located in the refreshed search supplies the all-color shrinking returns characterized in (40ca)--(40ck). |
| 2026-08-12 | Fresh fixed-number complexity search | [Bugeaud--Kaneko--Kim, arXiv:2510.17177v3](https://arxiv.org/abs/2510.17177) and [Bugeaud--Kim, arXiv:2510.02059v2](https://arxiv.org/abs/2510.02059) give only linear complexity bounds under irrationality-exponent hypotheses near 2. The known bound for \(\pi\) is too weak, and even their conclusions are exponentially below \(10^m\) coverage. |
| 2026-08-12 | Fresh power-orbit and S-unit search | [Stephan, arXiv:2607.11648v3](https://arxiv.org/abs/2607.11648) proves superlinear complexity for a related autonomous \((3/2)^n\) steering word while explicitly leaving density open; [Stephan, arXiv:2607.14774v2](https://arxiv.org/abs/2607.14774) gives weak finite binary complexity for powers of three. The fixed-group/autonomous hypotheses do not match the moving Machin denominators. The audited S-unit finiteness results are not interval-distribution theorems. |
| 2026-08-12 | Fresh Machin and empirical-\(\pi\) search | [Farhi, arXiv:2601.10300v1](https://arxiv.org/abs/2601.10300) refines Machin-like identities but proves no numerator-residue distribution. [Razeto--Rossi, arXiv:2608.06438v1](https://arxiv.org/abs/2608.06438) and [Roba--Podnieks, arXiv:2504.10394v1](https://arxiv.org/abs/2504.10394) are finite statistical studies and explicitly do not prove normality. |
| 2026-08-12 | Short exponential sums for the T45 pulse | The primary fixed-prime and subgroup estimates located, including [Kerr](https://arxiv.org/abs/1302.4170), require a pure projection and/or an orbit or subgroup polynomially large in the modulus. T45's full fixed composite modulus has only \(T\asymp\log Q\) useful iterates and a large nonunit 5-primary component, so no located theorem applies. |
| 2026-08-10 | Current-status search for “pi disjunctive every finite digit string proof” | A 2024 exposition states that disjunctivity of \(\pi\) is unknown and that finite testing cannot settle it: [Scientific American, 2024-03-14](https://www.scientificamerican.com/article/does-pi-contain-all-of-shakespeare/). The 2026 conclusion here is only that the bounded search found no proof. |
| 2026-08-10 | Definition and implication audit | Hertling gives the standard disjunctive-word/real-number framework: [J.UCS 2(7), 1996](https://doi.org/10.3217/jucs-002-07-0549). |
| 2026-08-10 | Normality and empirical-statistics search | Bailey et al. report finite statistical evidence, not normality: [Experimental Mathematics 21(4), 2012](https://doi.org/10.1080/10586458.2012.665333). |
| 2026-08-10 | Decimal digit statistics | Trueb's first 22.4 trillion decimal digits are consistent with normality for blocks of lengths 1–3, still only `experiment`: [arXiv:1612.00489](https://arxiv.org/abs/1612.00489). |
| 2026-08-10 | Irrationality measure of \(\pi\) | Zeilberger–Zudilin prove \(\mu(\pi)\le7.103205334137\ldots\): [paper and journal metadata](https://arxiv.org/abs/1912.06345), [journal DOI](https://doi.org/10.2140/moscow.2020.9.407). |
| 2026-08-10 | Restricted irrationality and factor complexity | Bugeaud--Kim's 2026 revision relates low word complexity to rational approximants whose denominators have repetition form: [arXiv:2510.02059v2](https://arxiv.org/abs/2510.02059v2). The local decimal \(\nu_{10}\) replay and its \(2.246979\ldots\) liminf threshold are a `proof sketch`, not a theorem stated for that restricted exponent and not an estimate proved for \(\pi\). Their separate limsup bound is nontrivial only below \(2.324717\ldots\). |
| 2026-08-10 | Distinct 2026 complexity bound | Bugeaud--Kaneko--Kim prove \(\mu(\xi)=2\Rightarrow\limsup p(\xi,b,n)/n\ge4/3\); for \(\mu>2\), their displayed gain is nontrivial only for \(\mu<11/5\): [arXiv:2510.17177v3](https://arxiv.org/abs/2510.17177v3). This is distinct from the Bugeaud--Kim thresholds above, and all of them lie far below the known \(7.103205\ldots\) upper bound for \(\pi\). |
| 2026-08-10 | Word-complexity baseline | Bugeaud–Kim state the Morse–Hedlund baseline used locally: [arXiv:1510.00279v3](https://arxiv.org/abs/1510.00279v3), [journal DOI](https://doi.org/10.1090/tran/7378). |
| 2026-08-10 | Fixed-power binary aperiodicity | Stephan uses Baker--Wüstholz estimates to prove period breaks for low binary digits of each fixed power \(3^m\), and obtains only the Morse--Hedlund floor \(p(n)\ge n+1\): [arXiv:2607.14774v2](https://arxiv.org/abs/2607.14774). The argument concerns a fixed \(S\)-unit, not the changing twelve-term Machin numerator, and supplies no decimal prescribed-word theorem for \(\pi\). |
| 2026-08-10 | Recurrent-factor complexity | Perrin's Proposition 8.14 states that a one-sided infinite word is ultimately periodic exactly when its recurrent-factor count is at most \(m\) at some length \(m\): [*Finite Automata*, 1990, p. 42](https://api.pageplace.de/preview/DT0400.9780080933924_A25089992/preview-9780080933924_A25089992.pdf). Its contraposition is the generic theorem formalized in T31, so no novelty is claimed. |
| 2026-08-10 | Sharp decimal recurrent language with \(\mu=2\) | For \(\kappa_{10}=\sum_{j\ge0}10^{-2^j}\), Shallit proves that its continued-fraction partial quotients belong to the finite set \(\{8,9,10,12\}\) after the initial zero, so \(\mu(\kappa_{10})=2\): [Theorems 8--9, journal p. 215](https://cs.uwaterloo.ca/~shallit/Papers/scf.pdf), [DOI](https://doi.org/10.1016/0022-314X(79)90040-4). The exact recurrent-language calculation below is an elementary local `proof sketch`, not a claim from Shallit's paper. |
| 2026-08-10 | Transcendence of the sharp separator | Adamczewski's Mahler-method proof shows that \(f(\alpha)=\sum_{j\ge0}\alpha^{2^j}\) is transcendental for every nonzero algebraic \(\alpha\) in the open unit disk; \(\alpha=1/10\) gives \(\kappa_{10}\): [Section 2, author PDF](https://adamczewski.perso.math.cnrs.fr/Kempner.pdf), SHA-256 `dae6b4a33b30114fa529e1eba9ab58cfde1c30154681b2ddfe209fb8bc6d2e1f`. Thus the exact T33 language is, up to one initial zero and rational scaling, also a transcendental-number separator; that elementary identification is a local `proof sketch`, not a Lean premise. |
| 2026-08-10 | Complexity in multiplicatively independent bases | Bugeaud--Kim, Theorem 1.3, prove for irrational \(\xi\) and multiplicatively independent bases \(r,s\) that \(p_r(\xi,n)+p_s(\xi,n)-2n\to\infty\): [primary journal DOI](https://doi.org/10.5802/aif.3134).  Applied to \(\pi\), bases 10 and 16 cannot both remain quasi-Sturmian; the theorem does not identify which side supplies the excess, and BBP gives no bound forcing it onto the decimal side. |
| 2026-08-10 | Stronger digit-change/complexity theorems | Bugeaud--Evertse's improved bounds apply to irrational algebraic numbers ([arXiv:0709.1560](https://arxiv.org/abs/0709.1560)); Adamczewski's exponential-period bound assumes irrationality exponent exactly two ([arXiv:1205.0961](https://arxiv.org/abs/1205.0961)). Neither hypothesis is known to apply to \(\pi\). |
| 2026-08-10 | Stoneham stable rational approximants | Stoneham's 1983 paper explicitly cannot place even `0123456789` inside the prefix stabilized to \(\pi/4\); its stable length is scale-incompatible with the cited periodic normality estimate: [DOI](https://doi.org/10.4064/aa-42-3-265-279), [primary PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa42/aa4233.pdf). |
| 2026-08-10 | BBP, conditional dynamics, and base transfer | BBP gives hexadecimal digit extraction, not a distribution theorem: [BBP DOI](https://doi.org/10.1090/S0025-5718-97-00856-9). Bailey–Crandall's normality route depends on an unproved hypothesis: [DOI](https://doi.org/10.1080/10586458.2002.10504704). Schmidt's theorem supplies counterexamples to transfer between multiplicatively independent bases: [DOI](https://doi.org/10.2140/pjm.1960.10.661). |
| 2026-08-10 | Exact unconditional BBP dynamical floor | Lagarias proves that the perturbed-remainder sequence attached to an irrational BBP-type constant has infinitely many limit points; density requires the unproved Weak Dichotomy Hypothesis. His digit-density equivalence is base-specific, so even the conditional base-16 conclusion would not establish decimal V1: [primary preprint](https://arxiv.org/abs/math/0101055). |
| 2026-08-10 | Nondecimal Machin-type extraction exclusion | Borwein--Borwein--Galway exclude Machin-type BBP formulas for \(\pi\) in bases that are not powers of two, hence in base 10: [primary journal page](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/finding-and-excluding-bary-machintype-individual-digit-formulae/BB7919C8E1AE66878AE8D7BC7F0EBFA3). This narrow 2004 impossibility theorem does not exclude every conceivable decimal extraction formula. |
| 2026-08-10 | Entropy-transfer applicability | Host-type and Lindenstrauss--Meiri--Peres dilation results act on invariant measures and require positive entropy or almost-everywhere genericity: [primary preprint](https://arxiv.org/abs/math/9905213). They provide no route from the single point \(\pi\), without a fixed-\(\pi\) entropy premise, to decimal orbit density. |
| 2026-08-10 | BBP zero relations | Bailey's 2023 compendium records the base-16 zero relation used in the non-Gosper separator, but describes such relations as PSLQ-discovered and numerically checked: [official PDF, formula (111)](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf). The exact partial-fraction integral displayed below supplies the proof needed here. |
| 2026-08-10 | Linear-recurrence limit sets | Chen--Ye--Zheng's April 2026 Theorems 1.1 and 1.3 apply to \(\pi10^n\): its omega-limit set is infinite, \(\limsup\|10^n\pi\|\ge1/11\), and at every arithmetic sampling scale one residue-class omega-limit set cannot fit in a circle arc shorter than \(1/10\). They do not give density or hit a prescribed arc: [arXiv:2604.14036v1](https://arxiv.org/abs/2604.14036v1). |
| 2026-08-10 | Latest extraction and lacunary-sum citation trail | Plouffe's decimal \(n\)-th-digit formula is an extraction algorithm, not a recurrence theorem ([arXiv:2201.12601](https://arxiv.org/abs/2201.12601)). Recent lacunary-sum results remain metric or existential rather than pointwise at \(\pi\): [Aistleitner et al., 2025](https://arxiv.org/abs/2502.20930), [Stefanescu, 2024](https://arxiv.org/abs/2406.19802), and the [2023 survey](https://arxiv.org/abs/2301.05561). A point mass at \(\pi\) cannot satisfy polynomial Fourier decay because its Fourier transform has modulus one. |
| 2026-08-10 | Exact Machin-recurrence cancellation audit | Metric expanding-map results require a Fourier-decaying measure or an almost-every point and therefore do not specialize to the point mass at \(\pi\) ([Tan--Zhou, 2025](https://arxiv.org/abs/2504.21555)). Fixed-modulus estimates require a pure geometric orbit modulo one prime ([Kerr, 2013](https://arxiv.org/abs/1302.4170)), a polynomial-size complete subgroup ([Di Benedetto et al., 2020](https://arxiv.org/abs/2003.06165); [Untrau, 2024](https://doi.org/10.1017/S0305004123000361)), or a finite-field family/complete sum ([Perret-Gentil, 2020](https://arxiv.org/abs/1703.06965)). The exact T38 stream has one selected residue at each changing composite modulus and a time-dependent forcing, so none of these theorems supplies cancellation. |
| 2026-08-10 | Period, G/E-function, and Mahler applicability | \(\pi\) is a period ([Kontsevich–Zagier](https://doi.org/10.1007/978-3-642-56478-9_39)), but the closest G-function digit theorem gives restricted repetition bounds at sufficiently small rational arguments, not coverage ([Fischler–Rivoal](https://doi.org/10.1007/s00229-017-0933-8)). D-finite finite-alphabet series are rational ([Bell–Chen](https://doi.org/10.1016/j.jcta.2017.05.002)), while standard Mahler-value theorems require algebraic points strictly inside the unit disk ([Adamczewski–Faverjon](https://doi.org/10.1112/plms.12038)). The exact hypothesis mismatch is recorded below. |
| 2026-08-10 | Classical interval-localization provenance | Erdős--Turán's 1948 papers use finite trigonometric-polynomial localization for interval counts: [Part I](https://users.renyi.hu/~p_erdos/1948-02.pdf), [Part II](https://users.renyi.hu/~p_erdos/1948-03.pdf). Related primary sources are [Jackson's 1912 approximation paper](https://doi.org/10.1090/S0002-9947-1912-1500930-2) and [Vaaler's 1985 extremal-functions survey](https://doi.org/10.1090/S0273-0979-1985-15349-2). These establish classical provenance; no novelty or literature-optimality is claimed for T19. |
| 2026-08-10 | Exact normalization/constants search for T19 | The bounded source and keyword search found no statement with the exact local pair \(2q\) and \(1/(24q)+1/(12q^3)\). This is only a negative search result, not evidence of priority. |
| 2026-08-10 | Single-forbidden-word automata and entropy | Guibas--Odlyzko's overlap method underlies exact word-avoidance counts: [1981 DOI](https://doi.org/10.1016/0097-3165(81)90005-4). A modern labeled-graph/Perron--Frobenius treatment is [Chandgotia--Marcus--Richey--Wu, 2026](https://doi.org/10.3934/dcds.2025152). [Staiger, 2002](https://www.jucs.org/jucs_8_2/how_large_is_the/Staiger_L.pdf) records the maximal-complexity characterization of disjunctive words. These sources support the avoidance-language context, not the elementary identity (7a), whose argument is displayed here. |
| 2026-08-10 | Current finite record and word completion data | Guinness reports a 314-trillion-digit record and length-13 coverage: [record entry](https://www.guinnessworldrecords.com/world-records/66179-most-accurate-value-of-pi). OEIS-reported completion positions are in [A080597](https://oeis.org/A080597) and [A032510](https://oeis.org/A032510). |
| 2026-08-01 | Installed mathlib search, recorded in the repository T35 audit | No declarations matching `disjunctive`, `WeylCancellation`, `factorEntropy`, or the omitted-word results were found. `Mathlib/Dynamics/SymbolicDynamics/Basic.lean` supplies general language/cylinder infrastructure only. |

No searched source supplies a proof of V1. A negative search is bounded by its
queries and access date; it is not a theorem that no unpublished proof exists.

## Experiments

### Exact local two-million-digit replay

Label: `experiment`.

- Certifier:
  [`work/theory/.../t17/t16-pi_certify.py`](work/theory/pi-lacunary-near-return-sparsity/library/t17/t16-pi_certify.py).
- Parameter: `fraction_digits=2000000`; no random seed.
- Arithmetic: exact integer Chudnovsky binary splitting, adjacent alternating
  partial-sum bounds, integer square-root enclosure, and singleton-floor
  equality.
- Terms: 142,877 and 142,878 adjacent partial sums.
- `pi_digits.txt` SHA-256, including final LF:
  `fe04c1787c7bfb1e9540ce7aba8e6fde8c1225a863a20f207a4f9412b55cf19e`.
- `certificate.json` SHA-256:
  `c47d10c780b303af4e9805663f89104797d1e0dc06d212d19f689da7371b7620`.
- Scan: deterministic exhaustive first-occurrence table over every overlapping
  substring; no sampling.

| Word length \(k\) | Distinct words seen | First complete fractional prefix | Last new word | T28 cutoff \(L_k\) | \(L_k/p_\pi(k)\) |
|---:|---:|---:|---:|---:|---:|
| 1 | 10 / 10 | 32 | `0` | 32 | 3.20000 |
| 2 | 100 / 100 | 606 | `68` | 605 | 6.05000 |
| 3 | 1,000 / 1,000 | 8,555 | `483` | 8,553 | 8.55300 |
| 4 | 10,000 / 10,000 | 99,849 | `6716` | 99,846 | 9.98460 |
| 5 | 100,000 / 100,000 | 1,369,564 | `33394` | 1,369,560 | 13.69560 |
| 6 | 864,799 / 1,000,000 | not complete at 2,000,000 | — | — | — |

Replay command, writing only to a temporary directory:

```bash
task_tmp=$(mktemp -d /tmp/ultrapi.XXXXXX)
python3 work/theory/pi-lacunary-near-return-sparsity/library/t17/t16-pi_certify.py \
  2000000 "$task_tmp/pi_digits.txt" "$task_tmp/certificate.json"
python3 - "$task_tmp/pi_digits.txt" <<'PY'
from pathlib import Path
import sys

digits = Path(sys.argv[1]).read_text(encoding="ascii").strip()
for k in range(1, 7):
    first = {}
    for i in range(len(digits) - k + 1):
        word = digits[i:i + k]
        first.setdefault(word, i + 1)
        if len(first) == 10**k:
            print(k, i + k, word, i + 1)
            break
    else:
        print(k, len(first), 10**k - len(first))
PY
```

The scan itself records the first index for every slice
`digits[i:i+k]`, for `k=1,...,6`, and stops a row when its dictionary reaches
size \(10^k\). The result agrees with OEIS A080597 for \(k\le5\) after removing
OEIS's initial integer digit `3` from its prefix length.
For completed rows, the one-based start of the last new word is exactly T28's
\(L_k=1+\max_w n(w)\), so the last column is an exact finite replay of the
appearance ratio used by T29. Its growth through \(k=5\) is only
`experiment`: it proves neither that the ratio is bounded nor that it is
unbounded.

### Current external finite coverage

Label: `experiment`.

OEIS A080597 reports that the first 294,420,436,740,326 digits when the initial
integer digit `3` is counted contain every 13-digit word. In canonical
fractional indexing, all 13-words have therefore appeared by fractional digit
294,420,436,740,325. OEIS A032510 reports the last new word as
`8683109988379`, beginning at fractional position 294,420,436,740,313. The
\(n=12,13\) extensions are credited there to Michael Kleber on 2026-04-13.
Guinness's entry reports that the 314-trillion-digit record was achieved on
2025-11-18 and also reports the length-13 coverage finding; it was accessed on
2026-08-10 and is not treated here as an independent verification of OEIS.

These finite facts have zero resolution leverage for V1. A length-14 word may
be absent from the computed prefix yet occur later, and some finite word may
be absent from \(\pi\) forever; finite computation distinguishes neither
possibility.

## Candidate approaches

1. **Attack the exact natural-scale condition (9).** Any proposed identity for
   \(\pi\) must be audited against the exact frequency range, orbit length,
   reduced modulus, multiplicative order of 10, and truncation error.
2. **Constrain sparse samples before estimating their energy.** A prescribed
   arithmetic schedule, a location bound, or a sampling rule independent of
   block values could make (5) informative. Unrestricted existential samples
   are retired by (7a).
3. **Seek a positive-definite Walsh/Fourier bridge.** Equal decimal-block
   energy is nonnegative and exposes multiplicity; a uniform bridge to the
   natural Fourier range could connect (5) and (9) without signed-cancellation
   bookkeeping.
4. **Do not treat more digit computation as an asymptotic route.** Computation
   is useful for falsifying proposed finite bounds and validating certificates,
   not for proving V1.

Rejected or currently inadequate routes are ordinary irrationality measure,
transcendence alone, generic almost-everywhere results, base-16 digit
extraction, phase-blind multiplier-10 telescoping, and currently audited
rational representations whose reduced moduli leave a square-root barrier
larger than the available orbit length.

## Complete-proof continuation audit: exact new obstructions

The status in this section is deliberately split. The cited source statements
were checked in a bounded search on 2026-08-10 and are
`literature-checked`. The elementary deductions below are `proof sketch`
unless a Lean theorem is named explicitly. None proves V1.

### The enlarged Furstenberg orbit does not yield the diagonal

Furstenberg's non-lacunary semigroup theorem gives the unconditional result

\[
  \{2^m5^n\pi:m,n\ge0\}\pmod 1
  \quad\text{is dense}. \tag{10}
\]

Here \(2\) and \(5\) are multiplicatively independent and \(\pi\) is
irrational. The target orbit, however, is only the diagonal \(m=n\). This is
not a removable technicality: Furstenberg states immediately after the
theorem that the conclusion fails for one-generator lacunary semigroups.

There is also an exact obstruction to a compactness/entropy diagonal
extraction. Let

\[
  T(x)=10x\pmod1,\qquad
  X_\alpha=\overline{\{T^n\alpha:n\ge0\}}.
\]

For every irrational \(\alpha\), the countable image family already satisfies

\[
  \overline{\bigcup_{m\ge0}2^mX_\alpha}=\mathbb R/\mathbb Z. \tag{11}
\]

Indeed, the union contains every \(2^m10^n\alpha\), and the semigroup
generated by \(2\) and \(10\) is non-lacunary. On the other hand, take

\[
  \alpha_F=\sum_{r\ge1}10^{-r!}.
\]

Its decimal word uses only 0 and 1, and its diagonal orbit closure has zero
entropy (a direct block count gives
\(p_{\alpha_F}(L)\le3L+1\)). Yet (11) says that the countable union of its
dilated zero-entropy images is dense. Thus two-parameter density, entropy
monotonicity under integer multiplication, and compactness do not pull
density back to \(X_\alpha\). A successful use of (10) needs genuinely
\(\pi\)-specific input absent from this example.

Schmidt's theorem gives a stronger separator.  On the Cantor set of numbers
whose decimal digits lie in \(\{0,\ldots,8\}\), almost every point for the
natural product measure is normal to every fixed base multiplicatively
independent of 10, with Schmidt's power-saving interval-discrepancy estimate.
Removing the countable algebraic points and intersecting
the full-measure sets for bases \(2,5,16,625\) produces a transcendental
\(\alpha\) that is normal in all four bases and has dense full
\(\times2,\times5\) semigroup orbit, yet its decimal orbit never enters
\([0.9,1)\).  The deduction is a `proof sketch` from the
`literature-checked` source theorem.  T19 then forces, for every positive
\(N\), some \(0<|h|\le20\) with

\[
 {|S_N(h;\alpha)|\over N}\ge {1\over240}+{1\over12000}.
\]

Thus even both generator marginals, full semigroup density, and base-16
normality together do not imply decimal disjunctivity or the T19 premise.
The exact base-conversion mismatch is

\[
 10^{4n}=16^n625^n,qquad
 S_{4M}(h)=\sum_{r=0}^3\sum_{n<M}
 e^{2\pi i h10^r625^n16^n\pi}.
\]

Base-16 normality controls fixed frequencies along \(16^n\pi\), whereas the
decimal sum contains the moving frequencies \(h10^r625^n\).  The Schmidt
separator proves that this mismatch cannot be repaired by an abstract
base-normality transfer.

Primary sources: [Furstenberg, 1967, Theorem IV.1](https://doi.org/10.1007/BF01692494)
and the [primary PDF](https://www.math.ucsd.edu/~asalehig/F_Disjointness.pdf).
The related positive-entropy dilation phenomenon is recorded by
[Lindenstrauss--Meiri--Peres, 1999](https://doi.org/10.2307/121075), and the
missing-digit normality separator uses
[Schmidt, 1960, Theorem 2](https://doi.org/10.2140/pjm.1960.10.661).

### BBP reweighting gives an exact rational recurrence, not density

The seemingly weaker request that the decimal orbit closure

\[
 X_\alpha=\overline{\{10^n\alpha\bmod1:n\ge0\}}
\]

be forward invariant under multiplication by 16 is already exact. For every
irrational \(\alpha\), write \(\|x\|\) for distance to the nearest integer.
Commutation and closedness give

\[
 16\alpha\in X_\alpha
 \iff16X_\alpha\subseteq X_\alpha
 \iff\liminf_n\|(10^n-16)\alpha\|=0. \tag{11a}
\]

For \(\alpha=\pi\), Furstenberg's theorem for the nonlacunary semigroup
\(\langle10,16\rangle\) makes these conditions equivalent to
\(X_\pi=\mathbb R/\mathbb Z\), hence to V1. Thus proving even that the single
point \(16\pi\) is a decimal-orbit limit point is not a weaker shortcut.

The BBP formula nevertheless gives a useful fixed-\(\pi\) arithmetic
reduction. Put

\[
 c_k={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 A_N=\sum_{k=0}^N{c_k\over16^k}.
\]

Positivity and the elementary BBP tail estimate give

\[
 0<\pi-A_N\le {16^{-N}\over15(N+1)^2},\qquad
 \left|\|(10^N-16)\pi\|-\|(10^N-16)A_N\|\right|
 \le{(5/8)^N\over15(N+1)^2}. \tag{11b}
\]

Consequently V1 is equivalent to the explicit rational diagonal condition

\[
 \liminf_N\|(10^N-16)A_N\|=0. \tag{11c}
\]

Equivalently, the rational sequence

\[
 u_N=\{10^NA_N\},\qquad
 u_{N+1}=\{10u_N+c_{N+1}(5/8)^{N+1}\}
\]

shadows \(\{10^N\pi\}\) with the error in (11b). More precisely, if
\(\omega(u)\) and \(\omega_{10}(\pi)\) denote the respective sets of
accumulation points, then

\[
 \omega(u)=\omega_{10}(\pi). \tag{11d}
\]

This is the exact conclusion of the perturbed-remainder calculation in
Lagarias's Theorem 3.1: here its tail is
\(t_N=10^N(\pi-A_N)\to0\), so
\(\{10^N\pi\}=\{u_N+t_N\}\). It is important not to replace (11d) by
equality of the two *full* orbit closures, since finitely many early rational
values \(u_N\) may contribute points not present in the other closure.
Lagarias's Theorem 3.3 and the irrationality of \(\pi\) do show that this
common omega-limit set is infinite: a finite limit-point set would be
equivalent to rationality. That is a fixed-\(\pi\) conclusion, but it is much
weaker than density. For the present target the distinction between full
closure and omega-limit is harmless: \(\{16\pi\}\) cannot equal any single
\(\{10^N\pi\}\), since that would make \((10^N-16)\pi\) an integer.
Thus (11a) asks whether \(\{16\pi\}\in\omega(u)\), and no audited theorem
establishes that membership.

There are now two sharper finite-cell transfers, neither of which supplies
that missing density.  Fix \(q=10^m\), put
\(X_N=\lfloor q\{10^N\pi\}\rfloor\) and
\(U_N=\lfloor q u_N\rfloor\).  Since the positive shadowing error is
eventually smaller than \(1/q\), one has
\(X_N=U_N\) or \(X_N=U_N+1\pmod q\).  T34 machine-checks the exact abstract
combinatorics: recurrent source values inject into recurrent target values
times a two-element branch type.  For \(m\ge1\), together with T31 this
conditionally gives at least \(\lceil(m+1)/2\rceil\) recurrent cells for the rational diagonal
stream.  The Lean theorem keeps the eventual two-lift relation explicit; the
elementary specialization to the actual \(A_N\) tail is a `proof sketch`.

Oversampling removes even this factor-two boundary loss.  The
`literature-checked` bound \(\mu(\pi)<8\) gives an onset \(A\) such that

\[
 {1\over10^{8t}}\le
 \left|\pi-{p\over10^t}\right|
 \quad(t\ge A,\ p\in\mathbb Z).
\]

On the other hand \(16^7>10^8\), so for every fixed \(m\), eventually
\(16^{7N}>10^{8(N+m)}\).  The positive BBP tail is then too short to cross
any decimal boundary of denominator \(10^{N+m}\).  Hence

\[
 \left\lfloor10^m\{10^N A_{7N}\}\right\rfloor
 =\left\lfloor10^m\{10^N\pi\}\right\rfloor
 \qquad(N\ge N_0(m)). \tag{11o}
\]

T35 machine-checks equality of the arithmetic floor codes, the floor-crossing
lemma, the eventual power inequality, and the exact quantifier conversion
from its explicit source-level irrationality premise.  Its approximation sequence is deliberately abstract:
the actual BBP identity, positivity, and tail estimate are not definitions or
proved premises in that Lean file.  T37 separately registers the elementary
bridge from this floor code to `piDigit`/`piCylinderCode`.  Thus (11o) for the displayed \(A_K\) is a
`proof sketch` assembled from a `machine-checked` conditional interface and
`literature-checked`/elementary external inputs, not an unconditional Lean
theorem about BBP truncations.

The oversampled rational values still obey an exact seven-term recurrence.
Writing \(v_N=\{10^N A_{7N}\}\),

\[
 v_{N+1}=\left\{10v_N+\eta_{N+1}\right\},\qquad
 \eta_{N+1}=10^{N+1}\sum_{j=1}^{7}{c_{7N+j}\over16^{7N+j}}. \tag{11p}
\]

If \(e_N=10^N(\pi-A_{7N})\), then
\(\eta_{N+1}=10e_N-e_{N+1}\) and
\(\{v_N+e_N\}=\{10^N\pi\}\).  Thus oversampling gives an exact rational
coding of every fixed recurrent decimal cell, but the recurrence remains a
time-dependent coboundary of the original orbit.  Proving that its cells are
dense is still V1 in different coordinates.

T36 removes the unformalized BBP-tail obligation by using a different,
fully explicit rational approximation.  Let

\[
 R_q(L)=\sum_{0\le j<L}{(-1)^j\over(2j+1)q^{2j+1}},\qquad
 M_K=16R_5(2K+2)-4R_{239}(2K+3)\in\mathbb Q.
\]

Mathlib's arctangent power series and Machin identity give, with the parity
chosen above, a one-sided lower approximation.  T36 machine-checks
the finite rational definitions, two-term partial-sum recurrence, exact
Machin recurrence, and the uniform estimate

\[
 0\le\pi-M_K<{1\over625^K}. \tag{11q}
\]

Because \(625^3=244140625>10^8\), triple rather than sevenfold sampling now
suffices.  With
\(B_m(x,N)=\lfloor10^{N+m}x\rfloor-10^m\lfloor10^Nx\rfloor\), T36 proves

\[
 B_m(M_{3N},N)=B_m(\pi,N)
 \qquad(N\ge N_0(m)), \tag{11r}
\]

conditional only on the explicit source-level proposition
`IrrationalityMeasureBelow Real.pi 8`.  The published theorem supplying that
proposition is not reproved in Lean, but all rational-series, sign, error,
scale, and floor-crossing steps are `machine-checked`; the full 8,493-job
kernel, exploit, and exact-axiom gate passes.

T37 now closes the arithmetic/symbolic representation gap without changing
the hypothesis.  For every real \(x\), every \(N,m\ge0\), including negative
\(x\) and \(m=0\), it machine-checks the half-open-cell identity

\[
 B_m(x,N)=\left\lfloor10^m\{10^Nx\}\right\rfloor. \tag{11s}
\]

For \(x=\pi\), this integer is exactly `(piCylinderCode m N).val` and exactly
the numerical value of the contiguous word `blockAt piDigit m N`.  Combining
this identity with (11r), T37 defines the explicit `Fin (10^m)`-valued Machin
stream and proves that, under the same source-level \(\mu(\pi)<8\) premise, it
is eventually equal term-for-term to the symbolic \(\pi\)-cylinder stream.
An independent automated audit checked negative inputs, terminating rational
endpoints, length zero, zero-based indexing, and the explicit premise; all
T37 declarations use only the exact allowed axiom set.

T38 makes the resulting rational dynamics exact and identifies its precise
asymptotic Fourier relation to the \(\pi\) orbit.  Put

\[
 v_N=\{10^NM_{3N}\},\qquad
 s_N=10^N(\pi-M_{3N}),\qquad
 \Delta_N=10^{N+1}(M_{3N+3}-M_{3N}),
 \quad \rho={10\over625^3}.
\]

The Machin approximants are strictly increasing, so \(\Delta_N\) is a
positive rational.  T38 machine-checks the exact recurrence and coboundary

\[
 v_{N+1}=\{10v_N+\Delta_N\},\qquad
 \Delta_N=10s_N-s_{N+1},\qquad
 \{v_N+s_N\}=\{10^N\pi\}, \tag{11t}
\]

together with \(0\le s_N<\rho^N\).  Consequently, if \(S_L^\pi(h)\) and
\(S_L^v(h)\) are the unnormalized integer-frequency exponential sums of the
two orbits, then for every \(L\ge0\) and \(h\in\mathbb Z\),

\[
 \left|S_L^\pi(h)-S_L^v(h)\right|
 \le {2\pi |h|\over1-\rho}. \tag{11u}
\]

The right side is independent of \(L\).  After division by \(L\), the
difference tends to zero, and T38 proves the exact equivalence

\[
 \operatorname{WeylCancel}(v)
 \quad\Longleftrightarrow\quad
 \operatorname{WeylCancel}(\{10^N\pi\}). \tag{11v}
\]

Thus the explicit rational recurrence is not a new randomizing input: its
forcing is a summable coboundary removable by the moving translation
\(v_N\mapsto\{v_N+s_N\}\).  Any fixed-frequency cancellation proof for it
would prove the corresponding currently open fixed-\(\pi\) estimate.  A
dated theorem-by-theorem audit found no applicable varying-denominator or
finite-field estimate: the available results require a random/almost-every
parameter, many residues at one fixed modulus, a polynomial-size subgroup,
or a pure fixed-prime geometric orbit, whereas this sequence supplies one
selected residue at each changing composite modulus.

The remaining arithmetic datum can nevertheless be exposed locally and
exactly.  T40 machine-checks the six-new-terms from each arctangent series,
including their signs and indices.  If \(a_j=12N+5+2j\), the resulting
rational identity is

\[
 \Delta_N=10^{N+1}\sum_{j=0}^{5}(-1)^j
 \left({16\over a_j5^{a_j}}+{4\over a_{j+1}239^{a_{j+1}}}\right). \tag{11w}
\]

T40 also regroups (11w) into three strictly positive adjacent pairs for each
base.  For a pair with odd exponents \(r,r+2\), it machine-checks

\[
 r(r+2)q^{r+2}
 \left({1\over rq^r}-{1\over(r+2)q^{r+2}}\right)
 =q^2(r+2)-r,
\]

and proves that the integer on the right is exactly twice an odd integer for
both \(q=5\) and \(q=239\).  This is pairwise local information; cancellation
between the six positive Machin pairs remains uncontrolled.

The following further nested-grid reduction remains a `proof sketch`, with
its signs and indices independently replayed by exact-rational computation.
Put

\[
 P_N=\prod_{r=0}^{6N+2}(2r+1),\quad
 Q_N=5^{12N+3}239^{12N+5}P_N,\quad D_N=Q_N/5^N,
\]

write \(M_{3N}=H_N/Q_N\) by clearing the displayed Taylor denominators, and
let \(b_N\) be the least nonnegative residue of \(2^NH_N\) modulo \(D_N\).
Then

\[
 v_N={b_N\over D_N},\qquad
 D_{N+1}=g_ND_N,qquad
 b_{N+1}\equiv10g_Nb_N+C_N\pmod {D_{N+1}}, \tag{11x}
\]

where
\(g_N=5^{11}239^{12}\prod_{j=0}^{5}(12N+7+2j)\) and
\(C_N=D_{N+1}\Delta_N\in\mathbb Z\).  This converts the last positive route
into one moving composite-modulus numerator problem.  It does not create an
ensemble over which a complete-sum estimate could average.

The product grid is deliberately loose.  From (11w), if
\(L_N=\operatorname{lcm}(12N+5,12N+7,\ldots,12N+17)\), the reduced forcing
denominator satisfies the sharper elementary divisibility

\[
 \operatorname{den}(\Delta_N)\mid
 5^{11N+14}239^{12N+17}L_N. \tag{11y}
\]

T42 machine-checks the foundations of the first valuation calculation.  Each
three-positive-pair block at base 5 or base 239 has exact two-adic order one,
and the even- and odd-indexed six-term Taylor windows are exactly the positive
or negative of such a block. T44 now machine-checks their differently weighted
combination and the outer power of ten, including the literal reduced-form
bridges. Let
\(\Lambda_N\) be the least common denominator of the twelve individually
reduced terms in (11w):

\[
 \Lambda_N=\operatorname{lcm}_{0\le j<6}\left(
 a_j5^{a_j-N-1},
 {a_{j+1}239^{a_{j+1}}\over\gcd(a_{j+1},5^{N+1})}\right).
\]

The pairwise numerator identity and twice-an-odd certificate used here are
supplied by T40. Tracking their combination and the outer factor
\(4\cdot10^{N+1}\) now gives, at `machine-checked` status for the first law,

\[
 v_2(\operatorname{num}\Delta_N)=N+4,
 \qquad
 v_3\!\left({\Lambda_N\over\operatorname{den}\Delta_N}\right)=1. \tag{11z}
\]

The second identity remains a `proof sketch`; it follows after regrouping the
shared interior indices and
using \(239\equiv5\pmod9\) at odd exponents.  These laws show that substantial
2-adic and one exact 3-adic component are rigid; they still do not control the
archimedean residue \(b_N/D_N\).

T43 closes the tempting inference from the first of these invariants.  It
machine-checks the artificial choice

\[
 \rho={2\over5^{11}},\qquad s_N={1\over2}\rho^N,\qquad
 \varepsilon_N=10s_N-s_{N+1}
 ={2^{N+4}\,15258789\over5^{11(N+1)}}. \tag{11ac}
\]

The forcing is positive, geometric, and summable, and the displayed numerator
has exact two-adic order \(N+4\).  Nevertheless the exact forced orbit
\(v_N=\{10^N/3-s_N\}\) satisfies
\(v_{N+1}=\{10v_N+\varepsilon_N\}\), tends to \(1/3\), and eventually avoids
the first decimal cell \([0,1/10)\).  This separator is not the Machin
forcing; it proves only that positivity, decay, summability, and the global
two-adic profile cannot by themselves yield recurrence.

A stronger nested-grid separator was obtained at the stop point and remains a
`proof sketch`.  Put
\(\kappa_{10}=\sum_{j\ge0}10^{-2^j}\) and
\(\alpha=1/9+\kappa_{10}\).  Its non-eventually-periodic decimal uses only the
digits 1 and 2, so \(x_N=\{10^N\alpha\}\in[1/9,2/9]\).  Use the same loose
product grids as in (11x), set \(G_N=Q_{N+1}/Q_N\), and choose residue classes
recursively by

\[
 r_{N+1}\equiv G_Nr_N+120\pmod {144}.
\]

In each class one may choose \(m_N\equiv r_N\pmod {144}\) so that, for
\(a_N=m_N/Q_N\),

\[
 {144\over Q_N}<e_N:=\alpha-a_N<{288\over Q_N}. \tag{11ad}
\]

The open interval contains the required residue-class grid point because its
length is one grid spacing and \(\alpha\) is irrational.  Since \(G_N>2\),
the errors strictly decrease and the \(a_N\) strictly increase.  With
\(s_N=10^Ne_N\) and
\(\Delta_N=10^{N+1}(a_{N+1}-a_N)=10s_N-s_{N+1}\), the exact bounds and
congruences are

\[
 0<s_N<{\rho^N\over1000},\qquad
 0<{\Delta_{N+1}\over\Delta_N}
   <{20\over G_N-2}<\rho,\qquad
 A_N:=m_{N+1}-G_Nm_N\equiv120\pmod {144}. \tag{11ae}
\]

Hence \(v_2(A_N)=3\), \(v_3(A_N)=1\), and, because \(Q_{N+1}\) is odd, the
reduced numerator of
\(\Delta_N=10^{N+1}A_N/Q_{N+1}\) has exact two-adic order \(N+4\); exactly one
factor 3 cancels from this displayed product-grid denominator.  Furthermore,
if \(b_N\equiv2^Nm_N\pmod {D_N}\), then

\[
 C_N=D_{N+1}\Delta_N=2^{N+1}A_N,\qquad
 b_{N+1}\equiv10g_Nb_N+C_N\pmod {D_{N+1}}.
\]

But \(s_N<1/1000\) prevents fractional-part wrap, so
\(\{10^Na_N\}=x_N-s_N<2/9\) for every \(N\); the decimal cell
\([3/10,4/10)\) is never visited.  Thus even nested 5/239/product grids,
positive geometric forcing, the exact moving-modulus recurrence, the
two-adic profile, and one 3-adic cancellation do not force coverage.  This
construction uses the deliberately loose \(Q_N\), not the actual Machin
approximants or the exact term LCD \(\Lambda_N\).  The actual twelve-term
numerator formula (11w) is therefore the remaining arithmetic information
specific to this route.

That information has now yielded one exact local theorem. For an interior
slot

\[
 p=12N+5+2k,\qquad k\in\{1,3,4\},
\]

with \(p>12\) prime and \(p\ne239\), the two terms whose linear denominator
is \(p\) combine over the numerator

\[
 4(-1)^k(4\cdot239^p-5^p).
\]

Fermat's theorem reduces the parenthesis modulo \(p\) to
\(4\cdot239-5=951=3\cdot317\). The slot congruences exclude 317, every other
term is \(p\)-integral, and T45 therefore machine-checks

\[
 \boxed{v_p(\Delta_N)=-1.} \tag{11af}
\]

Thus each such prime occurs exactly once in the reduced denominator of the
*actual* forcing.

T47 removes the remaining prime-slot qualification. It proves the left and
right endpoint valuations separately, proves the exceptional identity

\[
 v_{239}(\Delta_{19})=-245,
\]

and uses the four possible prime residues modulo 12 to machine-check

\[
 \boxed{\forall p>12\text{ prime}\;\exists N:\quad
 p\mid\operatorname{den}(\Delta_N).} \tag{11af$^\ast$}
\]

For \(p\ne239\) the selected forcing has valuation \(-1\); the displayed
239 valuation is the sole exceptional exponent in this routing. This is a
universal prime-survival law for the actual rational forcing, not an
archimedean distribution theorem.

The natural unreduced common numerator has the separate
`proof sketch` form

\[
 A_N=(239^{12})^N P_6(N)+(5^{12})^N Q_6(N),
 \qquad
 (E-239^{12})^7(E-5^{12})^7A=0, \tag{11ag}
\]

for explicit integer polynomials \(P_6,Q_6\) of degree six. This recurrence
is destroyed by division by the moving common denominator, so it is not a
recurrence for the rational orbit itself.

There is nevertheless a long exact prime projection. If
\(y_n=10^nM_{3n}\), then for such a fresh interior prime

\[
 py_{N+1+t}\equiv10^t c_{N,p}\pmod p,\qquad c_{N,p}\ne0, \tag{11ah}
\]

for \(0\le t\le2N\) when \(k=1\), and for \(0\le t\le2N+1\) when
\(k=3,4\). This pulse statement is currently a `proof sketch`; T45 proves its
load-bearing initial noncancellation exactly.

An adversarial correction is essential here. Unrolling T38 does **not** leave
arbitrary changing CRT weights. For every start \(n\),

\[
 y_{n+t}=10^ty_n+R_{n,t},\qquad
 R_{n,t}=10^ts_n-s_{n+t},\qquad
 0\le R_{n,t}<10^t\rho^n,\quad \rho={10\over625^3}. \tag{11ai}
\]

The entire pulse is therefore exponentially close to powers of one fixed
rational seed and one fixed composite denominator. This is a genuine
sharpening of the obstruction, but the available incomplete exponential-sum
theorems require an orbit or subgroup polynomially large in the modulus;
here the useful pulse has only \(T\asymp N\asymp\log Q\) terms.

T46 machine-checks this correction over the explicit rationals. It defines
the accumulated weighted forcing, proves its affine recurrence and exact
finite iterate, rewrites the main term over the reduced denominator of the
single initial sample, proves that the cast of the entire accumulation is
exactly the remainder in (11ai), and specializes the geometric estimate to

\[
 0\le R_{N+1,t}<10\rho(100\rho)^N\qquad(t\le2N+1). \tag{11aj}
\]

The statement is a fixed-denominator *representation*; later reduced
fractions may cancel further. No distribution premise is hidden in T46.

Moreover, an abstract fixed prime component is rigorously insufficient. Write
a denominator as \(pD\), with \(D=5^sD_*\) and
\(\gcd(5,pD_*)=1\), and fix any nonzero numerator component modulo \(p\).
CRT leaves a shifted grid of reduced alternative seeds of mesh at most
\(2/5^s\) with that same component. If \(2/5^s<10^{-L}\), every
length-\(L\) decimal cylinder contains such an alternative seed. One may in
particular select an all-5 prefix whose first \(L\) iterates avoid
\([0,1/10)\), while preserving the displayed prime pulse. To carry this
separator through the perturbation (11ai), the chosen cylinder must have a
guard larger than \(\max_{t<L}|R_{n,t}|\).

Its application to the actual Machin scale remains a `proof sketch`: one must
prove the required lower bound on the 5-exponent in the *reduced* fixed
denominator and the guard inequality. Exact computation verifies both with
wide slack for all 263 eligible pulses with \(N\le199\), but finite evidence
is not proof. More importantly, the CRT construction varies the numerator; it
does not preserve the actual Machin cofactor phase. It therefore separates
only arguments using the prime pulse plus denominator shape, not arguments
using the exact numerator. That is precisely the surviving task.

A stronger same-modulus obstruction is recorded in
[`fixed_modulus_attack.md`](work/ultrapi-resume/fixed_modulus_attack.md), also
at `proof sketch` status. Let \(Y_N=a_N/Q_N\) be the reduced pulse seed and
freeze the complete 5-primary and 239-primary components together with every
fresh T45 component. Write the controlled factor as \(F_N\) and the remaining
cofactor as \(D_N=Q_N/F_N\). For every prime
\((12N+15)/2<\ell\le12N+15\), except 239 and 317, a unique shared-exponent
term and the same residue 951 give \(v_\ell(Y_N)=-1\). T48 machine-checks
this complete-seed expansion, the endpoint exclusion, the valuation, and
exact multiplicity one in the reduced denominator. Hence the remaining
prime-number-theorem deduction, at `proof sketch` status, gives

\[
 \log D_N\ge6N+o(N),\qquad \omega(D_N)=o(N). \tag{11ak}
\]

Kanold's Jacobsthal bound \(J(D)\le2^{\omega(D)}\), applied after multiplying
the affine numerator progression by \(F_N^{-1}\bmod D_N\), yields alternative
reduced numerators at the same \(Q_N\) and with the same frozen components in
every length-\(2N+2\) decimal cylinder for all sufficiently large \(N\):

\[
 {J(D_N)\over D_N}<10^{-(2N+2)}. \tag{11al}
\]

Choosing the all-5 cylinder makes the corresponding frequency-one sum at
least \((2N+2)\cos(\pi/10)\), almost maximal. Exact rational computation has
zero failures through \(N=300\), but is only `experiment`. This construction
still varies \(a_N\bmod D_N\); it neither describes nor refutes cancellation
of the actual Machin numerator. It proves that even the currently known local
components jointly cannot replace that full residue.

The simultaneous version requires one correction. T47's consecutive right-
and left-endpoint slots create a fourth long pulse class, (p=12N+17), which
the original three-class T45 analysis omitted. T49 now machine-checks its
exact combined core and proves

\[
 v_p(y_{N+2+t})=-1\qquad(0\le t\le2N+1),            \tag{11am}
\]

outside (p=317). Its localized coefficient is again
(4\cdot951/(5\cdot239)), and the first omitted forcing contains (3p).
Consequently the common four-class prime product over a block of length
(L\sim\lambda j) has logarithm
((8-4\lambda)j+o(j)), not the former ((6-3\lambda)j+o(j)).

The old upper-half-only cofactor estimate cannot freeze that extra class for
all (L). The corrected separator uses two seed-prime bands. For
(d=12j+3), the unique-term band (d/3<p\le d) has coefficient
(4\cdot951/(5\cdot239)); the two-term band (d/5<p\le d/3) has coefficient

\[
 {5359397032\over1706489875}
 ={2^3\cdot11\cdot19\cdot233\cdot13757\over5^3\cdot239^3}. \tag{11an}
\]

T50 machine-checks valuation (-1) and exact denominator multiplicity one
throughout (d/5<p\le d), outside the seven fixed primes
(5,11,19,233,239,317,13757). It also closes the apparent endpoint hole:
if (p\mid d+2) in this band, then (d+2=5p), and the endpoint-adjusted
residue is still nonzero. Ordinary PNT and Kanold then restore the all-four-
class same-denominator separator at `proof sketch` status; the full audit is
[`multiprime_adversarial.md`](work/ultrapi-resume/multiprime_adversarial.md).
It still varies the complementary numerator and proves no statement about
the selected Machin phase.

A general-band calculation makes the endpoint even sharper. For

\[
 C_r=4\sum_{\substack{1\le m\le2r-1\\m\ \mathrm{odd}}}
 {\chi_4(m)\over m}\left({4\over5^m}-{1\over239^m}\right), \tag{11ao}
\]

every prime (d/(2r+1)<p\le d/(2r-1)) outside the endpoint has localized
residue (10^j\chi_4(p)C_r). Taking
(R=\lfloor\log d/(16\log\log d)\rfloor), an elementary height bound proves
that every non-endpoint prime (d/(2R+1)<p\le d) survives with exact exponent
one. Endpoint cancellation really can occur: the first exact example is
(N,p,r)=(43,41,6), so it is essential to discard, rather than silently keep,
the prime divisors of (d+2). Their total logarithmic cost is only
(O(\log d)). PNT therefore puts (d-o(d)) logarithmic prime mass in the actual
reduced seed denominator, leaving only an \(\exp(o(j))\) complementary
quotient. This is a `proof sketch`, independently derived and adversarially
checked in
[`general_seed_band_attack.md`](work/ultrapi-resume/general_seed_band_attack.md)
and
[`actual_numerator_phase_attack.md`](work/ultrapi-resume/actual_numerator_phase_attack.md).
The retained exact checks compare 10,098 complete seed/prime rows with the
localized coefficient criterion with no mismatch and find seven endpoint
cancellations through (N=5000); these finite checks are only `experiment`.

Crucially, this does not approach V1 by itself. If the actual phase is
\(x=b/(FD)\), \(r=b\bmod F\), and \(b=Fc+r\), then exactly

\[
 c=\lfloor Dx\rfloor,\qquad {r\over F}=\{Dx\}.       \tag{11ap}
\]

Thus the final complementary quotient is literally the coarse archimedean
cell containing the actual phase. Along powers of ten its Euclidean carry is
the next decimal digit. Controlling nearly every CRT component narrows the
number of possible quotients to subexponential size, but selecting the actual
one is the digit problem itself, not a leftover technicality. More local
congruences alone are therefore a circular continuation of this route.

T53 makes the carry sentence exact in the verified track. For a canonical
state \(b=Fc+r\), \(0\le c<D\), \(0\le r<F\), set

\[
 \kappa=\left\lfloor{10r\over F}\right\rfloor,
 \quad r'=(10r)\bmod F,
 \quad \delta=\left\lfloor{10c+\kappa\over D}\right\rfloor,
 \quad c'=(10c+\kappa)\bmod D.                    \tag{11au}
\]

Lean proves

\[
 10(Fc+r)=FD\delta+(Fc'+r'),\qquad
 \delta=\left\lfloor{10(Fc+r)\over FD}\right\rfloor<10. \tag{11av}
\]

It also proves that \(Fc'+r'\) is the canonical remainder modulo \(FD\),
and recovers \(c'\) and \(r'\) from that full state by division and
reduction modulo \(F\). All 15 propositions are registered and independently
checked. These identities are `machine-checked`; they expose rather than
solve the coarse-state problem.

Cross-index compatibility does not repair that loss. For the specific split
which freezes the complete 5- and 239-primary parts and the certified
high-prime parts, let \(D_j\) be the complementary moduli. Exact affine
recurrence shows that all compatible phase differences on \(J\le j\le K\) are

\[
 \theta_j=10^{j-J}\theta_J,\qquad
 \theta_J\in {1\over\gcd(D_J,\ldots,D_K)}\mathbb Z/\mathbb Z. \tag{11aq}
\]

There is a persistent exact 3-primary source of such differences. If
\(a_j\) is defined by \(3^{a_j}\le12j+3<3^{a_j+1}\), then the unique seed term
with the least 3-adic valuation gives

\[
 v_3(10^jM_{3j})=1-a_j,\qquad
 {12j+3\over9}<3^{a_j-1}\le {12j+3\over3}.         \tag{11ar}
\]

Equation (11aq) and its translated-phase consequence remain a `proof sketch`,
with exact finite checks. Equation (11ar), including exact reduced-denominator
multiplicity \(a_j-1\), is now the `machine-checked` T52 theorem. Together
they produce \(\Theta(J)\) tail-consistent translated
phases which preserve all components in this particular split. T46's exact
positive forcing bound then shows that, for every fixed finite word \(W\) and
all sufficiently large \(J\), one translated phase follows \(W\): the shifted
\(1/3^{a_J-1}\)-grid approximates the midpoint of its cylinder more closely
than the accumulated forcing can cross a digit boundary. The full audit is
[`cross_index_quotient_attack.md`](work/ultrapi-resume/cross_index_quotient_attack.md).
This symmetry disappears if the complete 3-primary numerator component is
also frozen; it therefore separates only the current component set. It still
proves that subexponential candidate count plus recurrence consistency cannot
select the actual quotient.

Nor can the subexponential count be multiplied by forbidden-word measure.
If \(U_{w,T}\) is the union of the length-\(T+|w|-1\) cylinders avoiding
\(w\), then \(D_j\mu(U_{w,T})=o(1)\) for \(T=\Theta(j)\), but this is only
the zero-mode/random-shift expectation. The deterministic shifted-grid count
has the exact bound

\[
 \#(G_j\cap U_{w,T})
 \le D_j\mu(U_{w,T})+R_w(T+|w|-1),                 \tag{11at}
\]

where \(R_w(n)\) is the number of connected cylinder runs. This boundary term
can be exponential; for \(w=0\), \(R_0(n)=9^{n-1}\). It is genuinely
load-bearing. The explicit reduced family

\[
 F=(5\cdot239)^S,\quad Q=81F,\quad
 x={9aF-1\over81F}={a\over9}-{1\over81F}
\]

has complementary modulus \(81\), known fine carry \(9\), fixed coarse state
\(9a-1\), and an arbitrarily long constant-\(a\) digit itinerary. A
cross-index version obeys the same affine shape with positive summable
geometric forcing. Thus a first-moment or automaton count cannot select the
actual Machin candidate; it needs an actual-shift resonant discrepancy bound
strong enough to make the integer count \(<1\). The derivation and exact
checks are in
[`subexponential_candidate_avoidance.md`](work/ultrapi-resume/subexponential_candidate_avoidance.md)
at `proof sketch`/`experiment` status.

The actual-shift discrepancy is now isolated exactly. Let \(n=T+|w|-1\),
\(M=10^n\), let \(A_w(n)\) be the leading-zero-padded length-\(n\) strings
avoiding \(w\), and put

\[
 S_{w,n}(h)=\sum_{k\in A_w(n)}e(-hk/M).
\]

For the shifted grid associated with \(Q=FD\) and \(r=b\bmod F\), the
endpoint-safe finite Fourier identity has a Poisson form (automatically free
of sampled cylinder endpoints once \(F\) contains a non-\(2,5\) prime):

\[
 \begin{aligned}
 N(D,r;w,T)={}&{D|A_w(n)|\over M}+\mathcal R(D,r;w,n),\\
 \mathcal R(D,r;w,n)={}&\lim_{H\to\infty}
 \sum_{0<|\ell|\le H}{1-e(-\ell D/M)\over2\pi i\ell}
 S_{w,n}(\ell D)e(\ell r/F).                     \tag{11aw}
 \end{aligned}
\]

The high-prime formulas do make the last phase an explicit product of local
characters. If \(P_j\) is the certified squarefree prime product and
\(F_j=F_{0,j}P_j\), its known high-prime part is

\[
 \prod_{p\mid P_j}e_p\!\left(
   \ell D_j10^j\chi_4(p)C_{s(p)}\right),          \tag{11ax}
\]

where each rational \(C_{s(p)}\) is reduced modulo \(p\). The product does
not average over \(p\); additive CRT recombines it with the \(F_{0,j}\)
component to one character. Exact quotient reciprocity gives

\[
 e(\ell r_j/F_j)=e(\ell D_jx_j),
 \qquad x_j=\{10^jM_{3j}\}.                       \tag{11ay}
\]

Thus the requested cancellation is precisely a digital Fourier
reconstruction evaluated at the selected actual Machin phase.

This conclusion survives an exact automaton expansion. If \(A_a\) is the
forbidden-word prefix-transition matrix and
\(B_t(h)=\sum_{a=0}^9e(-ha/10^t)A_a\), then

\[
 S_{w,n}(h)=v_0^{\mathsf T}\prod_{t=1}^nB_t(h)\mathbf1,
 \quad
 S_{w,n}(10^vh)=v_0^{\mathsf T}A^v
       \prod_{s=1}^{n-v}B_s(h)\mathbf1,           \tag{11az}
\]

with \(A=\sum_aA_a\). Perron diagonalization retains a leading
\(\lambda_w^v\) alias; for one forbidden digit the equality is exactly
\(S_{w,n}(10^vh)=9^vS_{w,n-v}(h)\). T38 replaces the associated phase by
\(e(qD_j10^{j+v}\pi)\) with error at most
\(2\pi10^{|w|-1}(100\rho)^j\), but leaves a variable-frequency fixed-
\(\pi\) lacunary sum.

The precise remaining `conjecture` may be stated as actual-shift resonance
(`ASR(w)`). At \(n_j=2j+|w|-1\), eventually

\[
 {D_j|A_w(n_j)|\over10^{n_j}}\le{1\over4},
 \qquad |\mathcal R(D_j,r_j;w,n_j)|\le{1\over2}. \tag{11ba}
\]

The first inequality follows from the growing-band `proof sketch`; the
second is unproved. Together they would make the integer count at most
\(3/4\), contradicting the actual avoiding member forced by a missing word.
The derivation is independently checked in
[`actual_shift_resonance_attack.md`](work/ultrapi-resume/actual_shift_resonance_attack.md)
and
[`actual_shift_resonance_independent_audit.md`](work/ultrapi-resume/actual_shift_resonance_independent_audit.md).
A dated primary-source audit there found only average, fixed-modulus, or
rational-counting estimates, none applicable to this pointwise changing
phase.

An exact `experiment` prevents a stronger heuristic from being promoted.
Freeze every actual denominator component except the complete three-primary
factor, so \(D_j=3^{v_3(Q_j)}\). Across 8,580 exact prefix checks through
\(j=80\), the proposed relative bound
\(|\mathcal R|\le D_j\mu(U_{w,T})\) fails 65 times. At \(j=35\), \(D=81\),
and forbidden digit 4 or 5 over 70 places,

\[
 N=1,\qquad D(9/10)^{70}=0.050752878606\ldots,
 \qquad\mathcal R=0.949247121394\ldots.           \tag{11bb}
\]

The next scale has count zero. This finite result falsifies only the naive
pointwise relative estimate, not eventual ASR and not V1.

### Nested three-primary schedule and actual selector tower

T54 now makes the special three-primary cross-index structure
`machine-checked`. If \(a_j\) and \(a_{j+1}\) are the T52 exponent windows,
then \(a_{j+1}=a_j\) or \(a_j+1\). Therefore

\[
 D_j=3^{a_j-1}\mid D_{j+1},\qquad
 {D_{j+1}\over D_j}\in\{1,3\}.                 \tag{11bc}
\]

Writing \(x_{j+1}=\{10x_j+\Delta_j\}\), the resonant phases consequently
obey the exact integral recurrence

\[
 e(\ell D_{j+1}x_{j+1})
 =e(10\ell(D_{j+1}/D_j)D_jx_j)
  e(\ell D_{j+1}\Delta_j).                      \tag{11bd}
\]

This repairs the divisibility failure of the general complementary factor,
but it does not create cancellation. When \(D\) triples, the new grid is the
disjoint union of three translates of the inherited grid. Summing all three
aliases kills two frequency classes by orthogonality, whereas the actual
orbit remains in the one inherited alias and retains those classes. During a
constant epoch, multiplication by ten only permutes the labels; for \(D\ge9\)
its order is \(D/9\), preserving each class modulo nine. Exact actual-seed
checks verify the phase and grid recurrences and also exhibit nonmonotone
avoidance counts. A separator using the actual numerical Machin forcing but a
different non-three fine residue maintains the exact T52 denominator across a
whole epoch while emitting one constant digit. Hence nesting, T53 carries,
and even the forcing values cannot give a contraction uniformly in the fine
state. This is a `proof sketch` obstruction, not a counterexample for the
actual numerator.

There is nonetheless additional exact actual-numerator structure. Put
\(y_j=10^jM_{3j}\), \(D_j=3^{a_j-1}\), and write its reduced fractional
numerator as \(b_j=F_jc_j+r_j\). For every fixed \(k\le a_j-1\), a finite
three-adic shell calculation gives

\[
 L_{j,k}:=D_jy_j\pmod {3^k}
 =10^j\!\sum_{\substack{1\le t\le h_{j,k}\\t\ \mathrm{odd}}}
 W_{j,k}(t),\qquad h_{j,k}<3^k.                  \tag{11be}
\]

The explicit weights \(W_{j,k}\) are recorded and independently replayed in
[`machin_three_adic_coarse_correlation.md`](work/ultrapi-resume/machin_three_adic_coarse_correlation.md).
When \(a_j\ge2k-1\), the shell stabilizes to the signed harmonic staircase

\[
 L_{j,k}\equiv
 -4\,10^j(-1)^{a_j-k+1}H_k(h_{j,k})\pmod {3^k}. \tag{11bf}
\]

In particular, \(L_{j,1}\) is \(1\) for odd \(a_j\) and \(2\) for even
\(a_j\). Modulo nine its three epoch stages are \((1,4,7)\) for odd \(a_j\)
and \((8,5,2)\) for even \(a_j\). The crucial actual coarse/fine selector is

\[
 \boxed{c_j\equiv L_{j,k}-r_jF_j^{-1}\pmod {3^k}.}           \tag{11bg}
\]

Thus the actual point belongs to a selected grid of \(D_j/3^k\) states, and
the same selector propagates through a fixed-seed decimal pulse by multiplying
\(L_{j,k}\) by \(10^t\). This is more precise than T52's valuation alone, but
the fine phase \(r_jF_j^{-1}\) remains indispensable. Exact checks through
\(j=80\) validate 314 sparse shells, 220 stabilized shells, 314 selectors,
6,594 pulse selectors, and 209 impulse recurrences. The selected modulo-nine
grid had no one-digit survivor after \(j=16\) in that finite range, yet its
naive relative discrepancy estimate still failed 42 times. These rows are an
`experiment`, not an asymptotic theorem.

The closest literature escape also fails sharply. Maynard's restricted-digit
Fourier lemma requires a non-base reduced denominator factor \(q_1>1\). The
original ASR modes reduce to denominators dividing \(10^n\), so \(q_1=1\).
A CRT lift to \(10^nD_j\) genuinely introduces \(q_1\mid D_j\), but every
fixed CRT row reconstructs the same occupancy count by gauge orthogonality.
Bezout reciprocity forces the mode \(1/(10^nD_j)\) into one such non-base row;
its normalized digital coefficient is at least \(\cos(\pi/D_j)\to1\), while
its full denominator violates Maynard's size range. The theorem controls a
real minor-arc slice, not the complete signed row. This boundary is
`literature-checked`; the regrouping identities remain `proof sketch`.

A growing-depth selector does not repair this. At the balanced choice

\[
 k_j=\lfloor a_j/2\rfloor,
 \qquad q_j={D_j\over3^{k_j}}\asymp\sqrt{D_j},                 \tag{11bh}
\]

the selected grid is exactly the actual-centered coset

\[
 \mathcal G_{j,k}=x_j+q_j^{-1}\mathbb Z/\mathbb Z.             \tag{11bi}
\]

Thus it is a smaller ensemble, but not an ensemble independent of the target.
If \(C_{j,k}\) and \(L_{j,k}\) denote the selected and leading residues, the
fine residual

\[
 R_{j,k}={F_j(C_{j,k}-L_{j,k})+r_j\over3^k}
\]

is integral and satisfies the exact depth recursion

\[
 3R_{j,k+1}=R_{j,k}+F_j(u_{j,k}-v_{j,k}),
 \qquad R_{j,k+1}\equiv3^{-1}R_{j,k}\pmod {F_j}.               \tag{11bj}
\]

This chooses one cube root of the parent phase; it does not average the three
roots. The corresponding ternary child can retain all of its parent's
avoiding occupancy. Exact arithmetic through \(j=240\) found 2,442 such full
concentrations for two-digit words, including 1,833 singleton-to-singleton
rows; these are `experiment`. A `proof sketch` separator preserves the actual
stable leading-residue tower through (11bh), the exact \(D_j\) schedule, and a
positive T46-scale coboundary while retaining an all-one prefix. It changes
the actual fine residual, so the remaining route-specific target is precisely
that Archimedean phase. The exact derivation and checker are in
[`machin_selector_multiscale.md`](work/ultrapi-resume/machin_selector_multiscale.md).

T57 separates the exact algebra from that Machin-specific interpretation.
For arbitrary integers satisfying

\[
 b=Fc+r,\qquad c=C+dt,\qquad F(C-L)+r=dR,
\]

with \(F,d\ne0\), it machine-checks the rational recombination

\[
 {b\over Fd}=t+{L\over d}+{R\over F}.                       \tag{11bk}
\]

Under the separately supplied fixed-depth carry transforms, it also proves

\[
 R'=10R+F(v-a),\qquad R'\equiv10R\pmod F.                  \tag{11bl}
\]

These are generic identities: the formal module supplies neither the
canonical Machin variables and carry ranges nor an estimate for \(R/F\).
An independent adversarial audit confirmed all four declarations and their
allowlisted axiom surface while retaining that boundary. The actual
instantiation and finite replay below remain `proof sketch` and `experiment`,
respectively.

That actual residual can nevertheless be closed exactly at `proof sketch`
level. With \(s_j=10^j(\pi-M_{3j})\), the balanced residual character is

\[
 e\!\left({R_j\over F_j}\right)
 =e\!\left(q_j10^j\pi-q_js_j-{L_j\over h_j}\right).        \tag{11bm}
\]

Thus the fine term is a coordinate copy of the linked fixed-\(\pi\) phase,
not an algebraic error or a fixed-rank S-unit. There is one genuinely
Machin-specific positive result. If \(B=12j+3\) and \(G_j\) is the product
of the primes \(B/2<p\le B\), excluding 239 and 317, then T48's primes remain
unitary denominator factors for every \(j+u\) with \(24u+4\le B\). Their
combined actual residual coordinate obeys

\[
 A_{j+u+1}^{(G_j)}\equiv
 10{q_{j+u+1}\over q_{j+u}}A_{j+u}^{(G_j)}\pmod {G_j},
 \qquad \log G_j=6j+o(j).                                  \tag{11bn}
\]

The window has \(j/2+O(1)\) transitions. Exact arithmetic through \(j=80\)
passed 43,799 prime-persistence checks and 1,027 fixed-factor recurrences.
This is stronger than T56/T57's generic algebra, but still transports one
phase by units. The complementary CRT character can align with it, and their
product is exactly (11bm). The bounded primary-source audit found no
fixed-rank S-unit, Subspace-Theorem, or large-sieve theorem controlling that
one changing transcendental phase; see
[`actual_fine_residual_sunit_attack.md`](work/ultrapi-resume/actual_fine_residual_sunit_attack.md).

The effective ×10×3 literature does not supply the missing phase theorem.
BLMV Theorem 3.2 can align the decimal exponent and place the three-adic
exponent in a strip ending at \(a_j-1\), but it selects an unspecified member
of that strip by averaging a complete multiplicative cycle. For the uniform
\(D_j\)-grid, reaching the endpoint forces \(\rho\le\delta/4\) while the theorem requires
\(\rho\ge20\delta\). More decisively, the complete linked multiplier set

\[
 \{10^s3^{a_j-1}:j\le s\le3j+C\}
\]

is Hadamard-lacunary. The BFK escaping theorem therefore gives
Diophantine-generic deleted-digit points whose full ×10×3 orbit satisfies
BLMV density while this linked slice avoids an open arc. This is a
`literature-checked` applicability obstruction, not a statement about \(\pi\); see
[`blmv_linked_slice_audit.md`](work/ultrapi-resume/blmv_linked_slice_audit.md).

The direct omitted-word/transcendence route reaches an independent boundary.
If a length-\(m\) word \(w\) is absent, then \(\{\pi\}\) lies in the
finite-state survivor set \(K_w\). Its adjacency spectral radius satisfies

\[
 9\le\lambda_w\le(10^m-1)^{1/m}<10,\qquad
 \dim_H K_w={\log\lambda_w\over\log10}<1.           \tag{11as}
\]

This entropy deficit is rigorous, but membership in a finite-state language
does not make the one selected path automatic or Mahler. Decimal truncation
still gives only the universal \(q^{-1}\) error, far from a contradiction
with the known irrationality measure of \(\pi\). Missing-digit survivor sets
contain transcendental badly approximable points of exponent 2, so even the
best possible scalar irrationality exponent would not exclude \(K_w\).
The stronger identity \(e^{i\pi}=-1\) does not currently change that verdict.
Effective logarithm and Lindemann--Weierstrass measures lower-bound a supplied
polynomial or exponential form; word omission supplies a survivor interval,
not a form small enough to violate those bounds. A nine-symbol decimal Cantor
subset of every \(K_w\) contains transcendental badly approximable points of
irrationality exponent exactly two. A separate `proof sketch` construction
inside the same subset even gives a transcendental omitted-digit point with a
Cijsouw-shape degree--height lower bound. Thus the output class of present
transcendence measures is logically compatible with omission. The updated
primary-source audit through 2026-08-12 is
[`logarithm_missing_word_attack.md`](work/ultrapi-resume/logarithm_missing_word_attack.md).
The dated source and mathlib applicability audit is
[`missing_word_transcendence_attack.md`](work/ultrapi-resume/missing_word_transcendence_attack.md).
Its sources are `literature-checked` and its local reductions are
`proof sketch`; it obtains no pointwise exclusion \(\pi\notin K_w\).

Two independent analytic representations were also audited. Hutton's
identity

\[
 {\pi\over4}=2\arctan(1/3)+\arctan(1/7)
\]

gives rational alternating brackets \(H_K<U^H_K\). T58 machine-checks their
definitions, rationality, the unconditional enclosure
\(H_K\le\pi\le U_K^H\), and the exact positive width

\[
 U_K^H-H_K={8\over(4K+5)3^{4K+5}}
             +{4\over(4K+5)7^{4K+5}}.                      \tag{11bo}
\]

On the matched schedules, further exact `proof sketch` inequalities and
exact-rational replay give

\[
 M_{3j}<H_{5j}<\pi<U^H_{5j}<U^M_{3j}\qquad(j\ge1).         \tag{11bp}
\]

The Hutton interval is strictly sharper than the Machin interval, but their
intersection is exactly the Hutton interval: two formulae do not create two
independent observations. Their sampled states differ by the explicit
rational translation \(d_j=10^j(H_{5j}-M_{3j})\), and their forcings differ
by the coboundary \(d_{j+1}-10d_j\). After a common-denominator lift the
residue pairs form one affine graph, not a product. A Hutton bracket can
certify any individual word whose entire scaled interval lies in its target
cylinder; proving such certificates for every word remains a stronger
unproved condition. The source audit and exact checker are in
[`alternate_machin_identity_attack.md`](work/ultrapi-resume/alternate_machin_identity_attack.md).

T59 makes that finite-certificate implication exact. For any
\(a<10^m\), integer \(z\), and zero-based start \(N\), it machine-checks

\[
 z+{a\over10^m}\le10^NH_K,\qquad
 10^NU_K^H<z+{a+1\over10^m}
 \quad\Longrightarrow\quad
 (\operatorname{piCylinderCode}(m,N)).\mathrm{val}=a.       \tag{11bq}
\]

The strict upper endpoint preserves the half-open decimal convention, and
the theorem includes leading-zero words and \(m=0\). The missing quantifier is
not hidden: a Hutton-bracket route to V1 would still have to prove, for every
\(m\) and \(a<10^m\), the existence of \(K,N,z\) satisfying the two displayed
inequalities. T59 proves only the implication from such witnesses.

The full Hutton period does not supply those witnesses. If \(q_K\) is the
reduced denominator of \(H_K\), remove its short 5-primary decimal transient
and put \(d_K=\operatorname{ord}_{q_K/5^{v_5(q_K)}}(10)\). An exact adjacent-
increment calculation gives, for every \(K\ge1\), at least one of
\(H_{K-1},H_K\) a three-primary component forcing

\[
 d\ge3^{4K+3-\lfloor\log_3(16K+13)\rfloor-2}.             \tag{11br}
\]

This period is exponential, whereas (11bo) ties the bracket to \(\pi\) only
through \(1.90848\ldots K+O(\log K)\) decimal positions. Full-period
coverage therefore returns an unlocalized offset far outside the transferable
prefix. Rotating the reduced numerator by a power of ten preserves the
denominator, order, and cyclic word census while moving first occurrences, so
those invariants cannot recover localization. Exact scans found the first
complete four-digit coverage for \(K=1,\ldots,8\) only after 81,030--125,672
digits, versus certified outer horizons 4--18; this is `experiment`. The
denominator argument, rotation separator, de Bruijn-shadow separator, source
audit, and checker are in
[`hutton_periodic_orbit_attack.md`](work/ultrapi-resume/hutton_periodic_orbit_attack.md).
The exact adjacent-increment identity used before the valuation step is now
separately `machine-checked` in T60. In the forward indexing \(K\mapsto K+1\),
Lean proves

\[
 H_{K+1}-H_K=
 {16(16K+29)\over(4K+7)(4K+5)3^{4K+7}}+
 {8(96K+169)\over(4K+7)(4K+5)7^{4K+7}}>0.                \tag{11br1}
\]

The deductions from this identity to reduced-denominator valuations,
multiplicative order, and the localization separator remain `proof sketch`;
T60 does not silently promote them.

T61 now closes the first of those valuation deductions for the actual Hutton
numerator.  Put \(R=4K+3\).  For every prime \(p>7\) satisfying

\[
 {R\over2}<p\le R,\qquad p\ne17,
\]

it machine-checks

\[
 v_p(H_K)=-1,
 \qquad v_p(\operatorname{den}H_K)=1.                    \tag{11br2}
\]

Only the two Taylor terms with odd exponent \(p\) can be singular.  Their
combined integer numerator contains \(4(2\cdot7^p+3^p)\), which is congruent
to \(68\pmod p\); \(p=17\) is therefore the genuine exceptional prime, while
the hypotheses \(p>7\) exclude the small base and low-index cases.  The
stronger local coordinate

\[
 pH_K\equiv(-1)^{(p-1)/2}{68\over21}\pmod p              \tag{11br3}
\]

remains `proof sketch`.  T62 separately machine-checks the simultaneous
product consequence.  If \(G_K\) is the product of these eligible upper-half
primes, it gives \(G_K\mid\operatorname{den}H_K\) and, by the prime number
theorem,

\[
 \log G_K={R\over2}+o(R).                                \tag{11br4}
\]

T62 now machine-checks the finite divisibility assertion
\(G_K\mid\operatorname{den}H_K\) itself: it defines exactly the eligible
prime set, proves its members pairwise coprime, imports T61's multiplicity-one
theorem for each member, and combines them into one product divisor.  Only the
asymptotic evaluation in (11br4) remains at `proof sketch` level.

T64 enlarges this exact finite divisor theorem.  The upper-half hypothesis
\(R<2p\) is stronger than necessary because every Taylor exponent is odd.
Under \(R<3p\), any positive multiple of \(p\) below \(3p\) is \(p\) or
\(2p\), and the latter is even.  Hence the same singular pair is still unique,
and Lean proves

\[
 p>7,\quad p\ne17,\quad {R\over3}<p\le R
 \quad\Longrightarrow\quad
 v_p(H_K)=-1,\qquad v_p(\operatorname{den}H_K)=1.       \tag{11br5}
\]

It also defines the exact finite set in (11br5), proves pairwise coprimality,
and proves that its whole squarefree product divides the reduced denominator.
This increases the prime-number-theorem logarithmic mass from
\(R/2+o(R)\) to \(2R/3+o(R)\) at `proof sketch` asymptotic level.  The finite
valuation and product assertions themselves are `machine-checked`; they do
not estimate the selected numerator or force a decimal cell.

T65 closes the next band.  Under \(R<5p\) and \(3p\le R\), the only singular
odd exponents are \(p\) and \(3p\).  Their four Hutton terms combine with a
factor whose Fermat residue is

\[
 21778=2\cdot10889\pmod p.
\]

Consequently Lean proves

\[
 p>7,\quad p\ne10889,\quad {R\over5}<p\le {R\over3}
 \quad\Longrightarrow\quad
 v_p(H_K)=-1,\qquad v_p(\operatorname{den}H_K)=1.       \tag{11br5a}
\]

It also proves divisibility by the complete squarefree product in this band.
Together T64 and T65 therefore force all eligible primes in \((R/5,R]\),
apart from the fixed exceptions 17 and 10889.  The corresponding logarithmic
prime mass is \(4R/5+o(R)\) by the prime number theorem at `proof sketch`
asymptotic level; the finite valuation and product theorems are
`machine-checked`.  This enlarges denominator support but still gives no
Archimedean selected-numerator estimate.

The exact base-five transient used below is no longer informal either.  T63
machine-checks, including \(K=0\),

\[
 5^e\le R<5^{e+1}
 \quad\Longrightarrow\quad
 v_5(H_K)=-e,qquad v_5(\operatorname{den}H_K)=e.       \tag{11br5b}
\]

The proof isolates one or two least-valuation odd exponents and proves their
scaled numerator cannot cancel modulo five.  T66 closes the formerly open
two-primary caveat.  Every paired Hutton term has exact two-adic valuation
two; their nonzero finite sum has valuation at least two, so its reduced
denominator is odd.  Lean therefore proves

\[
 \max\!\left\{v_2(\operatorname{den}H_K),
                 v_5(\operatorname{den}H_K)\right\}=e. \tag{11br5b'}
\]

Thus (e) is the whole base-ten denominator preperiod used in the CRT
reduction, not merely its five-primary component.  This exact transient still
does not estimate the selected post-transient numerator phase.

The two formal bands are instances of a general local-prefix law.  If
\(p>7\) is prime, \(p\le R<p^2\),
\(q=\lfloor R/p\rfloor\), and
\(n=\lfloor(q+1)/2\rfloor\), define the shorter Hutton prefix

\[
 A_n=\sum_{j=0}^{n-1}(-1)^j
 \left({8\over(2j+1)3^{2j+1}}+{4\over(2j+1)7^{2j+1}}\right).
\]

An independently audited `proof sketch` proves the exact localized identity

\[
 pH_K\equiv\chi_4(p)A_n\pmod p,                          \tag{11br5c}
\]

and hence \(v_p(H_K)=-1\) exactly when
\(p\nmid\operatorname{num}(A_n)\); otherwise \(p\) is absent from the
reduced denominator.  For any fixed band depth \(L\), all sufficiently large
primes \(R/(2L+1)<p\le R\) exceed the finitely many prefix numerators and
therefore survive.  A prime-number-theorem squeeze, with \(L\) taken fixed
before the limit and only then sent to infinity, gives

\[
 \log\operatorname{rad}(\operatorname{den}H_K)=R+o(R).   \tag{11br5d}
\]

Thus the Hutton denominator carries asymptotically all possible logarithmic
prime weight below \(R\); fixed-band denominator extraction is effectively
exhausted.  For a fixed \(L\), the selected band product has the corrected
size \((1-1/(2L+1))R+o(R)\), not \(R+o(R)\); the latter belongs only to the
full radical after the diagonal \(L\to\infty\).  The weighted global CRT
decomposition still leaves a reciprocal-prime phase known only to be \(o(1)\),
where a linear decimal shift needs exponential accuracy.  The corrected
report, 161,115-assertion checker, and independent audit are
[`hutton_multi_band_attack.md`](work/ultrapi-resume/hutton_multi_band_attack.md),
[`hutton_multi_band_check.py`](work/ultrapi-resume/hutton_multi_band_check.py),
and
[`hutton_multi_band_independent_audit.md`](work/ultrapi-resume/hutton_multi_band_independent_audit.md).

This is useful negative information as well as structure: the Hutton moduli
have growing prime support, so fixed-prime-set Korobov estimates do not
apply.  The bracket transfers only
\(1.908485\ldots K+O(\log K)=\Theta(\log\operatorname{den}H_K)\) orbit
states.  Existing general exponential-sum bounds require much longer
prefixes.  More decisively, neighboring Hutton moduli admit the coefficient
\(a=1\) for which the entire transferable sum is \(N-o(1)\); hence no
numerator-uniform denominator, order, CRT, or differencing estimate can work
at this scale.  For the actual numerator, fixed-frequency cancellation is,
up to the bracket error, precisely the corresponding Weyl cancellation for
\(\pi\), and the localized bracket-hit assertion is equivalent to V1.  The
full derivation, bounded source comparison, and exact replay are in
[`hutton_prefix_sum_attack.md`](work/ultrapi-resume/hutton_prefix_sum_attack.md);
the checker passed 13,418 prime-survival, 6,707 local-residue, 37,986 state,
200 neighboring-modulus, and 10,000 LTE assertions.  None of this supplies
the missing selected-numerator cancellation.

The selected upper-half residues can nevertheless be recombined exactly at
`proof sketch` level.  Write \(H_K=P_K/Q_K\) in lowest terms,
\(Q_K=C_KG_K\), and

\[
 \epsilon_p=(-1)^{(p-1)/2},\qquad
 S_K=\sum_{p\mid G_K}\epsilon_p{G_K\over p}.
\]

The independently audited local-to-global calculation gives

\[
 21P_K\equiv68C_KS_K\pmod {G_K},\qquad
 H_K={68\over21}{S_K\over G_K}+{T_K\over21C_K}          \tag{11br6}
\]

for an integer \(T_K\).  If \(b_K=v_5(Q_K)\),
\(m_K=Q_K/5^{b_K}=G_KB_K\), and
\(a_K\equiv2^{b_K}P_K\pmod {m_K}\), then

\[
 a_KB_K^{-1}10^s
 \equiv {68\over21}10^{b_K+s}S_K\pmod {G_K}.           \tag{11br7}
\]

The full local residue used here is an elementary deduction from T61's named
theorems, not itself a named Lean theorem, so (11br6)--(11br7) remain
`proof sketch`.  Exact replay verified 10,089 local congruences, 1,743 global
groups, and 4,980 CRT phases.  The factor \(C_K\) is essential: dropping it
already fails at \(K=3\).  Although the unshifted first coordinate lies within
\(O(1/\log R)\) of a 21-point grid, the mandatory factor
\(10^{b_K+s}\) makes that localization vacuous, and the complementary
\(B_K\)-coordinate remains correlated with the same decimal power.  Thus the
CRT collapse exposes the actual selected-prime phase without locating the
full rational state.  The corrected report and independent audit are
[`hutton_global_crt_attack.md`](work/ultrapi-resume/hutton_global_crt_attack.md)
and
[`hutton_global_crt_independent_audit.md`](work/ultrapi-resume/hutton_global_crt_independent_audit.md).

The signed reciprocal perturbation in that coordinate has additional exact
structure.  For the upper-half set, put
\(\Delta_K=\sum_p\chi_4(p)/p\) and

\[
 A_K=\prod_p(p+\chi_4(p)),\qquad
 V_K=\prod_p(p-\chi_4(p)).
\]

Then an exact logarithmic expansion gives

\[
 \left|\Delta_K-{1\over2}\log{A_K\over V_K}\right|
 \le\sum_p{1\over3p(p^2-1)}
 =O\!\left({1\over R^2\log R}\right).                  \tag{11br8}
\]

Unlike ordinary prime-race bounds, this approximation remains nonvacuous
after the mandatory \(5\)-primary shift for

\[
 0\le s\le(2-\log_5 10)\log_{10}R
 =0.569323441\ldots\log_{10}R.                         \tag{11br9}
\]

This is the first localized piece of the CRT coordinate that survives the
transient, but the window is logarithmic rather than linear.  The independent
audit also caught an important distinction: equidistribution of the real
proxy \(10^b\Delta_K\) would not by itself give equidistribution of the actual
modular \(21^{-1}\) coordinate; a lifted modular Weyl target is required.
The exact sparse recurrence has many plateaus, and both unconditional and
GRH prime-race estimates are already vacuous after the transient.  The
corrected `literature-checked`/`proof sketch` report and audit are
[`hutton_prime_character_phase.md`](work/ultrapi-resume/hutton_prime_character_phase.md)
and
[`hutton_prime_character_phase_independent_audit.md`](work/ultrapi-resume/hutton_prime_character_phase_independent_audit.md).

Cross-index averaging does not rescue this coordinate.  Put

\[
 \mathcal I_b=\left\{K:{5^b-1\over4}\le K\le
                    {5^{b+1}-5\over4}\right\}.
                                                               \tag{11br10}
\]

T63 and T66 imply that this is an exact common-transient block:
\(|\mathcal I_b|=5^b\), and the complete base-ten preperiod is \(b\) for
every \(K\in\mathcal I_b\).  If \(K_b=(5^b-1)/4\), nesting of the Hutton
brackets gives, for every integer \(h\),

\[
 \left|e(h10^{b+s}H_K)-e(h10^{b+s}H_{K_b})\right|
 \le 2\pi |h|10^{b+s}W_{K_b}.                              \tag{11br11}
\]

Consequently, for fixed \(h\ne0\) and fixed
\(0<\delta<\log_{10}3\), uniformly on
\(0\le s\le(\log_{10}3-\delta)5^b\),

\[
 \left|{1\over5^b}\sum_{K\in\mathcal I_b}
        e(h10^{b+s}H_K)\right|=1-o(1),                    \tag{11br12}
\]

the opposite of equidistribution.  If \(X_{K,s}\) and \(Y_{K,s}\) are the
selected and complementary additive-CRT factors, then exactly

\[
 X_{K,s}Y_{K,s}=e(10^{b+s}H_K),                            \tag{11br13}
\]

so (11br11) says that \(Y_{K,s}\) asymptotically conjugates \(X_{K,s}\)
times one common phase.  At every transferable pair, without fixing a block,
the same identity reads

\[
 Y_{K,s}=e(10^{b_K+s}\pi)\overline{X_{K,s}}+O(10^{b_K+s}W_K).
                                                               \tag{11br14}
\]

Thus cancellation of an isolated selected-prime factor cannot imply
cancellation of the full state.  Allowing an offset \(s=s(K)\) merely turns
the proposed average into a weighted exponential sum over different positions
of the actual fixed-π orbit.  This independently audited `proof sketch`
closes the apparent cross-\(K\) independence route; it is not a V1 theorem.
The corrected report, 5,841-check exact replay, and audit are
[`hutton_cross_k_phase_collapse.md`](work/ultrapi-resume/hutton_cross_k_phase_collapse.md),
[`hutton_cross_k_phase_collapse_check.py`](work/ultrapi-resume/hutton_cross_k_phase_collapse_check.py),
and
[`hutton_cross_k_phase_collapse_independent_audit.md`](work/ultrapi-resume/hutton_cross_k_phase_collapse_independent_audit.md).

A simultaneous-primary schedule makes the amount of known denominator mass
almost maximal without resolving the phase.  For

\[
 R_a=3^a7^{a+1},\qquad K_a=(R_a-3)/4,\qquad a\ge2,
\]

T68 machine-checks the general dominant-layer argument and the exact family

\[
 v_3(\operatorname{den}H_{K_a})=R_a+a,\qquad
 v_7(\operatorname{den}H_{K_a})=R_a+a+1.                 \tag{11br14a}
\]

Writing \(F_{0,a}=3^{R_a+a}7^{R_a+a+1}\), the actual post-transient additive
coordinate \(\xi_a\) is determined to growing primary precision:

\[
 \xi_a\equiv-8\,10^{b_a}7^{R_a}\pmod {3^{a+2}},\qquad
 \xi_a\equiv-4\,10^{b_a}3^{R_a}\pmod {7^{a+3}}.          \tag{11br14b}
\]

After adjoining every surviving prime above \(\sqrt{R_a}\), the remaining
complementary modulus is at most
\(R_a^{\sqrt{R_a}}=\exp(o(R_a))\).  The primary modulus itself has exact
decimal period

\[
 \operatorname{ord}_{F_{0,a}}(10)
 =2\,3^{R_a+a-2}7^{R_a+a}.                                \tag{11br14c}
\]

This still supplies no short-orbit cancellation.  The least CRT lift of the
shallow congruences in (11br14b) has normalized phase mean tending to one
through every horizon \(s\le(\log_{10}7-\delta)R_a\), so those local data
admit an explicit stationary countermodel.  Supplying the complete actual
coordinate removes the countermodel only by restoring the exact correlated
identity (11br13), namely the fixed-\(\pi\) phase.  The corrected report,
primary checker, and independent audit are
[`hutton_primary_phase_attack.md`](work/ultrapi-resume/hutton_primary_phase_attack.md),
[`hutton_primary_phase_check.py`](work/ultrapi-resume/hutton_primary_phase_check.py),
and
[`hutton_primary_phase_independent_audit.md`](work/ultrapi-resume/hutton_primary_phase_independent_audit.md).
The dominant-layer lemma and valuation family (11br14a) are
`machine-checked` in T68.  The leading-unit congruences, high-prime
completion, exact-period application, and stationary countermodel remain a
`proof sketch`; the finite replay is an `experiment`, and none is V1.

Recursive Machin-angle splitting removes a different technical obstruction
but reaches the same phase wall.  Exact identities begin with

\[
 {\pi\over4}=3\arctan {1\over7}+2\arctan {2\over11},       \tag{11br15}
\]

and may be refined so that every rational argument has reduced denominator
coprime to ten.  More generally, for reduced \(x=a/b\in(0,1)\), one can
choose a rational \(u=c/d\) near \(x/2\) so that

\[
 \arctan x=\arctan u+
 \arctan\!\left({ad-bc\over bd+ac}\right),               \tag{11br16}
\]

both child denominators are coprime to ten, and both child arguments are
less than \(2x/3\).  At recursion depth \(r\), an alternating Taylor bracket
with any fixed first-omitted odd exponent \(R\ge5\) therefore has width

\[
 W_{R,r}<{4C_0X_0^R\over R}
          \left[2(2/3)^R\right]^r\longrightarrow0,         \tag{11br17}
\]

while its base-ten preperiod remains \(O(\log R)\) for each finite tree.
This is a genuine rational-approximation improvement.  It does not provide
phase steering: at a fixed shift the nested intervals converge to the one
cell already containing \(10^s\pi\), and different split trees are affinely
coupled shadows of that same point.  The independently audited `proof sketch`,
exact replay, and bounded 2026-08-12 literature comparison are
[`machin_angle_splitting_attack.md`](work/ultrapi-resume/machin_angle_splitting_attack.md),
[`machin_angle_splitting_check.py`](work/ultrapi-resume/machin_angle_splitting_check.py),
and
[`machin_angle_splitting_independent_audit.md`](work/ultrapi-resume/machin_angle_splitting_independent_audit.md).

The complementary \(1/2+1/3\) arctangent identity fails for an exact and
different reason.  For \(R=4K+3\), let

\[
 E_K=4\sum_{\substack{1\le r\le R\\r\ {\rm odd}}}
 {\chi_4(r)\over r}\left(2^{-r}+3^{-r}\right).
                                                               \tag{11br18}
\]

Alternating-series bounds enclose \(\pi\) with width

\[
 W_K={4\over(R+2)2^{R+2}}+{4\over(R+2)3^{R+2}}.          \tag{11br19}
\]

The last \(2^{-R}\) term is the unique two-adic minimum.  T67 now proves
exactly

\[
 v_2(E_K)=2-R,qquad
 v_2(\operatorname{den}E_K)=R-2.                         \tag{11br20}
\]

The five-primary denominator exponent is no larger, hence \(R-2\) is the
complete decimal preperiod.  At its first post-transient position,

\[
 10^{R-2}W_K
 ={5^R\over100(R+2)}\left(1+(2/3)^{R+2}\right)>{1\over10}.
                                                               \tag{11br21}
\]

Thus for every nonempty word length the bracket is already wider than a
whole decimal cylinder, and remains wider thereafter.  The independently
audited multiband law still yields
\(\log\operatorname{rad}_{(6)}(\operatorname{den}E_K)=R+o(R)\) at
`proof sketch` level, but none of that post-transient prime orbit can certify
even one digit of \(\pi\).  Only the dyadic transient remains, where locating
the selected numerator is again the original fixed-π cylinder problem.
The T67 core is `machine-checked`; the multiband extension remains a
`proof sketch`.  The formal report, corrected exploratory report, exact
replays, and independent audits are
[`t67_two_three_arctan_shadow_report.md`](work/ultrapi-resume/t67_two_three_arctan_shadow_report.md),
[`t67_independent_audit.md`](work/ultrapi-resume/t67_independent_audit.md),
[`euler_two_three_attack.md`](work/ultrapi-resume/euler_two_three_attack.md),
[`euler_two_three_check.py`](work/ultrapi-resume/euler_two_three_check.py),
and
[`euler_two_three_independent_audit.md`](work/ultrapi-resume/euler_two_three_independent_audit.md).

The identity \(\sin\pi=0\) gives an even sharper circularity certificate. If
\(q_n=10^n\), \(p_n=\lfloor q_n\pi\rfloor\), and
\(x_n=\{q_n\pi\}\), then

\[
 x_n=q_n\arcsin\!\left(\sin {p_n\over q_n}\right),\qquad
 0\le x_n-q_n\sin(p_n/q_n)\le{1\over6q_n^2}.               \tag{11bs}
\]

Thus the normalized sine sample exactly recovers the unknown decimal tail.
For a forbidden word \(w\), all admissible truncation numerators form a set
\(S_w\) with \(\sum_{a\in S_w}a^{-1}<\infty\); consequently a nonzero
canonical product of order below one vanishes on all of \(S_w\). These nodes
are not an entire-function uniqueness set. The exact all-path automaton has a
Mahler matrix recursion, but it aggregates all legal paths and does not select
the path of \(\pi\). This `literature-checked`/`proof sketch` obstruction is
recorded in
[`sin_automaton_attack.md`](work/ultrapi-resume/sin_automaton_attack.md).

Exact GMP-rational computation through \(N=5000\), labeled only
`experiment`, found no identity-check, positivity, or monotonicity failure;
the rational codes covered all one-digit cells by \(N=31\), all two-digit
cells by \(N=604\), and 997 of 1,000 three-digit cells by \(N=5000\), missing
373, 483, and 500. They covered 3,952 four-digit cells. These finite counts
are compatible with random-looking behavior but prove no future hit or
asymptotic law. The exact run also verified the T44 exponent and T45 local
criterion at every tested row. The tempting equality
\(\Lambda_N/\operatorname{den}(\Delta_N)=3\) is refuted already at \(N=6\),
where the quotient is \(87=3\cdot29\); squarefree and one-extra-prime variants
also fail. Infinite extra-cancellation progressions such as
\(19\mid g_{7+57t}\) follow by elementary periodic congruences, but likewise
provide no archimedean distribution. Full deterministic artifacts are in
[`experiments/REPORT.md`](work/ultrapi-resume/experiments/REPORT.md).

T39 records the exact recurrent consequence of T37 rather than leaving it
implicit.  Eventual equality of two finite-alphabet streams preserves each
recurrent value in both directions, hence preserves the recurrent-value set
and its exact cardinality.  Under the same explicit source-level
`IrrationalityMeasureBelow Real.pi 8` premise,

\[
 \operatorname{Rec}(\operatorname{machinBlockCode}_m)
 =\operatorname{Rec}(\operatorname{piCylinderCode}_m),\qquad
 m+1\le\#\operatorname{Rec}(\operatorname{machinBlockCode}_m)
 \quad(m>0). \tag{11aa}
\]

The second conclusion combines the exact transfer with T31/T34 and removes
T34's earlier factor-two loss for this explicit Machin stream.  T39 also
proves that “every one of the \(10^m\) cells recurs” is equivalent for the two
streams; neither side is established.  Thus (11aa) is still linear recurrent
complexity, not prescribed-cell coverage.

T41 closes the final logical quantifier gap.  Occurrence of every finite word
is equivalent to occurrence arbitrarily late, and the fixed-length word-value
map is injective even for words with leading zeros.  It machine-checks

\[
 \mathrm{V1}
 \iff \forall m\ \forall a<10^m:\
   a\in\operatorname{Rec}(\operatorname{piCylinderCode}_m),
\tag{11ab}
\]

including \(m=0\).  Under the same explicit source-level
`IrrationalityMeasureBelow Real.pi 8` premise, T39 then turns (11ab) into the
exact rational target

\[
 \mathrm{V1}
 \iff \forall m\ \forall a<10^m:\
   a\in\operatorname{Rec}(\operatorname{machinBlockCode}_m).
\]

This is an exact equivalence, not a proof of either side.  In particular, the
published irrationality-measure input provides the representation transfer
only; it does not supply all-cell recurrence.

This is a genuine exact rational-coding advance, not a distribution theorem.
The approximant changes with \(N\), and its proved recurrence merely computes
   the same moving prefix more efficiently.  Nothing in T36--T43 proves the
   all-cell recurrence side of (11ab), so V1 remains a `conjecture`.

There is a tempting block-renormalization of this recurrence, but a sharp
separator shows that it is not enough.  Put
\(t_n=10^n(\pi-A_n)\) and
\(\delta_{n+1}=c_{n+1}(5/8)^{n+1}\).  Exact iteration gives

\[
 u_{n+r}=\{10^r u_n+B_{n,r}\},\qquad
 B_{n,r}=\sum_{j=1}^r10^{r-j}\delta_{n+j}
        =10^rt_n-t_{n+r}.
\]

In fact this is an exact time-dependent coboundary, not a new autonomous
source of mixing.  On the circle let
\(F_n(x)=10x+\delta_{n+1}\) and \(H_n(x)=x+t_n\).  Since
\(\delta_{n+1}=10t_n-t_{n+1}\),

\[
 H_{n+1}\circ F_n=T\circ H_n,\qquad T(x)=10x,
\]

and the analogous \(r\)-step identity holds.  For the actual BBP sequence,
\(H_n(u_n)=\{10^n\pi\}\) and already
\(H_0(u_0)=\pi-3\).  Thus generic expanding-map dynamics for the perturbed
recurrence is exactly the original decimal orbit in moving coordinates.
“Non-Gosper” can only say that this transfer is not rational/hypergeometric;
it cannot create statistical independence between its boundary term and the
orbit.

Scaling the forcing by \(\lambda\) does not create a deformation argument:
the conjugated seed is simply
\(\theta_\lambda=u_0+\lambda(\pi-47/15)\pmod1\).  Borel's theorem gives
normality for almost every parameter, while rational, eventually periodic
seeds occur for a countable dense set of parameters, so neither continuity
nor order singles out \(\lambda=1\).  Likewise the nonautonomous inverse
branches are just rotated ordinary decimal preimages under the maps \(H_n\);
their apparent specification tree contains no extra mixing theorem.

The BBP tail has

\[
 t_n={ (5/8)^n\over64n^2}\bigl(1+O(n^{-1})\bigr),\qquad
 -\log_{10}t_n=n\log_{10}(8/5)+2\log_{10}n+\log_{10}64+o(1).
\]

Since \(\log_{10}(8/5)\) is irrational, Weyl's criterion with summation by
parts makes the fractional parts of the expression on the right
equidistributed.  Taking
\(r_n=\lfloor-\log_{10}t_n\rfloor+k\) shows, for each fixed integer
\(k\), that the translations \(B_{n,r_n}\) are dense in
\([10^{k-1},10^k]\); varying \(k\le0\) reaches shifts arbitrarily close to
every point of the circle.  This does **not** make \(u_n\) dense, because
\(u_n\) and \(B_{n,r}\) come from the same tail and may cancel in a coupled
way.

An explicit positive moment model proves that this coupling is a real wall.
Define

\[
 c_n^\dagger=\int_0^1x^{8n}(1-x)(16-x^8)\,dx
 ={16\over(8n+1)(8n+2)}-{1\over(8n+9)(8n+10)}.
\]

These coefficients are positive, strictly decreasing, completely monotone,
and satisfy
\(c_n^\dagger=15/(64n^2)-29/(512n^3)+O(n^{-4})\), matching the actual BBP
leading coefficient and its \(x^{8n}\) moment geometry.  Nevertheless

\[
 {c_n^\dagger\over16^n}=Q_n-Q_{n+1},\qquad
 Q_n={16^{1-n}\over(8n+1)(8n+2)}.
\]

Thus \(\sum_{n\ge0}c_n^\dagger/16^n=8\), and for
\(A_N^\dagger=\sum_{n=0}^Nc_n^\dagger/16^n\),

\[
 t_N^\dagger=10^N(8-A_N^\dagger)
 ={(5/8)^N\over(8N+9)(8N+10)},\qquad
 \{10^NA_N^\dagger\}=1-t_N^\dagger\longrightarrow0.
\]

The same dense-mantissa and critical-translation argument therefore coexists
with a singleton omega-limit set.  This independently replayed calculation
is a `proof sketch`, not a Lean declaration.  It preserves positivity,
complete monotonicity, the moment structure, and the exact leading tail
scale; its pole classes telescope.  Hence a successful BBP proof must use
more than tail asymptotics and dense rescaled translations.

Even adding *failure* of Gosper telescoping is insufficient.  A sharpened
positive-moment separator starts from Bailey's base-16 zero relation (111),
but the identity needed here has an elementary independent proof.  Put

\[
 Z(x)=8-8x-4x^2-8x^3-2x^4-2x^5+x^6,\qquad
 z_n=\int_0^1x^{8n}Z(x)\,dx.
\]

Direct partial fractions give

\[
 {16Z(x)\over16-x^8}
 ={16x\over x^2-2}-{16(x-1)\over(x-1)^2+1};
\]

the two integrals on \([0,1]\) are \(-8\log2\) and \(+8\log2\), so
\(\sum z_n/16^n=0\) exactly.  With

\[
 P(x)=(1-x)(16-x^8),\quad
 G(x)=(x^8-1)Z(x)+{16\over105}P(x),\quad
 W(x)=P(x)+{G(x)\over100},
\]

one has \(\sum_n16^{-n}\int_0^1x^{8n}G(x)\,dx=0\).
Moreover \(G=(1-x)H\) and the exact coefficient bound
\(\sum|[x^j]H|=14218/105\) shows
\(W(x)>0\) on \([0,1)\), because
\(16-x^8+H(x)/100\ge15-14218/10500>0\).
Define

\[
 c_n^\#={2625\over2839}\int_0^1x^{8n}W(x)\,dx.
\]

Then \((-1)^k\Delta^kc_n^\#>0\) for every \(k,n\), so the coefficients are
strictly positive, strictly decreasing, and completely monotone.  They are a
single rational function of \(n\), have
\(c_n^\#=15/(64n^2)+O(n^{-3})\), and satisfy

\[
 \sum_{n\ge0}{c_n^\#\over16^n}={21000\over2839}.
\]

Consequently their perturbed decimal recurrence shadows the eventually
periodic orbit of this rational total and has a finite omega-limit set, while
retaining the same leading BBP tail scale.  Yet
\(c_n^\#/16^n\) has no hypergeometric antidifference: in the pole class
\(-3/8+\mathbb Z\), the two endpoint residues inherited from
\(z_{n+1}-z_n\) have ratio \(-1\), whereas a rational certificate
\(T(n+1)/16-T(n)\) forces ratio \(-1/16\); the other terms have no pole in
that class.  Gosper completeness then excludes such a certificate.

This is an independently algebra-checked `proof sketch`, not a Lean
declaration.  Bailey's compendium reports the underlying zero relation as a
computer-discovered identity, so the partial-fraction calculation above is
included rather than treating its numerical check as a proof:
[Bailey, *A Compendium of BBP-Type Formulas for Mathematical Constants*,
formula (111), 2023](https://www.davidhbailey.com/dhbpapers/bbp-formulas.pdf).
The separator leaves the exact four-pole BBP coefficient and its global value
arithmetic—not generic hypergeometric or moment properties—as the only
remaining distinguishing input in this route.

An exact all-index divisibility calculation explains why tail control alone
does not finish the argument. Put \(C_N=16^NA_N\). Then

\[
 \begin{aligned}
  &\mathcal R_{-1}=1,\quad \mathcal P_{-1}=0,\\
  &\mathcal R_N=d_N\mathcal R_{N-1},\qquad
   \mathcal P_N=16d_N\mathcal P_{N-1}+a_N\mathcal R_{N-1},
 \end{aligned}
\]

where \(a_N=120N^2+151N+47\) and
\(d_N=(2N+1)(4N+3)(8N+1)(8N+5)\). Direct induction gives the exact rational
recurrence

\[
 C_N={\mathcal P_N\over\mathcal R_N},\qquad
 A_N={\mathcal P_N\over2^{4N}\mathcal R_N}.
\]

The valuation theorem is

\[
 v_2(C_N)=v_2(N+1),\qquad
 v_2\!\left(\operatorname{den}(A_N)\right)=4N-v_2(N+1). \tag{11f}
\]

Here denominators are reduced and \(v_2\) is extended to rationals. A concise
2-adic proof is available. Regard

\[
 c(x)={120x^2+151x+47\over
 (2x+1)(4x+3)(8x+1)(8x+5)},\qquad
 F(x)=\sum_{j\ge0}16^jc(x-j)
\]

as analytic functions on \(\mathbb Z_2\). Since

\[
 c(-1-j)=-{4\over8j+7}+{1\over8j+3}
             +{1\over2(4j+1)}+{1\over2(2j+1)},
\]

termwise formal integration reduces \(F(-1)\) to the integral from 0 to 1
of

\[
 f(x)={x^2+x-4x^6\over1-16x^8}+{x\over1-16x^4}.
\]

In \(\mathbb Q_2(i)\), direct differentiation verifies the analytic primitive

\[
 {1\over16}\log(2R(x))+{1\over8i}\log\!\left({Q(x)\over Q(0)}\right),
\]

where

\[
 R(x)={(x^2-x+1/2)(8x^4+6x^2+1)\over
 16x^6+16x^5-4x^4-12x^3-4x^2+2x+1},\qquad
 Q(x)={1+i(2x-1)\over1-i(2x-1)}.
\]

The relevant normalized 2-adic logarithms converge on the corresponding
Tate-algebra units (in particular, \(2R-1\) is divisible by 4 throughout the
unit disk, and \(iQ-1=2x(i-1)/(1-i(2x-1))\) lies in the square of the
uniformizer ideal). Also \(R(0)=R(1)=1/2\), \(Q(0)=-i\), and \(Q(1)=i\),
while the logarithm vanishes on roots of unity. Hence \(F(-1)=0\). Moreover
\(F(-1+y)\equiv y\pmod2\), so
\(F(x)=(x+1)G(x)\) with \(G(x)\equiv1\pmod2\). Finally,

\[
 C_N=\sum_{j=0}^{N}16^jc(N-j),\qquad
 F(N)-C_N\in2^{4(N+1)}\mathbb Z_2,
\]

which proves (11f), since \(v_2(N+1)<4(N+1)\). In particular, for \(N\ge5\)
the reduced denominator of the rational diagonal term has exact dyadic
exponent

\[
 v_2\!\left(\operatorname{den}((10^N-16)A_N)\right)
 =4N-4-v_2(N+1). \tag{11g}
\]

The all-depth step is no longer based on finite pattern recognition.  A
separate primary report rewrites the reflected coefficient as the convergent
2-adic null series

\[
 \sum_{j\ge0}16^j\left(
 {1\over8j+2}+{1\over8j+3}+{2\over8j+4}-{4\over8j+7}
 \right)=0.
\]

Its logarithmic primitive has torsion endpoints and yields
\(F(X)=XU(X)\) with \(U(X)\equiv1\pmod2\).  Independent audit rederived the
Tate convergence, termwise primitive, tail separation, and every valuation;
it also corrected the general-\(c\) wording to require sufficiently large
depth *and* exponent.  The `proof sketch` and two independent finite replays
are
[`bbp_all_depth_two_adic_attack.md`](work/ultrapi-resume/bbp_all_depth_two_adic_attack.md),
[`bbp_all_depth_two_adic_check.py`](work/ultrapi-resume/bbp_all_depth_two_adic_check.py),
[`bbp_all_depth_two_adic_independent_audit.md`](work/ultrapi-resume/bbp_all_depth_two_adic_independent_audit.md),
and
[`bbp_all_depth_two_adic_independent_check.py`](work/ultrapi-resume/bbp_all_depth_two_adic_independent_check.py).
They prove no estimate for the nonzero circle residue and therefore no fixed
return or V1.

There is also an exact odd-prime subsequence. For \(s\ge1\), set

\[
 N_s=\begin{cases}(5^s-5)/8,&s\text{ odd},\\
                   (5^s-1)/8,&s\text{ even}.
     \end{cases}
\]

Then \(v_5(C_{N_s})=-s\). At the last summand, the unique large factor is
\(8N_s+5=5^s\) for odd \(s\), or \(8N_s+1=5^s\) for even \(s\); in the
even case the common factor in \(4N_s+3\) is canceled exactly once by the
numerator (indeed \(N_s\equiv3\pmod{25}\) and the numerator is
\(5\pmod{25}\)). Every earlier summand has 5-adic valuation at least
\(-(s-1)\).
The only two denominator factors that can be simultaneously divisible by 5
are \(4k+3\) and \(8k+1\); their difference relation
\(2(4k+3)-(8k+1)=5\), together with
\(120k^2+151k+47\equiv k+2\pmod5\), supplies the needed cancellation.
The non-Archimedean minimum is therefore unique. For \(s\ge2\),
\(N_s\ge3\) and \(10^{N_s}-16\equiv-1\pmod5\), so the factor \(5^s\)
survives in the reduced denominator of the diagonal rational approximation
as well. The edge case \(s=1,N_s=0\) has \(v_5(C_0)=-1\), but its multiplier
is \(-15\) and does cancel that single factor.

The surviving odd denominator is in fact exponential at every large index.
Let \(D_N\) be the reduced odd denominator of \(C_N\), and let \(B_N\) be
the squarefree product of the primes in the disjoint sets

\[
 \left\{p:{8N+5\over3}<p<4N\right\},\qquad
 \left\{p:4N+5<p<8N,\ p\equiv1,5\pmod8\right\}. \tag{11h}
\]

Every prime \(p>5\) in (11h) occurs in exactly one of the four linear
denominator factors among \(c_0,\ldots,c_N\), and then only to the first
power. For the first interval, \(3p>8N+5\) and
\(p>2N+1\); the residue classes \(1,3,5,7\pmod8\) select respectively
\(8k+1\), \(4k+3\), \(8k+5\), \(4k+3\). For the second interval, only the
selected \(8k+1\) or \(8k+5\) can reach \(p\). The four exact resultants

\[
 6,\quad20,\quad1920,\quad-32
\]

of \(120k^2+151k+47\) against
\(2k+1,4k+3,8k+1,8k+5\), respectively, show that no such \(p>5\) divides
the numerator. Thus one summand has valuation \(-1\) and every other
summand is a \(p\)-adic integer, proving \(B_N\mid D_N\). The prime number
theorem and its progression form modulo 8 then give

\[
 \log B_N=\left({10\over3}+o(1)\right)N. \tag{11i}
\]

After multiplication by \(10^N-16\), the surviving odd denominator is at
least

\[
 {B_N\over\gcd(B_N,10^N-16)}>{B_N\over10^N}
 =\exp\!\left(\left({10\over3}-\log10+o(1)\right)N\right), \tag{11j}
\]

whose exponent is \(1.030748\ldots\). This is independent of the surviving
dyadic exponent in (11g).

The remaining archimedean problem can be written as one exact moving CRT
residue. Let \(r_N=v_2(N+1)\),

\[
 p_N={\mathcal P_N\over2^{r_N}},\quad
 g_N=\gcd(p_N,\mathcal R_N),\quad
 \bar p_N={p_N\over g_N},\quad
 \bar R_N={\mathcal R_N\over g_N}.
\]

For \(N\ge5\), put
\(M_N=2^{N-4}5^N-1\) and
\(h_N=\gcd(M_N,\bar R_N)\). The diagonal rational in lowest terms is exactly

\[
 (10^N-16)A_N=
 { (M_N/h_N)\bar p_N\over
   2^{4N-4-r_N}(\bar R_N/h_N)}. \tag{11k}
\]

Thus all valuation information determines the increasingly fine rational
grid, but V1 asks where the numerator of (11k) sits on that grid. None of the
2-adic, 5-adic, or prime-product arguments controls its least absolute
residue.

The numerator is unusually simple at every selected prime, but this still
does not control the real residue.  Let \(S_N\) be the prime set in (11h).
If \(p\in S_N\), multiplying by the unique denominator factor \(p\) and
reducing in \(\mathbb F_p\) gives

\[
 pA_N\equiv\gamma_p\pmod p,\qquad
 \gamma_p=\begin{cases}
 4,&p\equiv1,5\pmod8,\\
 -2,&p\equiv3,7\pmod8.
 \end{cases} \tag{11l}
\]

The powers \(16^{-k}\) in the unique summand collapse by Euler's criterion
and Fermat's theorem; no nontrivial multiplicative character survives.  If

\[
 Z_N=\sum_{p\in S_N}{\gamma_p\over p},
\]

then \(A_N-Z_N\) is \(p\)-integral for each selected \(p\), while the
archimedean phase of this CRT proxy factors as

\[
 e((10^N-16)Z_N)
 =\prod_{p\in S_N}e\!\left({\gamma_p(10^N-16)\over p}\right),
 \qquad
 Z_N={\log6+o(1)\over\log N}. \tag{11m}
\]

The last asymptotic is Mertens' theorem in the four residue classes modulo
8.  Its ordinary error, after multiplication by \(10^N\), is far too large
to locate a fractional part.  More decisively, all of the local data in
(11l) admit a uniform archimedean separator.  Let

\[
 \alpha={1\over10}+\sum_{r\ge2}10^{-r!}.
\]

This \(\alpha\) is Liouville-transcendental, every decimal tail lies in
\([0,1/9]\), and \(\{16\alpha\}\in(3/5,7/9)\).  Hence
\(\|(10^N-16)\alpha\|\ge2/9\) for every \(N\).  Put
\(K_N=4N-v_2(N+1)\), choose an odd \(H_N\) coprime to \(B_N\) with

\[
 H_N\ge15\,2^{v_2(N+1)}(N+1)^2,
 \qquad Q_N=2^{K_N}B_NH_N,
\]

and use CRT to impose

\[
 U_N\equiv1\pmod2,\qquad
 U_N\equiv\gamma_p(Q_N/p)\pmod p\quad(p\mid B_N).
\]

The admissible integers form a lattice of step \(2B_N\), so a translate can
be chosen with

\[
 \left|{U_N\over Q_N}-\alpha\right|
 \le {1\over2^{K_N}H_N}
 \le {16^{-N}\over15(N+1)^2}.
\]

After reduction, \(U_N/Q_N\) retains the exact dyadic exponent \(K_N\),
every selected prime, and all residues (11l), yet

\[
 \left\|(10^N-16){U_N\over Q_N}\right\|
 \ge {2\over9}-{(5/8)^N\over15(N+1)^2}. \tag{11n}
\]

This independently replayed `proof sketch` proves that transcendence of the
limit, BBP-scale approximation, exact dyadic valuation, exponential odd
denominators, and every selected local numerator residue still do not imply
the diagonal limit in (11c).  Any successful argument must exploit the exact
global BBP recurrence and its coupled archimedean phase.

A separate exact pole-class argument retires ordinary telescoping. The
partial fractions are

\[
 c(k)={4\over8k+1}-{1\over8k+5}
      -{1\over2(4k+3)}-{1\over2(2k+1)}.
\]

Its four poles occupy distinct classes modulo \(\mathbb Z\). If a rational
function \(T(k)\) satisfied

\[
 {T(k+1)\over16}-T(k)=c(k),
\]

then in each pole class the finite pole set of \(T\) would produce two
uncancelled endpoint poles under the difference operator, whereas \(c\) has
only one. Hence no such rational \(T\) exists. Gosper's reduction shows that
a hypergeometric antidifference for \(16^{-k}c(k)\) would yield precisely
such a rational certificate, so there is no Gosper/hypergeometric collapse.
This is a `proof sketch`; hypergeometric tail formulae still exist, but they
do not simplify the diagonal residue.

As a controlled `experiment`, exact rational iteration of (11k) through
\(N=5000\), excluding \(N=0\), found successive record nearest-integer norms
at \(N=1,2,5,1558,3723\). The last two are approximately
\(5.71788\cdot10^{-5}\) and \(6.92495\cdot10^{-6}\). This finite decrease is
compatible with the required liminf, with a positive liminf below the tested
scale, or with irregular future behavior; it proves none of them.

Equations (11f)--(11n), the 5-adic subsequence, the displayed analytic
identities, the local-residue separator, and the pole-class obstruction are
independently symbolically
replayed `proof sketch`; they are not Lean declarations. The asymptotic input
in (11i) is the classical prime number theorem in arithmetic progressions;
a standard source is
[Davenport, *Multiplicative Number Theory*](https://link.springer.com/book/9780387950976).
These results show that the BBP multiplier cancels only a fixed four dyadic
powers (plus the intrinsic \(v_2(N+1)\)) and leaves exponentially many
denominator bits even after arbitrary odd-factor cancellation. They do
**not** bound the real moving residue away from or toward an integer: a large
reduced denominator is not an equidistribution estimate.

If
\(\tau_N=16^N(\pi-A_N)\), then
\(N^2\tau_N\to1/64\); conversion by
\(10^{4N}=625^N16^N\) magnifies that omitted tail by \(625^N\). A synchronized
Machin truncation has the same moving-residue obstruction: along
\(K=(5^r-1)/2\), its reduced denominator has 5-adic valuation \(5^r+r\),
while \(10^n-16\equiv-1\pmod5\).

The BBP identity and Lagarias's perturbed-remainder theorems are
`literature-checked`; equations (11a)--(11c), their specialization above, and
the valuation audit are `proof sketch`, not Lean declarations. Primary sources are
[BBP](https://doi.org/10.1090/S0025-5718-97-00856-9),
[Bailey--Crandall](https://doi.org/10.1080/10586458.2001.10504441), and
[Lagarias](https://doi.org/10.1080/10586458.2001.10504456). Lagarias
explicitly records that the relevant recurrence framework has no known
bridge to Furstenberg's problem. The 2024 attempted modular shortcut is also
not usable: its corrected version retracts that step
([Zudilin, v2](https://arxiv.org/abs/2409.10097v2)).

There is one fresh unconditional spread theorem, but it does not supply that
bridge. Theorems 1.1 and 1.3 of
[Chen--Ye--Zheng, 2026](https://arxiv.org/abs/2604.14036v1) apply literally
to \(x_k=\pi10^k\): take \(n=1\), \(\xi_1=\pi\), \(p_1=10\), and \(q_1=1\).
The paper allows \(q_1=1\), and irrationality of \(\pi\) is its required
alternative hypothesis.  Its Theorem 1.3 also applies with recurrence
polynomial \(R(X)=X-10\) and constant coefficient \(F=\pi\notin\mathbb Q\);
since \(L(R)=11\), it gives the fixed-\(\pi\) bound

\[
 \limsup_{k\to\infty}\|10^k\pi\|\ge {1\over11}.
\]

Besides infinitude of \(\omega_{10}(\pi)\), Theorem 1.1 gives

\[
 \forall M\ge1\ \exists l\ge0:\quad
 \omega\bigl((\{10^{kM+l}\pi\})_{k\ge1}\bigr)
 \text{ is not contained in any circle arc of length }<1/10. \tag{11e}
\]

The source and this specialization are `literature-checked`. Since
\(d_{\mathbb R/\mathbb Z}(u_n,\{10^n\pi\})\to0\), the elementary convergent
subsequence argument transfers both the infinite-limit-set statement and
(11e) to the rational BBP recurrence; that transfer is a `proof sketch`.
This rules out concentration in an arbitrarily short arc even after passing
to every fixed arithmetic sampling scale. It still chooses the residue
class \(l\), says nothing about any prescribed arc, and is compatible with
omitting a specified decimal cylinder. It therefore does not prove even one
new prescribed word occurrence.

An exact Sturmian separator shows that no combinatorial strengthening is
hidden here. Let \(f=0100101001\ldots\) be the Fibonacci word and

\[
 \beta_2=\sum_{j\ge0}2f_j10^{-j-1}=0.0200202002\ldots .
\]

This irrational decimal uses only `0` and `2` and has factor complexity
\(p_{\beta_2}(m)=m+1\). Chen--Ye--Zheng therefore gives (11e) for
\(\beta_2\) at every \(M\), although the digit-`1` cylinder is never hit.
Moreover every decimal tail lies in \([0,2/9]\), while
\(1/50\le\beta_2\le1/45\), so
\(16\beta_2\in[8/25,16/45]\) and hence
\(16\beta_2\notin X_{\beta_2}\). Thus (11e) implies neither a factor-count
improvement over Morse--Hedlund nor the missing multiplication-by-16
invariance. This separator is a `proof sketch`; its Sturmian input is the
same source-pinned Fibonacci fact used below.

### Exact transfer cost for rational approximations

For

\[
S_N(h;\alpha)=\sum_{0\le j<N}e^{2\pi i h10^j\alpha},
\]

the elementary Lipschitz estimate gives

\[
 |S_N(h;\alpha)-S_N(h;\beta)|
 \le {2\pi|h||\alpha-\beta|\over9}(10^N-1). \tag{12}
\]

Uniformly for \(0<|h|\le2q\), allocating only \(1/(48q)\) of normalized
error therefore requires

\[
 |\alpha-\beta|
 \le {3N\over64\pi q^2(10^N-1)}. \tag{13}
\]

Thus termwise transfer to the T19 window needs essentially \(N\) correct
decimal digits. Combining (13), the published exponent-8 consequence of the
irrationality-measure bound, and only a generic square-root Gauss bound for a
full rational period produces incompatible scales: the modular estimate
needs a period longer than \(48q\sqrt\ell\), while transfer over that period
requires exponentially finer accuracy than \(\ell^{-8}\). This rules out
that specific package--absolute termwise transfer plus a generic square-root
full-period estimate--not special-numerator cancellation or every rational
method.

The standard secondary identities do not repair the scale:

\[
 |S_N(h;\alpha)|^2
 =N+2\operatorname{Re}\sum_{r=1}^{N-1}
   S_{N-r}\bigl(h(10^r-1);\alpha\bigr), \tag{14}
\]

so even the first van der Corput correlation multiplies the frequency by at
least \(9\), and

\[
 |S_N(10^t h;\alpha)-S_N(h;\alpha)|\le2t. \tag{15}
\]

Equation (15) simplifies the ten-divisible frequencies only; \(90\%\) of the
positive integer frequencies are 10-adically primitive.

The fresh rational audit closes a seemingly favorable fast-decimal family
more sharply.  For the odd Abrarov--Quine two-term Machin truncation
\(\theta_E\), \(E\ge5\), exact alternating-tail and 2-adic bookkeeping gives
the `proof sketch`

\[
 {30\over(E+2)10^{E+2}}<|\pi-\theta_E|
 <{32\over(E+2)10^{E+2}},\qquad v_2(\operatorname{den}\theta_E)=E-5.
\]

Combining the lower error bound with (13) forces

\[
 10^{N-E}<{N(E+2)\over17q^2}.
\]

Consequently, after the unavoidable decimal transient, the usable coprime
periodic tail has length only \(O(\log N)=o(N)\).  Even perfect cancellation
on that tail leaves the \(1-o(1)\) pretransient prefix requiring essentially
the original T19 estimate.  Chudnovsky and AGM truncations do not evade this
calculation by multiplicative order: before rationalization they lie in
radical extensions, so their real-character orbits are not finite-period
modular orbits.  This is a method-specific obstruction, sourced from the
[Abrarov--Quine formula](https://arxiv.org/abs/1706.08835v3) and the dated
local audits [`T79`](work/theory/pi-lacunary-near-return-sparsity/library/t79/REPORT.md)
and [`T85`](work/theory/pi-lacunary-near-return-sparsity/library/t85/REPORT.md),
not a theorem excluding every rational approximation strategy.

### Why a tunable convergent does not itself force digits

Let \(P_m/D_m\) be a rational approximation with
\(0<\pi-P_m/D_m<E_m\). A length-\(k\) block with integer code
\(a\in\{0,\ldots,10^k-1\}\) is certified at position \(n\) only if the
moving residue

\[
 X_{m,n}=P_m10^{n+k}\pmod{D_m10^k}
\]

falls in the moving interval

\[
 [aD_m,(a+1)D_m-10^{n+k}D_mE_m). \tag{16}
\]

This is not a freely selectable congruence modulo \(10^k\); it is a
prescribed residue in a modulus that changes with the approximation index.
There is an exact circularity check. For any nested rational brackets
\([L_m,U_m]\ni\pi\) with \(U_m-L_m\to0\), the union of all block labels whose
scaled bracket \(10^n[L_m,U_m]\) fits inside a decimal cylinder is exactly the
actual block language of \(\pi\). One inclusion follows because the bracket
contains \(\pi\). The other follows because irrationality keeps every
\(10^n\pi\) off cylinder boundaries, so a sufficiently narrow bracket
eventually certifies each block that really occurs. Consequently, proving
that all safe residues in (16) occur is equivalent to V1 unless an independent
distribution theorem for those residues is supplied.

The exact test exposes the loss in the classical candidates.

- Wallis's lower approximant
  \(2^{4m+1}/((2m+1){2m\choose m}^2)\) has error of order \(1/m\), so only
  positions \(n=O(\log m)\) are certifiable while its coprime reduced modulus
  is exponential in \(m\).
- A Gregory partial sum again has error \(O(1/N)\) and a moving odd-lcm
  denominator. Euler corrections improve the error but do not supply a
  distribution theorem for the prescribed lcm residue.
- The audited two-term Machin truncation reaches linearly many digits, but its
  reduced denominator contains \(147153121^{\,2K-1}\). CRT exposes this
  growing coordinate but does not let one choose its numerator.

These are method-specific obstructions, not a proof that an undiscovered
arithmetic identity cannot settle V1.

### Stoneham's stable-prefix gap is explicit

Stoneham's 1983 rational-approximation program does not transfer its periodic
digit-distribution result to the digits stabilized to \(\pi/4\).  For his
Wallis approximants

\[
 r_n=\prod_{i=1}^n\left(1-(2i+1)^{-2}\right)
 =\frac{2^{4n}(n!)^3(n+1)!}{((2n+1)!)^2},
\]

Stirling's formula gives

\[
 r_n-\frac\pi4=\frac{\pi}{16n}+O(n^{-2}). \tag{17}
\]

Consequently the number \(S_n\) of stable leading decimal digits is only
\(O(\log n)\).  In Stoneham's decimal subsequence, his prime-power divisibility
conditions make the rational period \(\omega(q_n)=\Omega_q(n^2)\), whereas the
cited distribution theorem controls initial segments of length about
\(\omega(q_n)^{1/2+\eta}=\Omega_q(n^{1+2\eta})\).  Hence
\(S_n/\sqrt{\omega(q_n)}=O(\log n/n)\to0\): the guaranteed occurrence can lie
entirely in the unstable part of the rational expansion.

This is not merely a modern objection.  On p.277 Stoneham says that he cannot
tell whether `0123456789` occurs in the stable portion, and on p.278 identifies
exactly the missing stronger stable-prefix estimate.  Period normality plus
convergence therefore proves neither that example nor V1.  Source:
[Stoneham, 1983](https://doi.org/10.4064/aa-42-3-265-279) and the
[primary PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa42/aa4233.pdf).

### A forbidden-word automaton is not a digit generator

If a word \(w\) is absent, the decimal stream is a path in the finite
last-\((|w|-1)\)-symbol automaton recognizing the avoidance language. This
does not make the particular digit stream automatic or Mahler. Automatic
generation requires a finite decimation kernel controlling indices
\(10^e n+r\), whereas word avoidance supplies only local consecutive-index
constraints.

The quantifier mismatch has a concrete separator. Remove the first digit of
\(w\) from the alphabet and concatenate all finite words over the remaining
nine digits. The resulting stream avoids \(w\) but has at least \(9^n\)
length-\(n\) factors; an automatic sequence has only \(O(n)\) factor
complexity. Therefore the transfer matrix counting all allowed paths cannot
be reused as a Mahler equation for the one path formed by the digits of
\(\pi\). Euler's identity \(e^{i\pi}=-1\), Pólya--Carlson
natural-boundary results, and the standard automatic/Mahler value theorems do
not bridge this missing decimation hypothesis.

Euler's identity also sits on the wrong character group for the Fourier
route.  Decimal dynamics is on \(\mathbb R/\mathbb Z\), whose continuous
characters are \(x\mapsto e^{2\pi i h x}\) with integer \(h\).  The map
\(e^{ix}\) corresponds to the forbidden noninteger frequency
\(h=1/(2\pi)\) and does not descend to that circle.  Along the decimal orbit
it gives

\[
 \sum_{0\le j<N}e^{i10^j\pi}=N-2\qquad(N\ge1),
\]

since the first term is \(-1\) and every later term is \(1\).  Thus the one
algebraic exponential value supplies maximal off-lattice resonance, not the
integer-frequency cancellation needed by T19.  Taking a logarithm or a
noninteger power to return to the permitted characters simply reintroduces
\(\pi\) and a branch choice.  This is an exact `proof sketch` obstruction to
the direct Euler-identity route.

### Appearance time and positive-density gaps still do not imply coverage

The standard appearance length \(R'(m)\) is the shortest finite digit prefix
containing every length-\(m\) factor that occurs in the infinite word. With
the zero-based first starts used in T28,

\[
 R'(m)=L_m+m-1.
\]

Consequently, a bound \(L_m\le C_m p_\pi(m)\) would turn (28) into

\[
 {|S_{L_m}(h)|\over L_m}\le1-\frac1{32C_m}
\]

on at least \(10^m/16\) moving frequencies. This is the exact missing
appearance-ratio bridge. For every positive integer \(C_m\), the implication
is `machine-checked` in
[`T29T29AppearanceRatioRelativeGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean);
the premise is not proved for \(\pi\), and the conclusion still would not
prove V1.

A source-backed separator makes the limitation sharp. Let \(f\) be the
Fibonacci word fixed by \(0\mapsto01,\ 1\mapsto0\), and set
\(\beta=\sum_{j\ge0}f_j10^{-j-1}\). It omits digit `2` and has
\(p_\beta(m)=m+1\) for every \(m\). Cassaigne proves
\(\limsup R'(m)/m=\varphi+1\), so
\(\limsup L_\beta(m)/m=\varphi\):
[Cassaigne, 2008](https://doi.org/10.1051/ita:2008003). The word is Sturmian
([Bugeaud--Kim](https://doi.org/10.1090/tran/7378)), and
Adamczewski--Bugeaud's algebraic-complexity theorem therefore makes the
irrational number \(\beta\) transcendental:
[Annals, 2007](https://doi.org/10.4007/annals.2007.165.547).

Applying the generic selected-support argument behind T27 at
\(L_\beta(m)\) gives, for all sufficiently large \(m\), at least
\(10^m/16\) frequencies with

\[
 {|S_{L_\beta(m)}(h)|\over L_\beta(m)}
 \le1-\frac{m+1}{32L_\beta(m)}\le\frac{63}{64}.
\]

The exact power-of-ten shift calculation transports this fixed relative
saving up to a vanishing boundary error for each fixed shift, and the generic
T19 missing-cylinder resonance also holds. Nevertheless
\(p_\beta(m)=m+1\) exactly and V1 fails. The cited structural facts are
`literature-checked`; their assembly here is a `proof sketch`. It shows that
even transcendence, \(L_m=O(p(m))\), positive-proportion relative saving,
frequency transport, and empty-cell resonance cannot improve Morse--Hedlund
without a genuinely \(\pi\)-specific all-frequency input.

### The resonance and good-frequency sets need not intersect

Even a hypothetical intersection of T19's resonance witness with T28's
good-frequency set would not be contradictory. With

\[
 c_q={1\over24q}+{1\over12q^3},\qquad P=p_\pi(m),\qquad N=L_m,
\]

the two conclusions would only say

\[
 c_qN\le |S_N(h)|\le N-{P\over32}.
\]

The selected embedding gives \(P\le N\), so the upper endpoint is at least
\(31N/32\), whereas \(c_q\le1/8\), and \(c_q\le1/8000\) for \(m\ge3\).
The permitted interval is enormous. T25 transports only the additive gap,
giving \(N-|S_N(10^th)|\ge P/32-2t\), so it cannot close this numerical gap.

There is an exact finite-state decimal separator for the stronger hope that
the sets must at least meet. Let

\[
 \alpha={1\over81}=0.\overline{012345679}.
\]

At length three its nine factors are
`012,123,234,345,456,567,679,790,901`; hence \(P=L=9\), while `888` is
globally absent. For \(0\le j<9\),
\(\{10^j\alpha\}=(1+9j)/81\), so

\[
 |S_9(h;\alpha)|=
 \begin{cases}9,&9\mid h,\\0,&9\nmid h.\end{cases} \tag{31}
\]

Using T28's exact frequency indexing \(h=r+1\) with
\(r\in\operatorname{Fin}(1000)\), its selected-energy threshold is
\(P(P-3)/4=27/2\). Thus the generic T28 good set consists exactly of the
889 indices for which \(9\nmid h\). Every T19 resonance for (31) has
\(9\mid h\), and multiplication by 10 preserves that residue class modulo 9.
There is no intersection even though the appearance ratio is optimal
\(L/P=1\); on every good frequency the normalized sum is exactly zero.

The Fibonacci separator makes the same obstruction transcendental and
nonperiodic. Its \(P=m+1\) selected orbit tails all lie in \([0,1/9]\). For
every \(0\le t\le m\), midpoint rotation of the phase arc gives

\[
 \left|\sum_{i<P}e^{2\pi i10^t x_i}\right|
 \ge P\cos(\pi/9),\qquad
 E_{10^t}< {P^2\over8}.
\]

For \(m\ge5\), \(P\ge6\) and
\(P^2/8\le P(P-3)/4\). Hence every power-of-ten frequency index
\(10^t-1\), including the endpoint frequency \(10^m\), is excluded from
T28's final good set. At the same time, for every ambient prefix \(N\),

\[
 {|S_N(10^t;\beta)|\over N}\ge\cos(\pi/9),
\]

while every word containing digit `2` is absent. These deductions are
`proof sketch`, not new Lean declarations. They show that DFT positivity,
positive density, optimal appearance ratio, and power-of-ten transport cannot
be pigeonholed into V1; a successful intersection argument needs an extra
fixed-\(\pi\) property.

### Period, G/E-function, and Mahler boundary audit

The primary-source applicability facts in this subsection are
`literature-checked`; the deductions specialized below are `proof sketch`.
Although \(\pi=4\int_0^1(1+x^2)^{-1}\,dx\) is a
[Kontsevich--Zagier period](https://doi.org/10.1007/978-3-642-56478-9_39)
and is a G-value through \(4\arctan(1)\), the closest digit theorem for
G-functions works at sufficiently small rational arguments, with constants
depending on the fixed function, and concludes restricted equal-digit
repetition or rational-approximation bounds rather than all-word coverage:
[Fischler--Rivoal](https://doi.org/10.1007/s00229-017-0933-8).

A 2026 result is more directly applicable, but quantitatively much weaker
than a decimal-cylinder statement. In the paragraph after Theorem 3 of
[Fischler--Rivoal, *Transcendence of values of logarithms of
E-functions*](https://doi.org/10.1007/s00208-026-03374-z), every real
irrational simple zero \(\zeta\) of a nonpolynomial rational-coefficient
E-function satisfies an effective bound

\[
 \left|\zeta-{a\over b}\right|\ge \exp(-c b^d).
\]

Taking the E-function \(\sin z\) gives this theorem unconditionally for
\(\zeta=\pi\). At \(b=10^N\), however, the lower bound is
\(\exp(-c10^{dN})\), astronomically below the ordinary truncation error
\(10^{-N}\). It permits every numerator and therefore cannot distinguish a
prefix avoiding a fixed word. The corrected G-function theorem does apply to
the fixed identity
\(16\arctan(2z)-4\arctan(10z/239)\) at \(z=1/10\) only if ten exceeds its
function-dependent effective threshold, which the source does not establish;
varying the function to enlarge the denominator destroys the required
uniformity. Even the theorem's repetition conclusion is compatible with the
cube-free Thue--Morse decimal word, which omits digit 2. These and the nearby
E-value, logarithm, BBP, period, and restricted-numerator results are audited
in the dated primary-source report
[`special_values_digit_complexity_literature.md`](work/ultrapi-resume/special_values_digit_complexity_literature.md).
Its strongest missing input is a \(\pi\)-specific base-ten finite-state escape
theorem at scale \(10^{-N}\), not another scalar irrationality measure.

Two tempting ways to manufacture a ``small argument'' do not meet that
theorem's quantifiers. The half-angle identity

\[
 \pi=2^{r+1}\arcsin\!\left(\sin {\pi\over2^{r+1}}\right)
\]

uses an algebraic argument tending to zero, but Fischler--Rivoal's
power-denominator theorem requires a *rational* point \(a/b\); the algebraic
degree here grows with \(r\). Machin identities can instead express \(\pi\)
using very small rational arctangent arguments, but combining them into one
evaluation changes the G-function when the identity is changed. The required
lower bound on \(b\) depends on that fixed function, so sending the Machin
denominators to infinity is not a uniform argument. The representation
theorem in [Fischler--Rivoal, 2014](https://doi.org/10.4171/CMH/321)—every
real G-value is \(g(1)\) for a rational-coefficient G-function with
arbitrarily large convergence radius—does not remove this dependence. The
authors explicitly note in the digit paper that this construction gives no
control of coefficient-denominator growth, which is needed for their
constants. Thus neither rescaling \(g(Bz)\) and evaluating at \(1/B\), nor a
varying half-angle/Machin family, proves a restricted decimal approximation
bound for the single fixed number \(\pi\). Even such a bound would control
long repetitions, not coverage of arbitrary words.

There is a structural obstruction to transferring that representation to the
digit series. Put

\[
 D_\pi(z)=\sum_{n\ge1}d_nz^n.
\]

If \(D_\pi\) were D-finite over \(\overline{\mathbb Q}(z)\), the
finite-coefficient theorem of
[Bell--Chen](https://doi.org/10.1016/j.jcta.2017.05.002) would make it
rational over \(\overline{\mathbb Q}(z)\). Evaluation at \(z=1/10\)
would then make \(D_\pi(1/10)=\pi-3\) algebraic, a contradiction. Thus
the natural digit series is not D-finite and hence not a G-function. If its
Borel lift \(\sum d_nz^n/n!\) were D-finite, clearing the factorials in its
P-recursive coefficient relation would make \((d_n)\) P-recursive and
would make \(D_\pi\) D-finite. The lift is therefore not an E-function.
Pólya--Carlson also gives the unit circle as the natural boundary of
\(D_\pi\): its coefficients are integers, and irrationality rules out the
rational-function alternative.

The tempting lacunary Mahler series misses the target at a second, exact
place. For \(h\ge1\),

\[
 L_h(z)=\sum_{j\ge0}z^{h10^j},\qquad
 L_h(z)=z^h+L_h(z^{10}),\qquad
 S_N(h;\pi)=\sum_{j<N}z_\pi^{h10^j},\quad
 z_\pi=e^{2\pi^2 i}.
\]

But \(|z_\pi|=1\); the infinite series does not converge there because its
terms have modulus one, and its Hadamard gaps give the unit circle as a
natural boundary. Standard Mahler value theorems instead require an
algebraic point strictly inside the disk, as stated by
[Adamczewski--Faverjon](https://doi.org/10.1112/plms.12038).
Hermite--Lindemann and Siegel--Shidlovskii also do not apply to the
transcendental argument \(2i\pi^2\). This is an exact hypothesis audit,
not an impossibility theorem for every future boundary method.

The mismatch has a sharp separator. For the decimal Thue--Morse number
\(\alpha=0.011010011001\ldots\), Bugeaud's source-pinned theorem gives
\(\mu(\alpha)=2\); see the
[local audit](work/theory/pi-digits/library/t16/T16-decimal-thue-morse-countermodel.md)
and [primary DOI](https://doi.org/10.5802/aif.2666). Its digit series obeys
a Mahler equation and has a natural boundary, but every tail
\(x_j=\{10^j\alpha\}\) lies in \([0,1/9]\). Consequently

\[
 |S_N(1;\alpha)|\ge\Re S_N(1;\alpha)
 \ge N\cos(2\pi/9)
\]

for every \(N\), while the digit `2` never occurs. Transcendence, optimal
scalar irrationality exponent, a Mahler equation, and a natural boundary can
therefore coexist with permanent relative resonance and failure of V1.

### Forbidden-word survivor geometry makes the scalar wall exact

For a nonempty word \(w\), let \(K_w\) be the set of points whose decimal
orbit avoids the cylinder for \(w\). The KMP prefix automaton for \(w\) is a
primitive graph-directed system. If \(A_w\) is its adjacency matrix and
\(\lambda_w=\rho(A_w)\), the equal-contraction graph-directed dimension
theorem gives

\[
 \dim_HK_w={\log\lambda_w\over\log10},\qquad
 9\le\lambda_w\le(10^{|w|}-1)^{1/|w|}<10. \tag{32}
\]

The lower bound follows by deleting any one digit that occurs in \(w\); the
resulting nine-digit Cantor set is contained in \(K_w\). The upper bound
comes from splitting a word into aligned \(|w|\)-blocks. More exactly, if
\(c_j=1\) precisely when the shift by \(j\) is a self-overlap of \(w\), and
\(c_w(z)=\sum_{j=0}^{|w|-1}c_jz^j\), Guibas--Odlyzko's correlation formula is

\[
 \sum_{n\ge0}a_n(w)z^n
 ={c_w(z)\over z^{|w|}+(1-10z)c_w(z)},\qquad
 (10-\lambda_w)\sum_{j=0}^{|w|-1}c_j\lambda_w^{|w|-1-j}=1. \tag{33}
\]

These source facts are `literature-checked`: the graph-directed dimension
input is [Mauldin--Williams](https://doi.org/10.1090/S0002-9947-1988-0961615-4)
and the exact avoidance generating function is
[Guibas--Odlyzko](https://doi.org/10.1016/0097-3165(81)90005-4). Their
specialization here is a `proof sketch`.

The geometry shows why improving the ordinary irrationality exponent cannot
settle V1. Fishman's theorem implies that the nine-digit Cantor subset has a
full-dimensional intersection with the badly approximable numbers:
[Fishman, 2009](https://doi.org/10.1016/j.jnt.2009.02.005). Removing the
countable algebraic numbers leaves uncountably many points in every \(K_w\)
that are simultaneously transcendental, badly approximable, and of exact
irrationality exponent two. An explicit example is a rational affine image
of the decimal Thue--Morse number using two digits different from a digit in
\(w\); it lies in \(K_w\), is transcendental by
[Adamczewski--Bugeaud](https://doi.org/10.4007/annals.2007.165.547), and has
irrationality exponent two by
[Bugeaud](https://doi.org/10.5802/aif.2666).

The union \(\bigcup_wK_w\), namely the points with nondense decimal orbit up
to endpoint conventions, is itself a winning set of Hausdorff dimension one:
[Hu--Yu](https://doi.org/10.1016/j.jmaa.2014.04.026). Recent
arithmetic-Fourier estimates count rationals or give metric approximation
inside missing-digit sets, but do not exclude a named transcendental point:
[Chow--Varj\'u--Yu, 2026](https://doi.org/10.1016/j.aim.2026.110807).
Thus a successful fractal argument must distinguish \(\pi\) from every
individual \(K_w\) by a genuinely \(\pi\)-specific property; scalar
transcendence, even optimal Diophantine quality, is provably insufficient.

At the entropy level the reduction is exact. Subadditivity of
\(\log p_\pi(n)\) gives a limiting factor-entropy rate, and one omitted word
forces it below \(\log10\) by (32). Conversely V1 gives
\(p_\pi(n)=10^n\) at every length. The existing T32 module already
machine-checks the omitted-word entropy deficit; the exact maximal-entropy
equivalence is being isolated as a named formal bridge, not as a proof that
\(\pi\) has maximal entropy.

An independently audited finite-type/logarithm bridge now makes the remaining
quantifier mismatch explicit.  Pigeonholing length-(L) factors of one path
in (K_w) locates a repeated block only by the exponential return scale
(|\mathcal L_L(w)|\ge9^L).  The resulting ultimately periodic rational has
unreduced-denominator exponent only (1+L/j); the uniform guarantee can
therefore degrade to (1+L/9^L), and a nine-symbol de Bruijn path shows that
this delay is real at each finite scale.  Membership in a finite-state
language consequently supplies neither automaticity of the selected path nor
the long repetition required by the known Subspace-Theorem inputs.

The separation is constructive.  For every forbidden word (w), select a
digit (c) occurring in (w) and two different digits (a,b\ne c).  The
rational affine decimal Thue--Morse point

\[
 \eta_w={a\over9}+(b-a)\sum_{n\ge0}t_n10^{-n-1}
\]

uses only (a,b), so lies in (K_w); its selected digit path is automatic
and Mahler, it is transcendental, and its irrationality exponent is exactly
two.  Thus even all four properties can coexist with omission.  What this
separator deliberately lacks is the (\pi)-specific algebraic exponential
(e^{i\pi}=-1).

Two direct attempts to use that extra relation have an exact scale ledger.
Normalizing
(e^{i\lfloor10^n\pi\rfloor/10^n}+1) recovers the original uncontrolled
tail ({10^n\pi}).  The selected-tail integer polynomial

\[
 P_N(X)=\prod_{n=1}^N
 (10^nX-\lfloor10^n\pi\rfloor)
 (1-10^nX+\lfloor10^n\pi\rfloor)
\]

has degree (2N), height at most (30^N10^{N(N+1)}), and
(0<P_N(\pi)\le4^{-N}).  Cijsouw's applicable logarithm measure only gives
a lower bound of shape
(\exp[-O(N^4\log^2N)]), fully compatible with that upper bound.  The
bounded primary-source report, 553,628-check replay, and independent audit
are
[`subshift_log_algebraic_bridge.md`](work/ultrapi-resume/subshift_log_algebraic_bridge.md),
[`subshift_log_algebraic_bridge_check.py`](work/ultrapi-resume/subshift_log_algebraic_bridge_check.py),
and
[`subshift_log_algebraic_bridge_independent_audit.md`](work/ultrapi-resume/subshift_log_algebraic_bridge_independent_audit.md).
Their status is `literature-checked`/`proof sketch`/`experiment`; the open
input is a digit-sensitive exclusion of the algebraic logarithm (i\pi)
from every positive-entropy decimal survivor, not another scalar
transcendence estimate.

### An automaton-wide exponential form still misses the zero-estimate scale

The omitted-word hypothesis does create a genuine small arithmetic form; the
failure is no longer merely that a finite automaton cannot select the path of
\(\pi\).  Fix a nonempty forbidden word \(w\), set \(q=10^n\), and let
\({\cal A}_n(w)\) be the integers \(3q+[u]_{10}\) for all length-\(n\)
decimal words \(u\) avoiding \(w\).  Write \(N_n=|{\cal A}_n(w)|\).  If
\(w\) is absent from \(\pi\), then
\(p_n=\lfloor q\pi\rfloor\in{\cal A}_n(w)\).  The nonzero integer polynomial

\[
 {\cal E}_{n,w}(Z)=\prod_{p\in{\cal A}_n(w)}(1+Z^p)       \tag{34}
\]

satisfies, at the varying transcendental point \(Z=e^{i/q}\),

\[
 0<|{\cal E}_{n,w}(e^{i/q})|
   <q^{-1}\rho^{N_n-1},\qquad
 \rho=-2\cos2=0.832293673\ldots<1.                      \tag{35}
\]

The \(p_n\)-factor is small because \(p_n/q\) is the decimal truncation of
\(\pi\); every other candidate lies in \([3,4)\), where
\(|1+e^{ix}|\le\rho\).  This is exponentially small in the complete survivor
language and is stronger than the direct rational interpolation product.

The exact parameter ledger nevertheless rules out the available scalar
lower-bound comparison.  For any batch of \(s\) candidates containing
\(p_n\), multiplicity \(t\ge1\), and any valid
\(\nu>\mu(\pi)>1\), the logarithmic upper and factorwise lower exponents are

\[
 A=t\{\log q+(s-1)(-\log\rho)\},\qquad
 B=ts\{\nu\log q+\log(\pi/2)\}.                         \tag{36}
\]

Since \(0<-\log\rho<\log q\), one always has
\(A\le ts\log q<B\).  Thus the certified lower bound is smaller than the
constructed upper bound for every \(s,t\); batching more paths or increasing
zero multiplicity cannot produce a contradiction.  Expanded
Lindemann--Weierstrass bounds pay still more for degree and height.  Taking a
resultant to move from \(e^{i/q}\) to the fixed special value \(e^i\) removes
the useful decimal factor exactly: if \(g=(p_n,q)\) and
\(x=q\pi-p_n\), the relevant norm is

\[
 |1-e^{-ix/g}|^g\le(x/g)^g,                              \tag{37}
\]

not \(x/q\).  The construction, no-crossing inequality, primary-source
audit, and exact finite checks are recorded in
[`automaton_pade_attack.md`](work/ultrapi-resume/automaton_pade_attack.md)
and its
[`checker`](work/ultrapi-resume/automaton_pade_attack_check.py).  Their status
is `literature-checked`/`proof sketch`/`experiment`; (35) is meaningful new
working stone, not V1.

A cyclotomic and multiscale refinement reaches the correct lower-bound scale
but proves that this particular product cannot cross.  If \(\nu_w\) is the
Perron--Frobenius path measure of the avoidance automaton and
\(\alpha=\pi-3\), then a spacing and uniform-integrability argument gives

\[
 \log|{\cal E}_{n,w}(e^{i/10^n})|
 =N_n I_w(\alpha)+O_w(N_n\vartheta_w^n+n),\qquad
 I_w(\alpha)=\int\log|1-e^{i(x-\alpha)}|\,d\nu_w(x),       \tag{37a}
\]

for some \(0<\vartheta_w<1\).  Thus the exact decay rate is
\(c_w=-I_w(\alpha)\).  Since every legal node lies in the same arc used in
(35), with equality in the crude factor bound at only one endpoint and
\(\nu_w\) non-atomic,

\[
 c_w>-\log\rho=0.1835699279\ldots .                       \tag{37b}
\]

Spacing improves the factorwise lower bound from
\(\exp(-N_n\log q)\) to \(\exp(-C_wN_n-O(\log q))\), a genuine gain.
Nevertheless any valid constant-rate lower bound for this same actual product
must have \(C_w\ge c_w>-\log\rho\), whereas contradiction with (35) requires
the reverse strict inequality.  A child/parent quotient cancels the bulk to
an \(O(\log q)\) cocycle involving the actual next digit and tail, but its
numerator and denominator retain \(\Theta(qN_n)\) degree and coefficient
\(\ell^1\)-length \(2^{N_n}\).  Clearing it restores the full arithmetic
cost.  The derivation, exact identities, and both passing checkers are in
[`cyclotomic_language_product_attack.md`](work/ultrapi-resume/cyclotomic_language_product_attack.md)
and its
[`independent audit`](work/ultrapi-resume/cyclotomic_language_product_independent_audit.md).
This is a `proof sketch` separator for the product family, not an impossibility
theorem for every auxiliary construction.

The independently audited integer-Chebyshev variant reaches the same wall by
a different route.  Under omission of a nonempty word, both the compact
decimal survivor (K_w) and its cosine image
(J_w=\{2\cos x:x\in K_w\}) have positive logarithmic capacity.  Hence their
nonmonic integer Chebyshev constants satisfy

\[
 0<\operatorname{cap}(E)\le t_{\mathbb Z}(E)
 \le\sqrt{\operatorname{cap}(E)}<1,qquad E=K_w,J_w.    \tag{37c}
\]

Optimized integer polynomials can therefore be exponentially small in their
degree on every survivor, but positive capacity forbids a uniform
superexponential gain.  Applying a fixed degree-(d) detector to the first
(N) decimal tails creates degree (dN), unavoidable log-height
(\Omega(dN^2)), and only (\exp[-\Theta(N)]) smallness; Cijsouw's applicable
lower bound pays (O(d^3N^4\log^2(dN))).  The minimum monomial clearing at
the fixed value (e^i),

\[
 G_N(Z)=\prod_{j=1}^N(Z^{\lfloor10^j\pi\rfloor}-1)^2,
\]

instead has degree (\Theta(10^N)) and only exponential-in-(N) smallness.
Even the exact family ((Z^3+1)^{2D}), whose value at (e^i) is below
(49^{-D}), loses to the cubic degree penalty in the available lower bound.
Thus capacity optimization improves constants but does not cross the known
zero-estimate scale.  The report, checker, and independent audit are
[`integer_chebyshev_survivor_attack.md`](work/ultrapi-resume/integer_chebyshev_survivor_attack.md),
[`integer_chebyshev_survivor_attack_check.py`](work/ultrapi-resume/integer_chebyshev_survivor_attack_check.py),
and
[`integer_chebyshev_survivor_independent_audit.md`](work/ultrapi-resume/integer_chebyshev_survivor_independent_audit.md).
Their status is `literature-checked`/`proof sketch`/`experiment`; a finite
minimax computation there is explicitly only on admissible-prefix truncation
nodes, not necessarily points of (K_w), and no V1 conclusion follows.

### Furstenberg and BBP reduce to one return that is already V1

Let

\[
 K=\overline{\{10^N\pi\bmod1:N\ge0\}}.
\]

For multiplicatively independent integers \(b,c\ge2\) and irrational \(x\),
Furstenberg's nonlacunary-semigroup theorem gives the exact elementary
`proof sketch` equivalences

\[
 K_b(x)=\mathbb T
 \Longleftrightarrow cx\in K_b(x)
 \Longleftrightarrow cK_b(x)\subseteq K_b(x).             \tag{38}
\]

Indeed, a sequence \(b^{n_j}x\to cx\) and commutation imply
\(cK_b(x)\subseteq K_b(x)\); the dense joint
\(\langle b,c\rangle\)-orbit is then contained in \(K_b(x)\).  Consequently

\[
 \mathrm{V1}
 \Longleftrightarrow16\pi\in K
 \Longleftrightarrow
 \liminf_{N\to\infty}\|(10^N-16)\pi\|_{\mathbb T}=0.     \tag{39}
\]

This explains exactly why joint \(\times10,\times16\) density is not enough:
Furstenberg lets both exponents vary, whereas V1 fixes the \(16\)-exponent at
zero.  Even proving the single cross-base membership \(16\pi\in K\) would
already prove the whole target; it is not a weaker foothold.

T69 now isolates this statement in the verified track.  It defines the fixed
return \(16\{\pi\}\in K\), proves its all-radii sequential form, derives
forward \(\times16\)-invariance of \(K\), embeds the full
\(\{10^s16^t\pi:s,t\ge0\}\) orbit in \(K\), and converts \(K=\mathbb T\)
to the exact list-valued V1 statement by explicit decimal-cylinder inner
balls.  Conversely V1 supplies the fixed return directly.  With exactly the
density of the joint times-10/times-16 orbit of \(\pi\) retained as an
explicit premise, Lean proves

\[
 \boxed{\operatorname{Dense}\{10^s16^t\pi:s,t\ge0\}\Longrightarrow
   (\mathrm{V1}\iff16\{\pi\}\in K).}                    \tag{39a}
\]

This is the minimal topological premise used by the proof.  Furstenberg's
published 1967 theorem supplies it on paper from nonlacunarity and
irrationality of \(\pi\), but remains a literature input rather than a
formalized kernel theorem.  Thus (39a) is a `machine-checked` conditional
reduction, not an unconditional proof of either side.  Its report is
[`t69_fixed_sixteen_return_report.md`](work/ultrapi-resume/t69_fixed_sixteen_return_report.md).

The BBP partial sums \(A_N\) transfer (39) with exponentially vanishing error:

\[
 \mathrm{V1}\Longleftrightarrow
 \liminf_{N\to\infty}\|(10^N-16)A_N\|_{\mathbb T}=0.      \tag{40}
\]

Their standard recurrence shadows the hexadecimal orbit, while decimal
reweighting is an exact time-dependent coboundary conjugate to the original
decimal orbit.  Neither recurrence proves (40).  Schmidt's theorem supplies
a sharp separator: there are transcendental points normal in base 16 whose
decimal expansions use only digits \(0,\ldots,8\); their joint semigroup
orbits are dense and their hexadecimal radix recurrences have the expected
shadowing, yet decimal digit 9 is absent.  The exact derivation, source pins,
separator, and checker are in
[`furstenberg_bbp_bridge.md`](work/ultrapi-resume/furstenberg_bbp_bridge.md)
and its
[`checker`](work/ultrapi-resume/furstenberg_bbp_bridge_check.py).  This closes
the proposed cross-base shortcut without changing V1's `conjecture` status.

The exact rational synchronization version is equally sharp.  For any fixed
integer \(c\ge2\) multiplicatively independent of ten, V1 is equivalent to
the existence of \(N_j\to\infty\) and rationals \(A_j\) such that

\[
 (10^{N_j}-c)A_j\in\mathbb Z,
 \qquad |\pi-A_j|=o(10^{-N_j}).                         \tag{40a}
\]

The reverse implication takes \(A_j\) to be the nearest-integer rational
with denominator \(10^{N_j}-c\), so (40a) is the desired fixed return in
another form, not a weaker approximation lemma.

An independently audited Machin/Hutton attack finds three exact barriers to
the direct construction.  First, a divisor of \(10^N-c\) has eventually
fixed \(2\)- and \(5\)-adic valuations, excluding the full Hutton and
\(1/2+1/3\) shadows and infinitely many depths of every tested fixed split.
Second, if \(D_R\) is the natural common denominator of a positive Machin
truncation and \(\delta_R=\pi-L_R\), then

\[
                         D_R\delta_R\ge {32\over35}.     \tag{40b}
\]

Thus exact synchronization of the natural denominator cannot meet the
little-oh error in (40a).  Finally, for a private prime \(p\equiv3\pmod4\)
of one argument denominator, at depths \(T=p^e\) with odd \(e\), the fully
reduced denominator satisfies an exact endpoint valuation and
\(\operatorname{den}(L_{T+2})(\pi-L_{T+2})\to\infty\) exponentially.  This
applies to Hutton and all three denominator-safe split identities tested.
The corrected `proof sketch`, exact replay, and independent audit are
[`machin_synchronized_return_attack.md`](work/ultrapi-resume/machin_synchronized_return_attack.md),
[`machin_synchronized_return_attack_check.py`](work/ultrapi-resume/machin_synchronized_return_attack_check.py),
and
[`machin_synchronized_return_independent_audit.md`](work/ultrapi-resume/machin_synchronized_return_independent_audit.md).
They do not exclude a depth-varying signed/shared-prime identity with
exceptional exact cancellation and simultaneous discrete logarithms; no such
construction or source was found, and no V1 claim follows.

The independently audited signed/depth-varying attack resolves part of that
escape.  For fixed \(c\), if a fixed prime \(p\nmid10c\) survives linearly in
the reduced denominator \(q_j\) of a rational shadow of height \(H_j\), while
\(\log q_j=O(H_j)\), then \(q_j\mid10^{N_j}-c\) and Yu's \(p\)-adic
logarithmic-form estimate force \(N_j\ge\exp(\kappa H_j)\).  The published
\(\mu(\pi)<8\) bound simultaneously gives
\(|\pi-A_j|\ge\exp[-O(H_j)]\), so

\[
 \frac{|\pi-A_j|}{10^{-N_j}}\longrightarrow\infty.      \tag{40c}
\]

This obstruction is insensitive to real signed-tail cancellation.  Two exact
signed identities,

\[
 {\pi\over4}=3\arctan(1/3)-\arctan(2/11),\qquad
 {\pi\over4}=6\arctan(1/7)-\arctan(1457/22049),
\]

have infinite comparable-depth families with respectively linear surviving
11- and 1297-primary denominator layers, and are therefore excluded by
(40c).  The audit also found genuine signed cancellation—relative tail
cancellation below \(1/4000\)—and an exact failure of naive endpoint survival
at exponent 2059, where two top 11-adic layers cancel once.  Consequently the
result closes every schedule satisfying the stated fixed-prime premise, not
all signed/shared-prime schedules.  The `literature-checked` `proof sketch`,
finite `experiment` replay, and independent audit are
[`signed_depth_machin_attack.md`](work/ultrapi-resume/signed_depth_machin_attack.md),
[`signed_depth_machin_attack_check.py`](work/ultrapi-resume/signed_depth_machin_attack_check.py),
and
[`signed_depth_machin_independent_audit.md`](work/ultrapi-resume/signed_depth_machin_independent_audit.md).
They prove no fixed return and no V1.

A second independent audit tests whether classical product and fast-series
identities can pay the exact denominator anchor instead.  The answer is again
method-specific and negative.  Wallis approximants have error
\(>1/(2K+1)\) while their reduced denominator is exponential in \(K\), so
the depth required for transfer is incompatible with divisibility by
\(10^N-c\).  For Ramanujan's rational series

\[
 \frac{16}{\pi}=\sum_{k\ge0}
 \frac{(42k+5){2k\choose k}^3}{2^{12k}},
\]

let \(A_R\) be the reciprocal shadow obtained from the first \(R+1\)
terms.  Exact two-adic reduction gives a denominator at least
\(5\cdot4096^R/(R+1)^3\), whereas its positive error is bounded below on
the \(64^{-R}\) scale.  Consequently, for every fixed positive \(c\), the
strongest anchor \((10^N-c)A_R\in\mathbb Z\) forces

\[
 (10^N-c)(A_R-\pi)\longrightarrow+\infty,
\]

instead of zero.  At every even BBP truncation depth \(R\), the reduced
denominator also has exact two-adic valuation \(4R\), so it cannot divide
\(10^N-c\) at unbounded even depths.  The subsequent all-depth audit above
proves the sharper formula \(4R-v_2(R+1)\), eliminating the odd-depth escape
for the fixed multiplier 16.  Viète, AGM, and Chudnovsky finite shadows
pay the approximation error but retain an uncontrolled algebraic phase.
The exact replay and corrected independent audit are
[`fixed_multiplier_return_attack.md`](work/ultrapi-resume/fixed_multiplier_return_attack.md),
[`fixed_multiplier_return_check.py`](work/ultrapi-resume/fixed_multiplier_return_check.py),
and
[`fixed_multiplier_return_independent_audit.md`](work/ultrapi-resume/fixed_multiplier_return_independent_audit.md).
These are `proof sketch` obstructions to the named exact-anchor strategies,
not an impossibility theorem for approximate residues or a proof of V1.

A different restricted-denominator theorem reaches the right Archimedean
scale but fails an exact synchronization test.  Iyer proves uniformly for
every real \(\gamma\) that some displayed denominator \(d\le X\), whose
decimal digits are all 0 or 1, satisfies

\[
 \|d\gamma\|_{\mathbb T}\ll(\log X)^{-2}.              \tag{40d}
\]

At \(\gamma=\pi\) and \(X=10^N\), this is \(O(N^{-2})\).  To transfer it
to the fixed return one would need the same \(d\) to divide \(10^N-16\),
with cofactor \(k=(10^N-16)/d=o(N^2)\).  The independently audited
Cantor-denominator argument proves that this is impossible.  A rational in
the decimal \(\{0,1\}\) Cantor set has equal 2- and 5-adic reduced-
denominator exponents; hence \(1/k\notin C_{01}\), while its first \(N\)
digits agree with the zero-padded digits of \(d\).  Schleischitz's published
extrinsic distance theorem then yields the explicit global bound

\[
 \boxed{
 k>\frac{(N-\log_{10}32)^{\log_2 10}}{20},
 \qquad k>N^2
 }
 \quad(N\ge5),                                           \tag{40e}
\]

where the second inequality uses elementary finite ranges and the cubic
lower comparison for \(N\ge26\).  In particular \(k/N^2\to\infty\), so the
entire transfer of Iyer's guaranteed \(N^{-2}\) phase bound is closed.  This
does not exclude an aligned denominator with exceptionally smaller phase
\(\|d\pi\|=o(1/k)\); no checked theorem supplies one.  The
`literature-checked` `proof sketch`, exact `experiment` replay, and
independent audit are
[`restricted_denominator_iyer_attack.md`](work/ultrapi-resume/restricted_denominator_iyer_attack.md),
[`restricted_denominator_iyer_attack_check.py`](work/ultrapi-resume/restricted_denominator_iyer_attack_check.py),
and
[`restricted_denominator_iyer_independent_audit.md`](work/ultrapi-resume/restricted_denominator_iyer_independent_audit.md).
They prove no fixed return and no V1.

The exceptional aligned phase left by (40e) can also be sharply confined.
Write \(Q=10^N-16=kd\).  For fixed \(d\), the alignment exponents form either
the empty set or one residue class modulo \(\operatorname{ord}_d(10)\), so
\(k\|d\pi\|\to\infty\) along that progression.  More generally, the safe
published irrationality exponent \(888/125=7.104\) gives
for all sufficiently large \(d\)

\[
 k\|d\pi\|>{Q\over d^{888/125}}.                    \tag{40f}
\]

Consequently every hypothetical aligned sequence with
\(k\|d\pi\|\to0\) must satisfy

\[
 \boxed{
 {d\over Q^{125/888}}\to\infty,
 \qquad {k\over Q^{763/888}}\to0 .
 }                                                       \tag{40g}
\]

The exact local discrete-log and generalized-CRT sieve was independently
replayed on every one of the 2,047 distinct eligible 0/1 integers of two
through twelve digits.  It found 532 aligned candidates, 1,277 local subgroup
failures, and 238 CRT incompatibilities; every first-alignment product in the
box exceeds \(10^{180}\).  Independent review caught and corrected an initial
two-digit enumeration defect and the overstatement “eventually distinct”
(the proved conclusion is \(d_j\to\infty\), from which a distinct subsequence
may be selected).  The `literature-checked` `proof sketch`, primary
`experiment`, and independent audit are
[`exceptional_aligned_phase_attack.md`](work/ultrapi-resume/exceptional_aligned_phase_attack.md),
[`exceptional_aligned_phase_check.py`](work/ultrapi-resume/exceptional_aligned_phase_check.py),
[`exceptional_aligned_phase_independent_audit.md`](work/ultrapi-resume/exceptional_aligned_phase_independent_audit.md),
and
[`exceptional_aligned_phase_independent_check.py`](work/ultrapi-resume/exceptional_aligned_phase_independent_check.py).
Equations (40f)--(40g) are necessary conditions, not an existence theorem;
they prove no fixed return and no V1.

A corrected and independently audited Padé experiment shows that exact
alignment itself can occur without useful approximation.  Euler's identity
\(\pi/4=\arctan(1/2)+\arctan(1/3)\), with both Gauss continued fractions
truncated at depth six, gives the reduced rational

\[
 A_6={774756220\over246612571},\qquad
 246612571=19\cdot641\cdot20249.                         \tag{40h}
\]

Exact local discrete logarithms and generalized CRT give

\[
 246612571\mid10^{684842}-16,
 \qquad N\equiv684842\pmod{728928},                       \tag{40i}
\]

with (684842) the least positive alignment exponent.  Yet an exact
alternating-series lower bracket, using no numerical value of \(\pi\), proves

\[
 |\pi-A_6|>{1\over11560000},\qquad
 (10^{684842}-16)|\pi-A_6|>10^{684834}.                   \tag{40j}
\]

This enormous raw transfer term does **not** lower-bound the circle distance:
its integer part can disappear modulo one.  A high-precision finite
`experiment` gives the actual distance
\(0.4582011106795978822\ldots\), but that value is not used in a deduction.
For the classical one-angle Gauss family, independent exact Machin enclosures
found reduced approximation qualities below (0.8) at depths 200 and 1000,
contradicting the trend suggested by a source's unexplained
\(0.9058\ldots\) claimed limit.  The valid theorem-sized implication is only
conditional: an eventual reduced quality bound (M_n\le L+o(1)), (L<1),
would make every unbounded exact-divisibility transfer diverge.  No such
asymptotic was verified, so the branch is not declared closed.  The corrected
`literature-checked` `proof sketch`, exact `experiment`, and independent audit
are
[`fixed_denominator_pade_attack.md`](work/ultrapi-resume/fixed_denominator_pade_attack.md),
[`fixed_denominator_pade_attack_check.py`](work/ultrapi-resume/fixed_denominator_pade_attack_check.py),
[`fixed_denominator_pade_independent_audit.md`](work/ultrapi-resume/fixed_denominator_pade_independent_audit.md),
and
[`fixed_denominator_pade_independent_check.py`](work/ultrapi-resume/fixed_denominator_pade_independent_check.py).
It proves no fixed return and no V1.

The natural sampled Machin family admits an all-depth exact-alignment
obstruction of a different kind.  Put

\[
 M_j=\operatorname{machinLowerRat}(3j),\qquad
 R_j=10^jM_j.
\]

Let (F=\mathbb Q(\zeta_{16})),
(K=F(10^{1/16})), (E=F(2^{1/4})), and (L=KE).  Exact Kummer degree
calculations and the splitting witness (p_0=5521) give

\[
 [K:\mathbb Q]=128,\qquad [E:\mathbb Q]=16,
 \qquad [L:\mathbb Q]=256.                         \tag{40x}
\]

Chebotarev therefore gives density (1/256) to the primes which split
completely in (K) but not in (L).  For each such prime (p), (10) is
a sixteenth power modulo (p), while (2) is not a fourth power.  Hence
(16=2^4) is not a sixteenth power and

\[
                  p\nmid10^m-16\qquad(m\ge0).       \tag{40y}
\]

Every sufficiently large interval ((x/2,x]) contains one of these primes.
Taking (x=12N+15), the `machine-checked` T48 upper-half prime-survival
theorem puts that prime to exact exponent one in the reduced denominator of
(R_{N+1}).  Multiplication by the decimal unit (10^{N+1}) then proves
the all-depth quantifier statement

\[
 \boxed{
  \exists J\ \forall j\ge J\ \forall m\ge0:
        (10^m-16)M_j\notin\mathbb Z.}               \tag{40z}
\]

The exact witness (p=5521), (N=459) has
(10^{345}\equiv1), (2^{1380}\equiv-1\pmod{5521}), and an independent
full rational reconstruction gives
(v_{5521}(R_{460})=-1) with (5521R_{460}\equiv551\pmod{5521}).
Independent review corrected the relative splitting-field description,
ramification scope, and residue wording without changing (40x)--(40z).
The `literature-checked` `proof sketch`, two exact `experiment` replays, and
independent audit are
[`machin_chebotarev_anchor_obstruction.md`](work/ultrapi-resume/machin_chebotarev_anchor_obstruction.md),
[`machin_chebotarev_anchor_obstruction_check.py`](work/ultrapi-resume/machin_chebotarev_anchor_obstruction_check.py),
[`machin_chebotarev_anchor_independent_audit.md`](work/ultrapi-resume/machin_chebotarev_anchor_independent_audit.md),
and
[`machin_chebotarev_anchor_independent_check.py`](work/ultrapi-resume/machin_chebotarev_anchor_independent_check.py).
Nonintegrality only gives a reciprocal-denominator Archimedean lower bound;
it does not exclude a nonzero phase tending to zero and proves no V1.

The follow-up exact gcd ledger repairs the missing asymptotic accounting.
For the unreduced Gauss--Lambert continuants

\[
 X_n=(2n-1)X_{n-1}+(n-1)^2X_{n-2},\qquad
 A_n={4P_n\over Q_n},
\]

put

\[
 H_n=2^{\lfloor n/2\rfloor}
      \operatorname{odd}\!\left({n!\over\operatorname{lcm}(1,\ldots,n)}\right),
 \qquad E_n={\gcd(4P_n,Q_n)\over H_n}.
\]

Coefficient identities prove \(H_n\mid\gcd(4P_n,Q_n)\), and the integral
error gives analytic rate \(2\log(1+\sqrt2)\). Consequently the
\(0.7911979206687\ldots\) constant is a lower bound on reduced quality, not
an upper bound or an established limit. The actual limit at that value is
equivalent to \(\log E_n=o(n)\); for this transfer it would already suffice
to prove

\[
 \limsup_{n\to\infty}{\log E_n\over n}
 <0.4652000032604\ldots .                              \tag{40k}
\]

This is not routine denominator clearing. For every odd prime \(p\), the
exact shift law \(Q_{p+s}\equiv0\) and
\(P_{p+s}\equiv P_pQ_s\pmod p\) shows that large shifted prime divisors of
earlier continuants can enter \(E_{p+s}\); prime-power lifts add further
fluctuation. The finite checker reaches depth 1200 plus high-depth
checkpoints, but no asymptotic bound such as (40k) is proved. The corrected
`literature-checked` `proof sketch` and exact `experiment` are
[`gauss_pade_reduced_denominator_audit.md`](work/ultrapi-resume/gauss_pade_reduced_denominator_audit.md)
and
[`gauss_pade_reduced_denominator_check.py`](work/ultrapi-resume/gauss_pade_reduced_denominator_check.py).

The independently audited exceptional-gcd follow-up reduces the odd part to
one varying-prime zero set.  Put \(U_n=Q_n/n!\) and \(V_n=P_n/n!\).  The
normalized determinant gives, for every odd prime \(\ell\) and \(n\ge2\),

\[
 v_\ell(E_n)\le
 \lfloor\log_\ell n\rfloor+
 \lfloor\log_\ell(n-1)\rfloor-v_\ell(n).              \tag{40q}
\]

Hence the primes \(\ell\le\sqrt n\) contribute only
\(O(\sqrt n\log n)=o(n)\).  For \(\sqrt n<\ell<n\), write
\(n=a\ell+s\), where \(1\le a<\ell\) and \(0\le s<\ell\).  A Frobenius
coefficient identity, equivalently the specialized Lucas congruence for
Noe's generalized central trinomial coefficients, yields the exact strict
criterion

\[
 v_\ell(E_n)\ge1
 \quad\Longleftrightarrow\quad U_sV_a\equiv0\pmod\ell, \qquad
 v_\ell(E_n)\le2.                                    \tag{40r}
\]

Both alternatives in (40r) genuinely occur, including exponent-two examples
and complete prime blocks from \(\ell\mid P_a\).  They are not equally hard
asymptotically: splitting at \(a\le n^{1/3}\), bounding the selected prime
product by \(P_a\), and discarding divisibility for the complementary range
proves

\[
 \sum_{\substack{\sqrt n<\ell<n\\
                   \ell\mid V_{\lfloor n/\ell\rfloor}}}
       \log\ell=o(n).                                \tag{40s}
\]

It follows that the odd part has subexponential exceptional gcd if and only
if

\[
 \sum_{\substack{\sqrt n<\ell<n\\
                   \ell\mid U_{n\bmod\ell}}}
       \log\ell=o(n).                                \tag{40t}
\]

This is an exact diagonal, varying-characteristic zero-density problem; the
fixed-prime Lucas/automatic results do not prove (40t).  The formerly
experimental two-adic edge now has an independently audited all-depth
`proof sketch`:

\[
 v_2(Q_n)-\lfloor n/2\rfloor=
 \begin{cases}
 0,&n\equiv0,1\pmod4,\\
 1,&n\equiv2\pmod4,\\
 v_2(n+1),&n\equiv3\pmod4.
 \end{cases}                                             \tag{40ab}
\]

The unbounded class follows from the two-adic endpoint identity
\[
 \sum_{j\ge0}{j!\over(2j+1)!!}=0
\]
and a scaled isometry for
\(F(x)=\sum_{j\ge0}j!(2j+1)!!^{-1}\binom{x}{j}^2\):
\[
 v_2\!\left(F(2t-1)-F(2s-1)\right)=2+v_2(t-s).
\]
Independent review caught and repaired one crossed-partial-fraction
antiderivative; both primary and independent exact replays then passed,
including 297,984 signed-binomial Lipschitz cases and 38,808 high-pair
cases.  Equation (40ab) and the prior bound
\(v_2(E_n)\le v_2(Q_n)-\lfloor n/2\rfloor\) prove
\(v_2(E_n)=O(\log n)=o(n)\).  Thus (40t), not a hidden two-primary term, is
the only possible exponential-scale obstruction in this route.

Primary and independent exact replays for the odd-prime reduction pass,
respectively, on 84,219 and 118,613 strict large-prime pairs.  The corrected
`literature-checked` `proof sketch`, its `experiment`, and the independent
audit are
[`gauss_exceptional_gcd_upper_bound_attack.md`](work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_attack.md),
[`gauss_exceptional_gcd_upper_bound_check.py`](work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_check.py),
[`gauss_exceptional_gcd_upper_bound_independent_audit.md`](work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_independent_audit.md),
and
[`gauss_exceptional_gcd_upper_bound_independent_check.py`](work/ultrapi-resume/gauss_exceptional_gcd_upper_bound_independent_check.py).
The two-adic report, repaired primary checker, independent audit, and
independent checker are
[`gauss_two_adic_all_depth_attack.md`](work/ultrapi-resume/gauss_two_adic_all_depth_attack.md),
[`gauss_two_adic_all_depth_check.py`](work/ultrapi-resume/gauss_two_adic_all_depth_check.py),
[`gauss_two_adic_all_depth_independent_audit.md`](work/ultrapi-resume/gauss_two_adic_all_depth_independent_audit.md),
and
[`gauss_two_adic_all_depth_independent_check.py`](work/ultrapi-resume/gauss_two_adic_all_depth_independent_check.py).
Together these results prove neither (40t) nor V1.

The next independently audited reduction makes the remaining sum in (40t)
more concrete.  Set

\[
 A_t=2^tU_t=T_t(1,2,2),\qquad L_t(X)=2^tP_t(X),
\]

where \(P_t\) is the Legendre polynomial.  Its Gaussian resultant closes
exactly on the original integer:

\[
 \operatorname {Res}_X(X^2+1,L_t(X))=A_t^2.            \tag{40ae}
\]

Equivalently, for every odd prime \(p\),
\(p\mid A_t\) if and only if \(X^2+1\mid L_t(X)\) in
\(\mathbb F_p[X]\), including \(p\equiv3\pmod4\).  Thus the apparent square
in the resultant is no amplification and supplies no new norm estimate.

For a prime selected by (40t), put
\[
 a=\lfloor n/p\rfloor,\qquad s=n-ap,\qquad
 t=\min(s,p-1-s).
\]
The exact signed reflection of the first Frobenius block gives

\[
 p\mid A_t,\qquad p>2t,\qquad (2a+1)t\le n-a,
 \qquad
 p={n-t\over a}\ \ \hbox{or}\ \ p={n+1+t\over a+1}.    \tag{40af}
\]

Conversely, either affine identity, together with the displayed
divisibility and the original strict bounds \(\sqrt n<p<n\), reconstructs a
selected prime.  This removes the moving coefficient index but leaves a
pointwise prime-factor selector.

For an integer \(B\ge1\) and real \(T\ge1\), let \(C_n(B,T)\) denote the
part of \(W_n\) for which \(a\le B\) and \(t>T\).  Positivity and
\(A_t\le5^t\) remove the small-\(t\) tail, while the Chebyshev function
removes the large-\(a\) tail:

\[
 C_n(B,T)\le W_n\le C_n(B,T)
 +\vartheta\!\left({n\over B+1}\right)
 +{\log5\over2}T(T+1).                               \tag{40ag}
\]

Consequently
\[
 W_n=C_n(\lfloor n^{1/3}\rfloor,\lfloor n^{1/3}\rfloor)
       +O(n^{2/3}).
\]
The unresolved compact core has
\[
 a\le n^{1/3},\qquad n^{1/3}<t\le{n-a\over2a+1},
 \qquad p\mid A_t,
\]
and one of the two affine identities in (40af).  Fixed-prime zero counts
do not control this varying-prime diagonal.

The corrected primary and independent checkers pass on all 7,803 forward
selector pairs through \(n=10{,}000\), 1,371 independently generated
converse candidates, and 66,797 exact tail instances.  Independent review
also checked the floor boundary in (40ag), the \(p\equiv3\pmod4\)
polynomial-divisibility case, and the source pins.  The
`literature-checked` `proof sketch`, its `experiment`, and the independent
audit are
[`gauss_large_prime_zero_density_reduction.md`](work/ultrapi-resume/gauss_large_prime_zero_density_reduction.md),
[`gauss_large_prime_zero_density_check.py`](work/ultrapi-resume/gauss_large_prime_zero_density_check.py),
[`gauss_large_prime_zero_density_independent_audit.md`](work/ultrapi-resume/gauss_large_prime_zero_density_independent_audit.md),
and
[`gauss_large_prime_zero_density_independent_check.py`](work/ultrapi-resume/gauss_large_prime_zero_density_independent_check.py).
They prove neither \(W_n=o(n)\), the exceptional-gcd estimate, nor V1.

The independently audited medium-prime reduction eliminates the compact-core
selector from the asymptotic target.  With

\[
 A_n=\bigl[X^n\bigr]\,(X^2+2X+2)^n,
 \qquad
 M_n=\sum_{\substack{\sqrt n<p<n\\p\text{ odd prime}\\p\mid A_n}}\log p,
\]

the one-digit Lucas identity
\(A_{ap+s}\equiv A_aA_s\pmod p\) gives, for every integer \(B\ge1\),

\[
 \boxed{0\le M_n-W_n\le
 \vartheta\!\left({n\over B+1}\right)
 +{\log5\over2}B(B+1).}                              \tag{40am}
\]

Taking \(B=\lfloor n^{1/3}\rfloor\) proves

\[
 \boxed{W_n=o(n)\iff M_n=o(n).}                      \tag{40an}
\]

There is also an exact fixed-band diagonal.  If \(W_{n,a}\) restricts
\(W_n\) to \(\lfloor n/p\rfloor=a\), then

\[
 W_n=o(n)\iff
 \forall a\ge1\text{ fixed}:\ W_{n,a}=o(n),          \tag{40ao}
\]

and, for each fixed \(a\), all sufficiently large \(n\) satisfy

\[
 W_{n,a}=\sum_{\substack{n/(a+1)<p\le n/a\\
                 \sqrt n<p<n\\p\mid A_n}}\log p.
\]

For \(a=1\) this identity is exact at every depth because \(A_1=2\); hence
even the first unresolved task is

\[
 \sum_{\substack{n/2<p<n\\p\text{ odd prime}\\p\mid A_n}}\log p=o(n).
\]

This is pointwise in every \(n\), not an average or subsequence assertion.
The bounded source audit found no theorem that proves it.  In particular,
Wagner's coefficient asymptotics control total size rather than this moving
prime window, while Mikić's fixed-parameter divisibility theorem assumes a
coprimality condition that fails for \(A_n=T_n(2,2)\).  The corrected
`literature-checked` `proof sketch`, primary replay, independent audit, and
independent replay are
[`gauss_medium_prime_radical_reduction.md`](work/ultrapi-resume/gauss_medium_prime_radical_reduction.md),
[`gauss_medium_prime_radical_check.py`](work/ultrapi-resume/gauss_medium_prime_radical_check.py),
[`gauss_medium_prime_radical_independent_audit.md`](work/ultrapi-resume/gauss_medium_prime_radical_independent_audit.md),
and
[`gauss_medium_prime_radical_independent_check.py`](work/ultrapi-resume/gauss_medium_prime_radical_independent_check.py).
They prove no exceptional-gcd estimate, fixed return, or V1.

The independently audited first-band follow-up removes the remaining local
index ambiguity but also proves a sharp limitation of fixed-prime
information.  Write

\[
 S_n=\sum_{\substack{n/2<p<n\\p\text{ odd prime}\\p\mid A_n}}\log p.
\]

For a selected prime set \(t=n-p\) and
\(r=\min(t,p-1-t)\).  The one-digit Lucas law and the exact first-block
reflection give the duplicate-free two-ray description

\[
 \boxed{
 p=n-r\quad\hbox{or}\quad p={n+1+r\over2},\qquad
 1\le r\le{n-1\over3},\qquad p\mid A_r.}             \tag{40ap}
\]

Conversely, either prime in (40ap), subject to the displayed range and
divisibility, reconstructs a selected first-band prime.  The two images meet
only when
\(r=(n-1)/3\) and \(p=(2n+1)/3\), so that prime is counted once.

Let \(I_n(\delta)\) be the distinct-prime logarithmic weight in (40ap) with
\(\delta n\le r\le(1/3-\delta)n\).  For every fixed
\(0<\delta<1/6\), the prime number theorem at the four ray endpoints gives

\[
 0\le I_n(\delta)\le S_n,
 \qquad S_n\le I_n(\delta)+3\delta n+o_\delta(n).
                                                               \tag{40aq}
\]

The order of limits is fixed \(n\to\infty\) first and
\(\delta\downarrow0\) second.  Hence

\[
 \boxed{S_n=o(n)\iff
   \forall\delta\in(0,1/6)\text{ fixed}: I_n(\delta)=o(n)},
 \qquad
 S_n=o(n)\iff C_n=o(n/\log n),                        \tag{40ar}
\]

where \(C_n\) is the number of distinct selected first-band primes.  The
absolute small-\(r\) estimate
\(\sum_{r\le T}\log A_r\le(\log5)T(T+1)/2\) independently removes every
\(T=o(\sqrt n)\).

There is also an exact one-integer package.  With

\[
 P_n=\prod_{n/2<p<n}p,
 \qquad J_n=\sum_{n/2<p<n}{P_n\over p}A_{n-p}
\]

over odd primes, CRT orthogonality proves

\[
 \boxed{\exp(S_n)=\gcd(P_n,J_n)},
 \qquad \log P_n={n\over2}+o(n).                       \tag{40as}
\]

Thus generic gcd height still stops at linear scale.  More decisively, at
depths \(N_j=10^j\), assign each prime
\(3N_j/4<p<4N_j/5\) the single abstract minimal zero
\(z_p=N_j-p\), together with its reflection \(p-1-z_p\), and assign no
others.  These prescribed sets have one minimal zero per prime, exact
reflection, and no consecutive zeros, yet their selected direct-ray weight is

\[
 \vartheta(4N_j/5)-\vartheta(3N_j/4)
       =\left({1\over20}+o(1)\right)N_j.               \tag{40at}
\]

This model is not asserted to arise from \(A_r\).  Its exact role is to rule
out any deduction of \(S_n=o(n)\) from only per-prime zero counts,
reflection, and spacing.  The missing theorem must use arithmetic correlation
between the actual zero locations in different characteristics along the two
rays (40ap).  The primary `proof sketch`, exact `experiment` replay,
independent audit, and separately generated independent replay are
[`gauss_first_band_breakthrough_attack_20260813.md`](work/ultrapi-resume/gauss_first_band_breakthrough_attack_20260813.md),
[`gauss_first_band_breakthrough_attack_20260813_check.py`](work/ultrapi-resume/gauss_first_band_breakthrough_attack_20260813_check.py),
[`gauss_first_band_breakthrough_independent_audit_20260813.md`](work/ultrapi-resume/gauss_first_band_breakthrough_independent_audit_20260813.md),
and
[`gauss_first_band_breakthrough_independent_check.py`](work/ultrapi-resume/gauss_first_band_breakthrough_independent_check.py).
The primary and independent report SHA-256 values are respectively
`cba7b6115efc11de85b61634e1109430b9a215eda335cd0bea1cd2345a517e23`
and
`ce75d2280f7862f41fe04aa3d651a8c5e94b4681c045b8ba9fd70a675b0cba47`;
both checkers pass.  Equations (40ap)--(40at) prove neither \(S_n=o(n)\),
the exceptional-gcd estimate, nor V1.

An independently audited prefix-\(\gcd\) follow-up gives an exact diagnostic,
but also proves that its asymptotically harmless truncation is circular.  The
normalization is important:

\[
 A_m=[X^m]\,(X^2+2X+2)^m=[x^m]\,(1+2x+2x^2)^m;
\]

the superficially similar coefficient with \(4x^2\) is a different sequence
(already \(A_2=8\), not 12).  For \(n\ge2\), set

\[
 R_n=\prod_{1\le r\le\lfloor(n-1)/3\rfloor}A_r,
 \qquad G_n=\gcd(\operatorname{odd}(A_n),
                  \operatorname{odd}(R_n)).
\]

Then every odd prime below \(n\) in \(A_n\) already occurs in that prefix:

\[
 \boxed{\operatorname{rad}_{<n}^{\rm odd}(G_n)
       =\operatorname{rad}_{<n}^{\rm odd}(A_n).}       \tag{40be}
\]

Indeed, generalized Lucas supplies a nonzero base-\(p\) digit \(d\) with
\(p\mid A_d\), and first-block reflection also gives
\(p\mid A_{p-1-d}\).  If \(p\le2n/3\), the smaller reflected index is at most
\((n-1)/3\); if \(2n/3<p<n\), writing \(n=p+s\) gives
\(A_n\equiv2A_s\pmod p\) and \(s\le\lfloor(n-1)/3\rfloor\).  The reverse
inclusion is immediate from \(G_n\mid A_n\).

Writing \(E_n=\log\operatorname{rad}_{<n}^{\rm odd}(G_n)\), the only terms
outside the previously isolated medium window are primes at most \(\sqrt n\):

\[
 \boxed{0\le E_n-M_n\le\vartheta(\sqrt n)=o(n),\qquad
        E_n=o(n)\iff M_n=o(n).}                       \tag{40bf}
\]

Thus the below-\(n\), square-free prefix gcd is exactly a repackaging of the
open medium-prime target, not a new estimate.  The full integer gcd is
strictly stronger and noisier because it retains multiplicities and common
primes at least \(n\); exact finite witnesses are

\[
 G_{226}=131\cdot263\cdot577\cdot24071,
 \qquad G_{76}=17^2\cdot23\cdot97.                    \tag{40bg}
\]

The primary and independent checkers pass, including the exact support law
through \(n=3000\) and an independently generated replay through \(n=1200\).
The bounded source audit also corrects Xiaos title to *Greatest common
divisors for polynomials in almost units and applications to linear
recurrence sequences* and pins Rowland--Yassawi v2; neither constant-
coefficient recurrence gcd bounds nor fixed-characteristic automata control
this moving-prime problem.  The `literature-checked` `proof sketch`, finite
`experiment`, independent audit, and disjoint replay are
[`gauss_prefix_gcd_exact_circularity_20260813.md`](work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813.md),
[`gauss_prefix_gcd_exact_circularity_20260813_check.py`](work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_20260813_check.py),
[`gauss_prefix_gcd_exact_circularity_independent_audit_20260813.md`](work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_independent_audit_20260813.md),
and
[`gauss_prefix_gcd_exact_circularity_independent_check_20260813.py`](work/ultrapi-resume/gauss_prefix_gcd_exact_circularity_independent_check_20260813.py).
Their SHA-256 values are respectively
`e7faee8c575b526e79bc7488ae61d3b7fb88012a2257ec60c6a442eabe6a083e`,
`7d2f857c8c35c4d5a8783dd885ba2e20c8a100624ad197ffc2130eee2d72b8de`,
`ff0b6d197763758c640ca1f8c4fa02b7b2fd336cd3843eb99ba7a93242705053`,
and
`3d7c363bda6eb5b9edd63b3a31173301123a1a7fd9cb8313554016227610226e`.
No little-o estimate, fixed return, or V1 is proved.

The all-depth BBP identity has also been pushed to an exact short-orbit
normal form. If \(B_M=P_M/(2^{K_M}R_M)\) is reduced,
\(D_M=2^{K_M-4}\), and \(A_n=(10^n-16)/16\), then

\[
 (10^n-16)B_M
 =A_n\left({w_M\over D_M}+{c_M\over R_M}\right).       \tag{40l}
\]

The reflected two-adic null identity determines \(w_M\) and eight additional
bits. The complementary quotient \(c_M/R_M\) is exactly the missing
Archimedean phase. Moreover,

\[
 \min_{5\le n\le\lfloor M\log_{10}16\rfloor}
     \|(10^n-16)B_M\|_{\mathbb T}\longrightarrow0        \tag{40m}
\]

if and only if the fixed-\(16\) return, hence V1, holds. An explicit
separator preserves the complete actual reduced denominator, the complete
two-adic congruence, and better-than-BBP approximation to a fixed
transcendental limit while keeping every phase in this short orbit away from
zero. It deliberately does not preserve the four-pole BBP coefficient
recurrence; that recurrence is now the only remaining selector in this
route. The independently audited `proof sketch` and two exact `experiment`
replays are
[`bbp_short_orbit_return_attack.md`](work/ultrapi-resume/bbp_short_orbit_return_attack.md),
[`bbp_short_orbit_return_check.py`](work/ultrapi-resume/bbp_short_orbit_return_check.py),
[`bbp_short_orbit_return_independent_audit.md`](work/ultrapi-resume/bbp_short_orbit_return_independent_audit.md),
and
[`bbp_short_orbit_return_independent_check.py`](work/ultrapi-resume/bbp_short_orbit_return_independent_check.py).
They prove no fixed return and no V1.

The actual four-pole coefficient recurrence materially sharpens that normal
form.  The reflected BBP function satisfies

\[
 F(X+1)=16F(X)+a(X),
\]

which gives a closed finite carry for the complete dyadic coordinate
\(w_M\), and hence a closed cross-depth recurrence for the actual reduced odd
quotient \(q_M=c_M/R_M\):

\[
 q_{M+1}=q_M+{a(M+1)\over16^M}
          +{w_M\over D_M}-{w_{M+1}\over D_{M+1}}.     \tag{40u}
\]

For a possible denominator prime \(p>5\) with \(p^2>8M+5\), localizing all
four linear poles gives an explicit rational \(G_{M,p}\).  The corrected
survival statement is

\[
 G_{M,p}\not\equiv0\pmod p
 \quad\Longleftrightarrow\quad v_p(R_M)=1,             \tag{40v}
\]

and only on this event is the additive CRT coordinate defined.  The first
genuine cancellations, such as \((M,p)=(9,19)\), show why this qualification
is necessary.  The multiplier blocks nevertheless have a fixed rational
sign.  Their total absolute mass is uniformly bounded, while a common
denominator divides
\(2^{2N}\operatorname{lcm}(1,\ldots,N)\),
\(N=\lfloor(8M+5)/p\rfloor\).  Thus
\(\log H(G_{M,p})=O(N)\).  A moving cutoff
\(L_M\asymp\log M\) proves that every possible prime
\(p>M/L_M\) survives exactly once and is explicit.

If \(S_M\) is their product and \(C_M=R_M/S_M\), PNT in the fixed residue
classes and the prime-power ledger give

\[
 \log S_M=(6+o(1))M,\qquad
 P^+(C_M)=O(M/\log M),\qquad
 \log C_M=o(M),\qquad
 \log R_M=(6+o(1))M.                                \tag{40w}
\]

The phase is consequently an explicit dyadic carry plus explicit local
coordinates on \(S_M\), and only one residue modulo the subexponential
cofactor \(C_M\).  This is not yet a return theorem: the exact remaining
condition is cancellation in a selected, synchronized weighted sum over
\((\log_{10}16-1)M+O(1)\) consecutive powers of ten.  Neither (40w) nor a
generic power-generator estimate applies to that selected weight and
changing composite modulus.  The corrected independently audited
`literature-checked` `proof sketch` and two exact `experiment` replays are
[`bbp_actual_odd_quotient_attack.md`](work/ultrapi-resume/bbp_actual_odd_quotient_attack.md),
[`bbp_actual_odd_quotient_check.py`](work/ultrapi-resume/bbp_actual_odd_quotient_check.py),
[`bbp_actual_odd_quotient_independent_audit.md`](work/ultrapi-resume/bbp_actual_odd_quotient_independent_audit.md),
and
[`bbp_actual_odd_quotient_independent_check.py`](work/ultrapi-resume/bbp_actual_odd_quotient_independent_check.py).
They prove no fixed return and no V1.

An independently audited Fourier follow-up identifies exactly what the
weighted sum in that last paragraph contains.  If
\(L_M=\lfloor M\log_{10}16\rfloor\),
\(T_M=L_M-M+1\), and

\[
 {\cal S}_{M,h}=\sum_{n=M}^{L_M}
       e\!\left(h(10^n-16)B_M\right),
\]

then the full high-prime factor and cofactor factor collapse before any
estimate is made.  Uniformly over this entire proportional row,

\[
 \left|{{\cal S}_{M,h}\over T_M}
 -e(-16h\pi){1\over T_M}\sum_{n=M}^{L_M}e(h10^n\pi)\right|
 \le {2\pi|h|\over15(M+1)^2}.                         \tag{40ac}
\]

Thus all-depth cancellation of these rows at every nonzero frequency is
equivalent to base-ten normality itself; the common-subsequence condition
sufficient for the fixed return remains weaker and unproved.  Finite van der
Corput differencing does not simplify the phase:

\[
 \Delta_{r_k}\cdots\Delta_{r_1}
   \bigl(h(10^n-16)B_M\bigr)
 =h10^nB_M\prod_{j=1}^k(10^{r_j}-1).                \tag{40ad}
\]

It only promotes the frequency along the same lacunary family, in agreement
with the existing machine-checked T13 identity.

The audit also gives a sharp information barrier.  Keeping the complete
actual odd quotient \(c_M/R_M\), every odd CRT coordinate, the exact reduced
denominator, and reducedness, one can change only the dyadic coordinate to
obtain a rational \(B'_M\) with
\(|B'_M-B_M|\le2^{-M}\) whose normalized proportional-row mean has magnitude
tending to one.  Hence even all odd-coordinate information cannot force
cancellation without the selected dyadic carry.  This separator deliberately
violates the actual four-pole carry recurrence and is not a counterexample
for \(\pi\).  The primary report, two primary/self checkers, independent
audit, and independent checker are
[`bbp_weighted_sum_differencing_attack.md`](work/ultrapi-resume/bbp_weighted_sum_differencing_attack.md),
[`bbp_weighted_sum_differencing_check.py`](work/ultrapi-resume/bbp_weighted_sum_differencing_check.py),
[`bbp_weighted_sum_differencing_self_audit.md`](work/ultrapi-resume/bbp_weighted_sum_differencing_self_audit.md),
[`bbp_weighted_sum_differencing_self_audit_check.py`](work/ultrapi-resume/bbp_weighted_sum_differencing_self_audit_check.py),
[`bbp_weighted_sum_differencing_independent_audit.md`](work/ultrapi-resume/bbp_weighted_sum_differencing_independent_audit.md),
and
[`bbp_weighted_sum_differencing_independent_check.py`](work/ultrapi-resume/bbp_weighted_sum_differencing_independent_check.py).
The three exact replays pass 12,967, 41,175, and 17,762 checks.  This
`proof sketch` proves no cancellation, fixed return, normality, or V1.

The same four-pole recurrence does yield a telescope after replacing the
multiplier sixteen by ten, but its exact scope is now explicit.  For

\[
 D_N^u(q)={1\over N}\sum_{n<N}
       \bigl(e(16qu_n)-e(qu_n)\bigr),
 \qquad
 D_N^\pi(q)={1\over N}\sum_{n<N}
       \bigl(e(16qx_n)-e(qx_n)\bigr),
\]

the BBP tail \(t_n=10^n(\pi-B_n)\) satisfies
\(t_n\le(5/8)^n/(15(n+1)^2)\) and
\(\sum_{n\ge0}t_n\le8/45\).  Character Lipschitz bounds therefore give

\[
 \boxed{
 |D_N^u(q)-D_N^\pi(q)|
 \le {272\pi|q|\over45N}}
 \qquad(N\ge1).                                      \tag{40aa}
\]

Thus the BBP Fourier limit holds if and only if the same-time fixed-π limit
does.  Writing \(Z_n(m)=e(mu_n)\), the actual recurrence is

\[
 Z_{n+1}(m)=e(m\epsilon_{n+1})Z_n(10m),
\]

and its endpoint telescope stays entirely on multiplication-by-ten
frequency rays.  For nonzero \(q\), \(q\) and \(16q\) occupy distinct rays.
The ray-wise coefficient sum consequently rules out every finite Fourier
coboundary for \(e(16qx)-e(qx)\).  At the fixed point \(x=1/9\), the same
observable is nonzero whenever \(3\nmid q\); in particular \(q=1\) rules out
every continuous stationary coboundary needed for the target.  A universal
time-dependent identity whose transfer functions converge uniformly and
whose residuals vanish uniformly would limit to the same impossible
stationary identity.  These no-go results do not exclude an identity only
along the actual orbit or a nonlinear argument.

The corrected independently audited `literature-checked` `proof sketch`,
three exact `experiment` replays, self-audit, and independent audit are
[`bbp_four_pole_overlap_attack.md`](work/ultrapi-resume/bbp_four_pole_overlap_attack.md),
[`bbp_four_pole_overlap_check.py`](work/ultrapi-resume/bbp_four_pole_overlap_check.py),
[`bbp_four_pole_overlap_self_audit.md`](work/ultrapi-resume/bbp_four_pole_overlap_self_audit.md),
[`bbp_four_pole_overlap_self_audit_check.py`](work/ultrapi-resume/bbp_four_pole_overlap_self_audit_check.py),
[`bbp_four_pole_overlap_independent_audit.md`](work/ultrapi-resume/bbp_four_pole_overlap_independent_audit.md),
and
[`bbp_four_pole_overlap_independent_check.py`](work/ultrapi-resume/bbp_four_pole_overlap_independent_check.py).
The independent replay made 40,042 exact bounded checks.  It asserts no
overlap, Fourier limit, fixed return, or V1.

A separate dynamics audit shows why density and entropy cannot remove the
word “fixed.” For multiplicatively independent \(a,b\ge2\), every infinite
compact forward-\(\times a\)-minimal set \(M\) has pairwise disjoint slices
\(b^tM\), although their union is dense; all slices preserve Hausdorff
dimension and topological entropy. An explicit second separator starts with
the nine-digit Cantor Bernoulli measure. Its \(\times16^t\) pushforwards
have entropy \(\log9\), support dimension
\(\log9/\log10>19/20\), and pairwise mutual singularity, while their Cesaro
mean converges weakly to Lebesgue measure. Thus even intersecting supports,
large dimension, positive entropy, and averaged equidistribution do not imply
one fixed-slice return. The source-pinned, independently audited
`proof sketch` and exact `experiment` replays are
[`fixed_return_dynamics_attack.md`](work/ultrapi-resume/fixed_return_dynamics_attack.md),
[`fixed_return_dynamics_check.py`](work/ultrapi-resume/fixed_return_dynamics_check.py),
[`fixed_return_dynamics_independent_audit.md`](work/ultrapi-resume/fixed_return_dynamics_independent_audit.md),
and
[`fixed_return_dynamics_independent_check.py`](work/ultrapi-resume/fixed_return_dynamics_independent_check.py).
They are method separators, not statements about the fixed orbit of pi.

The BBP empirical audit makes the same obstruction coefficient-specific.
With the notation above, the exact coboundary relation is

\[
 \epsilon_{n+1}=10t_n-t_{n+1},\qquad
 u_{n+1}=\{10u_n+\epsilon_{n+1}\}.                    \tag{40n}
\]

Hence BBP and the actual decimal orbit have the same empirical-limit set.
Every limit \(\mu\) is a \(T_{10}\)-invariant probability supported on
\(K_\pi\), but none of ergodicity, nonatomicity, or overlap with
\(\nu=(T_{16})_*\mu\) follows.  If all three did hold, the dichotomy for
ergodic invariant probabilities would give \(\mu=\nu\).  The common support
would then be forward invariant under both multipliers and contain an
irrational point, so Furstenberg would give

\[
 \operatorname{supp}\mu=\mathbb T\subseteq K_\pi,
 \qquad K_\pi=\mathbb T.                               \tag{40o}
\]

On Fourier coefficients, equality of the two measures is exactly the
same-time estimate

\[
 {1\over N_j}\sum_{n<N_j}
 \bigl(e(16qu_n)-e(qu_n)\bigr)\longrightarrow0
 \quad\hbox{for every fixed }q\in\mathbb Z              \tag{40p}
\]

along one subsequence on which the empirical measures converge.  Unlike
the endpoint identity proving \(T_{10}\)-invariance, (40p) does not
telescopically collapse.  A Schmidt missing-digit construction shows that even an
ergodic nonatomic positive-entropy decimal limit can be singular to its
\(\times16\) pushforward.  The independently audited `proof sketch`, primary
and independent exact `experiment` replays, and source applicability audit
are
[`bbp_empirical_rigidity_attack.md`](work/ultrapi-resume/bbp_empirical_rigidity_attack.md),
[`bbp_empirical_rigidity_check.py`](work/ultrapi-resume/bbp_empirical_rigidity_check.py),
[`bbp_empirical_rigidity_independent_audit.md`](work/ultrapi-resume/bbp_empirical_rigidity_independent_audit.md),
and
[`bbp_empirical_rigidity_independent_check.py`](work/ultrapi-resume/bbp_empirical_rigidity_independent_check.py).
They prove no fixed return and no V1.

T70 now formalizes the conditional implication in 15 registered declarations.
The original interface proves support invariance under both multipliers after
the ergodic nonsingularity step, contains the complete joint semigroup orbit
of a supplied support point, promotes density of that orbit to full support,
and invokes the machine-checked cylinder bridge to V1.  The 2026-08-13
extension proves the strictly weaker topological core: conditional on the
explicit source-shaped `FurstenbergSourcePremise` from T77, every infinite
compact circle set forward invariant under both multipliers is the whole
circle.  It follows that infinite support plus either ergodic nonsingularity
or one-sided absolute continuity of the times-16 pushforward suffices; a
separately supplied dense point and nonatomicity are no longer needed.  The
module and its focused gate audit are
[`T70T70EmpiricalRigidityBridge.lean`](TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean)
and
[`t70_empirical_rigidity_audit.md`](work/ultrapi-resume/t70_empirical_rigidity_audit.md).
An adversarially independent audit, deterministic checker, and exact-type
Lean restatement are
[`t70_infinite_support_independent_audit.md`](work/ultrapi-resume/t70_infinite_support_independent_audit.md),
[`t70_infinite_support_independent_check.py`](work/ultrapi-resume/t70_infinite_support_independent_check.py),
and
[`t70_infinite_support_independent_checks.lean`](work/ultrapi-resume/t70_infinite_support_independent_checks.lean),
with SHA-256 values
`a39a437c7605f8789f34b2d0c472b8bb00aac24618763034b203626f40369c56`,
`fff4b5d9def83a887f5c7b1df949ff0ac655d9ab8a947643e83682fecadae046`,
and
`23cc27b8a679405190f0f467958897f64228cde921d08ff4f433c92201f2301f`.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in its axiom audit.
This is `machine-checked` as a conditional bridge; it does not establish the
source premise itself or infinite support, matching, absolute continuity,
ergodicity, or nonsingularity for an empirical limit of the fixed π orbit.

### One-character and adjacent-shift BBP reductions

Two independently audited 2026-08-13 follow-ups reduce the BBP endpoint
without proving it.  Put

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\quad
 b_k={a(k)\over16^k},\quad B_n=\sum_{k=0}^n b_k,
\]

and let \(q_n=10^n-16\), \(R_n=q_nB_n\),
\(V_n=e(B_n)\), and \(Z_n=e(R_n)\).  The positive BBP tail gives

\[
 0<q_n(\pi-B_n)\le{(5/8)^n\over15(n+1)^2}\longrightarrow0
 \qquad(n\ge2).
\]

Using the source-audited Furstenberg premise behind T69, the canonical target
therefore has the exact `proof sketch` form

\[
 \boxed{\mathrm{V1}\iff
 \liminf_n\|R_n\|_{\mathbb T}=0
 \iff\limsup_n\Re Z_n=1.}                            \tag{40ah}
\]

This is one pointwise character, not an all-frequency Weyl criterion.  It is
generated without an unevaluated occurrence of \(\pi\) by

\[
 \begin{aligned}
 V_{n+1}&=V_ne(b_{n+1}),\\
 Z_{n+1}&=Z_n^{10}V_n^{144}e(q_{n+1}b_{n+1}),
 \end{aligned}
 \qquad V_0=e(47/15),\quad Z_0=1.                    \tag{40ai}
\]

[Chen--Ye--Zheng (2026)](https://arxiv.org/abs/2604.14036v1) applies to the
limiting affine sequence \((10^n-16)\pi\).  It proves an infinite limit set,
\(\limsup_n\|R_n\|_{\mathbb T}\ge1/22\), and, for every modulus, one
residue-class subsequence not contained in any circle interval of length
less than \(1/10\).  This is unconditional dispersion in the opposite
direction from the missing liminf-zero return.  If that return fails with a
positive gap, a Fejer-kernel argument forces one fixed low power \(Z_n^h\)
to retain a quantitative negative Cesaro bias along a subsequence; no known
four-pole identity rules out that alternative.  A transcendental
irrationality-exponent-two Kempner separator shows that the generic
root-of-unity recurrence architecture cannot do so.  The report, primary
replay, independent audit, and independent replay are
[`bbp_one_character_return_attack.md`](work/ultrapi-resume/bbp_one_character_return_attack.md),
[`bbp_one_character_return_check.py`](work/ultrapi-resume/bbp_one_character_return_check.py),
[`bbp_one_character_return_independent_audit.md`](work/ultrapi-resume/bbp_one_character_return_independent_audit.md),
and
[`bbp_one_character_return_independent_check.py`](work/ultrapi-resume/bbp_one_character_return_independent_check.py).

An independently audited scalar elimination now removes the cumulative
partial sum from two consecutive instances of (40ai).  Put

\[
 C_n=R_{n+1}-10R_n,qquad h_n=C_{n+1}-C_n.
\]

Then, for every \(n\ge0\),

\[
 \boxed{
 R_{n+2}-11R_{n+1}+10R_n=h_n
 =(10^{n+2}-16)b_{n+2}+(160-10^{n+1})b_{n+1}.}       \tag{40au}
\]

The four-pole identity \(a(k)-a(k+1)>0\) gives the two exact endpoint signs
\(h_0,h_1>0\) and \(h_n<0\) for every \(n\ge2\).  More precisely,

\[
 \boxed{
 0<C_n-144\pi<{(5/8)^{n+1}\over(n+1)^2},qquad
 \sum_{j=N}^{\infty}|h_j|=C_N-144\pi\quad(N\ge2).}  \tag{40av}
\]

Thus \(C_n\) is a rational strictly decreasing upper approximation to
\(144\pi\).  If \(W_n=Z_{n+1}/Z_n\), exponentiating (40au) gives the exact
scalar recurrence

\[
 \boxed{W_{n+1}=W_n^{10}e(h_n),qquad
 Z_n=\prod_{j=0}^{n-1}W_j.}                          \tag{40aw}
\]

This is not independent mixing: writing
\(E_n=(10^n-16)(\pi-B_n)\), the unwrapped phase error satisfies

\[
 (R_{n+1}-R_n)-9\cdot10^n\pi=E_n-E_{n+1},qquad
 \sum_{j=0}^{n-1}(E_j-E_{j+1})=E_0-E_n.              \tag{40ax}
\]

Hence the scalar recurrence is an exponentially accurate derivative-orbit
restatement, while the unresolved event is still return of its accumulated
product.

Independent review found a substantive defect in the first proposed
rational separator: its nonintegral initial phase meant the displayed gap
did not apply to the partial product in (40aw).  The corrected model takes
\(\rho=5/8\), \(\varepsilon_n=\rho^n/3\), and

\[
 R_n^*={10^n-16\over9}-\varepsilon_n,qquad R_0^*=-2.
\]

It has strictly decreasing \(C_n^*=16+(25/8)\rho^n\), negative summable
\(h_n^*=-(75/64)\rho^n\), and \(W_n^*\to1\), yet now the anchored products
really equal \(e(R_n^*)\) and obey

\[
 \left\|R_n^*\right\|_{\mathbb T}
 ={1\over3}-\varepsilon_n\ge{1\over8}\qquad(n\ge1). \tag{40ay}
\]

Thus sign, one-sided monotonicity, summability, and local convergence do not
control the partial-product return; additional correlation in the exact
four-pole values of (40au) is essential.  The corrected primary report,
primary replay, independent audit, and independently generated replay are
[`bbp_character_breakthrough_attack_20260813.md`](work/ultrapi-resume/bbp_character_breakthrough_attack_20260813.md),
[`bbp_character_breakthrough_attack_20260813_check.py`](work/ultrapi-resume/bbp_character_breakthrough_attack_20260813_check.py),
[`bbp_character_breakthrough_independent_audit_20260813.md`](work/ultrapi-resume/bbp_character_breakthrough_independent_audit_20260813.md),
and
[`bbp_character_breakthrough_independent_check_20260813.py`](work/ultrapi-resume/bbp_character_breakthrough_independent_check_20260813.py).
Their report SHA-256 values are
`5a0e3027eb2b6c38b48e2b3ae075b4175b586bbd54ec1de68e6621cb0e03c264`
and
`c3d6f382972886e8c27d65159cc164ec55651ff353ac44f3300438033892304f`;
both exact checkers pass.  Equations (40au)--(40ay) prove no return or V1.

A separately independently audited separator shows how much more of the
scalar BBP data can still fail to force a return.  There is an explicit
rational proxy

\[
 g(n)={15(n+1)(8n-15)\over
 (2n+1)(4n+3)(8n+1)(8n+5)}                            \tag{40bh}
\]

whose first two forcing values, endpoint signs, first two coefficients on
both the \((5/8)^n\) and \(16^{-n}\) scales, and exact two-adic phase
valuation agree with the audited scalar laws.  Its anchored partial products
remain uniformly farther than \(1/16\) from the integers.  More generally,
for any fixed finite asymptotic jet, a denominator lift can preserve the
complete actual reduced BBP denominator and every two-adic bit determined by
it while the lifted phases tend to circle distance \(1/3\).  After a finite
anchor splice the construction also retains the true endpoint forcing
\(h_0,h_1\); the two splice-straddling rows are deliberately left
unconstrained.

This is a sharp scope statement.  The lift is chosen pointwise at each depth
and does **not** preserve the exact BBP increment relation or the cross-depth
odd-numerator coherence.  Therefore complete denominator data, all derived
two-adic information, and any fixed finite local asymptotic expansion cannot
alone prove (40aw); the genuinely remaining input is the exact coupled odd
numerator selected across depths.  The primary `proof sketch`, exact
`experiment`, independent audit, and disjoint replay are
[`bbp_scalar_padic_archimedean_separator_20260813.md`](work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813.md),
[`bbp_scalar_padic_archimedean_separator_20260813_check.py`](work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813_check.py),
[`bbp_scalar_padic_archimedean_separator_independent_audit_20260813.md`](work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_independent_audit_20260813.md),
and
[`bbp_scalar_padic_archimedean_separator_independent_check_20260813.py`](work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_independent_check_20260813.py).
Their SHA-256 values are respectively
`ce581bf5bb9c1b95d2405c27839bd6e894e90dda8d0a8c1808e1b722e059a357`,
`5c75450eda7f1998136a7e7583bb5c8925a791dfd8d1af4f76a57f94ec323350`,
`6cf12f644d3c9504997efebd5e44d64b0ce061e0e467d599c262da1d51df21b9`,
and
`b77c84b6e8d5ab54be930bde4cc94a76750664a6c1dc668ebde48d8a0eadd9d6`.
Both checkers pass; no fixed return or V1 is proved.

The second follow-up shifts the actual four-pole coefficient by one place.
Define

\[
 \widetilde B_n={1\over30}+\sum_{k=0}^n{a(k+1)\over16^k},\qquad
 u_n=\{10^nB_n\},\quad v_n=\{10^n\widetilde B_n\}.
\]

Then, for every \(n\ge1\),

\[
 \boxed{v_n=T_{16}u_n+a(n+1)(5/8)^n\pmod 1},         \tag{40aj}
\]

and the empirical shifted row is within \(5/(3N)\) in \(W_1\) of
\((T_{16})_*N^{-1}\sum_{n=1}^N\delta_{u_n}\), while its direct distance
in \(W_1\) from the actual \(16\cdot10^n\pi\) row is less than \(1/(9N)\).
This
coefficient-specific identity yields a strictly one-sided sufficient
criterion.  It is enough to find positive integers \(N_j\to\infty\), a
fixed positive integer congestion bound \(C\), sets
\(G_j\subseteq\{1,\ldots,N_j\}\), maps
\(\sigma_j:G_j\to\{1,\ldots,N_j\}\), and nonnegative \(\delta_j\to0\)
such that

\[
 {|G_j|\over N_j}\to1,\quad
 \max_m|\sigma_j^{-1}(m)|\le C,\quad
 \max_{n\in G_j}\operatorname{dist}(v_n,u_{\sigma_j(n)})\le\delta_j,
                                                               \tag{40ak}
\]

together with the anti-concentration condition

\[
 \lim_{\rho\downarrow0}\limsup_{j\to\infty}{1\over N_j^2}
 \#\{(m,n):1\le m,n\le N_j,\quad
              \operatorname{dist}(u_m,u_n)<\rho\}=0. \tag{40al}
\]

The matching makes the limiting \(T_{16}\)-pushforward dominated by the
original measure; (40al) makes that measure nonatomic.  Its support is then
forward invariant under both multipliers and contains an irrational point,
so Furstenberg gives full support and V1.  Neither (40ak) nor (40al) is
proved.  Finite cyclic-order matches are only an `experiment`, and generic
separators show that summably close forcing or a shared invariant empirical
limit does not imply the two hypotheses.  The corrected `proof sketch`, its
replay, independent audit, and independent replay are
[`bbp_adjacent_shift_matching_attack.md`](work/ultrapi-resume/bbp_adjacent_shift_matching_attack.md),
[`bbp_adjacent_shift_matching_check.py`](work/ultrapi-resume/bbp_adjacent_shift_matching_check.py),
[`bbp_adjacent_shift_matching_independent_audit.md`](work/ultrapi-resume/bbp_adjacent_shift_matching_independent_audit.md),
and
[`bbp_adjacent_shift_matching_independent_check.py`](work/ultrapi-resume/bbp_adjacent_shift_matching_independent_check.py).
They prove no fixed return and no V1.

An independently audited follow-up proves that the collision condition
(40al) is stronger than the Furstenberg step needs.  Retain the matching
(40ak), on the same sequence \(N_j\), but replace (40al) by the countable
family of fixed-period defects

\[
 \boxed{\forall P\ge1:\quad
 \liminf_{j\to\infty}{1\over N_j}\sum_{n=1}^{N_j}
 \bigl\|(10^P-1)u_n\bigr\|_{\mathbb T}^{2}>0.}      \tag{40az}
\]

Here \(P\) is fixed before \(j\to\infty\), its lower bound may depend on
\(P\), and every \(P\) is tested on the same \(N_j\).  If
\(N_j^{-1}\sum_{n\le N_j}\delta_{u_n}\Rightarrow\mu\), then for the
\(T_{10}\)-invariant probability \(\mu\)

\[
 \boxed{\operatorname{supp}\mu\text{ is infinite}
 \iff D_P(\mu):=\int\operatorname{dist}(T_{10}^Px,x)^2\,d\mu(x)>0
 \text{ for every }P\ge1.}                           \tag{40ba}
\]

Indeed, \(D_P=0\) confines the support to the finite fixed-point set of
\(T_{10}^P\), while a finite invariant support is permuted by \(T_{10}\)
and has a common period.  Matching (40ak) gives
\((T_{16})_*\mu\le C\mu\), hence \(T_{16}\operatorname{supp}\mu\subseteq
\operatorname{supp}\mu\).  An infinite closed set forward invariant under
both \(T_{10}\) and \(T_{16}\) is the whole circle: an irrational support
point has dense Furstenberg semigroup orbit; if all support points were
rational, the closed countable difference set would contain nonzero points
tending to zero, so Furstenberg's Lemma IV.2 would instead make that
difference set the whole circle.  Thus (40ak) plus (40az) implies V1 as a
`proof sketch`.

The new condition is also an exact fixed-lag statement on the one BBP row.
Iterating its perturbed decimal recurrence gives

\[
 u_{n+P}=T_{10}^Pu_n+E_{n,P},\qquad
 \sum_{n\ge1}E_{n,P}\le {10^P\over9}(1-16^{-P}),
\]

and therefore, for every \(N,P\ge1\),

\[
 \boxed{\left|{1\over N}\sum_{n=1}^N
 \left(\operatorname{dist}(u_{n+P},u_n)^2
 -\|(10^P-1)u_n\|_{\mathbb T}^{2}\right)\right|
 \le {10^P(1-16^{-P})\over9N}.}                      \tag{40bb}
\]

Consequently (40az) is equivalent to positive liminf of the mean squared
fixed-\(P\) displacement \(\operatorname{dist}(u_{n+P},u_n)\).  It is
strictly weaker than (40al):
\(\mu=(\delta_0+m)/2\), with \(m\) Lebesgue measure, has
\(D_P(\mu)=1/24\) for every \(P\) but atomic close-pair mass at least
\(1/4\).  Conversely, finite rational invariant grids show why every fixed
\(P\), not merely finitely many periods, is essential.

There is a second trade: if the empirical limit \(\mu\) is
\(T_{10}\)-ergodic, density-one matching in (40ak) can be weakened to

\[
 \boxed{\liminf_j{|G_j|\over N_j}>0,\qquad
 \max_m|\sigma_j^{-1}(m)|\le C,\qquad
 \max_{n\in G_j}\operatorname{dist}
 (v_n,u_{\sigma_j(n)})\to0.}                         \tag{40bc}
\]

A subsequential matched-pair measure then has a nonzero diagonal marginal
\(\rho\le(T_{16})_*\mu\) and \(\rho\le C\mu\), ruling out mutual
singularity.  The machine-checked T39 ergodic dichotomy forces
\((T_{16})_*\mu=\mu\); (40az) and (40ba) finish.  Neither ergodicity nor
(40bc) has been proved for the fixed BBP row.  The further exact identity

\[
                         \boxed{T_5v_n=T_8u_{n+1}\quad(n\ge1)} \tag{40bd}
\]

becomes only the tautology
\((T_5)_*(T_{16})_*\mu=(T_8)_*\mu\) at the measure level and cannot be
cancelled through the many-to-one maps.

The corrected primary `proof sketch`, exact `experiment` replay, independent
audit, and independently generated replay are
[`bbp_adjacent_matching_breakthrough_report.md`](work/ultrapi-resume/bbp_adjacent_matching_breakthrough_report.md),
[`bbp_adjacent_matching_breakthrough_check.py`](work/ultrapi-resume/bbp_adjacent_matching_breakthrough_check.py),
[`bbp_adjacent_matching_breakthrough_independent_audit.md`](work/ultrapi-resume/bbp_adjacent_matching_breakthrough_independent_audit.md),
and
[`bbp_adjacent_matching_breakthrough_independent_check.py`](work/ultrapi-resume/bbp_adjacent_matching_breakthrough_independent_check.py).
Their respective SHA-256 values are
`2b231d3c2e2ef717a2941a0452304ba402915318b72d305f6a6129ee8431f042`,
`2844f28d7ecdf13c02c623a3ba17c43dcde347efa4e8c4e864d48530eac873e9`,
`32cf25b1b2d00a37de57b325134ba0a53e8f5f6c129b16d3f419000a1620af93`,
and
`f7bca90e7dedd923c5b1a95ecf177905a23dbd3878d472625b43098286e2ce00`.
Both distinct exact checkers pass.  No matching, periodic-defect lower bound,
fixed return, or V1 is proved.

The fixed-period side is now reducible to one exact centered-carry stream.
For \(q_P=10^P-1\), define nearest integers and centered errors by

\[
 z_{n,P}=\left\lfloor q_P10^n\pi+\frac12\right\rfloor,
 \qquad e_{n,P}=q_P10^n\pi-z_{n,P},
\]

and the centered decimal carries

\[
 \gamma_{n,P}=z_{n+1,P}-10z_{n,P}=10e_{n,P}-e_{n+1,P}
 \in\{-5,-4,\ldots,5\}.                              \tag{40bi}
\]

Writing \(K_P(N)=\#\{0\le n<N:\gamma_{n,P}\ne0\}\) and
\(E_P(N)=\sum_{n<N}\|q_P10^n\pi\|_{\mathbb T}^2\), exact window estimates
give, on every prescribed sequence \(N_j\to\infty\),

\[
 \boxed{\liminf_j{E_P(N_j)\over N_j}>0
 \iff \liminf_j{K_P(N_j)\over N_j}>0.}              \tag{40bj}
\]

The rational BBP energy differs from \(E_P(N)\) by at most \(8q_P/45\) in
total, so (40az) is equivalent to positive lower density of these nonzero
carries for every fixed \(P\), all on the same \(N_j\).

Moreover, sevenfold oversampling makes the target wholly rational.  Put

\[
 \widehat z_{n,P}=\left\lfloor q_P10^nB_{7n}+\frac12\right\rfloor,
 \qquad
 \widehat\gamma_{n,P}=\widehat z_{n+1,P}-10\widehat z_{n,P}.           \tag{40bk}
\]

The source consequence \(\mu(\pi)<8\) separates \(q_P10^n\pi\) from every
half-integer by more than \((2^8q_P^7 10^{7n})^{-1}\), while the BBP error is
at most \(q_P10^n16^{-7n}/(15(7n+1)^2)\).  Since \(10^8<16^7\), the two
nearest integers, and hence the carries, agree for all sufficiently large
\(n\) at each fixed \(P\).  Thus the exact remaining noncollapse target is

\[
 \boxed{\forall P\ge1:\quad
 \liminf_j{1\over N_j}\#\{0\le n<N_j:
             \widehat\gamma_{n,P}\ne0\}>0.}          \tag{40bl}
\]

Known irrationality measures fall a factor \(N/\log N\) short.  From
Zeilberger--Zudilin's \(\mu(\pi)<888/125\), consecutive nonzero carries have
at most geometric gaps, which yields

\[
 \boxed{\liminf_{N\to\infty}{K_P(N)\over\log N}
 \ge {1\over\log(888/125)},\qquad
 \liminf_{N\to\infty}{E_P^B(N)\over\log N}
 \ge {1\over121\log(888/125)}.}                     \tag{40bm}
\]

The onset may depend on fixed \(P\); there is no uniform-in-\(P\) assertion.
This logarithmic order is an actual generic barrier: the transcendental,
badly approximable Kempner--Fredholm number has
\(\sum_{n<N}\|q_P10^n\kappa\|^2=\Theta_P(\log N)\) for every fixed \(P\),
while retaining the density-one matching from the preceding separator.
Therefore finite irrationality measure, transcendence, topological
excursions, and matching alone cannot supply (40bl); the missing input must
force linear carry density from the cross-depth four-pole numerator
coherence.

The independently refrozen primary report, replay, audit, and disjoint replay
are
[`bbp_fixed_period_carry_attack_20260813.md`](work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813.md),
[`bbp_fixed_period_carry_attack_20260813_check.py`](work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_check.py),
[`bbp_fixed_period_carry_attack_20260813_independent_audit.md`](work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_audit.md),
and
[`bbp_fixed_period_carry_attack_20260813_independent_check.py`](work/ultrapi-resume/bbp_fixed_period_carry_attack_20260813_independent_check.py).
Their SHA-256 values are respectively
`bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55`,
`48a9db36d577376b0229f48c37ae399cdebe62d1a9c0c2959bebd368a4fe9ceb`,
`ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91`,
and
`d784ae344752e5679657a8c61e6aa64f7508d61e72f4bb7a30e59fe44eb15204`.
The independent audit explicitly records and resolves the initial frozen-hash
mismatch.  Both checkers pass.  No positive Cesaro defect, matching theorem,
fixed return, or V1 is proved.

The rational carry stream has since been unfolded into exact cross-depth
integer coordinates.  With

\[
\begin{gathered}
 c_k=120k^2+151k+47,\qquad
 d_k=(2k+1)(4k+3)(8k+1)(8k+5),\\
 L_m=\operatorname{lcm}(d_0,\ldots,d_m),\qquad
 A_m=\sum_{k=0}^m c_k16^{m-k}{L_m\over d_k},\\
 D_n=2^{27n}L_{7n},\qquad
 U_{n,P}=q_P5^nA_{7n},\qquad
 S_{n,P}=U_{n,P}-D_n\widehat z_{n,P},
\end{gathered}                                                        \tag{40bn}
\]

put

\[
\begin{gathered}
 R_n={L_{7n+7}\over L_{7n}},\qquad
 H_n=\sum_{j=1}^7c_{7n+j}16^{7-j}{L_{7n+7}\over d_{7n+j}},\\
 \Lambda_n=2^{27}R_n,\qquad J_{n,P}=q_P5^{n+1}H_n.
\end{gathered}
\]

Splitting the BBP numerator after seven new terms gives the exact recurrence

\[
\boxed{\begin{aligned}
 D_{n+1}&=\Lambda_nD_n,\\
 U_{n+1,P}&=10\Lambda_nU_{n,P}+J_{n,P},\\
 S_{n+1,P}&=10\Lambda_nS_{n,P}+J_{n,P}
              -\widehat\gamma_{n,P}D_{n+1}.
\end{aligned}}                                                       \tag{40bo}
\]

The half-open convention \(-D_n\le2S_{n,P}<D_n\) makes the carry unique and
turns zero carry into the literal integer-interval test

\[
\boxed{\widehat\gamma_{n,P}=0\iff
 -D_{n+1}\le2(10\Lambda_nS_{n,P}+J_{n,P})<D_{n+1}.}                  \tag{40bp}
\]

Iterating (40bo) gives the analogous simultaneous test at every prefix of a
length-\(h\) zero block.  Independently audited all-depth two-adic algebra and
the elementary LCM update also give, for \(n\ge1\),

\[
\boxed{v_2(S_{n,P})=v_2(7n+1),\qquad
 R_n\mid\prod_{j=1}^7d_{7n+j},\qquad \log R_n=O(\log n).}            \tag{40bq}
\]

These facts expose rather than solve the selection problem.  The carry term
in (40bo) vanishes modulo every divisor of \(D_{n+1}\), so the complete
two-adic coordinate and every fresh odd-LCM congruence are carry-blind.  The
known irrationality measure still gives only

\[
 h<{763\over125}n+{763\over125}\log_{10}(q_P)-\log_{10}2
\]

for every sufficiently late zero block.  Exact rational computation even
finds five successive zero carries at \(n=761,\ldots,765\) although every
step has \(R_n>1\) and \(\gcd(J_{n,1},R_n)=1\).  This is an `experiment`, as
are the 943,633 nonzero carries among the first 1,048,571 certified true
\(P=1\) carries and the observed longest zero block of length six.  Conversely,
an autonomous finite-state or fixed-order carry-only recurrence is impossible:
eventual periodicity would make \(q_P\pi\) rational.  Neither observation
controls asymptotic frequency.

The generic algebra in (40bo)--(40bp) is now `machine-checked` in
[`T71T71CenteredCarryRecurrence.lean`](TheoryLib/PiQuantitativeBlockHitting/T71T71CenteredCarryRecurrence.lean):
half-open centered representatives are unique, the one-step remainder identity
and advanced old quotient are exact, and zero carry is equivalent to the
uncorrected numerator already lying in the new centered interval.  The module
deliberately does not instantiate the BBP coefficients or prove a density
claim.  The primary `proof sketch` and exact replay are
[`bbp_centered_carry_recurrence_20260813.md`](work/ultrapi-resume/bbp_centered_carry_recurrence_20260813.md)
and
[`bbp_centered_carry_recurrence_20260813_check.py`](work/ultrapi-resume/bbp_centered_carry_recurrence_20260813_check.py),
with SHA-256 values
`3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6`
and
`b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff`;
the replay passes.

Independent adversarial review of T71 also passes.  Its audit, separate Lean
boundary/type checks, and deterministic replay are
[`t71_centered_carry_independent_audit.md`](work/ultrapi-resume/t71_centered_carry_independent_audit.md),
[`t71_centered_carry_independent_checks.lean`](work/ultrapi-resume/t71_centered_carry_independent_checks.lean),
and
[`t71_centered_carry_independent_check.py`](work/ultrapi-resume/t71_centered_carry_independent_check.py),
with SHA-256 values
`37d8da4714efb37b8cd4bf8d22e755a401b2096cd6f203887b104532675e2ec9`,
`6ca67044ab3ae702e9fd3c7fe829246dcb33d837c1d97fe9d6a7186e8017a130`,
and
`ee87f7bbd75d7c9afb61fcc684951435352e3117b68bb7eaad5d967620892c7d`.
It verifies the lower tie is included, the upper tie excluded, all four audit
registrations occur exactly once, and only the existing allowed dependencies
`propext`, `Classical.choice`, and `Quot.sound` occur.  It also records the
chronological documentation lag in the frozen primary report: only T71's four
generic theorems may now be called `machine-checked`; the BBP, analytic, and
density deductions there retain their weaker labels.

The proposed adjacent-row matching endpoint has also been characterized
exactly.  If the two empirical rows converge to \(\mu\) and \(\nu\) on a
compact metric space, then, after passing to a subsequence,

\[
\begin{aligned}
 &\text{positive-mass, vanishing-distance matching with fixed congestion}
   &&\Longleftrightarrow\quad\mu\not\perp\nu,\\
 &\text{density-one matching with congestion }C
   &&\Longleftrightarrow\quad\nu\le C\mu.
\end{aligned}                                                        \tag{40br}
\]

The converses use finite injective matchings inside arbitrarily fine common
continuity-set partitions.  For the BBP rows \(\nu=(T_{16})_*\mu\).  If
\(\mu\) is \(T_{10}\)-ergodic, both measures are ergodic for the same map, so

\[
 \boxed{\text{either matching target}\iff(T_{16})_*\mu=\mu.}         \tag{40bs}
\]

Thus the finite matching language does not weaken the missing invariant-
measure statement in the proposed ergodic route.  Nor can one cancel the
exact identity \(T_5v_n=T_8u_{n+1}\) through its noninvertible fibres.  An
explicit fair-Bernoulli phase on decimal digits \(\{0,1\}\), corrected by the
same exact four-pole BBP tail, preserves all adjacent recurrences, this fibre
identity, ergodicity, entropy \(\log2\), nonatomicity, and every positive
fixed-period defect, yet satisfies
\(\mu\perp(T_{16})_*\mu\).  It does not preserve rationality of all finite
truncations, precisely isolating the selected rational phase as the remaining
possible leverage.

The matching `proof sketch`, primary replay, and disjoint replay are
[`bbp_fiber_matching_no_go_20260813.md`](work/ultrapi-resume/bbp_fiber_matching_no_go_20260813.md),
[`bbp_fiber_matching_no_go_check.py`](work/ultrapi-resume/bbp_fiber_matching_no_go_check.py),
and
[`bbp_fiber_matching_no_go_independent_check.py`](work/ultrapi-resume/bbp_fiber_matching_no_go_independent_check.py).
Their SHA-256 values are respectively
`9503ca68ac6ce64dedde9846ffdaec5c3073a2e5da28b8cd29df98827a9c8bca`,
`6ee7b3b88c8dcfaaa5df1d565d8ac968b6732f833f1b6f9da4f6628767bb0c2b`,
and
`abd825b76c0f09c48b2554b780f51d4b65e4cf105b75c962693c9b39c59938af`.
Both independent implementations pass and explicitly assert no V1 claim.

Finally, the fresh fixed-pi source audit finds a stronger topological but not
frequency conclusion.  Chen--Ye--Zheng's Theorem 1.3 applies directly to
\(x_n=q_P\pi10^n\) and proves

\[
 \boxed{\omega(\{x_n\})\text{ is infinite},\qquad
        \limsup_{n\to\infty}\|x_n\|_{\mathbb T}\ge{1\over11}.}       \tag{40bt}
\]

Since \(\gamma_{n,P}=0\) implies \(|e_{n,P}|<1/20\), this forces nonzero
centered carries at arbitrarily large indices.  It gives no number or density
of such indices: a sequence supported only at factorial times can satisfy the
same omega-limit and progression-slice spread conclusions while its empirical
measures converge to one atom.

Mahler's 1973 Theorem 2 is the closest unconditional all-word statement
located, but it has the wrong multiplier quantifier:

\[
 \boxed{\forall m\ \exists X_m\ \forall w\in\{0,\ldots,9\}^m\
        \exists^\infty n:\quad
        w\text{ occurs in the decimal expansion of }X_m\pi.}         \tag{40bu}
\]

The construction permits
\(1\le X_m<10^{2\cdot10^m+2m-1}\).  It neither sets \(X_m=1\), keeps one
multiplier for all \(m\), nor selects a repunit; finite multiplication carry
transducers cannot repair that quantifier mismatch.  Berend--Boshernitzan's
1994 Theorem 1.1 improves the multiplier for any one length-\(k\) block to
\(X<2\cdot10^{k+1}\), an order which their lower examples show is generally
best possible.  Applying that sharper theorem to a linearized length-
\(10^m+m-1\) decimal de-Bruijn word improves (40bu)'s common multiplier to

\[
                         X_m<2\cdot10^{10^m+m},
\]

but it remains word-length dependent and doubly exponential in \(m\); it
still gives no route to \(X_m=1\) for pi.  The dated
`literature-checked` report and passing checker are
[`pi_centered_carry_density_literature_audit_20260813.md`](work/ultrapi-resume/pi_centered_carry_density_literature_audit_20260813.md)
and
[`pi_centered_carry_density_literature_audit_20260813_check.py`](work/ultrapi-resume/pi_centered_carry_density_literature_audit_20260813_check.py),
with SHA-256 values
`61537ce66782bd89e96a7224d877acaf5f169b431beb2ca2ac0eaa11ea6fbd96`
and
`0f1c2d396dee752232dc55b3bc5deacdfff2e5404153afb2fe2ada1cd71fc8c4`.
The checker passes.  None of (40bn)--(40bu) proves (40bl) or V1.

The odd-LCM continuation resolves two tempting strengthenings of the carry
route.  From (40bo), every candidate correction \(c\in\mathbb Z\), not only
the actual carry, satisfies

\[
 \boxed{10\alpha_nS_{n,P}+J_{n,P}-cD_{n+1}
        \equiv J_{n,P}\pmod {R_n}.}                              \tag{40bv}
\]

Thus all congruences modulo new odd LCM prime powers are carry-blind.  The
exact replay exhibits five consecutive zero carries at \(n=761,\ldots,765\)
while every \(R_n\) is a square-free 31--106-bit product and
\(\gcd(J_{n,P},R_n)=1\); it also finds nonzero carries when \(R_n=1\).
These rows are an `experiment`, decisive against that local valuation rule
but not an asymptotic statement.

There is a second, structural correction.  Put
\(K_q=\{k/q\bmod1:0\le k<q\}\), with \(q=10^P-1\).  For the true
centered carries, irrationality removes all tie cases and gives

\[
 \boxed{
 \begin{aligned}
  \gamma_{n,P}=\cdots=\gamma_{n+H-1,P}=0
   &\iff \|q10^n\pi\|_{\mathbb T}<{1\over2\,10^H},\\
  \|qx\|_{\mathbb T}
   &=q\,\operatorname{dist}_{\mathbb T}(x,K_q).
 \end{aligned}}                                                    \tag{40bw}
\]

V1 makes every tail of the decimal orbit dense.  Multiplication by fixed
\(q\) is a surjection of the circle, so (40bw) implies the exact quantifier
order

\[
 \boxed{\mathrm{V1}\Longrightarrow
 \forall P,H\ge1\ \forall N\ge0\ \exists n\ge N:\quad
 \gamma_{n,P}=\cdots=\gamma_{n+H-1,P}=0.}                         \tag{40bx}
\]

The eventual fixed-\(P\) equality of the true and sevenfold rational carries
transfers (40bx) to the rational stream.  Consequently any uniform bounded
gap between nonzero carries would contradict V1.  Positive lower density is
still compatible with unbounded zero gaps, so this does not contradict the
average sufficient condition (40bl).

If \(h_P(n)\) is the maximal zero-run beginning at \(n\), (40bw) and
irrationality give the exact formula and the best currently available
unconditional scale

\[
 \boxed{h_P(n)=\left\lfloor
 -\log_{10}\!\left(2\|q10^n\pi\|_{\mathbb T}\right)
 \right\rfloor
 <{763\over125}n+{763\over125}\log_{10}q-\log_{10}2}             \tag{40by}
\]

for all sufficiently large \(n\), where the inequality uses
\(888/125>\mu(\pi)\).  More sharply, with constants allowed to depend on
\(P\),

\[
 \boxed{
 \begin{aligned}
 h_P(n)=O(\log(n+2))
 &\iff \|q10^n\pi\|_{\mathbb T}\ge c(n+2)^{-C},\\
 h_P(n)=o(n)
 &\iff-\log_{10}\|q10^n\pi\|_{\mathbb T}=o(n).
 \end{aligned}}                                                    \tag{40bz}
\]

The second line is exponent one only on the prescribed denominator grid
\(q10^n\), not a global irrationality-exponent claim.  The published
irrationality measure reaches only the linear bound (40by); even a
logarithmic gap bound by itself guarantees merely \(\Omega(N/\log N)\)
nonzero carries, not (40bl)'s \(\Omega(N)\).

The primary `proof sketch` and `experiment` replay are
[bbp_odd_lcm_carry_no_go_20260813.md](work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813.md)
and
[bbp_odd_lcm_carry_no_go_20260813_check.py](work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_check.py),
with SHA-256 values
`fcea6cb14082ee404fabf14a68215a3b7394d553ed401e51e8f70a333f234bfc`
and
`12d9ffef815f60b39d8f4d2f8c946bab10c1e29be94d25f19dfb1039ee15a905`.
The independent audit and disjoint checker are
[bbp_odd_lcm_carry_no_go_20260813_independent_audit.md](work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_independent_audit.md)
and
[bbp_odd_lcm_carry_no_go_20260813_independent_check.py](work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_independent_check.py),
with SHA-256 values
`9bce6cb05d99215f8a3bd8f83f754734dc07bd0eb54b5ca5096e98f7e614018a`
and
`0af6a02596bafec6253338e788b1b44d29bb1235511e9f8ac267c5b8eb3b484d`.
Both replays pass and assert no bounded-gap, logarithmic-gap, positive-density,
or V1 conclusion.

The exact target can now be expressed without any empirical or frequency
quantifier.  For \(P>0\), set \(q_P=10^P-1\), and define

\[
 \mathcal R(x):\Longleftrightarrow
 \forall P>0\ \forall\,0\le k<q_P\ \forall N\ \forall\varepsilon>0\
 \exists n\ge N:\quad
 \left|\{10^nx\}-{k\over q_P}\right|<\varepsilon.                  \tag{40ca}
\]

T72 proves in Lean, with ordinary real rather than circle distance,

\[
                  \boxed{\mathrm{V1}\iff\mathcal R(\pi).}          \tag{40cb}
\]

The reverse proof is endpoint-safe.  If a target word of length \(m\) has
integer value \(a\), it requests the interior color
\((10a+5)/(10^{m+1}-1)\), which lies strictly inside the word cylinder even
for leading-zero and all-nine words.  The forward proof first upgrades every
word occurrence to arbitrarily late occurrences, then approximates each grid
point through sufficiently long matching prefixes.  The ten supporting
declarations in
[`T72T72ColoredRepunitReturn.lean`](TheoryLib/PiQuantitativeBlockHitting/T72T72ColoredRepunitReturn.lean)
have SHA-256
`c5b59557d1d95a26c0c451d9cd8d62d073d3d7f918467e5b2b888233d2c83373`,
are registered exactly once in `audit/AxiomAudit.lean`, and passed the full
kernel, exploit, and exact-allowlist gate.  Their only dependencies are
`propext`, `Classical.choice`, and `Quot.sound`.  Equation (40cb) is an
equivalence, not a proof of either side.  The independent formal report
[`t72_colored_repunit_return_independent_audit.md`](work/ultrapi-resume/t72_colored_repunit_return_independent_audit.md),
SHA-256
`76279b1a0e5a9852097391b8a2dad75d9327106c9bcbdc5a03e3133b289ec916`,
recompiled the exact frozen T72 and axiom-audit hashes, checked all quantifier
orders and endpoint cases, and replayed the unchanged 8,493-job repository
gate with verdict `PASS`.

The centered formulation retains more combinatorial structure.  With
\[
 z_{n,P}=\left\lfloor q_P10^n\pi+\tfrac12\right\rfloor,\qquad
 \gamma_{n,P}=z_{n+1,P}-10z_{n,P},
\]
the elementary decimal-cylinder argument gives the `proof sketch`

\[
 \boxed{\mathrm{V1}\iff
 \begin{gathered}
 \forall P,H\ge1\ \forall\,0\le k<q_P\ \forall N\ge0\
 \exists n\ge N:\\
 z_{n,P}\equiv k\pmod {q_P},\qquad
 \gamma_{n,P}=\cdots=\gamma_{n+H-1,P}=0 .
 \end{gathered}}                                                     \tag{40cc}
\]

Literal endpoint colors split residue zero into the all-zero and all-nine
sides, but the residue version remains equivalent: every target word can be
extended by one digit to an interior color.  Conversely, a zero block at an
interior color \(k\) keeps the orbit within half the distance to the
endpoints of the corresponding periodic-word cylinder.  Eventual fixed-\(P\)
equality of true and sevenfold rational nearest integers transfers (40cc)
unchanged to \(\widehat z_{n,P},\widehat\gamma_{n,P}\).

All periods are controlled by one rational state.  Retain \(D_n\),
\(\Lambda_n=D_{n+1}/D_n\), and \(H_n\) from (40bn), and put

\[
 \begin{aligned}
 V_n&=5^nA_{7n}=a_nD_n+r_n,\qquad 0\le r_n<D_n,\\
 K_n&=5^{n+1}H_n,\\
 b_n&=\left\lfloor{10\Lambda_nr_n+K_n\over D_{n+1}}\right\rfloor,\\
 r_{n+1}&=10\Lambda_nr_n+K_n-b_nD_{n+1},\qquad
 a_{n+1}=10a_n+b_n .
 \end{aligned}                                                       \tag{40cd}
\]

Thus \(r_n/D_n=\{10^nB_{7n}\}\) is independent of \(P\).  Its exact split
color and carry are

\[
 \boxed{
 \begin{aligned}
 \widehat c_{n,P}
  &=\left\lfloor{q_Pr_n\over D_n}+\tfrac12\right\rfloor,\\
 \widehat z_{n,P}
  &=q_Pa_n+\widehat c_{n,P},\\
 \widehat\gamma_{n,P}
  &=q_Pb_n+\widehat c_{n+1,P}-10\widehat c_{n,P}.
 \end{aligned}}                                                       \tag{40ce}
\]

This isolates the remaining problem exactly: prove that the single changing
rational phase in (40cd), through all partitions (40ce), shadows every
interior periodic word for arbitrary lengths and arbitrarily late starts.
Fixed-modulus shortcuts cannot see that event.  Indeed

\[
 n\ge\left\lceil{q_P-1\over14}\right\rceil
 \Longrightarrow q_P\mid L_{7n}\mid D_n,\qquad
 D_n\widehat z_{n,P}\equiv-S_{n,P}\equiv0\pmod {q_P}.                \tag{40cf}
\]

The color remains variable because it is selected by the Archimedean ratio
\(r_n/D_n\), not by \(r_n\bmod q_P\).  The exact replay even finds equal
values modulo 9 at two depths with different colors.

Finally, the irrational sparse decimal

\[
                         \xi=\sum_{j=2}^{\infty}10^{-j!}             \tag{40cg}
\]

has arbitrarily late, arbitrarily long uncolored zero-carry blocks for every
fixed period, yet digit 2 never occurs.  This proves that the color quantifier
in (40cc) is essential.  The primary `proof sketch` and exact `experiment`
replay are
[`bbp_colored_zero_carry_v1_20260813.md`](work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813.md)
and
[`bbp_colored_zero_carry_v1_20260813_check.py`](work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_check.py),
with SHA-256 values
`159ff0d1c94d9fb145790e0ca4f11db571d0af211ef2c588b094201122ff279a`
and
`7fbce9df0a4a92831ce7cadc5c0343546be71dd771331f7b5f7270fd4150d916`.
The replay passes 3,200 phase/color identities and 11,102 periodic-word
checks while explicitly asserting neither (40cc) for pi nor V1.
The disjoint
[`independent audit`](work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_independent_audit.md)
and
[`independent checker`](work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_independent_check.py),
with SHA-256 values
`b750fb9bd3c7ff30316f87ae6e3317ad61dded1c2fb73a9ea8bfbe23abf41048`
and
`46c3b807872b7e483c05e1eabe9c42bb7b4307abf2ff5022b6e4f9e51ed75433`,
also report `PASS`: they rederive every equivalence and boundary case, check
14,021 zero-block/grid instances, all 99,998 interior colors at (P=5),
all 100,000 five-digit words through the (P=6) append construction, and
new common-phase, modulus-absorption, transfer, endpoint, and sparse-stream
rows.  Both artifacts explicitly assert neither the colored condition for pi
nor V1.

The independently audited rational-phase construction closes a different
class of local arguments.  The exact BBP forcing
\(\delta_n=q_P10^{n+1}(B_{7n+7}-B_{7n})\) has the unique bounded all-zero
solution

\[
          \boxed{t_n=-q_P10^n(\pi-B_{7n}),\qquad
                 t_{n+1}-10t_n=\delta_n.}                            \tag{40ch}
\]

It is irrational, negative, and tends to zero.  Hence a bounded rational
zero-carry phase cannot use the exact forcing after one final reset; this
proves infinitely many resets only, not positive reset density.

Let \(Q_{n,P}\) be the exact reduced denominator of
\(q_P10^nB_{7n}\).  The audited denominator ledger and Kanold's Jacobsthal
bound give

\[
 \begin{gathered}
 \log Q_{n,P}=(42+27\log2+o(1))n,\quad
 v_2(Q_{n,P})=27n-v_2(7n+1),\quad\omega(Q_{n,P})=o(n),\\
 \exists(A_n,Q_{n,P})=1:\quad
 \left|{A_n\over Q_{n,P}}-t_n\right|
 \le {2^{\omega(Q_{n,P})}+1\over Q_{n,P}} .
 \end{gathered}                                                       \tag{40ci}
\]

For all sufficiently large \(n\), the chosen phase \(A_n/Q_{n,P}\) lies in
\((-1/2,0)\), so every carry is zero.  Its reduced denominator is exactly
\(Q_{n,P}\), its raw centered numerator has the exact BBP two-adic order
\(v_2(7n+1)\), and its positive forcing satisfies

\[
 {\widetilde\delta_n\over\delta_n}
 =1+O\!\left(e^{-(42+\log5-o(1))n}\right).                            \tag{40cj}
\]

A distinct coherent separator resets at \(N_j=2^jN_0\) and between resets
uses
\[
 \overline e_n=t_n+10^{\,n-N_j}
       \left({A_{N_j}\over Q_{N_j,P}}-t_{N_j}\right).
\]
It has denominator dividing \(D_n\), zero carries everywhere, and

\[
 \boxed{\overline\delta_n=\delta_n
 \text{ except at }O(\log N)\text{ transitions below }N,\qquad
 \left|{\overline\delta_n-\delta_n\over\delta_n}\right|
 \le e^{-(c_0-o(1))n},\quad
 c_0=21-14\log2+\tfrac12\log5>12.1.}                                  \tag{40ck}
\]

The exact-\(Q\)/two-adic package in (40ci)--(40cj) and the density-one exact
forcing package in (40ck) belong to two different sequences; no single
separator is claimed to possess both.  Neither preserves the exact selected
numerator \(J_{n,P}=q_P5^{n+1}H_n\) at every depth.  The direct product over
\(K\) zero blocks has denominator exponent \(K\) and degree \(K\), so its
height ledger also loses the density factor; fixed finite differences enlarge
the \(O(\log N)\) reset set only by a bounded neighborhood.

The frozen primary report/checker and independent audit/checker are
[`bbp_rational_phase_density_separator_20260813.md`](work/ultrapi-resume/bbp_rational_phase_density_separator_20260813.md),
[`bbp_rational_phase_density_separator_20260813_check.py`](work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_check.py),
[`bbp_rational_phase_density_separator_20260813_independent_audit.md`](work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_independent_audit.md),
and
[`bbp_rational_phase_density_separator_20260813_independent_check.py`](work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_independent_check.py).
Their SHA-256 values are, respectively,
`1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198`,
`72dfd913b3532bfe41e1df9a87ebbb3000f6fe1d179af4edbc0163d2a36cc3bc`,
`52589a8caa68224b41331c265462f894daf80770c88b8b0861339bf25ecb01dd`,
and
`2d55e4abb1a92860a44798c07c970ea2831c33f98ff056ae721cae11f3386ea2`.
Both exact replays pass on disjoint periods and depths and assert no positive
carry density or V1.  A second independent audit and independently scoped
checker are
[`bbp_rational_phase_density_separator_20260813_second_independent_audit.md`](work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_second_independent_audit.md)
and
[`bbp_rational_phase_density_separator_20260813_second_independent_check.py`](work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_second_independent_check.py),
with SHA-256 values
`03c8ccd1f9905d0ae7cfb4627adc576de114a8227842cf1c6b00a66f1cb74ed0`
and
`7f76b9802318d89e1ae3f825e49049755e645e9d94f2fe730f2916ffeb99f96a`.
It reaches the same verdict and confirms explicitly that the coherent rows
need not retain the exact reduced denominator.  The surviving route must
inspect the exact selected numerator correlation at every depth, or leave the
BBP route entirely.

A stronger full-odd/growing-prefix separator now localizes that surviving
correlation further.  With

\[
 D_n=2^{27n}L_{7n},\qquad V_n=5^nA_{7n},\qquad
 t_n=-10^n(\pi-B_{7n}),\qquad \kappa_n=2n+4,
\]

choose (S_n^*\equiv V_n\pmod {2^{\kappa_n}L_{7n}}) closest to
(D_nt_n), and put (e_n^*=S_n^*/D_n) and (r_n^*=D_n+S_n^*).  Nearest
selection and the first omitted BBP term give

\[
 |e_n^*-t_n|\le2^{3-25n},\qquad
 {|e_n^*-t_n|\over|t_n|}
 \le2688(7n+1)^2(4/5)^n=o(1).                                  \tag{40cl}
\]

Thus (e_n^*\to0) from below.  At the same time the construction retains

\[
 \boxed{
 \begin{gathered}
 r_n^*\equiv V_n\pmod {L_{7n}},\qquad
 r_n^*\equiv V_n\pmod {2^{2n+4}},\\
 \gcd(qr_n^*-zD_n,D_n)=\gcd(qV_n,D_n)\quad(q\ge1, z\in\mathbb Z),\\
 K_n^*\equiv K_n\pmod {2^{2n+6}L_{7n+7}},\qquad
 {K_n^*/D_{n+1}\over K_n/D_{n+1}}
   =1+O\!\left(n^2(4/5)^n\right).
 \end{gathered}}                                                 \tag{40cm}
\]

Nevertheless every fixed repunit multiplier eventually has exact quotient
(b_n^*=9), split color (10^P-1), and zero centered carry forever.  The
same construction preserves (lfloor cn\rfloor) low binary digits for every
fixed (c<\log_2 5).  This bound is the threshold of the displayed
worst-case nearest-grid estimate, not an impossibility theorem at or above
that slope.  Hence even the complete odd selected residue, every determinant
gcd, the complete reduced denominator, a linear low-dyadic prefix, and the
corresponding transition class do not force an interior color.  The primary
[`proof sketch`](work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813.md)
and exact
[`experiment`](work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_check.py)
have SHA-256 values
`5edd6bdacb3d0d9a6b12b4265da777891bdc22d2b95a1c75bc102e475280d0f6`
and
`017c7d17b68700bea23f89f859df16390de4e1f65f6cb1a6298eb27d04b6171d`.
The disjoint
[`independent audit`](work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_selected_numerator_prefix_separator_20260813_independent_check.py),
SHA-256
`4baa094e86981677aed41c546774904f2eb8ce622dd32b270a7eaa94acb45d5d`
and
`b40896575c796525b1c3581c00feb1d17bc3c54ec4193f486edf43afce0dd240`,
both report `PASS` and explicitly assert neither the colored condition nor
V1.

There is, however, no freedom to turn such a separator into a second
BBP-quality approximation while also fixing the actual high-prime
coordinates.  In the reduced decomposition

\[
 16B_M={w_M\over D_M}+{c_M\over R_M},\qquad
 S_M=\prod_{\substack{p>M\\p\mid R_M}}p,\qquad
 C_M={R_M\over S_M},
\]

any shadow with the same (w_M) and every actual additive CRT coordinate at
(p>M) has (c'_M-c_M=S_Mt), and therefore exactly

\[
                  X_M(c'_M)-B_M={t\over16C_M}.                    \tag{40cn}
\]

The prime-power ledger gives

\[
 \log C_M\le\vartheta(M)+
  \sum_{\ell\ge2}\vartheta((8M+5)^{1/\ell})+O(\log M)
  =(1+o(1))M.                                                   \tag{40co}
\]

Distinct coordinate-preserving shadows are thus separated by at least
(exp(-(1+o(1))M)), whereas two points in the certified BBP window can
differ by at most
(2\,16^{-M}/(15(M+1)^2)=\exp(-(\log16+o(1))M)).  Since
(log16>1), the exact (B_M) is eventually the unique such shadow.  This
`proof sketch` closes CRT/Dirichlet/Jacobsthal steering of the remaining
cofactor inside the transfer window; it still gives no short-orbit estimate
for that unique point.  The frozen report and primary exact replay are
[`bbp_high_prime_coordinate_rigidity_20260813.md`](work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813.md)
and
[`bbp_high_prime_coordinate_rigidity_20260813_check.py`](work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_check.py),
with SHA-256 values
`419158fe378aafdeb9ceef977b702e2409a81ddfbeca5e2fe43ec119b426cd42`
and
`b80afdebbcb75b4c45a30a11fb3f8cf618119124d4354c637e559730bf3ef157`.
The replay reports `PASS` and asserts neither the fixed return nor V1.  A
disjoint
[`independent audit`](work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_high_prime_coordinate_rigidity_20260813_independent_check.py),
with SHA-256 values
`f77afc636a65c2dddf93d1ca22f243edc3373a4d409384171b275a5778aae557`
and
`71cff87466f5169a226ad86fffc487e84f4e4e24ebcbb50478da45674147564d`,
report `PASS`.  They rederive the lattice identity, the prime-power ledger,
and the uniqueness comparison, replay 53,952 coordinate tests and 676 exact
lattice identities, and stress the calculation through depth 300.  The audit
clarifies that exponent one for (p>M) uses both (p^2>8M+5) and the
pairwise-resultant exclusion, and that (40co) supplies a lower bound on the
lattice spacing rather than an asymptotic equality.  Neither clarification
changes the rigidity conclusion.

The formerly missing *complete* dyadic coordinate is now explicit.  For the
audited two-adic BBP function

\[
 F(X)=\sum_{j\ge0}16^j a(X-1-j)
\]

one has, as an ordinary rational identity,

\[
 \boxed{F(N+1)={A_N\over L_N}=16^N B_N},\qquad
 w_n=\left[{5^nF(7n+1)\over2^{r_n}}\right]_{2^{27n-r_n}},
 \quad r_n=v_2(7n+1).                                      \tag{40cp}
\]

Seven iterations of the four-pole recurrence give the exact diagonal update

\[
 \boxed{
 w_{n+1}=2^{-r_{n+1}}
 \left[5^{n+1}G_n+5\,2^{28+r_n}w_n\right]_{2^{27(n+1)}}.}    \tag{40cq}
\]

At every *fixed* precision the underlying map is perfectly mixing: if
\(Z(n)=5^nF(7n+1)\), then

\[
 \boxed{v_2(Z(n)-Z(n'))=v_2(n-n')}\qquad(n\ne n'),           \tag{40cr}
\]

so \(Z\bmod2^s\) permutes all residues modulo \(2^s\).  More precisely, on
the valuation stratum
\(n=a_r+2^{r+1}m\), where
\(a_r\equiv7^{-1}(2^r-1)\pmod {2^{r+1}}\), the reduced units
\(U_r(m)=Z(n)/2^r\) satisfy

\[
 \boxed{v_2(U_r(m)-U_r(m'))=1+v_2(m-m')},                    \tag{40cs}
\]

and therefore biject the \(2^{s-1}\) parameter classes onto all odd residues
modulo \(2^s\).  This includes the independently audited even-depth result as
the case \(r=0\).  The quantifier obstruction is now exact: the selected
precision is \(27n-r_n\), while a full permutation at the raw precision
\(27n\) has period \(2^{27n}\).  Fixed-level bijectivity supplies no estimate
on that exponentially moving diagonal.

The dual construction also shows why knowing every dyadic bit is not enough.
It produces a distinct rational recurrence with the same complete dyadic
selected coordinate, the same complete next-depth dyadic forcing class, and
relative BBP forcing error tending exponentially to zero, yet with eventual
zero carries and only the all-nine color.  A stronger mixed construction
retains in addition both clean high-prime bands

\[
 Q_M=\prod_{p\in\mathcal P_{1,M}\cup\mathcal P_{2,M}}p,
 \qquad \log Q_M=(10/3+o(1))M,                              \tag{40ct}
\]

and constructs states satisfying

\[
 \boxed{
 S_n^\diamond\equiv V_n\pmod {2^{27n}Q_{7n}},\qquad
 K_n^\diamond\equiv K_n
       \pmod {2^{27(n+1)}Q_{7(n+1)}}}                       \tag{40cu}
\]

with the same eventual zero-carry/all-nine behavior.  The nearest-grid proof
works for retained odd logarithmic mass \((\rho+o(1))M\) exactly in the
certified range

\[
 \rho<\rho_*:=6-{\log(2^{27}/5)\over7}
       =3.5563520053\ldots .                                \tag{40cv}
\]

This is the threshold of that construction, not an impossibility statement
above it.  At the opposite end, (40cn)--(40co) show that retaining every
actual prime above \(M\), all dyadic data, and the BBP real window makes the
shadow unique.  Thus the gap between separator and rigidity is not missing
coordinate bookkeeping: uniqueness merely reconstructs the one still
undistributed phase.

The residual odd coordinate can now be localized more tightly as well.  If
all actually surviving simple-pole coordinates above \(\sqrt{8M+5}\) are
removed, the remaining cofactor \(C_M^\square\) obeys

\[
 \boxed{P^+(C_M^\square)\le\sqrt{8M+5},\qquad
        \log C_M^\square=O(\sqrt M\log M)=o(M).}              \tag{40cw}
\]

Its full 5-primary part is nevertheless unavoidable and exactly known:

\[
 \boxed{v_5(R_M)=\lfloor\log_5(8M+5)\rfloor.}                \tag{40cx}
\]

Consequently the shortcut \(10^n\equiv16\pmod C\) has no solution, since
it already fails modulo 5.  Writing \(C=5^eC_0\) and using its additive CRT
coordinates \(\beta_5,\beta_0\), the corrected rowwise identity is

\[
 A_n{\eta\over C}\equiv-{\beta_5\over5^e}
       +A_n{\beta_0\over C_0}\pmod1,
 \qquad n\ge\max(4,e).                                     \tag{40cy}
\]

Thus the entire 5-primary phase is constant along every relevant BBP row,
but the remaining small-prime power orbit is not controlled.  The independent
audit caught the formerly omitted \(n\ge4\) integrality condition, exhibited
the exact excluded counterexample \((M,n)=(48,3)\), and rechecked all intended
rows after correction.

Equations (40cp)--(40cq) and the complete-dyadic separator are recorded in
[`bbp_high_dyadic_archimedean_separator_20260813.md`](work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813.md)
and its
[`checker`](work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_check.py),
SHA-256
`d0d975ff9bab6ce456723085cb3e031a3be83a171fa6a94d8656d76d8b0457b3`
and
`69d07d421b215b85bd5e5f7a7d4036c9d38544a3a0a8fc7db4a6947687cb0ab8`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_high_dyadic_archimedean_separator_20260813_independent_check.py),
SHA-256
`8a9d1010e79103f03a9dc805b0b0148163ae47fd0b291e198df489d0ba81a7a8`
and
`b64e69dec2e19d969d61f41a1ae26873254028c70a8276820ab9c18d1d924f2b`,
report `PASS`.

The even-depth and all-stratum `proof sketch` reports and exact `experiment`
checkers are respectively
[`bbp_even_depth_dyadic_mixing_20260813.md`](work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813.md),
[`checker`](work/ultrapi-resume/bbp_even_depth_dyadic_mixing_20260813_check.py),
[`bbp_all_stratum_dyadic_mixing_20260813.md`](work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813.md),
and
[`checker`](work/ultrapi-resume/bbp_all_stratum_dyadic_mixing_20260813_check.py),
with SHA-256 values
`3d47a6a17e759d18b0aafb6215405226eadb99d1d83241a160dc93f6f8a3e623`,
`d05ed720b94c23d3d59c23b6bc300d46e6d88dc9f37d31ab5dddb604ce19a839`,
`5089d63f83de1978731c50964c7fce45e7a4cc88e989a29acd99e08b8a9c8360`,
and
`dbbf1cbeba9915f3377ae5dbb4a03026be031b1112bc924ab7211227dccc0fcf`.
Their independent audits/checkers have hashes
`6b23b2dd6789141611373be5f41218b07136dc7401f0e8ca6f2387e836700a5c`,
`0ec0eef61677f5d963d936ad8e52e2ee285f998de50b8a90b7876b8f474ac29b`,
`3bc52a90be2b6379c43218520b0c1a1d86a5418a98c7eafab56ef6df751b14f4`,
and
`8a71e6b3d337c4fe848978d600411f8735b3fd1e533eeb8f0a913c041338ad73`;
all report `PASS`.

The mixed threshold (40ct)--(40cv) is independently passed in
[`bbp_mixed_coordinate_height_separator_20260813.md`](work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813.md),
[`checker`](work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_check.py),
[`audit`](work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_independent_audit.md),
and
[`independent checker`](work/ultrapi-resume/bbp_mixed_coordinate_height_separator_20260813_independent_check.py),
whose SHA-256 values are
`950b18b4ac30adc7d65a8a0d418f7fc4b7c5536d7b51d4f08b984f745d2c5820`,
`6549b99503cb34aaf757f0c428702b3797714144d0bc8e1f77a336fe965d6846`,
`55f45caf07a2f1bf02b178f6884bae1c8f4c4d9643d47ee4dcf4422a8e1ccff9`,
and
`c95daf68ea535cc3fb41b30cedab7c4723bd3eca0776bea364fac8073b365fe0`.

Finally, (40cw)--(40cy) are the corrected `proof sketch` in
[`bbp_odd_cofactor_short_orbit_experiment_20260813.md`](work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813.md),
with exact `experiment`
[`checker`](work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_check.py),
SHA-256
`c648520d7c118ed63326afffce407a05ff2b05ca69efae36caeb20d1a06851c3`
and
`5f35c22f15f65dc8ca979908dbf58e7c88879d022287ee480821f5f88fb4b664`.
The
[`independent audit`](work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_independent_check.py),
SHA-256
`e31e6a64dd1e3df5d7c8cceb21f69ae74c9330ed364f54ebc69d0c440f6c54d1`
and
`3912cad4ba139c966447d3e7ca48b10b53e9ca439496672ff669451bf0a12f26`,
report final `PASS`.  These results isolate a smaller synchronized phase but
prove neither the fixed return nor V1.

The full high-prime additive phase itself has a further exact compression.
For every actual prime \(p>M\) in the reduced odd denominator, its localized
coordinate \(G_{M,p}=a_{M,p}/b_{M,p}\) has \(b_{M,p}\mid105\).  The elementary
residue lift

\[
 { [ab^{-1}]_p\over p}\equiv
 {\kappa_{a,b}(p)\over b}+{a\over bp}\pmod1,
 \qquad \kappa_{a,b}(p)p\equiv-a\pmod b,                       \tag{40cz}
\]

therefore gives

\[
 \boxed{
 \Xi_M^>\equiv {J_M\over105}+H_M\pmod1,
 \qquad
 H_M=\sum_{\substack{p>M\\p\mid R_M}}{G_{M,p}\over p}.}       \tag{40da}
\]

Here \(J_M\bmod105\) is an explicit weighted count of primes in the six
fixed bands and residue classes modulo \(840\); no inverse modulo a growing
integer remains in this grid term.  Fixed-modulus PNT in progressions plus
partial summation yields the positive asymptotic

\[
 \boxed{
 H_M={C_>\over\log M}+O(\log^{-2}M),\qquad
 C_>=32.525874511493811\ldots>0.}                            \tag{40db}
\]

For \(A_n=(10^n-16)/16\), the return action becomes exactly

\[
 \boxed{
 A_n\Xi_M^>\equiv {A_nJ_M\over105}
       +10^n{H_M\over16}-H_M\pmod1.}                         \tag{40dc}
\]

The first term lies on a \(1/35\)-grid because \(A_n\bmod105\) has the
six-cycle \(99,54,24,39,84,9\).  Hence the exponentially large high-prime
CRT object has been reduced to a fixed grid plus the decimal shift of one
explicit signed reciprocal-prime rational.  This is a structural advance,
not a distribution theorem: evaluating (40db) inside (40dc) would require
absolute precision \(o(10^{-n})=\exp(-\Theta(M))\), whereas PNT/AP and
Siegel--Walfisz provide only \(\exp(-o(M))\)-scale information and do not
determine \(J_M\bmod105\).

The localization extends to a moving cutoff.  For every fixed
\(\varepsilon>0\), one may choose a fixed cutoff parameter so that eventually

\[
 \boxed{
 \Xi_M^\star\equiv {J_M^\star\over E_M}+H_M^\star\pmod1,
 \quad E_M\le M^\varepsilon,\quad H_M^\star=o(1),\quad
 \prod_{\substack{p>Y_M\\p\mid R_M}}p
       \mid\operatorname{den}(H_M^\star).}                    \tag{40dd}
\]

The product in (40dd) has logarithmic mass \((6+o(1))M\), so the tiny real
lift still has an exponentially large exact denominator.  Moreover a single
row exponent can locally annihilate at most \(n\log10\le M\log16\) of that
mass.  Thus at least \((6-\log16+o(1))M\) remains unannihilated (and at least
\((5-\log16+o(1))M\) for the fixed \(p>M\) cutoff).  This is only a
logarithmic-mass statement: surviving CRT components may cancel
Archimedeanly, so it supplies no lower bound for the phase.

The primary `proof sketch` and exact `experiment` are
[`bbp_high_prime_phase_compression_20260813.md`](work/ultrapi-resume/bbp_high_prime_phase_compression_20260813.md)
and its
[`checker`](work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_check.py),
SHA-256
`47f56886b769a36f5f397cad567579838d455f59b75af8ca458a8000dfb7c564`
and
`7df64d082de31da1d902fa0e6418b97a5101cd14f93e495d141631535f3925ed`.
The
[`independent audit`](work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_high_prime_phase_compression_20260813_independent_check.py),
SHA-256
`5bce359596b5c07f58f8e9f3a7c1c3d13401a3c40461c44a27100d28b6b990d7`
and
`49298d7adabe2cb7a7f6993998130789bf07d70da9069de56ff30ba7e3b2a5f9`,
report `PASS`.  The audit independently verifies the band constant, bounded
endpoint errors, moving-cutoff quantifiers, reduced-denominator survival,
periods, and annihilation ledger.  It explicitly limits the precision no-go
to direct uniform asymptotic replacement; a new pointwise exponential-sum
theorem for the exact rational phase remains possible and is now the active
analytic target.

Cross-depth variation does not provide a second averaging parameter.  The
increment of the reciprocal-prime lift is completely local: at depth
\(M+1\), at most four new pole events enter and the possible boundary prime
\(q=M+1\) leaves, so

\[
 \boxed{
 H_{M+1}-H_M=
 \sum_{p\in\mathcal N_{M+1}}{\varepsilon_{M+1,p}\over p}
 -\mathbf1_{\{q\ \mathrm{prime},\ q\mid R_M\}}{G_{M,q}\over q},
 \qquad |H_{M+1}-H_M|\le{320\over M+1}.}                      \tag{40de}
\]

After adjoining the dyadic coordinate, the true 5-primary coordinate, and
the residual cofactor, these potentially macroscopic component jumps cancel
exactly.  On two adjacent rows sharing the exponent \(n\),

\[
 \boxed{
 \Phi_{M+1,n}-\Phi_{M,n}
 =(10^n-16){a(M+1)\over16^{M+1}},qquad
 0<\Phi_{M+1,n}-\Phi_{M,n}\le{1\over15(M+1)^2}.}              \tag{40df}
\]

Consequently, for fixed \(n\), all admissible depths form a column of
diameter \(O(n^{-2})\) around the one actual orbit point
\(z_n=(10^n-16)\pi\).  More globally, if

\[
 \mathcal D_X=\{(M,n):48\le M\le X,\ M\le n\le
                   \lfloor(\log_{10}16)M\rfloor\},
\]

and \(w_X(n)\) counts rows containing \(n\), then every fixed Fourier
frequency satisfies

\[
 \boxed{
 \sum_{(M,n)\in\mathcal D_X}e(h\Phi_{M,n})
 =\sum_n w_X(n)e(hz_n)+O_h(\log X).}                          \tag{40dg}
\]

Thus the \(\Theta(X^2)\) double array contains only \(O(X)\) asymptotically
distinct columns; normalized cancellation for it is a triangularly weighted
version of the original one-dimensional pi-orbit problem.  Pigeonhole on
these repetitions yields close pairs, not the prescribed point zero.  The
exact countermodel \(x=1/45\) has

\[
                  (10^n-16)x\equiv13/15\pmod1\quad(n\ge1),   \tag{40dh}
\]

so every pair gap is zero while every point stays \(2/15\) from the target.

The double-audited `proof sketch` and exact `experiment` are
[`bbp_cross_depth_phase_compensation_20260813.md`](work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813.md),
[`checker`](work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_check.py),
[`independent audit`](work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_independent_audit.md),
and
[`independent checker`](work/ultrapi-resume/bbp_cross_depth_phase_compensation_20260813_independent_check.py),
with SHA-256 values
`3ff784ebad18c8dda7c63691ba99120f80299953361362f7d2f2f8cd26f89d3f`,
`0a62b6d88414536fdb160a25a4d177e12d95cd712f76d980a0a0d40405541724`,
`72e130351d6abf8fffbd5fe60c1e13be9baa5ff3c72969b766185b8aaba8c986`,
and
`bc7d1c0edbc3fd7c924d00705e5151b82cbc85ab1eae5f877047972afc6779fd`.
Both implementations report `PASS`.  They show compensation and duplicated
sampling, not a fixed-sixteen return.

The selected dyadic diagonal has now been reduced to an exact nonautonomous
decimal recurrence.  With

\[
 Z_n=5^nF(7n+1),\qquad K_n=27n,\qquad
 X_n={[Z_n]_{2^{K_n}}\over2^{K_n}},
\]

seven iterations of the BBP functional equation give

\[
 \boxed{X_{n+1}=\{10X_n+\Gamma_n\},\qquad
 \Gamma_n={[5^{n+1}G_n]_{2^{27(n+1)}}\over2^{27(n+1)}}.}    \tag{40di}
\]

This is the complete normalized coordinate, not a fixed-precision
projection.  More importantly, its forcing is no longer opaque.  For seven
explicit quartic odd denominators \(d_{n,j}=O(n^4)\), and explicit residues
\(0\le h_{n,j}<d_{n,j}\),

\[
 \boxed{
 \Gamma_n=\left\{\sum_{j=1}^7{h_{n,j}\over d_{n,j}}
                    +\varepsilon_n\right\},\quad
 h_{n,j}\equiv-C_{n,j}(5\,2^{-27})^{n+1}\pmod {d_{n,j}},}   \tag{40dj}
\]

where \(C_{n,j}\) is the displayed quadratic/power-of-two coefficient and

\[
 0<\varepsilon_n\le {16^7-1\over15(7n+1)^2}
       \left({5\over2^{27}}\right)^{n+1}.                    \tag{40dk}
\]

Thus the remaining dyadic problem is a simultaneous discrepancy theorem for
seven rational-base power residues modulo changing quartic integers, strong
enough to survive the expanding recurrence (40di).  Fixed-level perfection
does not prove this: although \(Z\bmod2^s\) permutes every fixed residue
ring, the selected precision is \(27n\).  The exact mod-four table

\[
                    (Z(0),Z(1),Z(2),Z(3))=(1,0,3,2)          \tag{40dl}
\]

has two cycles, so the induced isometry is measure-preserving but not
ergodic on all of \(\mathbb Z_2\); moreover the diagonal samples values of
\(Z\), not iterates of that map.  The rational states are infinite and not
eventually periodic, but that does not force one prescribed interval.

The primary `proof sketch` and exact `experiment` are
[`bbp_dyadic_diagonal_functional_recurrence_20260813.md`](work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813.md)
and its
[`checker`](work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_check.py),
SHA-256
`8768abbdd38d21721955f76a0c1ba90054ed9177a95b9b393aa393fc0d7466ba`
and
`c7d04bb733cf50b08ed46dddf52bb98bbe726c0897f74c93f00533313a67f651`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_dyadic_diagonal_functional_recurrence_20260813_independent_check.py),
SHA-256
`8c5291225a6a3d39f60f87fbba9cd4a93d38427b627b5beeafb2f469f6571640`
and
`d97c1026884fb9f2a4110a5e1045b578114b3929cda5713373faa4c88f83eb1c`,
report `PASS` through depth 3072 and 21,497 independent phase lifts.  The
audit notes only that one auxiliary \(p<M\) proof starts at \(n=1\); all
\(n=0\) canonical-height checks still pass.  No discrepancy or V1 claim is
made.

The high-prime product also admits a genuine positive analytic theorem at
every bounded dimension.  If \(t_p=\operatorname{ord}_p(10)\), \(T_M\) is
the proportional-row length, and \(S_{M,p,h}\) is the actual selected local
character, Kerr's theorem and complete-period splitting give

\[
 \boxed{{|S_{M,p,h}|\over T_M}
 \ll {\sqrt p\over t_p}+T_M^{-1/4+o(1)}.}                    \tag{40dm}
\]

Erdős--Murty imply
\(t_p\ge\sqrt p\exp((\log p)^\delta)\) outside
\(O(x/\log^{1+\alpha}x)\) primes up to \(x\).  The exceptional retained
primes therefore carry only \(o(M)\) logarithmic mass, while the good
retained primes still carry \((5+o(1))M\).  Almost all high-prime mass is
locally mixing.

For every fixed \(k\), let \(Q_M\) be any product of at most \(k\) good
retained primes and let \(\Xi_{M,Q}\) be the actual primitive additive
coordinate.  A necessary period correction is explicit: split
\(T_M=u\operatorname{ord}_{Q_M}(10)+r\), apply Bourgain--Chang Corollary
4.2 to the complete subgroup periods, Corollary 4.5 only to a proper long
remainder, and the trivial bound to a short remainder.  This proves, at
`proof sketch` level, some \(\varepsilon_k>0\) with

\[
 \boxed{\left|\sum_{n=M}^{L_M}
 e\!\left(hA_n\Xi_{M,Q}\right)\right|
 \ll_k T_M^{1-\varepsilon_k}.}                              \tag{40dn}
\]

The correction matters: \((M,p,T_M,t_p)=(48,73,10,8)\) is an exact
period-crossing witness, so a direct incomplete-sum invocation is invalid.
It does not change the global wall.  For the product of all retained primes,

\[
 Q_M^>=\exp((5+o(1))M),\qquad
 \omega(Q_M^>)=\Theta(M/\log M),\qquad T_M=\Theta(\log Q_M^>),             \tag{40do}
\]

and every local order is only \(O(M)\).  The bounded-factor and
positive-power hypotheses fail, and the synchronized dyadic/cofactor weight
cannot be deleted from the character sum.  Local mixing therefore does not
yet imply the full fixed return.

The corrected primary
[`report`](work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_check.py)
have SHA-256 values
`23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d`
and
`fb0925503b7ffbb6ec06a83c0c4d84779f13c8d81a41be84c1436a26ee2ff8c7`.
The independently corrected
[`audit`](work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_large_sieve_short_orbit_20260813_independent_check.py),
SHA-256
`327b409a9f5baeac2c47e46bd3da6a68c47310dd82fba379d9836f0226b22fc2`
and
`6bb233921592a5cd2e2868c53c8b3ce6e6de8e99624ea894bc206f4de3ec288c`,
report final `PASS`; the independent replay reaches depth 600.  The analytic
claims are `proof sketch`, the bounded rows are `experiment`, and the dated
source audit is `literature-checked`.

Finally, the missing-word/G-function route has been separated at the exact
categorical boundary.  If a word \(w\) of length \(m\) were absent, its
survivor prefix count \(R_w(N)\) would satisfy

\[
 \boxed{9^N\le R_w(N)\le
 10^r(10^m-1)^{\lfloor N/m\rfloor},\quad
 \log9\le h(X_w)\le {\log(10^m-1)\over m}<\log10,}           \tag{40dp}
\]

where \(r=N-m\lfloor N/m\rfloor\).  This is a proper positive-entropy SFT,
not an automatic description of the one selected digit path.  Bell--Chen
instead gives the useful opposite implication

\[
 \boxed{\pi\notin\mathbb Q\quad\Longrightarrow\quad
 D_\pi(z)=\sum_{n\ge1}d_nz^n\text{ is not D-finite}.}        \tag{40dq}
\]

Indeed a D-finite finite-valued coefficient series would be rational and its
digits eventually periodic.  This does not exclude \(D_\pi\) from an SFT:
every one-word survivor contains a mapped Thue--Morse path which omits the
word while being automatic/Mahler, transcendental, and of irrationality
exponent two.  Conversely Machin gives the unrelated fixed G-function

\[
 H(z)=16\arctan(2z)-4\arctan(10z/239),\qquad H(1/10)=\pi,    \tag{40dr}
\]

but no checked theorem transfers this value identity through decimal floors
and carries to a functional equation for \(D_\pi\).  Current G-value
approximation and repetition theorems are either outside their verified
base-10 threshold or language-insufficient.  Direct auxiliary products also
lose: the all-candidate polynomial has degree at least \(9^N\), while the
selected-tail polynomial has value at most \(4^{-N}\) but only a known
lower bound \(\exp[-O(N^4\log^2N)]\).

The `literature-checked` primary
[`report`](work/ultrapi-resume/gfunction_subshift_entropy_attack_20260813.md)
and exact
[`checker`](work/ultrapi-resume/gfunction_subshift_entropy_attack_20260813_check.py)
have SHA-256 values
`3fe1e0639411421cef5b28786190717e41bdde1d893fe15fb6bd7e0600efb3b9`
and
`c150a72f596794655ed00d911def69db88b92c578c69a463cb7ea05086baa6d7`.
The
[`independent audit`](work/ultrapi-resume/gfunction_subshift_entropy_attack_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/gfunction_subshift_entropy_attack_20260813_independent_check.py),
SHA-256
`c1ad079743d1e32be4fc735eb7848d351c6596900f08559de579c8dad8560bab`
and
`6c0b96cf3f2b9f8bd611b17495d1c3c2471854e660808d1634f0f3d85117a804`,
report `PASS`, reproduce all 14 source pins, and independently check 11,110
mapped survivors plus more than a million exact submultiplicativity cases.
This closes several category errors, not the canonical conjecture.

### Exact three-primary epochs, 28 poles, and the selected-root wall

The formerly empirical three-primary denominator pattern has an exact
all-depth `proof sketch`.  Write the reduced BBP partial sum as

\[
 B_M={P_M\over2^{K_M}3^{E_M}S_M},\qquad
 (P_M,6S_M)=1,
\]

and let \(u_M\in\{1,2\}\) be the leading unit modulo three.  For odd \(e\),
put \(\delta_e=(3^e-3)/4\) and
\(\alpha_{e+1}=(3^{e+1}-1)/8\).  For even \(e\), put
\(A=(3^e-1)/8\).  The complete half-open epoch formula is

\[
\boxed{
\begin{array}{c|c}
\text{depth interval}&(E_M,u_M)\\ \hline
[\delta_e,\alpha_{e+1}),\ e\text{ odd}&(e,1)\\
[A,4A),\ e\text{ even}&(e,1)\\
[4A,5A),\ e\text{ even}&(e,2)\\
[5A,6A),\ e\text{ even}&(e-1,2).
\end{array}}                                                \tag{40ds}
\]

The drop at \(5A\) is exact.  The three height-\(e\) poles at
\(A,4A,5A\) have normalized leading sum zero modulo three, but their cluster
is divisible by exactly \(3^2\) in \(\mathbb Z_{(3)}\); the complete list of
height-\(e-1\) poles contributes leading residue two.  The next pole at
\(6A\) has height \(e+1\).  Thus the one-level drop is a forced cancellation,
not numerical noise.

If

\[
 \beta_M\equiv P_M(2^{K_M}S_M)^{-1}\pmod {3^{E_M}},\qquad
 g_n={10^n-16\over3},
\]

then \(v_3(10^n-16)=1\), \(g_n\equiv1\pmod3\), and the isolated residual
coordinate is

\[
 \boxed{{\delta_{M,n}\over3^{E_M-1}},\qquad
 \delta_{M,n}\equiv\beta_Mg_n\pmod {3^{E_M-1}}.}            \tag{40dt}
\]

For \(E_M\ge2\), its exact period is
\(T_E=3^{E_M-2}\), and one period is a bijection onto

\[
 \boxed{\{u_M+3j:0\le j<T_E\}\pmod {3^{E_M-1}}.}            \tag{40du}
\]

The proportional exponent row contains a complete period at every last
pre-drop depth \(M=5A-1\), and at every depth of every drop interval
\([5A,6A)\) for even \(e\ge4\).  Its mesh tends to zero.  No nontrivial odd
epoch contains a full period.  Most importantly, the full phase is

\[
 {\delta_{M,n}\over3^{E_M-1}}+\chi_{M,n}\pmod1,             \tag{40dv}
\]

where the complementary CRT phase \(\chi_{M,n}\) uses the same exponent.
The complete first-coordinate grid gives no joint hit without controlling
that synchronized complement.  Bourgain--Chang cannot simply absorb it:
the natural unreduced modulus is \(3^{E_M}Q\), while their bounded-factor
hypothesis bounds the sum of prime-power multiplicities and their incomplete
result requires a large order at every base prime; here \(E_M\to\infty\) and
\(\operatorname{ord}_3(10)=1\).

The associated universal finite-orbit facts are now `machine-checked` in
[`T73T73ThreePrimaryOrbit.lean`](TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean),
SHA-256
`1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009`.
T73 proves the exact order of ten, injectivity of a full period, exact
division in \((10^n-16)/3\), the residue-one property, and the cardinality of
the residual range.  It deliberately does not formalize (40ds), identify the
range with the whole coset as a set, or control \(\chi_{M,n}\).

The independent formal
[`audit`](work/ultrapi-resume/t73_three_primary_orbit_independent_audit.md),
[`Lean harness`](work/ultrapi-resume/t73_three_primary_orbit_independent_checks.lean),
and
[`hygiene checker`](work/ultrapi-resume/t73_three_primary_orbit_independent_hygiene_check.py)
have SHA-256 values
`701bb59a5bf1fcdb47a4f391a1e681a7a1273dc97b712098eb8e51d164514991`,
`da35143093d1f77fd7b63592b1a66aab40223e12cf43fa29b1c471aba95d2cb7`,
and
`2a67224e152a84f562141bb9f8c88e20f3c10b4b7918c02d5fcd9dddfc275e9a`.
On the frozen T73 hash above, it reports `PASS`: all nine declarations occur
exactly once in the central audit, no forbidden construct occurs, and the
axiom output is only `propext`, `Classical.choice`, and `Quot.sound`.  As an
independent downstream check, the harness reconstructs the unrestricted
collision criterion and the equality of the period image with the whole
residue-one coset.  Those audit-only lemmas do not enlarge T73's stated BBP
scope.

The primary `proof sketch` and exact `experiment` are the
[`three-primary report`](work/ultrapi-resume/bbp_three_primary_epoch_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_three_primary_epoch_20260813_check.py),
SHA-256
`5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7`
and
`4cb663d1d484c750ad99d2120d13143c24297ab4f81860a9f1584d5018ea2fa1`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_three_primary_epoch_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_three_primary_epoch_20260813_independent_check.py),
SHA-256
`be4ef5dcf93c1a9bad6d0c00771d6634cb404f968845ddf03be7bc9f896da8cb`
and
`c15ef949abc0d2f3f0cd7331bccd2fb8ecf0a4109142091427f1438aaafd9e8f`,
report `PASS`; the independent replay checks 6,201 exact rational states,
symbolic epochs through \(e=160\), and residual orbits through \(e=12\).

The endpoint units themselves satisfy an exact ninefold decimation.  Write

\[
 f_i(k)={c_i\over(a_i k+b_i)16^k},\qquad
 (a_i,b_i,c_i)=(8,1,4),(2,1,-1/2),(8,5,-1),(4,3,-1/2)
\]

and put \(d=(1,4,5,6)\).  The four affine denominators fold by a factor
of nine, and direct rational algebra gives

\[
 \boxed{9f_i(9r+d_i)-f_i(r)
 =f_i(r)\bigl(16^{-(8r+d_i)}-1\bigr).}             \tag{40ec}
\]

LTE gives \(v_3(16^q-1)=1+v_3(q)\), so every paired error in (40ec)
has exact valuation one.  All terms outside the distinguished residue class
are also in \(3\mathbb Z_{(3)}\) after multiplication by nine.  Therefore,
with \(F_i(q)=0\) for \(q<0\) and
\(F_i(q)=\sum_{r=0}^q f_i(r)\) otherwise,

\[
 \boxed{9B_M-\sum_{i=1}^4F_i\!\left(
       \left\lfloor{M-d_i\over9}\right\rfloor\right)
       \in3\mathbb Z_{(3)}}                              \tag{40ed}
\]

for every \(M\ge0\).  At
\(A_e=(3^e-1)/8\), \(M_e^-=5A_e-1\), and \(M_e^+=5A_e\), the cutoff
vectors in (40ed) differ from the preceding endpoint only by explicitly
three-integral pole terms.  Hence, for even \(e\ge4\),

\[
 \boxed{
 U_e^-:=3^eB_{M_e^-}\equiv U_{e-2}^-\pmod {3^{e-2}},\qquad
 U_e^+:=3^{e-1}B_{M_e^+}\equiv U_{e-2}^+\pmod {3^{e-3}}.} \tag{40ee}
\]

Both endpoint units are thus Cauchy in \(\mathbb Z_3^\times\).  For every
fixed exponent, multiplication by nine maps the new pre-drop grid to the old
one.  The independent audit found and retained the necessary small-epoch
qualification: pre-drop fibres are nine-to-one for every even \(e\ge4\),
the first drop transition \(e=4\to2\) is only three-to-one, and drop fibres
are nine-to-one from \(e\ge6\).  The frozen primary report's unqualified
drop-grid sentence must be read with exactly this correction.

The same rows are genuinely transferable to pi.  With
\(T=3^{e-2}\) and \(M=M_e^-=(45T-13)/8\), the entire complete period
\(M\le n<M+T\) satisfies

\[
 \boxed{|(10^n-16)(\pi-B_M)|
 \le { (8/5)^5\over15(M+1)^2}
       \left({31250\over32768}\right)^T.}          \tag{40ef}
\]

This exponentially small real shadow makes full-phase control on the
endpoint rows sufficient; it does not control the synchronized complement.

Exactly the twelve elementary ingredients of (40ec)—four affine folds, four
exponent folds, and four rational one-term identities—are now
`machine-checked` in
[`T74T74ThreePrimaryDecimation.lean`](TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean),
SHA-256
`eb103c72fd7cf7b0f91c85a102d8d7ed5165028b1d64ae23dac714f6093f2727`.
They are registered exactly once in the central axiom audit.  Direct
`--trust=0`, barrel, central-audit, forbidden-construct, and full 8,493-job
checks passed with only `propext`, `Classical.choice`, and `Quot.sound`.
T74 does not state LTE, (40ed)--(40ef), the complementary phase, or V1.

The `proof sketch` decimation
[`report`](work/ultrapi-resume/bbp_three_primary_decimation_20260813.md)
and exact
[`checker`](work/ultrapi-resume/bbp_three_primary_decimation_20260813_check.py)
have SHA-256 values
`29d4f903dca429ebe2cedad248f0a726b985492bfd0f06471a668a47e652ede0`
and
`abda4aa38bc575439320ecc60a44d0df8418be042b2bb0558f70f05c1c2dfc71`.
The
[`independent audit`](work/ultrapi-resume/bbp_three_primary_decimation_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_three_primary_decimation_20260813_independent_check.py),
SHA-256
`5dc190f913c1eb727e4a1cbc9bef2d8f3373af00b17e1aa50244ae8efceb3371`
and
`1304e1e4cb70c0bfba65b40cf32f7c282d447af3461398e305893e26e7f4f0ec`,
report `PASS_WITH_BOUNDARY_QUALIFICATION`, independently derive every
display above, exercise the exceptional \(e=4\) drop, and audit all twelve
formal declarations and registrations.

The complete primary period also admits an exact Fourier diagonalization.
Write the reduced odd part as

\[
 B_M={P_M\over3^EC},\qquad (P_M,3C)=1,qquad T=3^{E-2},
\]

and let
\(\beta\equiv P_MC^{-1}\pmod {3^E}\) and
\(\kappa\equiv P_M(3^E)^{-1}\pmod C\).  Since
\(r_E(n)=(10^n-1)/9\pmod T\) permutes \(\mathbb Z/T\mathbb Z\) over
one period, pulling the complementary CRT phase back through its inverse
\(\nu(r)\) gives

\[
 \boxed{{1\over T}\sum_{n=n_0}^{n_0+T-1}
 e\!\left(h(10^n-16)B_M\right)
 =e_{3^E}(-15h\beta)\,
   \mathcal F_TW_{M,h,n_0}(-h\beta),}             \tag{40eg}
\]

where
\(W(r)=e_C(h\kappa(10^{\nu(r)}-16))\) and
\(\mathcal F_TW(k)=T^{-1}\sum_rW(r)e_T(-kr)\).  Thus a complete grid
does not average the complement: the actual BBP numerator selects one
coefficient of the actual BBP complement.

There is nevertheless exact square-root oscillation in the isolated factor.
For \(3\nmid a\), \(E\ge4\), and
\(f_{E,a}(j)=e_{3^E}(a10^j)\), elementary autocorrelation and nine-term
orthogonality give

\[
 \boxed{|\widehat f_{E,a}(\ell)|^2=
 \begin{cases}9T,&\ell\equiv a\pmod9,\\0,&\ell\not\equiv a\pmod9.
 \end{cases}}                                      \tag{40eh}
\]

Exactly \(T/9\) coefficients survive, all with magnitude \(3\sqrt T\).
For the exponent-coordinate complement \(w\), this implies the conditional
bound

\[
 \boxed{|S_{M,h,n_0}|\le {3\over\sqrt T}
   \sum_{\ell\equiv a\ (9)}|\widehat w(-\ell)|
 =3\sqrt T\,\mathcal A_{T,a}(w).}                \tag{40ei}
\]

Low-Fourier-complexity complements therefore yield square-root cancellation.
No such bound is known for the changing BBP complement.  Parseval alone
returns the trivial \(T\)-bound, and the artificial unit weight
\(W(r)=e_T(-h\beta r)\) saturates (40eg).  Nor is the three-primary period a
complete joint period: at the genuine row \(M=40\), \(T=9\), while the
projection including the surviving \(7^2\) factor has order
\(\operatorname{lcm}(9,42)=126\).

The independently audited `proof sketch` Fourier
[`report`](work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_check.py)
have SHA-256 values
`0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12`
and
`7d8a8f7ff85c02b251845ba781d373dbf222a87ba69e0d6f82b1e995b9315e2c`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_check.py),
SHA-256
`44aabae56bfafd647e6bb8a899a97030641630044c4b57df5a45c8e858863c81`
and
`42c575e7d5446b46b26941c2c0db8b8289ae44846987f45a3e47beb0e12075be`,
report `PASS`.  They rederive (40eg)--(40ei), including nonunit harmonics and
the \(E=4\) boundary, and retain two wording qualifications: \(h\ne0\) when
writing \(v_3(h)\), and a fixed-period complement means an ordinary periodic
sequence restricted to the length-\(T\) window when its period does not divide
\(T\).  Neither artifact asserts the missing selected-coefficient bound.

### Full endpoint phase and a directly sufficient gap target

The isolated coordinate is not the final object, so the complete rational BBP
phase was computed on the last pre-drop and first-drop rows

\[
 M_e^-={5(3^e-1)\over8}-1,\qquad M_e^+=M_e^-+1
\]

for every even \(e=4,6,\ldots,14\).  Put

\[
 X_e^\pm=\left\{\left\{(10^n-16)B_{M_e^\pm}\right\}:
 M_e^\pm\le n\le\lfloor\log_{10}(16^{M_e^\pm})\rfloor\right\},
\]

let \(L_e^\pm=|X_e^\pm|\), and let \(G_e^\pm\) be the largest circular
gap.  Six rows were evaluated as exact reduced fractions and the other six by
directed MPFR enclosures transferred through the positive BBP-tail bound.  The
independently reconstructed finite result is

\[
 \boxed{0.899<{L_e^\pm G_e^\pm\over\log L_e^\pm}<1.084}
 \quad(11\le L_e^\pm\le610188).                    \tag{40ej}
\]

This has label `experiment`.  In particular, it does not prove the working
`conjecture`

\[
 \boxed{G_e^\pm\le C{\log L_e^\pm\over L_e^\pm}}
 \quad\hbox{for all sufficiently large even }e,             \tag{40ek}
\]

or even the weaker conclusion \(G_e^\pm\to0\).  It does show that this is a
quantitative, falsifiable target for the **complete** phase: the first two
Fourier magnitudes decrease, \(\sqrt L\rho_3\) stays between \(0.526\) and
\(1.331\) from \(e=6\) through \(14\), and the distance to zero is visibly
nonmonotone.  The near equality of the pre-drop and drop gaps is not an
independent-trials effect.  On their common exponent range,

\[
 (10^n-16)(B_{M+1}-B_M)
 =(10^n-16){a(M+1)\over16^{M+1}}
 \le {1\over15(M+1)^2},                            \tag{40el}
\]

so the complementary coordinates almost exactly compensate for the
factor-three change of the isolated primary period.

The logical implication of (40ek) needs all targets, not just a return to
zero.  Here is the endpoint-safe `proof sketch`.  Let
\(c=\{16\pi\}\), let \(t=k/(10^P-1)\) be any T72 color, and prescribe
\(N\) and \(\varepsilon>0\).  For either endpoint sign the real-shadow error
satisfies

\[
 \delta_e:=\sup_{M_e^\pm\le n\le U_{M_e^\pm}}
 (10^n-16)(\pi-B_{M_e^\pm})
 \le {1\over15(M_e^\pm+1)^2}\longrightarrow0.       \tag{40em}
\]

If \(0<t<1\), choose a late row with \(M_e^\pm\ge N\) and
\(G_e^\pm/2+\delta_e<\min(\varepsilon,t,1-t)\), then choose a row phase
within \(G_e^\pm/2\) of \(t-c\) on the circle.  Adding the fixed phase
\(c\) and transferring by (40em) produces \(n\ge N\) with ordinary real
distance \(|\{10^n\pi\}-t|<\varepsilon\); the margins prevent wraparound.
For \(t=0\), put \(r=\min(\varepsilon/4,1/4)\), target \(r-c\), and require
\(G_e^\pm/2+\delta_e<r\).  Then
\(0<\{10^n\pi\}<2r<\varepsilon\).  Thus \(G_e^\pm\to0\) for even one sign
would prove every quantifier of `ColoredRepunitReturns Real.pi`, after which
T72 would give V1.  By contrast, the single zero-target inequality
\(d_e^\pm\le G_e^\pm/2\) alone supplies only T69's fixed-sixteen return and
does not invoke T72.

The alternate `conjecture` that every fixed nonzero Fourier mode of the
endpoint empirical measures tends to zero is also sufficient: Weyl's
criterion gives convergence to Haar measure, and compactness rules out a
positive-length empty arc along any subsequence, hence forces
\(G_e^\pm\to0\).  Only modes one and two were measured.

The endpoint-safe transfer just used is now `machine-checked`, independently
of the unproved BBP input, in
[`T75T75UniformShadowCover.lean`](TheoryLib/PiQuantitativeBlockHitting/T75T75UniformShadowCover.lean).
T75 defines three explicit premises—eventual uniform circle coverage of every
shadow row, all row exponents tending past every threshold, and uniform
vanishing circle error from a fixed shift of the real decimal orbit—and
proves

\[
 \boxed{\text{uniform shadow cover}+\text{late exponents}
 +\text{vanishing shifted error}\Longrightarrow\mathrm{V1}(\pi).}
                                                               \tag{40en}
\]

The proof first obtains arbitrarily late circle density, then converts it to
T72's ordinary-real colored returns.  Positive colors use margins to both
endpoints; color zero is approached via a small positive interior center.
All four claim-supporting declarations are registered in the central axiom
audit.  The module, SHA-256
`002cac6a91c36f1e23499c16c0fafd1c259d5d93b974697ffc512ca4d6e4cc9b`,
passed focused `--trust=0`, barrel, forbidden-construct, central-audit, and
the complete 8,493-job verification gate with only `propext`,
`Classical.choice`, and `Quot.sound`.  T75 asserts none of its analytic BBP
premises, so (40ek) and the actual cover remain `conjecture`s.  A disjoint
adversarial
[`audit`](work/ultrapi-resume/t75_uniform_shadow_cover_independent_audit.md),
[`Lean replay`](work/ultrapi-resume/t75_uniform_shadow_cover_independent_replay.lean),
and
[`checker`](work/ultrapi-resume/t75_uniform_shadow_cover_independent_check.py),
SHA-256
`144cb3a2a83f63d633f68a5f4859cb363a93fed085cba8094284a4e9cc0cdf85`,
`c144ad045d93f433256ba3264a2d18be4af145ddc4c4f6969bd5b7bca18e24ee`,
and
`3534523d5966d74eff1f64fa9bffecfbe38b026d16a6cc90a82f0ea43da010c9`,
independently rederive the two critical bridges without invoking T75's four
bridge theorems and report `PASS`; the independent full gate also passed.

The frozen full-phase
[`report`](work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_check.py)
have SHA-256 values
`f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80`
and
`502ecbb618c778c319bbbadb5e338281dded77138a569b98d3c0062f896e3458`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_three_grid_full_phase_experiment_20260813_independent_check.py),
SHA-256
`6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9`
and
`a80e8ba9a4fa6fb49689ab773667f110296e866fdbb522a6e2695ade6fad3c6d`,
report `PASS`.  They reproduce all twelve grids, 24 Fourier recomputations,
and exact record
`2ef85d90315e487fb006ce6b39ca17731d8b20d6f0e129de0faf9422f9501f3d`.
The audit records the preceding T72 qualification explicitly; no asymptotic
`conjecture`, fixed return, or instance of V1 is asserted.

The independently audited epoch-16 extension increases the row length by a
further factor of nine.  Both the pre-drop row at (M=26{,}904{,}199) and
the first-drop row at (M=26{,}904{,}200) have (L=5{,}491{,}685), and
their common 18-digit center gap is

\[
 \widetilde G={2736782005017\over10^{18}},\qquad
 {L\widetilde G\over\log L}=0.968476769148622.       \tag{40eu}
\]

Directed evaluation independently certifies the required pi prefix through
32,395,907 fractional places.  Its one-sided truncation error gives the
strict actual-orbit bound

\[
       G_\pi<{2736782005019\over10^{18}}<10^{-5}.     \tag{40ev}
\]

Translation by (16\pi) preserves gaps, so (40ev) meets every half-open
five-digit decimal cylinder.  A disjoint direct count confirms all 100,000
five-digit words in each row, with minimum multiplicity 23.  This is a finite
`experiment`, not length-six coverage or an asymptotic statement.

The frozen primary
[`report`](work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.md),
[`checker`](work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.py), and
[`record`](work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_record.txt)
have SHA-256 values
`b9dfc7682b525afae6d70379982f6503962dfce55389c4b0d2a8efb87505c9aa`,
`d9fc5d4f8bff417bb50812788c0f893a03d9c02c343b1a031f69b390a2320e13`,
and
`2a9b25378bdf0a0a7a8d796c76c5e7058932876bb0a8004f21322d792edf982d`.
The independent
[`audit`](work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_independent_check.py),
SHA-256
`a17ea0268bd7f824b0344c167142864c7f6e4948e65ee56858d3bdf4479b83d9`
and
`332c9bcaae58d626a0aa5614f5a5f928b2be9245532241ec6061d4d0e7fb46db`,
report `PASS`; their complete stdout has SHA-256
`c3cb9f506f25dff49469159623661ac877c64d31c3329414ffe7a2d18a94f3ee`.
Neither implementation asserts the endpoint-gap `conjecture` or V1.

The exact sparse-support calculation can be sharpened once more, but the
result is a calibrated no-go rather than cancellation.  On every pre-drop
row \(T=9H\), the complement splits exactly into the selected dyadic carry,
a constant five-primary phase, a small-prime cofactor, a six-periodic
\(1/105\)-grid, and the reciprocal high-prime lift.  For any complement
weight \(W\), define its unnormalized Fourier energy in one residue class by
\(E_b(W)=\sum_{k\equiv b\ (9)}|\widehat W(k)|^2\).  Nine-block
orthogonality gives

\[
 \boxed{E_b(W)=H\sum_{u<H}
   \left|\sum_{m=0}^8W(u+mH)e_9(-bm)\right|^2,
   \qquad |S_{M,h}|^2\le E_{-a}(W).}                \tag{40ep}
\]

If every off-diagonal nine-block correlation were merely \(o(H)\), the
diagonal in (40ep) would still give

\[
 {E_{-a}(W)\over T^2}={1\over9}+o(1),qquad
 {|S_{M,h}|\over T}\le {1\over3}+o(1),             \tag{40eq}
\]

which is not decay.  Thus ordinary complement mixing or selected-class
energy is intrinsically too coarse; the missing estimate must retain the
phase of the primary--complement pairing.

One block differencing step does not make that pairing classical.  Its
dyadic factor has the two equivalent exact forms

\[
 e_{2^L}(\alpha10^u)=e_{2^{L-u}}(\alpha5^u),
 \qquad L-u\ge {1151\over405}M-O_h(\log M),         \tag{40er}
\]

so it has either fixed modulus with nonunit base or unit base with changing
modulus.  Simultaneously, every nonzero block lag leaves at least

\[
 \left(5-{64\log10\over405}+o(1)\right)M
 =(4.636134701\ldots+o(1))M                        \tag{40es}
\]

of high-prime logarithmic modulus.  This places the residual sum outside the
checked fixed-prime-support, bounded-factor, and positive-power-length
theorems; it is not itself a lower bound on cancellation.

The frozen `literature-checked` `proof sketch`
[`report`](work/ultrapi-resume/bbp_complement_fourier_attack_20260813.md)
and exact `experiment`
[`checker`](work/ultrapi-resume/bbp_complement_fourier_attack_20260813_check.py),
SHA-256
`eccb19ffdd7a931cb9de1efb4ab1136ba3f8fb543a84ab00c3e320fd16f2316a`
and
`4edba7339272813f152dbb9fb2a4af1ef8d8bd8ab76d4a28d45e1eee8494ff4c`,
report `PASS` with exact record
`c2b4d4f305958430abad628fd8370e3bb00416491e22621cfa4293dc23178190`.
The bounded rows \(e=4,6,8\) show selected complement energies near
\(1/9\) while the actual pairing becomes much smaller, but this finite fact
is not promoted to an asymptotic estimate.  No selected-coefficient decay,
fixed return, or V1 is asserted.  A disjoint standard-library
[`audit`](work/ultrapi-resume/bbp_complement_fourier_attack_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_complement_fourier_attack_20260813_independent_check.py),
SHA-256
`e3e726b81ff1f8a91ddad1a95bd04e77042755c5d0050882c6070950aa157e63`
and
`0415e9902c539a0ca9a09015dd8bd7794c15b2db580cf4b80e10ea6cb7c2caa4`,
report `PASS_WITH_INTERPRETIVE_CLARIFICATION` with record
`845304289ec54327dfe80ea79e42413eee213b2fe4c6364927ee3e7eaf07ea38`.
The qualification is important but nonfatal: prime annihilation applies to
the original, equivalently recombined, high-prime factor
\(J_M/105+H_M\), not necessarily to \(H_M\) in isolation, where a denominator
dividing 105 can remain until the grid term cancels it.  The audit also
derives \(\omega(Q)\gg M/\log M\) and independently confirms every constant,
sign, and source-exclusion used above.

A higher-order continuation rules out marginal Gowers uniformity as the
missing phase estimate.  If

\[
 f_{e,a}(j)=e_{3^e}(a10^j),\qquad T=3^{e-2},\qquad3\nmid a,
\]

then LTE and the exact complete primary orbit give, for every fixed
\(s\ge2\),

\[
 \|f_{e,a}\|_{U^s}^{2^s}\ll_s {e^{s-1}\over T},\qquad
 \|f_{e,a}\|_{U^2}^4={9\over T}.                    \tag{40ew}
\]

This decay is real but insufficient.  The artificial unit complement
\(W=\overline f\) has the same vanishing fixed-order norms while

\[
 {1\over T}\sum_{j<T}f(j)W(j)=1,
 \qquad D_aW(u)=9\overline{f(u)}.                   \tag{40ex}
\]

Thus no generalized-von-Neumann inference based only on a marginal
\(U^s(W)\) bound can control the selected pairing.

There is nevertheless an exact positive average theorem.  For any
unit-modulus complement and
\(S_a(W)=\sum_{j<T}e_{3^e}(a10^j)W(j)\), Ramanujan orthogonality gives

\[
 {1\over\varphi(3^e)}\sum_{3\nmid a}|S_a(W)|^2
 =T-\Re\sum_{j<T}W(j+T/3)\overline{W(j)}\le2T,
\quad
 \#\{a:|S_a(W)|\ge\eta T\}\le {12\over\eta^2}.     \tag{40ey}
\]

The actual endpoint coefficient is not sampled from this family: it follows
one coherent lift
\(a_e\equiv a_{e-2}\pmod {3^{e-2}}\).  The conjugate construction can obey
the corresponding ninth-root compatibility, so (40ey) alone does not show
that this selected path ever leaves the exceptional set.  Moreover every
second cube term and every third cube term at the dissociated lags
\((1,2,4)\) stays nondegenerate and retains, respectively, high-prime
logarithmic mass at least

\[
 (4.545168376\ldots+o(1))M,\qquad
 (4.499685214\ldots+o(1))M,                         \tag{40ez}
\]

together with linear dyadic depth.  This termwise persistence is not a lower
bound on the sum; it shows why a fixed number of formal differencing steps
does not terminate the hard family.

The frozen
[`report`](work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_check.py),
SHA-256
`3bd9a948945570e975defd7bd2297338da0068f9c82eb027be84364a66bb528e`
and
`24adf41ff8197d354ea8a5569dbb227f521346e96287006d013b77e6fb3fdea9`,
report `PASS` with exact record
`12253c483c206d11e741f6656b1f3dad61042ac0bef312fd697c28d04ce4d2fb`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_cf36_gowers_cube_persistence_20260813_independent_check.py),
SHA-256
`46642011eb928e85ed7e707524ed79589c957cf5f1d742db5f0177c3e4887b51`
and
`ddb579322dd7e9238024e313947bc94ae0bf9d3ce33af28cdf7859ea73370bdf`,
independently rederive the algebra and report `PASS` with record
`3fbfbe3ce0508db971bfa77e8e5476b1d7565d797bb36b6ef1683b8f7c9178e8`.
All analytic statements in this paragraph retain label `proof sketch`; no
CF36 bound, fixed return, or V1 is asserted.

The obvious attempt to turn endpoint nesting into a deterministic gap
recursion has also been checked and fails.  Although the exponent windows
obey exact near-ninefold recurrences, residue-matched full phases satisfy only
a three-localized identity

\[
 \boxed{9(10^n-16)B_{M_e^\pm}-(10^\rho-16)B_{M_{e-2}^\pm}
 \in\mathbb Z_{(3)}}
 \quad\left(n\equiv\rho\pmod {T_{e-2}^\pm}\right),          \tag{40et}
\]

not an Archimedean small-error estimate.  Exact rational reconstruction of
all four transitions \(4\to6\) and \(6\to8\) gives
\(G_e^\pm>G_{e-2}^\pm/9\), falsifying the most tempting recursion on every
available exact transition.  More strongly, an exhaustive `experiment` over
all 41,924 pairs of consecutive complete-primary-period subwindows finds a
primary-compatible ideal child missing by a fixed positive distance in every
pair (thresholds \(3/20,1/10,1/4,1/6\) in the four cases).  This excludes
the natural matching forced by the primary inverse system, not arbitrary
global matching by a different primary fibre.

An elementary `proof sketch` countermodel preserves exactly the listed
valuation pattern, three-localized decimation, endpoint-unit nesting,
complete primary grids, and arbitrarily close adjacent signs while making
the full gap exceed \(1-\varepsilon\).  It is explicitly not a BBP sequence,
does not satisfy T74's individual pole identities, does not preserve the
actual selected numerator, and does not shadow pi.  Its scope is therefore a
method no-go: those structural inputs alone cannot prove (40ek).

The frozen
[`report`](work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_check.py),
SHA-256
`6a4a8b77164acf76316e8effa197843d0b76629c9a596fa4b342742746d41c1d`
and
`0c8967858d1023e001cbc3fb011ae525cdd1800d3622e92d7d1fc0dd712cc780`,
report `PASS`; the complete checker output has SHA-256
`3490c218eeef3e1d572b5ce198298f214bde4f69592c411db948bd78b8c97f8a`.
A disjoint adversarial
[`audit`](work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_endpoint_gap_recursion_20260813_independent_check.py),
SHA-256
`8f4adf877ff7b591e4374eb4dc51b871134b0709b5bf4f73353d80b9b40d11a1`
and
`d047954e714e5dd89967fbd1f9d6e9fabf128c0726404cb1206925186f0b12bc`,
independently reconstruct equations (R6)--(R33), all 41,924 window pairs,
and the strengthened rational countermodel, and report `PASS`; their stdout
has SHA-256
`4aca87279281396a63a69297d198d63a34ac304567f6f53c9bc34639d455863d`.
The audit emphasizes that the zero defect in (R17) belongs only to the
isolated three-primary projection and that the countermodel is not a BBP/pi
model.  These results prove no all-depth gap inequality, return, or V1.

The dyadic diagonal also has a sharper exact normal form.  For the last of
the seven BBP slots the two formal half-integral pieces must not be reduced
separately.  Their exact Bezout recombination is

\[
 \boxed{-{s\over2(2k+1)}-{s\over2(4k+3)}
 =-{s(k+1)\over2k+1}+{s(2k+1)\over4k+3}.}          \tag{40dw}
\]

Together with the other 26 pieces this gives exactly 28 odd-linear terms,
not 26 linear terms plus one irreducible quadratic.  If
\(L_t(n)=A_tn+B_t\) is one of them and
\(H_t\equiv C_tR^{n+1}\pmod {L_t(n)}\), with
\(R=5\,2^{-27}\), then

\[
 \boxed{\Gamma_n=\left\{\sum_{t=1}^{28}{H_t\over L_t(n)}
                         +{b_n\over2^{27(n+1)}}\right\}.}    \tag{40dx}
\]

There is an equivalent division-safe formulation obtained by doubling the
forcing and reducing every pole modulo \(2^{27(n+1)+1}\).  This second route
is useful for the distinguished-root audit and agrees with (40dx).

For a prime value \(p=An+B\), rational Fermat gives the fixed binomial
relation

\[
 \boxed{H_n^A\equiv C^AR^{A-B+1}\pmod p.}                    \tag{40dy}
\]

For a composite value, if \(p\mid An+B\) and \(q=(An+B)/p\), the exact
local relation is instead

\[
 \boxed{H_n^A\equiv C^AR^{q+A-B}\pmod p,}                   \tag{40dz}
\]

so the allowed local set depends on the complementary cofactor.  At prime
values the normalized selected root \(r=B_0^n\), with
\(B_0=5\,2^{-27}\), satisfies
\(r^A\equiv B_0^{1-B}\pmod p\).  Clearing denominators gives

\[
 F_{A,B}(Y)=5^{B-1}Y^A-2^{27(B-1)}.                         \tag{40ea}
\]

Every \(A\) is even and every \(B\) is odd, so (40ea) factors as a
difference of squares.  For each of the 24 primitive prime-capable forms the
root set has exactly
\(\gcd(A,p-1)=\gcd(A,B-1)\in[2,56]\) members; the exponential formula
selects one, never the whole root set.  Four of the 28 forms have fixed
divisor seven, and the remaining 24 cannot all be prime because one of three
explicit surviving forms is divisible by three for each class of
\(n\pmod3\).  Thus an all-prime reduction is impossible, while Hooley,
Duke--Friedlander--Iwaniec, Toth, Ngo, Wang, Zehavi, and
Kowalski--Soundararajan have the wrong all-root, all-modulus, polynomial, or
joint-coordinate quantifiers for the selected 28-vector.

Even a hypothetical scalar density theorem for the forcing would not close
the state problem.  With \(r_k\) the base-two van der Corput sequence, define

\[
 Y_{2k}=0,\quad Y_{2k+1}=r_k/10,\qquad
 \Delta_{2k}=r_k/10,\quad\Delta_{2k+1}=\{-r_k\}.             \tag{40eb}
\]

Then exactly \(Y_{n+1}=\{10Y_n+\Delta_n\}\); every state remains in
\([0,1/10)\), while the odd forcing subsequence is uniformly distributed and
the initial forcing sets have mesh \(O(1/N)\).  Likewise, cancellation of
one selected root factor \(z_n\) does not survive an arbitrary complementary
unit weight: \(W_n=\overline{z_n}\) makes \(W_nz_n=1\).  These are logical
separators, not models of the exact BBP correlation.  They locate the missing
statement as joint cancellation for the actual synchronized 28-coordinate
product together with its generated state.

The corrected `literature-checked` fractional-parts
[`audit`](work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813.md)
and exact
[`checker`](work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_check.py)
have SHA-256 values
`55383eb4a52f65373c841dd86fdc5bf939d96e5a8ad536bae4a03e43de71135d`
and
`8c43ce5a7739337fd3273b6a612879ae68d302b7bbc5b18ba0b5aea8ad4f4885`.
Its
[`independent audit`](work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_fractional_parts_density_application_audit_20260813_independent_check.py),
SHA-256
`3ef0bf47394f6ae4d330b5614ecc5eed1d8ade5c57234c3640b3b5bc2adc365c`
and
`55d105e2933bc6e9cfddd4b8416c2ab61577b5f4b33cfc079ec1725bd10097be`,
report `PASS`; the independent replay checks all 28 signs and thousands of
prime and composite binomial instances.  At \(p=5\), the composite formula
is the direct identity \(0=0\), not an application of Fermat.

The complementary
[`distinguished-root report`](work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_check.py)
have SHA-256 values
`d70f8cd56885e77aecdec9eb09f67575d2b8ffe4e972d66ff9a69d82386466b8`
and
`e7103ffab23b88fb5bdf83fab73bcc1979f2ce3075dce2740d074d65f3b2b304`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_dyadic_distinguished_root_20260813_independent_check.py),
SHA-256
`1a7b9c798477f7350285b8f07ee5c59473225f0d70e5936c6690d80e7cbac531`
and
`fdd1fec1266f6e471ec2f56123ffd1ac8e57fe3baaee94a245d981df0d2294d3`,
also report `PASS`.  All analytic conclusions in this subsection stop at
`proof sketch` or `literature-checked`; none proves a full-phase return or V1.

### Fresh bounded literature verdict

Lagarias calls V1 digit-density and proves exactly its equivalence with
density of the remainder orbit in (2):
[Lagarias, 2001, Definition and Theorem 2.1](https://arxiv.org/abs/math/0101055).
The fresh primary-source search found no unconditional theorem establishing
that density for \(\pi\), and no credible 2025--2026 proof.

A second dated search through 2026-08-13, recorded in the
[`fresh special-value/fractal audit`](work/ultrapi-resume/fresh_special_value_fractal_literature_20260813.md),
SHA-256
`0852d12d67609fffae963f49369643b2378e319852f0e13eabf716581725abfe`,
checked recent special-value, missing-digit, fractal-intersection,
shrinking-target, and lacunary-gap papers against the fixed-pi quantifiers.
It likewise found no theorem proving V1.  Its material positive comparison is
Peres--Yang, arXiv:2606.28860v1: for every Hadamard-lacunary integer
divisibility chain, including \(a_n=10^n\), they prove for Lebesgue-almost
every fixed \(x\)

\[
                         {N G_N(x)\over\log N}\longrightarrow1.       \tag{40fa}
\]

Their upper/no-hit proof uses Lebesgue integration over survivor sets,
Paley--Zygmund, a mesh union bound, and Borel--Cantelli; the independent
mixed-radix digits are needed for the matching lower bound, not this upper
bound.  Measure preservation under \(x\mapsto10^{M_e^\sigma}x\) therefore
also gives at `proof sketch` level, simultaneously for both endpoint signs
and almost every fixed \(x\),

\[
 \limsup_{\substack{e\to\infty\\ e\ \mathrm{even}}}
 {L_e^\sigma G_e^\sigma(x)\over\log L_e^\sigma}\le1.       \tag{40fb}
\]

Neither (40fa) nor (40fb) contains the named point pi or the changing
rational points \(B_{M_e^\sigma}\).  The exact missing theorem is a
deterministic, selected-BBP-numerator version of their no-hit estimate.

An endpoint-specific primary derivation and a disjoint audit now make this
boundary exact.  For an \(L\)-point row, divide the circle into \(K\) equal
half-open cells, write \(c_a\) for the occupancy of cell \(a\), and put
\(C_h=\sum_n\zeta_K^{h\lfloor Kx_n\rfloor}\).  Finite Fourier inversion
gives the exact integer identity

\[
 Kc_a=L+\sum_{h=1}^{K-1}C_h\zeta_K^{-ha},\qquad
 \text{all cells hit}\Longleftrightarrow
 \min_a\Re\sum_{h=1}^{K-1}C_h\zeta_K^{-ha}>-L.       \tag{40fc}
\]

Taking \(K\sim2L/((1+\varepsilon)\log L)\) would give the desired
constant-one gap upper bound.  This is a growing-band, signed-trough
condition, not a fixed-mode or energy condition.  Parseval only gives

\[
 \sum_{h=1}^{K-1}|C_h|^2=K\sum_ac_a^2-L^2,qquad
 c_a=0\Longrightarrow
 \sum_{h=1}^{K-1}|C_h|^2\ge {L^2\over K-1}.          \tag{40fd}
\]

At the exact \(M=454\), \(L=93\), \(K=20\) row, the actual fully covered
histogram has energy 1211.  A one-empty histogram
\((6^6,5^{11},1^2,0)\) has exactly the same energy 1211.  Hence even equal
scalar Fourier energy cannot decide coverage.  Three further exact
same-denominator `experiment`s separately preserve the full odd CRT
coordinate or the full dyadic coordinate while making the row gap greater
than \(917/1000\) or \(1-10^{-639}\); preserving both coordinates fixes the
whole selected numerator and leaves no averaging parameter.

The frozen endpoint-specific
[`report`](work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813.md)
and
[`checker`](work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_check.py),
SHA-256
`3721a8e1a43fd3c4244ab8ffa11e0da0581e169d037cdf04f85e18ec1a539b60`
and
`121fad4ba825591d701b4156c6a570962e0609173b875d9b9fe5246afb0a8bcb`,
report `PASS`.  The disjoint
[`audit`](work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/peres_yang_bbp_endpoint_attack_20260813_independent_check.py),
SHA-256
`8c138103b4b2afb3e2b6e559c147c9b1ed69495e3689c1d00fa9fe50cee062ff`
and
`6a44ffd9c30b22302e90df4c14a3049feba66b9d3f1621ac88fa80cc2afb0d48`,
report `PASS_WITH_SCOPE_CLARIFICATIONS` and `PASS`, with exact record
`aad0c3e1eddfcab8077d50822e4cc3819ace9295c5e974edaf4be649d23d6633`.
They independently rederive the summable finite bad-set bounds, the
measure-preserving late-window shifts, both endpoint signs, and the first
Borel--Cantelli step without row independence.  Their conclusion remains an
almost-everywhere upper limsup at `proof sketch` level; it proves no statement
for \(\pi\), the selected changing \(B_M\), a fixed return, or V1.

The growing-band continuation identifies two further losses.  If
\(q_n=\lfloor Kx_n\rfloor\), \(\theta_n=\{Kx_n\}\), and the unquantized
full BBP phase splits as
\(e(x_n)=e_{3^e}(aR_n)W_n\), then exactly

\[
 C_h=\sum_n e_{3^e}(haR_n)W_n^h e(-h\theta_n/K),
 \qquad
 \left|C_h-\sum_ne(hx_n)\right|
 \le L\min\!\left(2,{2\pi h\over K}\right).        \tag{40fe}
\]

At the required \(h\asymp K\), rounding is an \(O(L)\) full-phase factor,
not a perturbation.  Removing the rounding does not recover independence.
For

\[
 \mathcal T(h,b)=\sum_ne_{3^e}(bR_n)W_n^h,
 \qquad S_h=\mathcal T(h,ha),                         \tag{40ff}
\]

For all additive coefficients \(b\bmod 3^e\), ordinary character
orthogonality controls each horizontal slice through the exact collision
second moment

\[
 {1\over3^e}\sum_{b\bmod3^e}|\mathcal T(h,b)|^2
 =\#\{(m,n):R_m\equiv R_n\pmod{3^e}\}.             \tag{40ffa}
\]

The sharper unit--Ramanujan average applies only when \(3\nmid h\): when
\(3\mid h\), the diagonal coefficient \(b=ha\) is not a unit.  In either
domain the actual BBP values still occupy one unselected diagonal
\(b=ha\), which may meet an exceptional point on every slice.  Moreover the
artificial obstruction can be chosen with one fixed complementary sequence,
\(W_n=\overline{e_{3^e}(aR_n)}\), for which the diagonal sum equals \(L\)
for every \(h\); no retuning of \(W\) while \(b\) varies is needed.  Summing
over \(h\) merely recombines the CRT factors into polynomials and pair
spacings of the full points.

The finite rows expose the required precision.  At \(e=8,10,12\), the
positive occupancy peak already makes the symmetric condition
\(\max_a|Kc_a-L|<L\) false even though every cell is occupied.  At \(e=12\),

\[
 L=67799,\qquad K=6094,\qquad
 min_a(Kc_a-L)=-61705=-L+K,                        \tag{40fg}
\]

so an approximation to the negative trough needs a one-sided error smaller
than \(K\asymp L/\log L\), or an exact nonvanishing argument; a bare
\(o(L)\) remainder does not decide the event.

Finally, six exact countermodels through \(e=8\) keep the complete reduced
denominator and the actual additive three-primary numerator coordinate, hence
the full primary grid, but replace the complementary numerator by a small
coprime lift.  Their complete rows collapse into arcs from \(<10^{-126}\) to
\(<10^{-10682}\).  They do not preserve the full BBP numerator and are not
alternative truncations; they show that primary nesting, local primitivity,
and growing-band power structure do not select the necessary joint phase.

The frozen
[`growing-band report`](work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_check.py),
SHA-256
`e44096cba88629cce55668332096c22f14950ff9e6c209cdd6b0a1cd36c776b6`
and
`edd7cdb4971b3969aaa05f3764036f7ad78cfecfe1a5362c9d5e1a00b981b30b`,
report `PASS` with exact record
`cc2cdf5824f772cc8062205f661ea605e244f369100132f1820f70fd481648c6`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_independent_audit.md),
[`checker`](work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_independent_check.py),
and
[`record`](work/ultrapi-resume/bbp_growing_band_joint_harmonic_20260813_independent_record.txt),
SHA-256
`b94f0423632fdcca4d99b3c7d2bdbfdedebe1085ecf4524e43fd1774158dd1cb`,
`d9083af5009f7953f5e262daa2899f69293b95122a723e9327de9eb210443d86`,
and
`ba497c805aa9bb446106ef0159f29629d45a265471bf92a7513dbceab3f8d8f6`,
report `PASS_WITH_SCOPE_CLARIFICATIONS` and `PASS`; the independent exact
record hash is
`3212a0030910842034d223bf495077502306bd8e2e63d7b7539a2558857db3b3`.
The audit independently recovers the additive-character second moment and
the fixed-sequence countermodel, while correcting the unit scope of the
Ramanujan average.  It does not select the BBP diagonal.
All analytic conclusions remain `proof sketch` and all bounded rows remain
`experiment`; no endpoint gap, fixed return, or V1 is proved.

The coherent-path continuation extracts an exact horizontal structure from
the exceptional coefficients.  Put \(q_e=3^e\), \(T_e=3^{e-2}\), and, for
one weight \(W\) held fixed while the coefficient varies,

\[
 S_e(a;W)=\sum_{j<T_e}e_{q_e}(a10^j)W(j).
\]

Since \(q_e=9T_e\) and \(10^j\equiv1\pmod9\), every unit \(a\) and
\(0\le k<9\) satisfy

\[
 S_e(a+kT_e;W)=e_9(k)S_e(a;W),
 \qquad |S_e(a+kT_e;W)|=|S_e(a;W)|.                \tag{40fh}
\]

Thus the macroscopic exceptional coefficients are complete nine-lift fibres,
and the GX17 second moment bounds their parent fibres by

\[
 \#\{b\bmod T_e:|S_e(b;W)|\ge\eta T_e\}
 \le {4\over3\eta^2}.                              \tag{40fi}
\]

For any sequence of unit weights \(W_e\) fixed in advance, the corresponding
bad unit cylinders in \(\mathbb Z_3^\times\) consequently obey

\[
 \mu(E_e(\eta))\le {2\over\eta^2T_e},\qquad
 \sum_{r\ge0}\mu(E_{4+2r}(\eta))\le {1\over4\eta^2}.       \tag{40fj}
\]

The first Borel--Cantelli lemma, followed by the countable thresholds
\(\eta=1/m\), therefore gives at `proof sketch` level

\[
 \text{for Haar-a.e. }a\in\mathbb Z_3^\times,\qquad
 {S_e(a\bmod3^e;W_e)\over T_e}\longrightarrow0
 \quad(e\text{ even}).                              \tag{40fk}
\]

No independence between epochs is used.  This is nevertheless a metric
statement about almost every path, not a selection theorem for the one
computable BBP path.  Replacing \(W_e\) by \(F_e/f_{e,a}\) while varying \(a\)
would make the selected correlation identical for every \(a\) and would
invalidate the coefficient average.

The actual weights also fail to nest without a twist.  If
\(M=M_e\), \(N=M_{e+2}\), \(\Delta=N-M=5\cdot3^e\), and \(B_e=B_{M_e}\),
then the frozen decimation `proof sketch` gives
\(a_{e+2}\equiv a_e\pmod{3^e}\), hence
\(f_{e+2,a_{e+2}}(j)^9=f_{e,a_e}(j)\) on the first \(T_e\) exponents.  Direct
substitution, however, gives the exact complementary law

\[
 {W_{e+2}(j)^9\over W_e(j)}
 =e\!\left(10^{M+j}D_e+C_e\right),
 \quad
 D_e=9\,10^\Delta B_{e+2}-B_e,
 \quad C_e=16B_e-144B_{e+2}.                       \tag{40fl}
\]

Writing \(K_R=4R-v_2(R+1)\), reducedness gives

\[
 v_2(\operatorname{den}D_e)=K_N-\Delta,\qquad
 K_N-\Delta-M-j>0\quad(0\le j<T_e).               \tag{40fm}
\]

The nonconstant dyadic twist therefore becomes deeper, rather than
disappearing, across epochs.  Equation (40fh) relates nine siblings using the
same upper-level weight; it supplies no implication between the exceptional
sets formed with \(W_e\) and \(W_{e+2}\).  The all-unit `experiment` through
\(e=14\) finds selected normalized correlations
\(0.296266,0.052329,0.019238,0.011022,0.004014,0.001185\), but every sampled
same-threshold persistence test fails.  Decrease in six finite values is not
an asymptotic estimate.

The frozen exceptional-path
[`report`](work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813_check.py),
SHA-256
`95e3b5d67784adefeda89357b3c652b7dd2b9d2550a26f00dedf2a0f489e01dc`
and
`1c151a8cbe253fb6323006f156719a85f970c3eb4b5feed0961e218a59c67b3e`,
report `PASS`.  The disjoint
[`audit`](work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813_independent_audit.md)
and
[`checker`](work/ultrapi-resume/bbp_exceptional_path_actual_complement_20260813_independent_check.py),
SHA-256
`58e622b2ecdd2ab0c1feb3ab6ba39f1eda0ba7daddd280d2d28a38a94959f0e1`
and
`3b115d0730293ac03bf210ee7b1dec38d34272f6ed178be797db0c7fcc4352f8`,
also report `PASS`; their retained record has SHA-256
`1e4ee83a41804238b32656d3ebf8466179c69583f7464fca22f977f3a39342f6`.
The audit independently rederives (40fh)--(40fm) and clarifies that T74
machine-checks the twelve one-term fold identities, not the summed endpoint
nesting itself.  That nesting therefore remains part of the decimation
`proof sketch`.  No deterministic exceptional-path exclusion, fixed return,
or V1 follows.

The selected-path arithmetic can nevertheless be sharpened beyond mere
nesting.  Write

\[
 \delta_e=9B_{M_{e+2}}-B_{M_e},\qquad
 U_e=3^eB_{M_e}\qquad(e\ge2\text{ even}).
\]

A pole-by-pole decimation calculation in \(\mathbb Z_{(3)}\) gives the
all-depth `proof sketch`

\[
 \boxed{\delta_e\equiv1\pmod{9\mathbb Z_{(3)}}},\qquad
 \boxed{U_{e+2}-U_e\equiv3^e\pmod{3^{e+2}\mathbb Z_{(3)}}}.  \tag{40fp}
\]

The four pole totals modulo nine are \(8,8,0,3\).  This includes the exact
paired cutoffs \((M_e+1,M_e+1,M_e,M_e)\), paired-term counts
\((0,0,2,2)\bmod3\), cancellation of complete nonlift blocks, the last
residues \(0,\ldots,4\), and both regular boundary terms.  Thus the residue
one is not inferred from the finite table.

It is not, however, the next visible lift digit by itself.  Let

\[
 \begin{aligned}
 x_e&\equiv U_e10^{M_e}\pmod{3^{e+2}},\quad0\le x_e<3^{e+2},\\
 a_e&\equiv x_e\pmod{3^e},\quad0\le a_e<3^e,\\
 \ell_e&=(x_e-a_e)/3^e\in\{0,\ldots,8\},\\
 a_{e+2}&=a_e+\kappa_e3^e.
 \end{aligned}
\]

Since \(M_{e+2}-M_e=5\cdot3^e\), LTE and (40fp) give the exact lift law

\[
                         \boxed{\kappa_e\equiv\ell_e+1\pmod9}. \tag{40fq}
\]

The exact bounded rows are

\[
\begin{array}{c|rrrrrrr}
e&2&4&6&8&10&12&14\\ \hline
a_e&2&29&29&29&26273&203420&1797743\\
\ell_e&2&8&8&3&2&2&0\\
\kappa_e&3&0&0&4&3&3&1.
\end{array}                                                     \tag{40fr}
\]

Consequently \(a_{16}=6{,}580{,}712\).  These bounded values have label
`experiment`.  In particular the repeated bare integer \(a_e=29\) at
\(e=4,6,8\), followed by lifts \(0,0,4\), rules out only an
epoch-independent transition whose complete state is that displayed integer.
It does not rule out a state containing \(e\), the modulus, hidden digits, or
some other finite augmentation.

The frozen
[`selected-path report`](work/ultrapi-resume/bbp_selected_padic_path_20260813.md)
and
[`checker`](work/ultrapi-resume/bbp_selected_padic_path_20260813_check.py),
SHA-256
`5d8a4259ec2ad4f0f0f0d77558ce854ac345a79b10b672060419cc6445e67481`
and
`24f8858a1c80a4df6710c21d5aa09d8d7d4e2a402f789c0c41c9e6b95ff74563`,
report `PASS`, with exact record
`fb3e99511c46f3cbe2d6772dcbae5fc7e33516cde7ef9c1a1ccf2c4035e1d9a0`.
The disjoint
[`audit`](work/ultrapi-resume/bbp_selected_padic_path_20260813_independent_audit.md),
[`checker`](work/ultrapi-resume/bbp_selected_padic_path_20260813_independent_check.py),
and
[`record`](work/ultrapi-resume/bbp_selected_padic_path_20260813_independent_record.txt),
SHA-256
`17248399e0aed68a1392b904be1afa047dca5dc9c8fd88a04d94bbc592e22e7a`,
`0cb582ab0a523d412d831a3fe76f9bcb3ee6ffab8f880d6a343e12b87a786ef3`,
and
`c3e3b8798cd699a0c9ac65c2670796d43b0b21bdbc05f381043094c0dbb3406c`,
independently report `PASS` with the state-scope clarification above.  No
selected correlation decay, exceptional-fibre escape, fixed return, or V1 is
deduced from (40fp)--(40fr).

T77 now machine-checks the finite rational shell and the complete stable
residue ledger behind (40fp), without silently promoting (40fp) itself.  For
every \(M\), Lean proves the exact decomposition

\[
 9B_{9M+13}-B_M
 =\sum_{i=1}^4\bigl(\text{paired errors}+	ext{complete complements}
                     +\text{five-term tail}+	ext{boundary}_i\bigr), \tag{40fs}
\]

including every inclusive cutoff and boundary sign.  It then proves
\(M_{2t}\equiv4\pmod9\), the pair-count residues
\((0,0,2,2)\bmod3\), zero complete-block totals, the tail vector
\((6,3,6,0)\), the boundary vector \((2,5,0,0)\), and finally

\[
 (0,0,3,3)+(6,3,6,0)+(2,5,0,0)
 =(8,8,0,3),\qquad8+8+0+3=1\quad\text{in }\mathbb Z/9. \tag{40ft}
\]

The
[`T77 module`](TheoryLib/PiQuantitativeBlockHitting/T77T77SelectedPadicDefectShell.lean),
SHA-256
`7185e8ca571cebc326f717d18dc660d2e31e4cbbaee1a3910498ac7f441de3e0`,
and
[`report`](work/ultrapi-resume/t77_selected_padic_defect_shell_report.md),
SHA-256
`3b40bb3a8de1925e16aee408455a66cbf9e370fd7ed34ad744ae1ad9f17af618`,
are `machine-checked` within that scope.  All 26 theorem declarations are
registered in `audit/AxiomAudit.lean`; the full 8,493-job gate reports `PASS`
and only the allowed logical dependencies.  The remaining formal bridge is
uniform rather than combinatorial: after cancelling arbitrary powers of
three from a pole denominator, one must transport each rational shell term
through \(\mathbb Z_{(3)}\) to the corresponding entry of (40ft).  Until that
bridge is formalized, the all-depth congruence (40fp) remains a `proof sketch`,
not `machine-checked`.

T76 separately machine-checks the abstract outer-cover core.  For an alphabet
of size \(p\ge2\), suppose the bad prefix family \(B_n\) at every depth has
one uniform cardinality bound \(|B_n|\le C\).  Giving every depth-\(n\)
cylinder weight \(p^{-n}\), Lean proves that the paths whose prefixes lie in
\(B_n\) infinitely often have, for every \(\varepsilon>0\), an explicit
countable tail-cylinder cover of total weight below \(\varepsilon\):

\[
 \sum_{k\ge0}|B_{N+k}|p^{-(N+k)}
 \le {Cp^{-N}\over1-p^{-1}}<\varepsilon.           \tag{40fn}
\]

It also proves the exact real-series identity used in (40fj),

\[
 \sum_{r\ge0}{2\over\eta^2 3^{2+2r}}={1\over4\eta^2}
 \qquad(\eta\ne0).                                 \tag{40fo}
\]

The
[`T76 module`](TheoryLib/PiQuantitativeBlockHitting/T76T76ExceptionalPathCylinderCover.lean),
SHA-256
`8d2bf71483c313d234b0ad49f0f0a7b2ca902571ea61b54cdb8ef6a86955cbe9`,
and its
[`report`](work/ultrapi-resume/t76_exceptional_path_cylinder_cover_report.md),
SHA-256
`011ae508561d9ccc967d5b5a062e5288ead791afb8cb7cba8d9df18cfbfcc476`,
are `machine-checked`: all 15 supporting theorems are registered in
`audit/AxiomAudit.lean`, the full `scripts/check.ps1` gate reports `PASS`, and
the audit prints only `propext`, `Classical.choice`, and `Quot.sound`.  T76 is
deliberately measure-free and conditional on the bounded prefix families.  It
does not formalize the BBP correlation estimate, prove that the changing
exceptional fibres are a nested tree, or exclude the named deterministic BBP
path.  It therefore proves nothing about pi or canonical V1.

The search also sharpens why arithmetic quality is insufficient. There are
badly approximable, hence irrationality-exponent-\(2\), numbers with nondense
base-10 orbit; the exceptional set is winning and has full Hausdorff
dimension:
[Broderick--Bugeaud--Fishman--Kleinbock--Weiss, 2010](https://doi.org/10.4310/MRL.2010.v17.n2.a10).
Thus even an optimal irrationality exponent would not imply T19 or V1.

A more specialized Diophantine milestone can be stated, but it is still much
weaker than coverage.  For denominators
\(Q_{u,v}=10^u(10^v-1)\), let \(\nu_{10}(\pi)\) be the corresponding
restricted irrationality exponent.  A localized replay of the
Bugeaud--Kim low-complexity argument gives the `proof sketch`

\[
 \nu_{10}(\pi)\le M<2.2469796037\ldots
 \quad\Longrightarrow\quad
 \liminf_n{p_\pi(n)\over n}>1.
\]

The cutoff is the positive root condition
\(M^3-2M^2-M+1<0\).  This is not a published estimate for \(\pi\): the
current ordinary bound \(\mu(\pi)\le7.103205334137\ldots\) is far above the
threshold, and even success would yield only a strict linear factor-complexity
gain.  See the [2026 revision of Bugeaud--Kim](https://arxiv.org/abs/2510.02059v2),
the [Zeilberger--Zudilin bound](https://arxiv.org/abs/1912.06345), and the
dated local applicability audit
[`T87 REPORT`](work/theory/pi-lacunary-near-return-sparsity/library/t87/REPORT.md).

An exact determinant audit makes the best known near-miss quantitative.
For Hata's Gaussian linear form \(L_n=A_n+B_n\pi\), the central coefficient

\[
 v_n=[z^{3n}]\bigl((z-1)(z-2)(z-1-i)\bigr)^{2n}
\]

has the additional divisibility \(v_n=(1+i)^nt_n\) with
\(t_n\in\mathbb Z\). Along \(n=2^k\) its exact \((1+i)\)-adic valuation is
\(n+2\), so this exponential factor cannot be uniformly strengthened;
moreover \(t_{pm}\equiv t_m\pmod p\) for odd primes \(p\), and in particular
\(t_{5^k}\not\equiv0\pmod5\). Including Hata's entire source-certified
clearing divisor and this Gaussian factor gives the optimistic restricted
exponent

\[
 M=2.275040879722662309\ldots,
\]

still above the strict \(2.246979603717467061\ldots\) threshold. It would
need a new target-compatible common divisor of rate more than
\(e^{0.047103487012601784n}\). The exact decimal denominator
\(10^u(10^v-1)\) supplies no such factor uniformly: the repunit is odd and
prime-power divisibility in it requires the corresponding multiplicative
order of 10 to divide \(v\). Salikhov and Zeilberger--Zudilin remain farther
from the threshold even under unrealistically favorable complete-overlap
assumptions. Hata's source identities are `literature-checked`; the new gcd,
valuation, and determinant calculation is a `proof sketch` pending formal or
independent human review. The primary source is
[Hata, 1993](https://doi.org/10.4064/aa-63-4-335-349), with the pinned local
[PDF](work/theory/pi-positive-decimal-factor-entropy/library/t79/hata-1993.pdf).
Even crossing this threshold would prove only a strict-superlinear factor
complexity sibling, not V1.

The recent items checked do not change the status.
[Silva-García--Cardona-López--Flores-Carapia (2025)](https://doi.org/10.3390/math13020313)
assume fair independent binary digits, and their overlapping-window
independence step is invalid;
[Roba--Podnieks (2025)](https://arxiv.org/abs/2504.10394),
[Razeto--Rossi (2026)](https://arxiv.org/abs/2608.06438), and Trüb are finite
empirical studies. Bailey--Crandall/Lagarias BBP consequences retain an unproved
dynamical dichotomy and concern base 2 or 16; Schmidt's theorem prevents an
automatic transfer to base 10. These are bounded negative findings, never
evidence that no unpublished proof exists.

## Machine-checked fixed-π spectral advance

Put

\[
 S_N(h)=\sum_{0\le j<N}e^{2\pi i h10^j\pi},\qquad
 C_N=\operatorname{Chg}_\pi(N).
\]

The new T20 module proves the exact unconditional inequality

\[
 N\sin^2\!\left(\frac{\pi}{100}\right)C_N
 \le N^2-|S_N(1)|^2. \tag{18}
\]

The proof is finite and deterministic.  A changed adjacent digit pair keeps
the corresponding orbit increment between \(1/100\) and \(9/10\) away from
zero in its absolute representative, so its phase chord has squared length at
least \(4\sin^2(\pi/100)\).  A path Poincaré inequality then converts the sum
of changed-edge energies into the Fourier defect.  The module also proves the
ordered-pair identity

\[
 N^2-|S_N(h)|^2=
 \sum_{a,b<N}\left(1-\cos(2\pi h(x_b-x_a))\right)
\]

for an arbitrary finite circle path.

T21 combines a rational weakening of (18) with the already checked fact that
the decimal digit stream of \(\pi\) is not eventually periodic.  It obtains

\[
 \frac{C_N}{5000}\le N-|S_N(1)|,
 \qquad
 \forall B\in\mathbb N\;\exists N_0\;\forall N\ge N_0:\
 B\le N-|S_N(1)|. \tag{19}
\]

T22 generalizes the digit bridge to any irrational decimal seed and uses the
exact conjugacy between frequency \(h\) on the \(\pi\) orbit and frequency one
on the orbit seeded by \(\{h\pi\}\).  Since \(\{h\pi\}\) is irrational for
every integer \(h\ne0\), the strongest result is

\[
 \forall h\in\mathbb Z\setminus\{0\}\;\forall A\in\mathbb R\;
 \exists N_0\;\forall N\ge N_0:\quad
 A\le N-|S_N(h)|. \tag{20}
\]

T24 takes the maximum of the finitely many eventual cutoffs in (20).  It
therefore proves the exact simultaneous statement

\[
 \forall H\in\mathbb N\;\forall A\in\mathbb R\;\exists N_0\;
 \forall N\ge N_0\;\forall h\in\mathbb Z:\quad
 0<|h|\le H\Longrightarrow A\le N-|S_N(h)|. \tag{21}
\]

For example, one may set \(H=2\cdot10^k\) and \(A=k\).  The resulting cutoff
can depend arbitrarily on \(k\), however, and (21) gives no relation between
the additive saving \(k\) and the much later prefix length \(N\).

T25 records the exact orbit identity behind the tempting power-of-ten
frequency amplification route.  With \(x_j=\{10^j\pi\}\) and
\(G_N(h)=N-|S_N(h)|\), it proves

\[
 S_N(10^t h)+S_t(h)=S_N(h)+
   \sum_{0\le j<t}e^{2\pi i h x_{N+j}},
 \qquad
 |G_N(10^t h)-G_N(h)|\le2t. \tag{22}
\]

Thus a power-of-ten shift transports an additive rate up to a fixed boundary
error; it does not amplify that rate by \(10^t\) or by \(N\).

T23 isolates a different finite structure.  Let \(\mathcal F_m\) be the set
of distinct length-\(m\) factors of \(\pi\), put \(P=p_\pi(m)\), let \(n(w)\)
be the first start of \(w\), and define the explicit canonical cutoff

\[
 N_m=1+\sum_{w\in\mathcal F_m}n(w).
\]

The first-occurrence cell codes are injective.  Averaging ordered-pair cosine
energy over the exact frequencies \(1,\ldots,10^m\) gives, for \(m\ge3\),
some \(1\le h\le10^m\) such that

\[
 \left|\sum_{w\in\mathcal F_m}e^{2\pi i h x_{n(w)}}\right|^2
 \le \frac{P(P+3)}2. \tag{23}
\]

This is a genuine relative saving on the one-representative-per-factor
sample: its normalized squared bound tends to \(1/2\) as \(P\) grows.  Since
every omitted ordered-pair energy is nonnegative, the same averaging argument
also supplies a (possibly different) \(1\le h\le10^m\) with

\[
 N_m^2-|S_{N_m}(h)|^2
 \ge \frac{P(P-3)}2
 \ge \frac{(m+1)(m-2)}2. \tag{24}
\]

The bare existence in (24) is not stronger than T21, which can force an
arbitrarily large defect at frequency one by taking an uncontrolled prefix.
T23's new content is that \(N_m\) is the explicit prefix containing every
first occurrence and \(h\) lies at the natural decimal scale.  The loss is
also exact: the repeated visits between selected starts can swamp (23), and
there is no upper bound on \(N_m\).  Controlling those multiplicities or that
cutoff is another form of the unresolved fixed-\(\pi\) input.

T26 keeps T23's whole frequency average instead of extracting only one
witness.  Let \(\mathcal G_m\subseteq\{1,\ldots,10^m\}\) contain the
frequencies whose full-prefix defect reaches one quarter of the robust
ordered-pair scale.  For every \(m\ge3\), it proves

\[
 10^m\le16|\mathcal G_m|,\qquad
 N_m^2-|S_{N_m}(h)|^2
 \ge {P(P-3)\over4}
 \ge{(m+1)(m-2)\over4}
 \quad(h\in\mathcal G_m). \tag{26}
\]

The exact normalization audit is

\[
 \left({|S_{N_m}(h)|\over N_m}\right)^2
 \le1-{P(P-3)\over4N_m^2}. \tag{27}
\]

T27 retains the selected-energy good set rather than enlarging it to all
full-defect witnesses.  On every retained frequency it first proves that the
representative sum has norm at most \(31P/32\).  The complement contains
exactly \(N_m-P\) unit vectors, so the triangle inequality gives the stronger
full-prefix additive gap \(N_m-|S_{N_m}(h)|\ge P/32\), with no multiplicity
hypothesis.

T28 then replaces the sum cutoff by

\[
 L_m=1+\max_{w\in\mathcal F_m}n(w),
\]

the least positive orbit prefix containing every representative start, and
proves \(L_m\le N_m\).  For a set
\(\mathcal H_m\subseteq\{1,\ldots,10^m\}\), definitionally the same
selected-energy set used by T27, the resulting theorem is

\[
 10^m\le16|\mathcal H_m|,\qquad
 L_m-|S_{L_m}(h)|\ge {P\over32}\ge {m+1\over32}
 \quad(h\in\mathcal H_m),\qquad m\ge3. \tag{28}
\]

This removes the artificial sum-of-first-occurrences cutoff and proves that
the linear additive gap survives arbitrary intervening multiplicity.  The
normalized saving is nevertheless only \(P/(32L_m)\), which may vanish
because no unconditional bound on \(L_m/P\) is known for \(\pi\).  Even a
hypothetical \(L_m=O(P)\) estimate would give only a constant relative saving
on a positive proportion of frequencies; T19 needs near-zero relative sums
at *every* frequency in a growing window.

The loss is logically unavoidable from T23's inputs alone.  For \(q=P\), put
selected points at \(j/q\), so their frequency-one sum is zero; place the last
selected representative at an arbitrarily late ambient index and put every
unselected ambient point at zero.  The full normalized sum then tends to one.
This is a `proof sketch` separator, not a decimal-orbit theorem, but it shows
that injective cell labels plus selected cancellation cannot control the
ambient prefix without representative-density or multiplicity information.

Equations (18)--(24), (26), and (28) are `machine-checked`; every supporting
declaration is registered in `audit/AxiomAudit.lean`.  Equation (27) is the
displayed algebraic normalization of (26), recorded here as a `proof sketch`
rather than as a separately named Lean theorem.  These are real fixed-\(\pi\) progress,
but the word *additive* is decisive: (20) is compatible with
\(|S_N(h)|=N-\sqrt N\), whose normalized magnitude tends to one.  T29's
possible fixed-frequency linear resonance under failure of V1 is therefore
not contradicted.

There is an explicit separator, currently a `proof sketch`, showing that this
logical gap cannot be removed abstractly.  Let

\[
 \alpha=\sum_{r\ge1}10^{-2^r},\qquad
 R_N=\#\{r\ge1:2^r\le N\}.
\]

Its decimal digits are ones exactly at positions \(2^r\), so \(\alpha\) is
irrational and omits every digit outside \(\{0,1\}\).  Its change count is
\(C_N=R_N+R_{N-1}\).  Direct geometric summation, together with the same
path-energy lower bound, gives

\[
 \frac{1-\cos(\pi/50)}4 C_N
 \le N-|S_N(1;\alpha)|
 \le \frac{2\pi}{9}R_N+\frac{2\pi}{81}. \tag{25}
\]

Thus its additive gap is \(\Theta(\log N)\to\infty\), while
\(|S_N(1;\alpha)|/N\to1\) and even the one-letter word `2` never occurs.
The same example blocks the finite-window escape: after optionally adding the
digit at position one, a direct geometric-tail estimate gives, for
\(N\le2^R\),

\[
 |N-S_N(h;\alpha)|\le \frac{20\pi |h|}{81}(R+1).
\]

Hence \(|S_N(h;\alpha)|/N\to1\) uniformly on every fixed window
\(0<|h|\le H\), even though the generic irrational-seed theorem gives the
simultaneous additive divergence (21).  This refinement is still a
`proof sketch`, not a registered Lean theorem.  Accordingly, the remaining
fixed-\(\pi\) input must be a relative, not merely unbounded additive,
cancellation mechanism.

## Machine-checked recurrent-language advance

Call a length-\(m\) block recurrent when it occurs at starts beyond every
prescribed threshold, and write \(p^{\mathrm{rec}}_\pi(m)\) for the number of
distinct recurrent length-\(m\) blocks.  T31 proves the unconditional bound

\[
 \forall m\ge1:\qquad p^{\mathrm{rec}}_\pi(m)\ge m+1. \tag{29}
\]

The argument is short but its quantifiers matter.  At a fixed length there
are only finitely many possible blocks.  Every nonrecurrent block has some
threshold after which it never appears, so one can take a common maximum
threshold \(C\).  Every factor of the shifted stream
\((d_{C+i})_{i\ge0}\) is then recurrent in the original stream.  If that
shifted stream were eventually periodic, the original stream would also be
eventually periodic, contradicting irrationality of \(\pi\).  One-sided
Morse--Hedlund therefore gives at least \(m+1\) distinct factors in the
shifted stream, and the value-preserving map from those tail factors to
recurrent original factors is injective.

This generic characterization is classical: it is exactly the
contrapositive of Perrin's Proposition 8.14 cited in the literature log.
The contribution of T31 is its audited Lean formalization and specialization
to the repository's exact decimal digit stream, not a novelty claim.

The fully expanded Lean theorem produces a finite set of at least \(m+1\)
blocks and proves for each member \(w\) and each \(N\) the existence of a
start \(i\ge N\) with block \(w\).  It is strictly stronger than the earlier
two-recurrent-digit baseline and stronger than the ordinary
\(p_\pi(m)\ge m+1\) statement in recurrence content.  It still gives only a
linear, unspecified sublanguage; V1 requires all \(10^m\) prescribed blocks.

T32 sharpens the structure behind (29).  For every \(m\ge0\),

\[
 p^{\mathrm{rec}}_\pi(m)+1
 \le p^{\mathrm{rec}}_\pi(m+1). \tag{30}
\]

More concretely, there are a recurrent length-\(m\) word \(w\) and distinct
digits \(a\ne b\) such that both \(wa\) and \(wb\) recur arbitrarily late.
Thus the recurrent language has a right-special factor at every length.

The proof uses the last-symbol deletion map
\(\rho_m:\mathcal R_{m+1}\to\mathcal R_m\).  It is onto: given a recurrent
\(m\)-factor, take an occurrence beyond a common cutoff after which every
occurring \((m+1)\)-factor is recurrent, and retain its next digit.  If
\(\rho_m\) were injective at any length, then on that late tail the ordinary
prefix-deletion map would be both injective and surjective.  The tail's
factor complexities at \(m\) and \(m+1\) would be equal, so one-sided
Morse--Hedlund would make the tail, and hence the original digit stream,
eventually periodic.  Irrationality of \(\pi\) rules this out.  A collision
under \(\rho_m\) gives the two recurrent extensions, and finite-cardinality
counting gives (30).

This is still a branching-existence theorem, not prescribed branching.  It
does not identify \(w\), \(a\), or \(b\), and linear strict growth remains
compatible with omitting nearly every length-\(m\) word.  Consequently it
does not change V1's `conjecture` status.

The linear bound is sharp even in base 10 under the strongest possible
ordinary irrationality exponent.  Let

\[
 \kappa_{10}=\sum_{j\ge0}10^{-2^j}
       =0.1101000100000001\ldots{}_{10}.
\]

Shallit's continued-fraction formula shows that \(\kappa_{10}\) has bounded
partial quotients (only \(8,9,10,12\), apart from the initial zero); hence
\(\mu(\kappa_{10})=2\).  At any fixed positive length \(m\), sufficiently
late gaps between its decimal ones exceed \(m\).
The recurrent factors are therefore exactly

\[
 0^m,\qquad 0^r10^{m-1-r}\quad(0\le r<m),
\]

because each singleton-one placement occurs around arbitrarily late isolated
ones, whereas every block containing two or more ones disappears after a
finite cutoff; digits 2 through 9 never occur.  Thus
\(p^{\mathrm{rec}}_{\kappa_{10}}(m)=m+1\) exactly, and the all-zero factor is
its sole recurrent right-special factor.

T33 machine-checks the full combinatorial statement for the stream
`0,1,1,0,1,0,0,0,1,...`, exactly the fractional digit stream of
\(\kappa_{10}/10\); deleting its initial zero gives the digits of
\(\kappa_{10}\).  It proves
aperiodicity, the exact recurrent-factor cardinality, a bijection with
`Option (Fin m)`, realization and uniqueness of every zero/singleton-one
shape, and uniqueness of the recurrent right-special factor even at length
zero.  Shallit's bounded-partial-quotient theorem and Adamczewski's
Mahler-method transcendence theorem are `literature-checked`; the elementary
real-number identification, rational-scaling step, and invariance of
irrationality exponent under rational scaling remain a `proof sketch`, not
Lean premises.  Together these results show that neither transcendence,
optimal scalar Diophantine approximation, nor the generic T32 argument can
force a larger recurrent decimal language.  Any improvement must use
arithmetic information specific to the decimal orbit of \(\pi\).

## Formalization map

- Lean statement: `Theory.PiDigits.V1` in
  [`T7Statements.lean`](TheoryLib/PiDigits/T7Statements.lean).
- Exact digit stream: `Theory.PiDigits.piDigit`, zero-based after the decimal
  point.
- Existing mathlib ingredients: `Real.digits`, `Real.pi`,
  `irrational_pi`, real fractional part, finite sums, circle characters,
  and general symbolic-dynamics cylinder/language infrastructure.
- Existing project ingredients: factor complexity, decimal cylinders,
  orbit-density equivalence, Weyl sums, forbidden-word automata, collision
  energy, and long-lag reductions.
- New verified modules:
  [`T18T18SharperNaturalScaleResonance.lean`](TheoryLib/PiQuantitativeBlockHitting/T18T18SharperNaturalScaleResonance.lean)
  and
  [`T19T19ExactNaturalScaleResonance.lean`](TheoryLib/PiQuantitativeBlockHitting/T19T19ExactNaturalScaleResonance.lean).
  T19 contains the triangular injection and cardinality identity, coefficient
  mass calculation, generic empty-interval resonance, direct hitting
  contrapositive, decimal-orbit specialization, T18-to-T19 implication,
  T19-to-V1 implication, and generic strictness witness.
- New unconditional fixed-orbit modules:
  [`T20T20DigitChangeFourierDefect.lean`](TheoryLib/PiQuantitativeBlockHitting/T20T20DigitChangeFourierDefect.lean),
  [`T21T21UnboundedFourierGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T21T21UnboundedFourierGap.lean),
  and
  [`T22T22AllFixedFrequencyGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T22T22AllFixedFrequencyGap.lean),
  together with the first-occurrence, finite-window, and frequency-shift
  modules
  [`T23T23MorseHedlundFrequencyDefect.lean`](TheoryLib/PiQuantitativeBlockHitting/T23T23MorseHedlundFrequencyDefect.lean),
  [`T24T24FiniteWindowAdditiveDivergence.lean`](TheoryLib/PiQuantitativeBlockHitting/T24T24FiniteWindowAdditiveDivergence.lean),
  [`T25T25PowerTenFrequencyShift.lean`](TheoryLib/PiQuantitativeBlockHitting/T25T25PowerTenFrequencyShift.lean),
  [`T26T26ManyFrequencyFirstOccurrenceDefect.lean`](TheoryLib/PiQuantitativeBlockHitting/T26T26ManyFrequencyFirstOccurrenceDefect.lean),
  [`T27T27ManyFrequencyLinearGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T27T27ManyFrequencyLinearGap.lean),
  and
  [`T28T28LastFirstOccurrenceLinearGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T28T28LastFirstOccurrenceLinearGap.lean).
  They contain the finite path/cosine identities, the exact digit-change
  defect bound, generic bounded-change-to-periodicity lemmas, the fixed-seed
  conjugacy, eventual additive-gap divergence at every fixed nonzero integer
  frequency, relative cancellation on the canonical first-occurrence support,
  its ambient-prefix energy transfer, the simultaneous finite-window form,
  the exact power-of-ten boundary identity, the positive-proportion
  many-frequency strengthening at T23's canonical cutoff, the
  multiplicity-robust linear additive gap, and its least-first-start-prefix
  specialization.
- New conditional boundary module:
  [`T29T29AppearanceRatioRelativeGap.lean`](TheoryLib/PiQuantitativeBlockHitting/T29T29AppearanceRatioRelativeGap.lean).
  It proves the exact conversion from \(L_m\le C p_\pi(m)\) and T28's
  additive gap to normalized saving \(1/(32C)\), while retaining the
  \(1/16\) frequency proportion. It proves no appearance-ratio premise.
- New exact entropy bridge:
  [`T30T30MaximalEntropyEquivalence.lean`](TheoryLib/PiQuantitativeBlockHitting/T30T30MaximalEntropyEquivalence.lean).
  It proves for every decimal stream that factor entropy equals \(\log10\)
  exactly when the stream is disjunctive, and specializes this to
  \(h_{10}(\pi)=\log10\iff\mathrm{V1}\). It proves no entropy lower bound for
  \(\pi\).
- New recurrent-language theorem:
  [`T31T31RecurrentFactorComplexity.lean`](TheoryLib/PiQuantitativeBlockHitting/T31T31RecurrentFactorComplexity.lean).
  It proves generically that every non-eventually-periodic stream over a
  finite alphabet has at least \(m+1\) recurrent length-\(m\) factors, and
  specializes the result to the exact decimal digit stream of \(\pi\), both
  as a cardinality inequality and with all late-occurrence quantifiers
  expanded. It proves no prescribed-block occurrence.
- Recurrent-branching strengthening:
  [`T32T32RecurrentRightSpecial.lean`](TheoryLib/PiQuantitativeBlockHitting/T32T32RecurrentRightSpecial.lean).
  It proves that recurrent prefix deletion is surjective, that injectivity at
  any length forces eventual periodicity, and hence that every aperiodic
  finite-alphabet stream has a recurrent right-special factor at every
  length.  It specializes both the expanded two-extension statement and the
  strict successive-complexity inequality (30) to \(\pi\).  It prescribes
  neither the factor nor its extension symbols.
- Exact sharpness separator:
  [`T33T33RecurrentSharpnessSeparator.lean`](TheoryLib/PiQuantitativeBlockHitting/T33T33RecurrentSharpnessSeparator.lean).
  For the decimal stream spiking at zero-based powers of two, it proves
  nonperiodicity, classifies recurrent factors bijectively by an optional
  singleton-one coordinate, obtains exact complexity \(m+1\), and proves the
  all-zero factor uniquely recurrent right-special at every length.  This
  closes the generic recurrent-language route rather than proving a new
  \(\pi\)-specific occurrence.
- Recurrent rational-shadow transfer:
  [`T34T34RecurrentCellTransfer.lean`](TheoryLib/PiQuantitativeBlockHitting/T34T34RecurrentCellTransfer.lean).
  It proves the general two-lift recurrent-value injection and factor-two
  bound, connects recurrent symbolic \(\pi\) factors to canonical decimal
  cylinder labels, and leaves the intended diagonal-BBP shadow relation as an
  explicit premise.
- Oversampled floor-grid stability:
  [`T35T35OversampledBBPGridStability.lean`](TheoryLib/PiQuantitativeBlockHitting/T35T35OversampledBBPGridStability.lean).
  It proves the one-sided no-grid-crossing lemma, the sevenfold scale
  inequality, and the source-quantifier conversion.  Its approximation
  sequence is abstract; it does not machine-check the BBP identity or tail.
- Explicit rational Machin specialization:
  [`T36T36MachinGridStability.lean`](TheoryLib/PiQuantitativeBlockHitting/T36T36MachinGridStability.lean).
  It defines rational Taylor sums, proves their partial and Machin
  recurrences, one-sidedness, the \(625^{-K}\) tail, triple-scale inequality,
  and eventual equality with \(\pi\)'s matching arithmetic floor code under
  the sole explicit source-level \(\mu(\pi)<8\) premise.  It proves no
  distribution of those codes.
- Exact floor-to-symbolic bridge:
  [`T37T37FloorSymbolicBridge.lean`](TheoryLib/PiQuantitativeBlockHitting/T37T37FloorSymbolicBridge.lean).
  It proves the generic floor/fractional-part identity, packages every block
  label in `Fin (10^m)`, identifies the \(\pi\) label exactly with both
  `piCylinderCode` and the contiguous `blockAt piDigit` word value, and
  transfers T36 to eventual symbolic-code equality.  It covers negative
  reals, endpoints, and \(m=0\), but proves no code coverage.
- Exact forced-orbit/Fourier transfer:
  [`T38T38MachinForcedOrbit.lean`](TheoryLib/PiQuantitativeBlockHitting/T38T38MachinForcedOrbit.lean).
  It proves strict increase and positive rational forcing, the sampled
  base-ten recurrence, the exact error coboundary, the geometric error bound,
  a uniform fixed-frequency exponential-sum transfer, and equivalence of
  real Weyl cancellation with the original decimal \(\pi\) orbit.  It proves
  no cancellation premise.
- Exact eventual recurrent transfer:
  [`T39T39EventualRecurrentTransfer.lean`](TheoryLib/PiQuantitativeBlockHitting/T39T39EventualRecurrentTransfer.lean).
  It proves generic equality of recurrent sets and counts for eventually
  equal streams, specializes it to the Machin and \(\pi\)-cylinder codes under
  the explicit source premise, transfers the full \(m+1\) recurrent lower
  bound, and states all-cell recurrence only as an equivalence.
- Exact local Machin forcing arithmetic:
  [`T40T40MachinLocalForcing.lean`](TheoryLib/PiQuantitativeBlockHitting/T40T40MachinLocalForcing.lean).
  It expands the sampled increment into the exact six-plus-six rational
  window, regroups it into three positive adjacent pairs per base, clears a
  general pair denominator, and proves the base-5 and base-239 cleared
  numerators are twice odd.  It proves no global residue distribution.
- Exact V1/recurrent-cell equivalence:
  [`T41T41MachinV1Equivalence.lean`](TheoryLib/PiQuantitativeBlockHitting/T41T41MachinV1Equivalence.lean).
  It proves V1 equivalent to recurrence of every canonical decimal cylinder
  cell at every length and, under the explicit source premise, equivalent to
  recurrence of every rational Machin-code cell.  The proof covers leading
  zeros and length zero; neither equivalent side is established.
- Two-adic Machin-forcing foundations:
  [`T42T42MachinTwoAdicForcing.lean`](TheoryLib/PiQuantitativeBlockHitting/T42T42MachinTwoAdicForcing.lean).
  It proves the odd-denominator presentations, exact two-adic order one for
  each three-pair block at bases 5 and 239, and both six-term regroupings.  It
  intentionally stops short of the combined \(N+4\) valuation; T44 now closes
  that gap.
- Exact two-adic forcing separator:
  [`T43T43TwoAdicForcingSeparator.lean`](TheoryLib/PiQuantitativeBlockHitting/T43T43TwoAdicForcingSeparator.lean).
  It proves (11ac), positivity, summability, the exact forced recurrence,
  convergence to \(1/3\), and eventual avoidance of \([0,1/10)\).  This closes
  the coarse two-adic route, not the actual twelve-term Machin numerator
  problem.
- Exact total two-adic forcing:
  [`T44T44MachinTotalTwoAdicForcing.lean`](TheoryLib/PiQuantitativeBlockHitting/T44T44MachinTotalTwoAdicForcing.lean).
  It proves the combined rational valuation \(N+4\), oddness of the actual
  reduced denominator, and exact two-adic valuation \(N+4\) of the reduced
  integer numerator. All three meanings are stated as Lean theorems.
- Actual interior-prime survival:
  [`T45T45MachinPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T45T45MachinPrimeSurvival.lean).
  It decomposes the literal twelve-term block into regular and singular
  parts, proves the cancellation factor nonzero modulo every eligible
  interior prime, and obtains \(v_p(\Delta_N)=-1\). It proves no
  archimedean distribution statement.
- Fixed-initial-modulus telescope:
  [`T46T46MachinFixedModulusTelescoping.lean`](TheoryLib/PiQuantitativeBlockHitting/T46T46MachinFixedModulusTelescoping.lean).
  It proves the exact rational one-step and finite-step recurrences, the
  fixed-initial-denominator form, positivity of the accumulated forcing, its
  exact error-coboundary cast, and both the generic geometric and explicit
  pulse-length bounds. It deliberately proves no exponential-sum estimate.
- Universal actual-forcing prime survival:
  [`T47T47MachinAllPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T47T47MachinAllPrimeSurvival.lean).
  It proves both endpoint cases, the exceptional 239-adic valuation at
  \(N=19\), the four-class routing for all primes above 12, and the resulting
  reduced-denominator divisibility theorem. It deliberately proves no
  archimedean ordering or decimal-cell statement.
- Full-seed upper-half prime survival:
  [`T48T48MachinSeedUpperHalfPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T48T48MachinSeedUpperHalfPrimeSurvival.lean).
  It expands the literal fixed seed, isolates the unique common singular
  pair, proves the extra endpoint is integral, obtains valuation \(-1\), and
  records exact multiplicity one in the reduced denominator for every
  eligible upper-half prime. The PNT, Jacobsthal, and cylinder layers remain
  a separately sourced `proof sketch`.
- Endpoint-to-endpoint class-five pulse:
  [`T49T49MachinEndpointPulse.lean`](TheoryLib/PiQuantitativeBlockHitting/T49T49MachinEndpointPulse.lean).
  It proves the exact two-endpoint core, its nonzero localization, and
  valuation -1 through the full `t <= 2*N+1` window. The first omitted
  forcing contains exponent `3*p`; no longer pulse is claimed.
- Full-seed lower two-band survival:
  [`T50T50MachinSeedLowerBandPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T50T50MachinSeedLowerBandPrimeSurvival.lean).
  It proves the `p,3*p` cancellation coefficient and the unique-term band,
  discharges the only possible endpoint divisor, and concludes exact reduced-
  denominator multiplicity one throughout `d/5 < p <= d`, subject only to
  seven explicit fixed primes. It proves no archimedean residue statement.
- Full-seed third-band survival:
  [`T51T51MachinSeedThirdBandPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean).
  It proves the exact \(p,3p,5p\) coefficient and its five genuine
  nonbase exceptions on \(d/7<p\le d/5\), classifies the only endpoint as
  \(d+2=7p\), excludes endpoint cancellation by its modulo-12 class, and
  concludes valuation \(-1\) and exact reduced-denominator multiplicity one.
  It proves no archimedean distribution statement.
- Persistent three-primary seed factor:
  [`T52T52MachinSeedThreePrimaryPersistence.lean`](TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean).
  It proves the cancellation factor has exact 3-adic order one, identifies
  \(3^a\) as the unique least-valuation common exponent below \(12j+3\),
  bounds the entire regular remainder one valuation step higher, and obtains
  \(v_3(10^jM_{3j})=1-a\) together with exact reduced-denominator
  multiplicity \(a-1\). It proves no numerator-phase distribution.
- Exact complementary quotient and carry:
  [`T53T53MachinQuotientCarry.lean`](TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean).
  It proves the rational coarse/fine split, both Euclidean reconstruction
  identities, the fine and coarse state bounds, equality of the coarse carry
  with the full-denominator quotient, and the canonical digit bound. It
  formalizes equations (11au)--(11av) without asserting that the actual
  coarse state enters any prescribed cell.
- Nested three-primary schedule:
  [`T54T54ThreePrimaryNestedSchedule.lean`](TheoryLib/PiQuantitativeBlockHitting/T54T54ThreePrimaryNestedSchedule.lean).
  It proves that adjacent T52 exponent windows differ by zero or one, so the
  complete three-primary factor stays fixed or triples, forms a divisibility
  chain, and has exact adjacent quotient one or three. This validates the
  integral cross-index frequency map, but it does not estimate its actual
  phase or force a forbidden-word state to die.
- Exact coarse selector:
  [`T55T55ThreePrimaryCoarseSelector.lean`](TheoryLib/PiQuantitativeBlockHitting/T55T55ThreePrimaryCoarseSelector.lean).
  It proves the full-remainder cast, the pre-inverse congruence \(Fc=A-r\),
  and the exact modular identity \(c=AF^{-1}-rF^{-1}\) whenever \(F\) is a
  unit modulo \(D\). This machine-checks the generic algebra underlying
  (11bg), while exposing rather than controlling the indispensable fine
  phase.
- Exact residual lift:
  [`T56T56ThreePrimaryResidualLift.lean`](TheoryLib/PiQuantitativeBlockHitting/T56T56ThreePrimaryResidualLift.lean).
  It proves the lifted residual numerator, cancels the nonzero old selector
  modulus to obtain \(3R'=R+F(u-v)\), and reduces this identity to
  \(R'=3^{-1}R\) in `ZMod F`. This machine-checks the generic algebra
  underlying (11bj), not its Machin-specific instantiation, and makes the
  limitation explicit: depth transport permutes the fine phase rather than
  contracting it.
- Exact generic phase recombination:
  [`T57T57ThreePrimaryPhaseRecombination.lean`](TheoryLib/PiQuantitativeBlockHitting/T57T57ThreePrimaryPhaseRecombination.lean).
  It proves (11bk) from the supplied Euclidean and residual splits, proves the
  fixed-depth residual carry identity, and reduces that carry identity to
  \(R'\equiv10R\pmod F\). It does not construct canonical Machin carries or
  ranges. Multiplication by ten is exact transport, not necessarily a
  permutation and not a distribution estimate.
- Exact Hutton rational shadow:
  [`T58T58HuttonRationalShadow.lean`](TheoryLib/PiQuantitativeBlockHitting/T58T58HuttonRationalShadow.lean).
  It machine-checks Hutton's \(3/7\) arctangent identity at adjacent even/odd
  rational Taylor truncations, both sides of the enclosure, and the exact
  width (11bo). It proves no periodic-orbit coverage, decimal cell hit, or
  V1; the all-index comparison (11bp) with the Machin bracket remains a
  `proof sketch` backed by exact replay.
- Exact Hutton cylinder certificate:
  [`T59T59HuttonCylinderCertificate.lean`](TheoryLib/PiQuantitativeBlockHitting/T59T59HuttonCylinderCertificate.lean).
  It proves the generic bracket-in-cylinder implication, specializes it to
  T58, and identifies the conclusion with the canonical symbolic
  `piCylinderCode` value in (11bq). The supplied containment inequalities are
  the entire unresolved existence problem; the theorem does not produce
  them.
- Exact adjacent Hutton increment:
  [`T60T60HuttonAdjacentIncrement.lean`](TheoryLib/PiQuantitativeBlockHitting/T60T60HuttonAdjacentIncrement.lean).
  It expands the forward step into the four newly added rational Taylor terms,
  proves the closed formula (11br1), and proves strict monotonicity of the
  lower shadows. The subsequent reduced-denominator valuation and localized-
  prefix problem are outside its theorem scope.
- Exact upper-half-prime survival for the Hutton shadow:
  [`T61T61HuttonUpperHalfPrimeSurvival.lean`](TheoryLib/PiQuantitativeBlockHitting/T61T61HuttonUpperHalfPrimeSurvival.lean).
  It isolates the two singular Taylor terms, proves their combined
  cancellation factor is nonzero modulo every eligible prime, proves the
  remaining block is \(p\)-integral, and concludes (11br2), including exact
  denominator multiplicity one.  Its hypotheses explicitly require \(p>7\)
  and \(p\ne17\).  It does not prove the prime-number-theorem product
  consequence (11br4), short-prefix cancellation, or V1.
- Exact joint eligible-prime divisor:
  [`T62T62HuttonEligiblePrimeProduct.lean`](TheoryLib/PiQuantitativeBlockHitting/T62T62HuttonEligiblePrimeProduct.lean).
  It packages the exact T61 hypotheses as a finite set, proves membership and
  the odd-index witness, proves pairwise coprimality and individual
  multiplicity one, and concludes that the complete squarefree product
  divides the reduced Hutton denominator.  It deliberately contains no
  asymptotic product estimate or decimal-orbit claim.
- Exact one-third-band Hutton divisor:
  [`T64T64HuttonOneThirdPrimeProduct.lean`](TheoryLib/PiQuantitativeBlockHitting/T64T64HuttonOneThirdPrimeProduct.lean).
  It replaces T61's condition \(4K+3<2p\) by \(4K+3<3p\), proves that parity
  still leaves the exponent \(p\) as the unique singular odd exponent, and
  proves exact valuation \(-1\), denominator multiplicity one, and divisibility
  by the whole squarefree product over \(((4K+3)/3,4K+3]\), outside the same
  explicit small exceptions.  It proves no asymptotic product estimate,
  selected-numerator distribution, decimal-cylinder hit, or V1.
- Exact Hutton five-primary transient:
  [`T63T63HuttonFiveAdicTransient.lean`](TheoryLib/PiQuantitativeBlockHitting/T63T63HuttonFiveAdicTransient.lean).
  It proves (11br5b), including the zero-exponent edge case, by isolating and
  proving noncancellation of the one- or two-term minimum layer.  T66 below
  proves the complementary two-primary denominator exponent is zero, so this
  is in fact the whole decimal denominator preperiod.  It is not a phase
  distribution theorem.
- Exact one-fifth-band Hutton divisor:
  [`T65T65HuttonOneFifthPrimeProduct.lean`](TheoryLib/PiQuantitativeBlockHitting/T65T65HuttonOneFifthPrimeProduct.lean).
  It combines the singular pairs at exponents \(p\) and \(3p\), proves the
  fixed residue \(21778=2\cdot10889\), proves exact valuation and multiplicity
  one outside \(10889\), and combines the complete band product.  The
  exception is genuine for the local residue, but the module does not declare
  denominator absence at that exceptional instance.  It proves no asymptotic,
  selected-numerator estimate, decimal-cylinder hit, or V1.
- Exact Hutton base-ten denominator transient:
  [`T66T66HuttonDecimalTransient.lean`](TheoryLib/PiQuantitativeBlockHitting/T66T66HuttonDecimalTransient.lean).
  It proves exact two-adic valuation two for every paired summand, valuation
  at least two for the positive full lower shadow, oddness of its reduced
  denominator, and the exact maximum formula (11br5b').  It removes a CRT
  bookkeeping ambiguity but supplies no numerator-phase estimate or V1.
- Exact \(1/2+1/3\) transient wall:
  [`T67T67TwoThreeArctanShadow.lean`](TheoryLib/PiQuantitativeBlockHitting/T67T67TwoThreeArctanShadow.lean).
  It proves the rational bracket, exact two-adic valuation of the lower
  shadow and its reduced denominator, the matching upper bound on the
  five-primary denominator, and therefore exact decimal preperiod \(4K+1\).
  It also proves that scaling the exact bracket width by \(10^{4K+1}\)
  exceeds \(1/10\).  Thus a complete-period argument starts too late to
  transfer even one prescribed digit; T67 closes that route and proves no
  numerator-phase estimate, cylinder hit, or V1.
- Exact simultaneous Hutton primary layers:
  [`T68T68HuttonSimultaneousPrimary.lean`](TheoryLib/PiQuantitativeBlockHitting/T68T68HuttonSimultaneousPrimary.lean).
  It proves the general odd-prime dominant-layer score lemma and specializes
  it at \(R_a=3^a7^{a+1}=4K_a+3\), \(a\ge2\), to exact rational valuations
  and reduced-denominator multiplicities \(R_a+a\) at 3 and \(R_a+a+1\) at
  7.  It contains no leading-unit congruence, CRT/high-prime completion,
  short-orbit phase estimate, cylinder hit, or V1.
- Fixed-times-sixteen return bridge:
  [`T69T69FixedSixteenReturn.lean`](TheoryLib/PiQuantitativeBlockHitting/T69T69FixedSixteenReturn.lean).
  It proves the metric form of the one fixed return, the resulting
  \(\times16\)-invariance and semigroup-orbit containment, full-orbit-closure
  implication to exact V1, the converse V1-to-return implication, and the
  equivalence conditional on the explicit density of the joint
  times-10/times-16 orbit of \(\pi\).  It introduces no source theorem as an
  axiom and proves no fixed return, decimal-cylinder hit, or V1.
- Empirical rigidity and carry interfaces:
  [`T70T70EmpiricalRigidityBridge.lean`](TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean)
  and
  [`T71T71CenteredCarryRecurrence.lean`](TheoryLib/PiQuantitativeBlockHitting/T71T71CenteredCarryRecurrence.lean).
  T70 machine-checks conditional invariant-support/absolute-continuity routes
  under its explicit Furstenberg-shaped source premise; T71 machine-checks
  the generic centered-remainder carry algebra.  Neither constructs its
  fixed-pi distribution premise or proves a return.
- Exact all-color and endpoint-grid bridges:
  [`T72T72ColoredRepunitReturn.lean`](TheoryLib/PiQuantitativeBlockHitting/T72T72ColoredRepunitReturn.lean),
  [`T73T73ThreePrimaryOrbit.lean`](TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean),
  [`T74T74ThreePrimaryDecimation.lean`](TheoryLib/PiQuantitativeBlockHitting/T74T74ThreePrimaryDecimation.lean),
  and
  [`T75T75UniformShadowCover.lean`](TheoryLib/PiQuantitativeBlockHitting/T75T75UniformShadowCover.lean).
  T72 proves V1 equivalent to all endpoint-safe repunit-color returns; T73
  proves the exact primary power-of-ten orbit; T74 proves the four one-term
  ninefold folds; and T75 proves the corrected abstract implication from
  uniform late shadow coverage and vanishing shifted error to all T72 colors
  and V1.  T73--T74 control only the isolated primary structure, while T75
  asserts no coverage premise for the actual BBP phase.  Their conjunction
  therefore still does not prove V1.
- Exceptional-path outer cover:
  [`T76T76ExceptionalPathCylinderCover.lean`](TheoryLib/PiQuantitativeBlockHitting/T76T76ExceptionalPathCylinderCover.lean)
  machine-checks the abstract countable cylinder cover and the exact
  even-epoch geometric sum.  Its 15 supporting declarations are registered;
  it neither proves the BBP correlation bound nor excludes the actual path.
- Nested product-grid separator: equations (11ad)--(11ae) are a
  `proof sketch`.  They preserve the loose 5/239/product grids, moving residue
  recurrence, geometric forcing bound, exact two-adic order, and one 3-adic
  cancellation while omitting a decimal cell.  They do not instantiate the
  actual Machin Taylor numerators or the exact LCD \(\Lambda_N\).
- Sparse audit status: the earlier unrestricted identity (4)–(7a) remains a
  `proof sketch`, but T23 now supplies the meaningful constrained sampling
  theorem. T27 removes repeated-visit multiplicity from the additive-gap
  transfer, T28 minimizes the first-start cutoff, and T29 exposes the exact
  consequence of a relative bound on that cutoff. The remaining loss is the
  absence of that bound and, more decisively, of all-frequency cancellation.
- Missing mathematical input for the resolution route: the strict relative
  fixed-\(\pi\) exponential-sum estimate in (9), uniformly over its natural
  frequency window for every \(k\).  Eventual additive divergence (20) does
  not supply this estimate.
- Main theorem and axiom audit: no theorem proving V1 exists. Do not add V1 to
  the verified track unless its full premise is established, the exact theorem
  is registered in `audit/AxiomAudit.lean`, and `scripts/check.ps1` passes.

The supporting T18--T77 theorems and helper lemmas are registered explicitly
in `audit/AxiomAudit.lean`. Direct compilation and the explicit audit compile
accept the new declarations with only `propext`, `Classical.choice`, and
`Quot.sound`. T46--T60 respectively contribute 12, 32, 22, 35, 49, 37, 25,
15, 5, 3, 3, 4, 14, 4, and 3 proposition declarations; T61 contributes 15
and T62 contributes 9 declarations (including its two definitions). T63,
T64, T65, and T66 contribute 33, 11, 26, and 7 declarations respectively,
including their definitions; T67 and T68 contribute 29 and 42 proposition
declarations respectively. T69 adds one proposition definition and eight
registered theorem declarations. T70--T77 add their displayed conditional,
carry, colored-return, primary-orbit, decimation, and uniform-cover
declarations; in particular all 12 T74 and four claim-supporting T75 theorems
are registered exactly once, all 15 T76 declarations are registered, and all
26 T77 declarations are registered.
Their focused builds, aggregate builds, direct audits, and concrete checks
pass; T63--T77 also have independent adversarial audits where recorded.  The
T77-integrated
`pwsh -File scripts/check.ps1` replay also ended with
`PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.`

## Independent review

- Statement checked by: repository source audit and literature audit on
  2026-08-10; no independent human disposition.
- Proof checked by: Lean and the clean axiom audit for T18--T77; separate
  automated adversarial reviews found no mismatch in the T18/T19 constants,
  T20 path-energy constant, T21 change-count indexing, or T22 fixed-frequency
  conjugacy. A further repository-wide audit found no hidden unconditional
  premise discharging relative cancellation; independent checks found T23's
  cell geometry, \(q/2\) pair-energy constant, first-occurrence embedding,
  and Morse--Hedlund arithmetic clean, as well as T24's finite-cutoff
  aggregation, T25's boundary orientation/constants, and T26's aggregate
  energy reordering, \(1/16\) proportion, and selected-to-full transfer;
  T27's \(31/32\) norm constant and complement count; and T28's finite-sup
  edge case, least-prefix quantifiers, embedding, and minimal-prefix transfer;
  and T29's appearance-ratio inequality direction, casts, positivity, and
  preserved frequency quantifiers. An independent automated audit found
  T30's universal entropy bound, limsup steps, empty-word handling,
  list/function block translations, and both equivalence directions clean;
  it also confirmed that no maximal-entropy premise for \(\pi\) is proved.
  A separate automated adversarial audit replayed T31's common cutoff,
  shifted-tail aperiodicity, value-preserving factor injection, recurrent
  subtype cardinality, and fully expanded arbitrary-late occurrence
  statement and found no semantic or axiom issue.  An independent T32 audit
  then checked recurrent-prefix surjectivity, the injectivity-to-flat-tail
  bridge, the strict cardinal inequality, distinct-final-symbol extraction,
  the \(m=0\) edge case, and both exact \(\pi\) specializations.  It found no
  mathematical or axiom issue and prompted registration of the two remaining
  helper lemmas.  A separate T33 audit checked the powers-of-two indexing,
  arbitrary-start eventual-period contradiction, late-window cutoff,
  support-index injection and bijection, exact shape classification,
  positive-length cardinal equality, and length-zero right-special edge case;
  it found no mathematical, documentation, forbidden-construct, or axiom
  issue.  The T34--T37 audit then checked recurrent two-lift selection and
  injection, the factor-two arithmetic, all zero-length cases, floor-crossing
  orientation, source-onset conversion, sevenfold and triple scale bounds,
  Machin parity/signs, the \(625^{-K}\) error including \(K=0\), rational
  recurrence indices, claim scope, all registrations, and the exact axiom
  allowlist.  For T37 it additionally checked the all-real floor/fractional
  identity at negative inputs and zero scale, terminating half-open
  endpoints, \(m=0\)/`Fin 1`, exact zero-based indexing, `blockAt` word value,
  and preservation of the explicit source premise.  It found no mathematical
  or axiom issue.  The T38 audit independently checked the six-term step
  indices and signs, strict increase and positive forcing, exact fractional
  recurrence and error coboundary, the \(K=0\) geometric bound, phase constant,
  empty-prefix case, uniform Fourier estimate, and both Weyl-cancellation
  directions.  It also replayed the exact rational formula and finite
  computations.  The T39 audit checked both directions of eventual recurrent
  transfer, literal set and subtype-cardinality equality, the source premise,
  and the \(m>0\) lower-bound scope.  The T40 audit independently replayed the
  six-plus-six Taylor indices and signs, the \(+16/+4\) three-positive-pair
  regrouping, the denominator-clearing identity \(q^2(r+2)-r\), and the exact
  twice-an-odd formulas \(2(12r+25)\) and
  \(2(28560r+57121)\).  The T41 audit checked the list/function
  occurrence bridge, arbitrary-late quantifiers, leading-zero injectivity,
  \(m=0\), and both rational-transfer directions.  No mathematical, scope,
  forbidden-construct, registration, or axiom issue was found.  There is no
  independent human disposition. T44 was then independently checked for its
  block indices, signs, unequal-valuation argument, nonzero obligations,
  odd-denominator bridge, literal reduced-numerator statement, registration,
  and axiom scope. T45 was independently checked for the singular-pair sign,
  Fermat reduction to 951, exclusion of 317, regular-term width bound,
  unequal-valuation sum, and precise exclusion of endpoints and \(p=239\).
  Both audits found no mathematical or scope defect. T47's endpoint routing,
  exceptional 239 calculation, residue-class exhaustion, and denominator
  bridge were checked through the compiled theorem types and full axiom
  registration. A separate T48 audit checked the seed-prefix indices and
  signs, upper-half uniqueness, extra-endpoint exclusion, residue 951,
  regular-term integrality, decimal scaling, exact denominator multiplicity,
  all 22 registrations, and forbidden-construct scope; it found no defect.
  A separate T49 audit checked both endpoint indices, the Fermat residue,
  cancellation separation, all 35 registrations, and the exact pulse cutoff;
  the first omitted forcing is precisely where exponent `3*p` enters. A
  separate T50 audit checked both prime bands, coefficient factorization,
  valuation-to-denominator conversion, and then removed the apparent endpoint
  hole by classifying it as `d+2 = 5*p` and proving the endpoint-adjusted
  residue nonzero. It found no defect in the 49 registered propositions.
  T51 was separately checked for the \(p,3p,5p\) band decomposition, the
  five genuine coefficient exceptions, endpoint classification
  \(d+2=7p\), modulo-12 endpoint exclusion, all 37 registrations, forbidden
  constructs, and the allowlisted axiom surface; the full integrated gate
  passed. T52 was independently checked for its modulo-nine cancellation
  factor, unique three-primary minimum, regular-remainder bound, endpoint,
  direct \(j\)-index conversion, decimal scaling, denominator conversion, all
  25 registrations, and allowed axioms; 80 full seeds and the component
  identities also passed exact finite replay. T53 was independently checked
  for the rational split, two-stage reconstruction, quotient/remainder
  ranges, canonical digit bound, all 15 registrations, and axiom surface;
  its independent checker passed 9,537,393 enumerated cases. Neither audit
  found a defect.
  T54 then formalized the adjacent three-primary schedule: its five audited
  propositions prove exponent change zero-or-one, factor fixed-or-tripled,
  divisibility, and quotient one-or-three. Its focused build, direct audit,
  and full exact-allowlist gate all passed; this is arithmetic nesting only,
  not an ASR estimate.
  T55 was then independently checked against the exact Euclidean split. Its
  three registered propositions prove the full-remainder cast, \(Fc=A-r\),
  and the unit-cancelled selector in `ZMod D`; focused compilation, direct
  axiom inspection, exploit scan, and the full gate passed. The companion
  leading-unit checker passed through \(j=150\), \(K=8\), but those finite
  shell calculations remain `experiment` and the general shell derivation
  remains a `proof sketch`.
  T56 then machine-checked the exact residual lift in three registered
  propositions. Focused compilation, direct axiom inspection, and the full
  `scripts/check.ps1` gate passed with only the exact allowlist. This is the
  generic algebraic permutation statement underlying (11bj), not its
  Machin-specific instantiation or a cancellation estimate.
  T57 then machine-checked four generic recombination and fixed-depth carry
  declarations. An independent adversarial audit replayed both T56 and T57,
  confirmed their focused builds, exact registrations, forbidden-construct
  scan, and complete direct axiom audit, and found only the allowlisted
  dependencies. It emphasized that T57's modulo-\(F\) multiplication by ten
  is transport rather than a permutation without an additional unit premise,
  and that neither module instantiates the actual Machin state or estimates
  its phase. The independent report is
  [`t56_t57_independent_audit.md`](work/ultrapi-resume/t56_t57_independent_audit.md).
  T58 then machine-checked fourteen unconditional declarations for the
  rational Hutton lower/upper sums, Hutton identity, enclosure, exact omitted-
  term width, positivity, and lower-tail bound. Its focused build and direct
  audit report only the exact allowlist. Independent adversarial review
  replayed the Taylor parities, exact \(K=0\) endpoints and width, and all
  registrations; no decimal-hit claim is inferred from a narrower bracket.
  T59 then machine-checked four declarations converting any supplied scaled
  bracket containment into the arithmetic block code and canonical symbolic
  `piCylinderCode` value, including the half-open upper boundary, leading
  zeroes, length zero, negative translated cells, and zero-based starts. The
  audit compiled twelve exact endpoint/indexing examples, including a
  nonvacuous \(K=0\) certificate for the first fractional digit, and found all
  eighteen T58/T59 registrations exactly once with only the allowlisted axiom
  surface. It proves no existence of the containment witnesses and therefore
  no V1. The report is
  [`t58_t59_independent_audit.md`](work/ultrapi-resume/t58_t59_independent_audit.md).
  The separate exact arithmetic through \(N=5000\) discussed earlier belongs
  to the Machin checker; it is not evidence for T58 or T59.
  T60 then machine-checked the four-term adjacent increment, its closed
  positive rational formula, and strict monotonicity. An independent audit
  checked the forward-index convention, both Taylor signs, the constants
  \(16K+29\) and \(96K+169\), denominator powers, all three registrations,
  and exact rational examples for \(K=0,1,2,3\). Focused and aggregate builds,
  the direct audit, and the full gate pass with only the allowlisted axioms.
  The report is
  [`t60_independent_audit.md`](work/ultrapi-resume/t60_independent_audit.md).
  No valuation, localized prefix hit, or V1 follows from T60 alone.
  T61 then machine-checked fifteen declarations isolating the singular Hutton
  pair and proving exact valuation \(-1\) and denominator multiplicity one for
  every eligible upper-half prime.  Independent adversarial review checked
  the odd-exponent endpoints, the factor \(4(2\cdot7^p+3^p)\), Fermat residue
  68, genuine \(p=17\) cancellation, the necessary \(p>7\) exclusions, all
  fifteen registrations, exact rational examples for \(K=0,\ldots,8\), and
  the axiom surface.  Focused, aggregate, direct-audit, exploit-scan, and full
  verification-gate runs pass with only the allowlisted axioms.  The report is
  [`t61_independent_audit.md`](work/ultrapi-resume/t61_independent_audit.md).
  It explicitly proves no prime-product asymptotic, short-prefix distribution,
  cylinder hit, or V1.
  T62 then machine-checked the joint finite product theorem in nine registered
  declarations.  An independent audit verified the exact set endpoints, odd
  witness, empty-set cases, pairwise-coprime induction, individual
  multiplicity-one scope, finite examples through \(K=4\), all registrations,
  and the axiom surface.  Focused and aggregate builds, direct audit, exploit
  scan, and the full verification gate pass with only the allowlist.  The
  report is
  [`t62_independent_audit.md`](work/ultrapi-resume/t62_independent_audit.md).
  It deliberately proves no product asymptotic, prefix theorem, or V1.
  T64 then machine-checked the wider one-third band in eleven registered
  declarations.  Independent review verified the strict lower endpoint,
  inclusive upper endpoint, parity elimination of \(2p\), the exact \(p=17\)
  exclusion, individual multiplicity one, pairwise-coprime product, concrete
  boundary cases, every registration, and the axiom surface.  Direct,
  aggregate, audit, and full-gate runs pass with only the allowlisted axioms.
  The audit and independent Lean checks are
  [`t64_independent_audit.md`](work/ultrapi-resume/t64_independent_audit.md)
  and
  [`t64_independent_checks.lean`](work/ultrapi-resume/t64_independent_checks.lean).
  The result is denominator arithmetic, not a decimal-prefix theorem or V1.
  T63 independently passed its full endpoint, minimum-layer, reduction, and
  axiom audit for all \(5^e\le4K+3<5^{e+1}\), including \(e=0\) and the
  one- versus two-minimum transition.  The audit corrected only the original
  overbroad preperiod wording; T66 subsequently closes that two-primary
  caveat.  Its report and exact replay are
  [`t63_independent_audit.md`](work/ultrapi-resume/t63_independent_audit.md)
  and
  [`t63_independent_checks.lean`](work/ultrapi-resume/t63_independent_checks.lean).
  T65 independently passed its four-term algebra, strict \(R<5p\) endpoint,
  fixed residue \(21778\), genuine exception \(10889\), regular-block
  valuation, finite product, registration, and axiom audit.  The audit
  stresses that the exception is to this noncancellation mechanism; T65 does
  not assert complete denominator absence at the exceptional instance.  See
  [`t65_independent_audit.md`](work/ultrapi-resume/t65_independent_audit.md)
  and
  [`t65_independent_checks.lean`](work/ultrapi-resume/t65_independent_checks.lean).
  T66 then machine-checked seven registered declarations proving oddness of
  the reduced Hutton denominator and the exact base-ten denominator exponent
  (11br5b').  Its focused build, concrete replay, direct audit, and
  T66-integrated full gate pass with only the allowlist.  Independent review
  re-derived the pair valuation and finite-sum argument, added direct reduced-
  fraction and boundary checks, and found no defect.  The primary report and
  audit are
  [`t66_hutton_decimal_transient_report.md`](work/ultrapi-resume/t66_hutton_decimal_transient_report.md)
  and
  [`t66_independent_audit.md`](work/ultrapi-resume/t66_independent_audit.md).
  T67 then machine-checked 29 registered declarations for the exact
  \(1/2+1/3\) arctangent shadow.  Independent review re-derived its bracket,
  exact two-primary reduced-denominator exponent, five-primary bound,
  decimal-preperiod identity, and strict scaled-width obstruction; it also
  replayed focused, aggregate, direct-audit, exploit-scan, and full-gate
  checks with only the allowlisted axioms.  The primary report, independent
  Lean checks, and audit are
  [`t67_two_three_arctan_shadow_report.md`](work/ultrapi-resume/t67_two_three_arctan_shadow_report.md),
  [`t67_independent_checks.lean`](work/ultrapi-resume/t67_independent_checks.lean),
  and
  [`t67_independent_audit.md`](work/ultrapi-resume/t67_independent_audit.md).
  This is an exact obstruction to the complete-period route, not a selected-
  transient estimate, cylinder hit, or V1.
  T68 then machine-checked the general dominant-layer lemma and exact
  simultaneous 3- and 7-primary Hutton valuations in 42 registered
  declarations.  Independent review re-derived the unique-minimum argument,
  verified the boundary \(a=2\) values \(R=3087\), \(K=771\), and denominator
  multiplicities 3089 and 3090, counted every declaration and registration
  exactly once, and replayed the focused, aggregate, direct-audit, and full
  gates with only the allowlist.  The primary report, independent Lean
  checks, and audit are
  [`t68_hutton_simultaneous_primary_report.md`](work/ultrapi-resume/t68_hutton_simultaneous_primary_report.md),
  [`t68_independent_checks.lean`](work/ultrapi-resume/t68_independent_checks.lean),
  and
  [`t68_independent_audit.md`](work/ultrapi-resume/t68_independent_audit.md).
  This is exact denominator arithmetic, not leading-unit/CRT completion,
  phase steering, a cylinder hit, or V1.
  T69 then machine-checked one proposition definition and eight registered
  theorem declarations for the fixed-times-sixteen bridge.  Independent
  review checked the sequential closure quantifiers, commutation and closure
  invariance, semigroup-orbit containment, irrationality-free forward
  direction, explicit decimal-cylinder inner-ball transfer, and the converse
  V1-to-return argument.  It identified an initially over-strong T77 premise;
  the module was corrected to assume exactly
  `Dense (tenSixteenOrbit (piCircleOrbit 0))`, after which the direct compile,
  axiom audit, and full 8,493-job gate passed.  The primary report and audit
  are
  [`t69_fixed_sixteen_return_report.md`](work/ultrapi-resume/t69_fixed_sixteen_return_report.md)
  and
  [`t69_fixed_sixteen_return_independent_audit.md`](work/ultrapi-resume/t69_fixed_sixteen_return_independent_audit.md).
  The premise is the published Furstenberg density conclusion, not a
  formalized source theorem or a new axiom.  T69 proves no fixed return or V1.
  Three additional adversarial route audits also passed.  The
  integer-Chebyshev audit verified positive capacity and every degree/height
  ledger, while correcting the scope of its finite truncation-node
  experiment.  The signed-Machin audit independently checked both Gaussian
  identities, Yu and Zeilberger--Zudilin applicability, the infinite
  score-separated families, deep real cancellation, and the exact exponent-
  2059 p-adic cancellation.  The restricted-denominator audit checked Iyer's
  quantifiers, the decimal-Cantor denominator lemma, Schleischitz's Theorems
  3.4 and 4.9, every endpoint in the explicit cofactor bound, and both exact
  modular examples.  Their reports and independent audits are linked at
  (37c) and (40c)--(40e).  All are `proof sketch` route separators with finite
  `experiment` replays; none proves V1.
  Two subsequent adversarial audits also passed after correcting their
  primary artifacts.  The all-depth BBP audit independently verified the
  reflected null identity, 2-adic logarithmic primitive, analytic unit,
  tail separation, and exact denominator exponent, while narrowing one
  general-\(c\) quantifier; its fixed-16 conclusion is unaffected.  The
  exceptional-alignment audit corrected the two-digit enumeration and the
  distinctness quantifier, then independently reproduced the 2,047-case CRT
  classification with a separate exact Machin enclosure for \(\pi\), as well
  as the exponent cutoff (40f)--(40g).  Both remain `proof sketch` route
  results, not V1.  A corrected Padé audit also passed for its narrowed
  scope: it independently reproduced the depth-six denominator, least CRT
  alignment exponent, and exact error lower bracket (40h)--(40j), while
  preserving the earlier audit failure that exposed an unsupported reduced-
  quality asymptotic.  Only the finite alignment and conditional quality
  lemma remain; there is no asymptotic family closure, fixed return, or V1.
  The BBP recurrence, all-index dyadic valuation, normalized 2-adic primitive,
  5-adic subsequence, prime-interval denominator product, CRT reduction,
  selected-prime residues, block-renormalization conjugacy, positive-moment
  finite-omega separators, and pole-class non-Gosper obstruction, as well as
  the exact \(1/81\)/Fibonacci frequency separators, were separately replayed
  as adversarial `proof sketch` audits;
  they are not promoted to `machine-checked`.
  The actual shifted-grid Poisson formula, forbidden-word transfer product,
  local-character CRT factorization, reciprocity back to the actual Machin
  phase, power-of-ten aliases, and equations (11aw)--(11bb) were separately
  audited. The companion checker passed 1,700 automaton, 1,350 CRT, and 6,750
  reciprocity cases and reproduced all 8,580 prefix rows in the falsification
  experiment. The obstruction is sound at `proof sketch`/`experiment`
  status, but ASR remains an unproved `conjecture`.
  A subsequent exact three-primary audit closed the cross-index frequency
  map and classified threshold aliases. It found that tripling the grid adds
  three aliases, but the actual orbit remains in the single inherited alias;
  cancellation obtained only after summing all three is therefore unavailable
  pointwise. Exact checks through \(j=80\) verified 79 transitions, 1,343
  frequency identities, 2,213 telescopes, and 85,800 one-digit membership
  tests. A companion quotient-automaton audit retained the actual Machin
  forcing while varying the non-three fine residue and produced complete-epoch
  avoiding states. These are `proof sketch`/`experiment` separators, not
  statements about the actual numerator.
  The dated nested-resonance literature audit located no theorem closing this
  pointwise gap. The closest individual Fourier estimate is Maynard's Lemma
  8.2 (also Lemma 10.1), but it requires a reduced denominator component
  \(q_1>1\) coprime to ten. Every ASR frequency \(\ell D_j/10^{n_j}\) reduces
  to a denominator dividing \(10^{n_j}\), so \(q_1=1\) identically. The audit
  is `literature-checked`; ASR remains a `conjecture`.
  Three 2026-08-13 adversarial audits then passed the medium-prime,
  one-character, and adjacent-shift reductions.  The Gauss audit independently
  rederived (40am)--(40ao), fixed a false journal attribution for Wagner's
  preprint, and left the first-band little-o estimate explicitly unproved.
  The one-character audit rechecked the T69 dependency, BBP tail and rational
  recurrence, Chen--Ye--Zheng hypotheses, Fejer alternative, and Kempner
  separator without changing the primary mathematics.  The adjacent-shift
  audit made the positivity and integer-frequency quantifiers explicit and
  inserted the required \(W_1\) passage from the pushforward row to the
  shifted row before the matching argument.  A transient generic checker-name
  collision was detected before integration; all three independent replays
  were rebuilt and rerun under distinct scoped filenames.  Primary and
  independent checkers, Python compilation, source pins, and diff hygiene
  pass.  The Gauss audit also reran `scripts/check.ps1` successfully.  These
  remain `proof sketch` reductions plus finite `experiment` replays; none is
  `machine-checked` as a new theorem and none proves V1.
  A fourth 2026-08-13 adversarial audit then passed the Gauss first-band
  follow-up (40ap)--(40at).  It independently rederived the finite-field
  coefficient identity, scalar reflection, Lucas step, both affine rays and
  their unique merger, the endpoint order of limits, count equivalence, and
  CRT package.  It also checked that the abstract one-zero construction has
  exactly the limited no-go scope claimed: it rules out a local-statistics
  inference but is not represented as an actual zero set of \(A_r\).  The
  primary and independent replays pass on disjoint implementations; artifact
  links, UTF-8/C0 hygiene, source pins, Python compilation, and diff hygiene
  pass.  No formal code changed, and the first-band little-o estimate remains
  unproved.
  A fifth adversarial audit passed the scalar BBP reduction
  (40au)--(40ay), but only after catching and repairing a material separator
  error.  The first model had a nonintegral initial phase, so its claimed gap
  was not a gap for the required partial product.  The corrected model has
  \(R_0^*=-2\) and the anchored lower bound \(1/8\).  Independent derivations
  then verified the coefficient polynomial, all endpoint signs, monotone
  \(144\pi\) approximation, exact tail variation, scalar recurrence,
  derivative-orbit telescope, and corrected separator.  Both distinct exact
  replays, all pins, C0/UTF-8 hygiene, and diff checks pass.  This audit
  strengthens confidence in the reduction while confirming that it proves no
  accumulated return.
  An eighth adversarial audit then passed the scalar p-adic/Archimedean
  separator (40bh).  It independently verified all endpoint fractions and
  signs, the uniform \(1/16\) gap, exact phase two-adic valuations, both local
  forcing scales, arbitrary fixed finite jets, the full-denominator lift, and
  the precise finite-splice scope.  Its checker imports no primary code and
  also passes at deeper parameters.  The lift is pointwise in depth and
  deliberately does not preserve the exact BBP increment or cross-depth odd
  numerator; it closes a class of local/denominator arguments but does not
  prove or refute the true return.
  A sixth adversarial audit passed the weakened adjacent-matching reduction
  (40az)--(40bd) after two reproducibility corrections: both matching maps
  now have explicit finite codomains, and the exact T39 dependency plus the
  versioned Chen--Ye--Zheng and Technau--Rudnick PDFs are pinned.  Independent
  derivations verified the measure domination, same-subsequence quantifiers,
  infinite-support characterization, rational-support difference-set case,
  fixed-lag endpoint constant, strict \(1/24\)-versus-\(1/4\) weakening, and
  the positive-mass ergodic alternative.  The primary and independent exact
  replays pass with disjoint implementations.  This removes collision
  anti-concentration from the sufficient criterion but proves neither the
  fixed-period defects nor the adjacent matching for \(\pi\).
  A ninth adversarial audit passed the centered-carry reduction
  (40bi)--(40bm), after first stopping an input hash mismatch caused by a
  genuine sevenfold-oversampling addition and then explicitly refreezing the
  two inputs.  It independently checked the common-denominator recurrence,
  least residues, carry-energy equivalence, rational nearest-integer shadows,
  logarithmic irrationality bound, and sparse Kempner separator.  Its disjoint
  checker imports no primary implementation.  The onset is only for each
  fixed \(P\), and the result proves \(\Omega(\log N)\), not the required
  \(\Omega(N)\) carry count.
  A seventh adversarial audit passed the Gauss prefix-gcd identity
  (40be)--(40bg).  It independently rederived the correct coefficient
  normalization, generating function, recurrence, full Lucas product,
  reflection scalar, both prime ranges with strict endpoints, and the exact
  below-\(n\) radical equality.  It confirmed that the truncated logarithm is
  equivalent to \(M_n=o(n)\), while the untruncated gcd leaks both large
  common primes and multiplicities.  The audit corrected Xiaos title and
  added an exact Rowland--Yassawi v2 pin.  Both frozen checkers pass; this is
  a `proof sketch` route closure, not the missing estimate or V1.
  Separately, T70 was extended from nine to 15 registered declarations.  The
  new `machine-checked` theorems show, under T77's explicit source-shaped
  Furstenberg premise, that infinite common invariant support is full and
  give both ergodic-nonsingular and nonergodic absolute-continuity interfaces
  to V1.  The full kernel build, exploit scan, and exact axiom allowlist gate
  pass.  No Furstenberg premise or fixed-pi infinite-support/matching premise
  is constructed.
  T71 then passed an independent adversarial formal audit.  Its four generic
  centered-integer theorems machine-check the one-step recurrence, quotient
  orientation, correction sign, uniqueness, and both half-open boundaries;
  the independent Lean and integer replays cover 36,912 rows, all four exact
  audit registrations, and the unchanged axiom allowlist.  T71 does not
  instantiate the BBP integers or prove carry density, a word hit, or V1.
  Two further independently replayed `proof sketch` closures sharpen the
  surrounding obstruction.  The full sevenfold recurrence (40bn)--(40bq)
  shows every denominator congruence is carry-blind even though the selected
  two-adic valuation is exact and each odd-LCM increment has only
  \(O(\log n)\) bits.  The matching characterization (40br)--(40bs) shows
  that, under ergodicity, both proposed finite matching targets are already
  equivalent to the missing equality \((T_{16})_*\mu=\mu\); a same-forcing
  Bernoulli separator preserves all other proposed hypotheses while making
  the two measures singular.  The fresh source audit (40bt)--(40bu) adds
  arbitrarily late fixed-amplitude pi excursions and Mahler's movable-
  multiplier all-word theorem, but neither supplies positive frequency or a
  theorem for the unmultiplied digits of pi.  The independently audited
  odd-LCM continuation (40bv)--(40bz) then removes two misleading targets:
  fresh-prime congruences cannot see the carry, and bounded carry gaps would
  contradict V1 because V1 forces arbitrarily late zero-carry blocks of every
  length.  Its exact zero-run formula reduces logarithmic or sublinear gaps to
  new restricted-denominator approximation estimates, while the published
  irrationality measure gives only a linear bound.  None supplies the missing
  positive Cesaro density.
  T72 then machine-checks the exact all-color target (40ca)--(40cb), including
  arbitrary lateness and endpoint-safe leading-zero/all-nine cylinders.  Its
  ten declarations are registered once, and an independent formal audit
  recompiled them and replayed the full 8,493-job gate with verdict `PASS`;
  it proves no colored return for pi.  The rational common-state derivation
  (40cc)--(40cg) expresses the same target through the exact BBP colors and
  shows both why fixed congruences become vacuous and why uncolored long
  zero-carry blocks are insufficient; its disjoint independent audit and
  checker pass exhaustive (P=5) color and five-digit-word replays plus new
  (P=5,6,7) recurrence and boundary tests.  Finally, two independent audits of
  (40ch)--(40ck) pass: exponentially accurate rational zero-carry separators
  retain either exact denominator/two-adic data or density-one exact forcing,
  but not the exact selected numerator at every depth.  This is a method
  boundary, not the missing all-color return theorem.
  T73 then machine-checks nine declarations for the full power-of-ten orbit
  modulo \(3^{e+2}\), and T74 machine-checks twelve elementary declarations
  for the four BBP ninefold decimations.  Every declaration is registered in
  the central axiom audit; the T74-integrated 8,493-job verification gate
  passes with only the exact allowlist.  The summed decimation, LTE endpoint
  nesting, and sparse primary Fourier transform remain independently audited
  `proof sketch`, because the synchronized complementary coefficient is
  uncontrolled.  The initial full-phase `experiment` through \(e=14\)
  was independently reconstructed on all twelve rows and all 24 retained
  Fourier values.  Its gap and every-mode decay targets remain
  `conjecture`s; its audit explicitly corrects the all-color T72 implication
  and asserts neither a fixed return nor V1.  The separately audited
  epoch-16 extension adds two rows of length \(5{,}491{,}685\) and a strict
  actual-orbit gap below \(10^{-5}\), certifying all 100,000 five-digit words
  only in that finite prefix.
  T75 subsequently machine-checks that corrected abstract implication in four
  registered declarations: uniform late shadow coverage plus vanishing
  shifted-shadow error gives every colored repunit return and then V1, with a
  separate positive-interior argument at color zero.  Focused checks and the
  complete 8,493-job gate pass with only the allowlisted axioms.  The actual
  BBP coverage premise remains unproved.
  Two exact continuation attacks then narrow why.  The complement-Fourier
  nine-block identity shows that ordinary off-diagonal mixing leaves one
  ninth of the selected energy and that each differenced block still contains
  linear dyadic precision plus exponential high-prime modulus.  Separately,
  the endpoint recursion audit falsifies the factor-nine gap recursion on all
  four exact transitions and rejects every primary-compatible pair among
  41,924 complete subwindows.  A carefully scoped non-BBP countermodel shows
  that the listed primary structure alone allows gaps arbitrarily close to
  one.  These are `proof sketch`/`experiment` method separators, not a
  refutation of the actual endpoint-gap `conjecture`.
  The collision-energy identity (7a) and separator (25) remain `proof sketch`;
  there is no independent human disposition.
- Novelty/attribution checked by: bounded dated search only. The method is
  classical, and neither novelty, sharpness, nor literature-optimality is
  claimed for the numerical specialization.
- Resolution status: not a `candidate resolution`; not a
  `verified resolution`.

## Operator stop snapshot

On Marcel's request on 2026-08-10 UTC, the active proof search was stopped and
all three live research agents were interrupted.  This document consolidation
and the verification gate were the only remaining actions.  No complete proof
of V1 was obtained, no theorem asserting V1 was added, and no phone
notification was sent for this stop because the agreed complete-proof
breakthrough condition was not met.

The clean restart point, if research is explicitly resumed, is narrow: either
use information special to the actual twelve-term numerator in (11w) to
control its moving archimedean residue, or leave the Machin route and prove a
fixed-\(\pi\) distribution statement such as (9), maximal decimal factor
entropy, or all-cell recurrence directly.  Reusing positivity, summability,
geometric decay, nested product grids, the \(N+4\) two-adic profile, or the
single 3-adic cancellation alone is ruled out by the separators above.

### Resume snapshot — 2026-08-12 UTC

Marcel explicitly resumed the search. At this audit point the durable pause
marker is absent and `allmath-research-orchestrator.service` is active; this
note did not start a duplicate supervisor. Mutable workflow observations are
not promoted here: only their deterministic audits may change a claim label,
and no audited post-stop record supplies the missing fixed-\(\pi\) premise.
The manual resumed branch produced T44--T50,
the exact computation dossier, the corrected fixed-denominator pulse analysis,
and the growing-prime-band quotient reduction above. T51 formalized the
complete third seed band; T52 formalized the exact persistent three-primary
denominator; T53 formalized the complementary quotient/carry recurrence; T54
formalized that the three-primary factor stays fixed or triples at each
adjacent seed and always divides its successor; T55 formalized the exact
generic coarse/fine selector while retaining the fine phase as an explicit
uncontrolled term; T56 formalized the inverse-three residual lift; T57
formalized the generic phase recombination and fixed-depth decimal transport;
T58 formalized the exact Hutton rational bracket and width; and T59 formalized
the exact finite cylinder certificate from a supplied bracket containment;
their independent adversarial review passed. T60 formalized the exact positive
adjacent Hutton increment used by the denominator route and has passed its
focused build, integrated verification gate, and independent adversarial
review. T61 formalized exact survival and multiplicity one for every eligible
upper-half prime in the actual reduced Hutton denominator; its focused build,
and independent audit pass. T62 then formalized their complete squarefree
product as a divisor of the reduced denominator; its focused and independent
audits pass. T64 enlarged that product from the upper-half band to the
one-third band using parity of the Hutton exponents; all eleven declarations,
their registrations, independent checks, and the T64-integrated full
verification gate pass. T65 then closed the next band
\(R/5<p\le R/3\) outside the exact fixed exception 10889, in twenty-six
registered declarations. T63 proved the exact five-primary denominator
exponent, and T66 proved that the reduced Hutton denominator is odd, making
that exponent the complete decimal preperiod. Their focused checks,
independent adversarial audits, registrations, and the T66-integrated full
verification gate pass. T67 then formalized the exact \(1/2+1/3\) shadow:
its decimal preperiod is \(4K+1\), but at that first post-transient scale its
bracket is already wider than \(1/10\). All 29 declarations, registrations,
independent checks, and the T67-integrated full verification gate pass. T68
then formalized a simultaneous Hutton primary family: for every \(a\ge2\),
with \(R_a=3^a7^{a+1}\) and \(K_a=(R_a-3)/4\), its 3- and 7-primary reduced-
denominator multiplicities are exactly \(R_a+a\) and \(R_a+a+1\). All 42
declarations are registered exactly once, and focused, aggregate, direct-
audit, independent-replay, and full-gate checks pass with only the allowlist.
T69 then formalized the fixed-times-sixteen bottleneck in eight registered
theorems.  Independent audit found and resolved one interface overstatement:
the final theorems assume exactly density of the joint times-10/times-16 pi
orbit, not the larger two-field T77 source structure.  The corrected focused
build, direct axiom audit, and full 8,493-job gate pass with only the
allowlist.  This is a conditional equivalence and proves no fixed return.
The
independently audited fixed-prefix law extends
the finite bands to
\(\log\operatorname{rad}(\operatorname{den}H_K)=R+o(R)\) at `proof sketch`
level. The
companion Hutton-prefix audit proves at `proof sketch` level that the
resulting growing prime support still leaves only a logarithmic transferable
orbit and cannot support a coefficient-uniform cancellation estimate. The
independent automaton--Padé audit constructs the exponentially small
all-language form (35), but its exact exponent comparison never crosses a
known lower bound. The Furstenberg--BBP audit identifies the single cross-base
return as an exact equivalent of V1, not a weaker theorem supplied by BBP.
The actual-shift Poisson formula and its power-of-ten aliases were
independently audited, and the naive relative-discrepancy bound was falsified
by exact actual-residue computation. Three further independently audited
attacks close the most plausible denominator variants: common-transient
cross-\(K\) Hutton phases collapse rather than spread; recursive denominator-
safe Machin splitting sharpens resolution without steering; and the
\(1/2+1/3\) shadow's linear dyadic transient ends only after its bracket has
become wider than a full nonempty cylinder; T67 now machine-checks the core
of this third obstruction. The independently audited synchronized-return
attack additionally proves the natural Machin denominator--error product
cannot vanish and isolates the only unclosed possibility as exceptional
signed/shared-prime cancellation.  The signed-depth audit then excludes that
escape whenever one fixed prime survives linearly, but also exhibits a real
one-layer p-adic cancellation showing why no all-depth survival claim follows.
The fixed-multiplier audit proves exact
Wallis and Ramanujan denominator/error incompatibilities; the later
all-depth BBP audit upgrades its even-depth obstruction to the exact exponent
\(4N-v_2(N+1)\).  The integer-Chebyshev audit proves that positive
survivor capacity limits uniform integer-polynomial smallness to the wrong
zero-estimate scale.  Finally, the Iyer--Schleischitz audit proves the
cofactor bound (40e), closing transfer at Iyer's guaranteed (N^{-2}) phase
scale.  The exceptional-alignment audit then confines any surviving
fixed-pi phase to the exponential window (40g), without eliminating it.  The
corrected Padé audit adds the exact aligned instance (40h)--(40j), but its
huge rational-approximation error is not a modulo-one lower bound and its
classical family-wide quality premise remains unproved.  The final
T69-integrated full gate, T57--T69 focused builds, and the complete direct
axiom audit pass. No
complete proof was obtained, so no phone notification was sent
under the agreed breakthrough-only policy.

### Continuation snapshot — 2026-08-13 UTC

Marcel explicitly continued the search.  A resume audit found the research
service stopped and the durable pause marker present.  Before resuming, the
operator-stop script was corrected to use the same
`.research/research-orchestrator.stop` path as the orchestrator; a focused
regression now rejects the former mismatched filename.  The full orchestration
suite passed with 358 tests and two expected failures.  The interrupted P68
ledger item was already abandoned with no live lease, while the stale T164
lease was harvested from its completed record and released.  At this snapshot
the supervised service is active, its directors use
`openai/gpt-5.6-sol`, its medium/low workers and independent review use
`openai/gpt-5.6-terra`, and its bounded jobs retain the configured inactivity
and hard timeouts.  Runtime observations remain untrusted until their normal
deterministic audits complete.

The three new manual branches above have independently audited frozen
artifacts: (40am)--(40ao) reduce the Gauss odd-prime obstruction to the
medium radical and already to its first band; (40ah)--(40ai) reduce the BBP
endpoint to one rational root-of-unity return; and (40aj)--(40al) give the
adjacent-shift matching-plus-anti-concentration criterion.  Every primary and
independent checker passes after the bibliographic, quantifier, and scoped-
filename corrections recorded above.  No new Lean theorem asserts any of
their unproved asymptotics.  Canonical V1 remains a `conjecture`, so the
breakthrough-only phone notification was not sent.

The subsequent first-band audit also passes.  Equations (40ap)--(40at)
replace the selected-prime interval by two exact affine rays from minimal
reflected zeros, remove both endpoint neighborhoods, give equivalent
pointwise core/count formulations and a CRT gcd encoding, and prove by an
abstract countermodel that per-prime sparsity cannot be the missing input.
They do not establish the required cross-characteristic correlation or any
little-o estimate.  The proof-ledger watch `ultrapi-root-20260813` was
registered on `local:pi-digits` before depending on concurrent sibling work;
its initial poll contained no pending events.  Orchestrator observations
remain coordination data only until deterministic acceptance.  No
complete-proof notification was sent.

The corrected scalar-BBP audit also passes.  Equations (40au)--(40ax) give a
local four-pole recurrence, a strictly decreasing rational upper
approximation to (144\pi), exact remaining total variation, and an explicit
derivative-orbit telescope.  They leave the needed accumulated product
return untouched.  The independent audit rejected the original unanchored
separator and verified the replacement (40ay) with (R_0^*=-2) and a true
partial-product gap (1/8).  This is a material audit correction, not a V1
advance.  Both independently written exact replays pass, and no
complete-proof notification was sent.

The stronger scalar p-adic separator also passes independent audit.  It
preserves the complete actual denominator, every derived two-adic bit, both
audited local forcing scales, and any chosen fixed finite asymptotic jet while
retaining nonreturn, eventually after an explicit finite splice.  Its exact
scope is equally important: the depthwise lift does not preserve the true
cross-depth odd-numerator recurrence.  The unresolved selector has therefore
been narrowed to that global coherence; no complete-proof notification was
sent.

The improved adjacent-BBP audit also passes.  Equations (40az)--(40bb)
strictly replace all-pairs collision anti-concentration by noncollapse at
each fixed decimal period on the same subsequence; (40bc) additionally lowers
density-one matching to positive matching mass when the empirical limit is
ergodic, and (40bd) records an exact but noncancellable coefficient identity.
The audit corrected two quantifier/source pins before independently
rederiving every implication.  The two remaining alternatives are now
matching plus every-fixed-period noncollapse, or ergodicity plus
positive-mass matching plus the same noncollapse.  None is proved for
\(\pi\), so no complete-proof notification was sent.

The centered-carry audit now passes on explicitly refrozen inputs.  Equations
(40bi)--(40bl) turn each fixed-period defect into the positive-density problem
for an eventually exact rational BBP carry stream.  Equation (40bm) proves
only the unconditional logarithmic count furnished by the published
irrationality measure, and the separator shows why abstract methods cannot
upgrade it to linear density.  This is a material exact reduction, not V1;
no complete-proof notification was sent.

The subsequent prefix-gcd audit also passes.  Equations (40be)--(40bg) prove
that its below-\(n\) square-free support is exactly the support already
measured by the medium-prime radical, up to the elementary
\(\vartheta(\sqrt n)\) term.  The full gcd adds large-prime and multiplicity
obligations instead of removing the missing estimate.  This exact
`proof sketch` closes the proposed shortcut but proves no little-o bound.

T70 has meanwhile been extended and fully gated.  Fifteen registered
declarations now machine-check the infinite-support topological bridge under
the explicit T77 source premise, including a one-sided absolute-continuity
interface aligned with (40ak).  The source premise and the fixed-pi
noncollapse/matching hypotheses remain unproved, so this is conditional and
no complete-proof notification was sent.

T71 has also passed independent formal audit and the full gate.  Its four
registered declarations machine-check exactly the generic centered-remainder
step in (40bo)--(40bp), including both tie boundaries; they do not prove the
BBP instantiation or a frequency theorem.  The independently replayed
cross-depth arithmetic gives (40bq) but also proves that all denominator
congruences delete the carry.  The independently replayed matching audit gives
(40br)--(40bs), so under ergodicity the proposed matching premise is exactly
the still-missing times-sixteen invariance.  Chen--Ye--Zheng supplies (40bt)
and Mahler supplies (40bu); their topological and movable-multiplier
  quantifiers do not yield (40bl).  These are material boundary results, not
  V1, so no complete-proof notification was sent.

The final odd-LCM report and its independent adversarial audit also pass on
their pinned hashes.  Equations (40bv)--(40bz) show that every new-denominator
valuation is correction-independent, while V1 itself entails unbounded
zero-carry gaps.  The exact maximal-run formula identifies the remaining
worst-gap question with approximation on the restricted grid
\((10^P-1)10^n\); existing irrationality estimates reach only a linear scale,
and even logarithmic gaps would not prove positive density.  This is a
material route correction, not V1, so no complete-proof notification was sent.

T72 now passes the full gate as well.  It machine-checks
\(\mathrm{V1}\iff\mathcal R(\pi)\) in (40ca)--(40cb), using real distance and
an explicit interior color to handle both decimal endpoints.  The companion
carry derivation (40cc)--(40cg) and its exact replay identify one common
rational BBP phase for all colors, but do not prove it visits them.  The
double-audited separators (40ch)--(40ck) further show that exact denominator
data or density-one agreement with the BBP forcing cannot replace the exact
selected-numerator correlation.  These are material exact reductions and
route exclusions, not V1, so no complete-proof notification was sent.

## Bottom line

The desired universal statement is still a `conjecture`; no theorem here
proves that every finite sequence occurs in \(\pi\). The genuine
`machine-checked` breakthrough is the strictly weaker sufficient condition
(9): cutoff \(2\cdot10^k\) and threshold
\(1/(24\cdot10^k)+1/(12\cdot10^{3k})\), replacing T6's
\(128\cdot10^k\) and \(1/(16388\cdot10^k)\). Equations (18)--(24), (26), and
(28) are a
second, unconditional fixed-\(\pi\) advance: every fixed finite frequency
window has an additive Fourier gap tending past any fixed threshold, and
power-of-ten frequency shifts change that gap by at most a boundary term;
moreover, one sixteenth of the natural frequencies have additive gap at least
\(p_\pi(m)/32\) at the least orbit prefix containing every first-occurrence
start.
T29 machine-checks the precise conditional relative saving that an
appearance-ratio bound would provide, but the Fibonacci separator shows that
even a uniform ratio and positive-density relative saving need not improve
factor complexity at all. T30 machine-checks the exact alternative target
\(h_{10}(\pi)=\log10\iff\mathrm{V1}\), without proving the left side. The
T31 and T32 give a further unconditional advance:
\(p_\pi^{\mathrm{rec}}(m)\ge m+1\) and
\(p_\pi^{\mathrm{rec}}(m+1)\ge p_\pi^{\mathrm{rec}}(m)+1\); at every length a
recurrent block has two distinct recurrent one-digit continuations.  These
results still supply neither exponential complexity nor any prescribed word.
The transcendental Kempner-number separator attains equality in both
recurrent-complexity bounds while having irrationality exponent \(2\); T33
machine-checks its exact recurrent shapes and unique right-special factor.
Thus no improvement can come from a generic aperiodicity, transcendence, or
scalar irrationality-measure argument alone.
T34--T56 give a separate exact-rational advance.  A one-sided shadow loses at
most a factor of two in recurrent cell count; sevenfold oversampling removes
that boundary loss abstractly; and the explicit rational Machin sums satisfy
\(M_K\le\pi\), \(\pi-M_K<625^{-K}\), so triple sampling eventually matches
every fixed-length arithmetic floor code of \(\pi\), conditional only on the
published \(\mu(\pi)<8\) proposition.  T37 identifies this floor code exactly
with the canonical symbolic `piCylinderCode` and contiguous `piDigit` block,
including the length-zero and endpoint cases.  All approximation,
representation, and transfer steps are machine-checked and fully gated.  This
still does not show that the resulting rational codes visit any prescribed
value, much less all values.  T38 additionally proves the exact positive
rational recurrence, geometric error coboundary, uniform fixed-frequency
Fourier transfer, and equivalence of Weyl cancellation with the decimal
\(\pi\) orbit.  This closes the tempting claim that the rational recurrence
itself supplies mixing: its remaining cancellation problem is exactly the
fixed-\(\pi\) problem in moving coordinates.
T39 then shows that the eventual symbolic equality preserves the entire
recurrent-value set and count, so the explicit rational code inherits the
full \(m+1\) recurrent lower bound without a factor-two loss.  All-cell
recurrence is equivalent between the rational and symbolic streams, but
neither side is proved; the exponential gap from \(m+1\) to \(10^m\) remains.
T40 exposes the exact local six-plus-six forcing window and proves the
twice-an-odd numerator structure of every positive adjacent pair, without
controlling cancellation among the pairs or the moving archimedean residue.
T41 proves that filling this remaining all-cell recurrence gap is exactly V1,
including leading-zero words and length zero; it does not fill the gap. T42
formalizes the local two-adic foundations, and T44 now proves the global
valuation, odd reduced denominator, and exact reduced-numerator exponent for
the actual forcing. T43 proves that even the exact \(N+4\) numerator profile,
combined with positive summable geometric forcing, can coexist with eventual
avoidance of a decimal cell.  The product-grid separator (11ad)--(11ae)
strengthens that obstruction at `proof sketch` status: even the loose nested
grids, exact moving-modulus recurrence, and one 3-adic cancellation remain
insufficient. T45 then extracts genuinely route-specific information from the
actual signed numerator: every eligible interior prime survives in the
reduced denominator with exponent one. This yields long geometric prime
projections and a fixed-composite-modulus pulse after exact telescoping, but
the CRT mesh separator proves that the prime projection alone can preserve an
avoiding seed. The unproved task is now the full actual cofactor/initial phase,
not merely a valuation or local residue.
T46 makes the telescoping sentence literal and machine-checked, including its
nonnegativity and exponentially decaying pulse bound. It supplies no
cancellation theorem for the resulting logarithmic-length orbit.
T47 closes the prime bookkeeping completely: endpoint slots and the
exceptional base 239 join T45's interior slots, so every prime above 12
survives in the reduced denominator of some actual forcing. This strengthens
the exact arithmetic input but does not constrain the complementary CRT phase
of the selected Machin seed.
T48 then validates the stronger full-seed input behind the fixed-modulus
analysis: almost every prime in the upper half of the seed's linear-
denominator range occurs exactly once after reduction. The resulting large
cofactor can support a same-denominator separator, but that separator varies
the cofactor residue and therefore still says nothing about the one numerator
selected by Machin's formula.
T49 closes the missing class-5 endpoint-to-endpoint pulse with an exact
length-(2N+2) valuation window. T50 then expands seed survival from the upper
half to the full range (d/5<p\le d), removes the endpoint exception, and
proves exact denominator multiplicity one outside seven fixed primes. T51
adds the third band (d/7<p\le d/5), including the genuine coefficient
exceptions and a machine-checked elimination of its 7p endpoint. A
general-band `proof sketch` goes further: all but (o(j)) logarithmic mass of
the non-base denominator radical survives. But exact quotient reciprocity
shows why this still stops: after those components are fixed, the remaining
quotient is exactly the archimedean grid-cell index—and its carries are the
decimal digits being sought. The route has nearly exhausted denominator
information without acquiring control of the selected numerator's order.
T52 turns the formerly experimental three-primary persistence into an exact
theorem: if \(3^a\le12j+3<3^{a+1}\), then the seed valuation is \(1-a\)
and its reduced denominator contains exactly \(3^{a-1}\). T53 then
machine-checks that the unknown complementary quotient generates the digits
through the coarse carry in (11au)--(11av). These are genuine arithmetic
advances, but they prove no phase distribution.
T54 closes the corresponding adjacent-index bookkeeping: the exponent can
increase by at most one, so \(3^{a-1}\) stays fixed or triples and forms a
divisibility chain. This makes the three-primary resonant frequencies close
exactly across indices. It still gives no contraction: at a tripling threshold
the full new grid is three aliases, while the selected actual orbit remains in
only the inherited alias, where the two cancellable frequency classes survive.
T55 machine-checks the generic selector equation itself: after reducing the
full numerator, the coarse state is \(AF^{-1}-rF^{-1}\) modulo the
three-primary factor. Thus the new formal theorem confirms the precise reason
the fixed-depth shell is not a digit theorem—the complementary fine phase is
part of the selector, not an error term that can be discarded.
T56 machine-checks the generic algebra of the next layer: a ternary selector
lift satisfies
\(3R'=R+F(u-v)\), hence \(R'=3^{-1}R\pmod F\). The compatibility is therefore
an invertible phase permutation, not decay. This closes the algebraic gap in
the balanced-depth `proof sketch` without machine-checking its Machin-specific
instantiation or supplying the missing Archimedean estimate.
T57 machine-checks the complementary generic coordinate algebra: (11bk)
reconstructs the rational phase from its leading and residual parts, while
(11bl) transports the residual by multiplication by ten modulo the fixed
fine modulus. It neither supplies the actual Machin carry hypotheses nor
makes that transport cancellative or equidistributed.
T58 supplies an independent exact rational advance: Hutton's \(3/7\) lower
and upper shadows enclose \(\pi\) with the exact width (11bo). This improves
the computable interval, but (11bp) and the affine-coupling audit show why a
second formula is not a second random residue. No theorem makes the usable
linear-length prefix of that rational orbit visit a prescribed cylinder.
T59 turns a bracket wholly inside one cylinder into the exact canonical block
value (11bq), but the Hutton period audit makes the quantifier barrier sharp:
the provable period is exponential while the transferable prefix is linear,
and full-cycle invariants survive rotations that move every first occurrence.
T60 now machine-checks the exact positive neighboring increment (11br1), so
the elementary identity behind that period analysis is no longer merely
informal. T61 goes farther: every eligible upper-half prime survives exactly
once in the actual reduced denominator, giving the first machine-checked
valuation layer of the Hutton route. The prime product has logarithm
\((4K+3)/2+o(K)\) at `proof sketch` level; T62 machine-checks its joint finite
divisibility, and T64 widens the exact surviving band to
\((4K+3)/3<p\le4K+3\), whose product has logarithm
\(2(4K+3)/3+o(K)\) at `proof sketch` asymptotic level. T65 adds
\((4K+3)/5<p\le(4K+3)/3\) outside 10889, while the independently audited
general local law proves
\(\log\operatorname{rad}(\operatorname{den}H_K)=4K+3+o(K)\). T63 and T66
jointly prove that \(\lfloor\log_5(4K+3)\rfloor\) is the complete decimal
preperiod. The transferable orbit still has only
\(1.908485\ldots K+O(\log K)\) points. Existing short exponential-sum
bounds do not reach this logarithmic regime, and exact neighboring examples
rule out any estimate uniform in the numerator. T61 therefore supplies real
arithmetic structure without localizing a hit. The global CRT audit goes one
step further by recombining all selected local residues into (11br6)--(11br7),
where the complementary denominator cancels from one actual additive-CRT
coordinate. The mandatory decimal transient destroys the resulting 21-grid
localization, however, and the other CRT coordinate stays correlated. This is
a sharper description of the selected numerator, not a digit hit.
The common-transient cross-\(K\) audit makes that correlation exact:
throughout a linear transferable window the full phases have mean modulus
\(1-o(1)\), while the complementary coordinate conjugates the selected
coordinate back to the fixed-\(\pi\) phase. Recursive denominator-safe Machin
splitting can make the bracket arbitrarily narrow at fixed Taylor depth, but
only resolves whichever cell \(\pi\) already occupies. Conversely, the
\(1/2+1/3\) shadow has an exact linear dyadic preperiod that outlasts its
entire cylinder-transfer horizon; T67 machine-checks that bracket, preperiod,
and strict width comparison. The first two independently audited `proof
sketch` results and the third `machine-checked` obstruction remove more
indices, more approximants, and faster convergence as stand-alone ways around
the selected-phase problem.
T68 adds an exact infinite simultaneous-primary family: at
\(R_a=3^a7^{a+1}=4K_a+3\), the reduced Hutton denominator has 3- and
7-adic exponents \(R_a+a\) and \(R_a+a+1\).  This is much stronger than
isolated local survival, but the independently audited leading-unit model
shows that low-primary congruences can remain nearly stationary; restoring
the complementary coordinate again reconstructs the unknown fixed-\(\pi\)
phase.  The synchronized-return audit makes the denominator target exact and
proves \(D_R(\pi-L_R)\ge32/35\) for the natural positive Machin truncations,
with exponential divergence on private-prime subsequences.  Separately,
Wallis and Ramanujan shadows have exact denominator/error mismatches under a
\(10^N-c\) divisibility anchor, and every BBP depth has the exact unbounded
two-primary exponent \(4N-v_2(N+1)\).  These independently checked results
close the named exact-anchor constructions; they do not control a small
nonzero residue and therefore do not prove the fixed return or V1.
Allowing signed and unequal Taylor depths does create genuine real
cancellation, but the fixed-prime synchronization squeeze (40c) rules out
every family with one linearly surviving prime.  The exact cancellation at
exponent 2059 shows that arbitrary schedules cannot be covered by merely
asserting endpoint survival.  Independently, the decimal-0/1 denominator
route has the right Iyer phase scale but the wrong synchronized geometry:
(40e) forces its cofactor to grow faster than \(N^2\), closing precisely the
guaranteed \(N^{-2}\) transfer and leaving only exceptionally smaller
fixed-\(\pi\) phases.  Equations (40f)--(40g) force any such survivor into a
narrow exponential size band and exclude every fixed denominator, but do not
prove that the survivor set is empty.
The fixed-depth leading-unit shell (11be)--(11bf) and actual selector (11bg)
then add the first joint three-primary coarse/fine information. They identify
one residue class modulo every fixed \(3^k\) and shrink the local candidate
grid by \(3^k\), but only after the actual fine residue is supplied. At fixed
\(k\) this is a constant-factor saving; at \(k=a_j-1\) it is the original
actual numerator encoded as a singleton. No proved multiscale estimate bridges
those extremes. A CRT attempt to import Maynard's missing-digit decay exposes
a genuine non-base factor but also an ultra-major alias with normalized
coefficient tending to one, so it does not close the signed reconstruction.
The cross-index `proof sketch` sharpens the obstruction: compatible candidates
form a gcd subgroup, and the exact seed has a persistent 3-primary subgroup
of order \(\Theta(j)\). Its translated forced orbits can realize any
prescribed fixed finite itinerary while preserving the current frozen
components. Freezing that 3-primary component removes this particular
symmetry but merely returns to the complete-numerator phase problem. The
separate missing-word audit likewise shows that finite-state avoidance gives
only a tiny entropy deficit, not the automatic/Mahler structure or exceptional
rational approximation needed by current transcendence tools. Finally, the
subexponential candidate count does not combine with that entropy deficit by
a first-moment argument: the shifted-grid boundary term is exponential, and
an exact reduced \(D=81\) carry model realizes the resonance for arbitrarily
long avoiding itineraries. Equations (11aw)--(11az) now identify that missing
estimate exactly: a forbidden-word transfer-matrix Fourier sum weighted by
the one actual phase \(e(\ell D_jx_j)\). Local prime characters recombine to
that phase, and power-of-ten aliases retain their Perron leading term. The
exact experiment (11bb) shows a signed resonance of
\(0.949247\ldots\) against a zero mode of only \(0.050753\ldots\), so the
naive pointwise relative bound is false. The theorem-sized ASR bound (11ba)
would force a contradiction, but it remains a `conjecture`. What is missing
is signed cancellation for the one actual Machin shift, not another
candidate-count or absolute-Fourier estimate.
The exact \(1/81\) and Fibonacci models show that T19 resonance, T25 transport,
T28 positive-density cancellation, and even an optimal appearance ratio need
not produce a common useful frequency. BBP reweighting reduces the missing
×16 invariance to the explicit rational recurrence (11c). Equations
(11f)--(11n) prove that its truncations retain exact dyadic and exponentially
large odd denominators and have exceptionally simple selected-prime residues,
but they supply no bound on the moving archimedean numerator residue. The
positive moment separators show that dense critical translations, the exact
leading BBP tail scale, complete monotonicity, and even non-Gosper forcing can
coexist with a finite omega-limit set. The explicit separator
(25) independently shows why fixed-window additive divergence does not imply
digit coverage. The refined Furstenberg bridge makes the cross-base wall
exact: \(16\pi\in K_{10}(\pi)\), \(\times16\)-invariance of the decimal orbit
closure, and V1 are equivalent. T69 machine-checks this reduction under the
minimal explicit joint-orbit density premise and independently passes the
full gate; it does not prove the return. The BBP partial sums transfer that
same unknown return but do not prove it.  T70 now also machine-checks the
weaker infinite-support endpoint under T77's explicit Furstenberg source
premise, with either ergodic nonsingularity or one-sided absolute continuity;
it proves none of those fixed-pi inputs. Finally, the automaton-wide product
(34) does make every forbidden language produce an exponentially small
nonzero integer-polynomial value, yet the exact exponent comparison (36)
loses for every batch size and multiplicity. The integer-Chebyshev refinement
cannot repair the exponent: positive survivor capacity permits only
exponential-in-degree uniform smallness, while the known logarithm measure
pays polynomially higher degree and height costs. These are genuine new
auxiliary forms, not a contradiction.

The latest audited reductions make three remaining endpoints unusually
explicit.  On the Gauss side, (40am)--(40ao) replace the moving selector by
the medium-prime radical of the single integer \(A_n\), but even its first
band \(n/2<p<n\) has no pointwise little-o proof.  The follow-up
(40ap)--(40at) now identifies that band with two affine rays, removes all
endpoint mass, and rules out closing it from per-prime zero counts,
reflection, and spacing alone; a cross-characteristic correlation estimate
is still absent.  The prefix-gcd identity (40be)--(40bf) proves that the
natural below-\(n\) square-free shortcut is exactly equivalent to that same
medium-prime target, while the full gcd only adds large-prime and
multiplicity noise.  On the BBP side,
(40ah)--(40ai) show that one rational root-of-unity character returning to
one is already equivalent to V1 at `proof sketch` level, while the available
linear-recurrence theorem disperses it only away from zero.  The scalar
elimination (40au)--(40ax) proves strong one-sided local control but telescopes
back to the same derivative orbit; the anchored separator (40ay) rules out
deducing the accumulated return from that local control alone.  The stronger
separator (40bh) additionally preserves the full actual denominator, all
derived two-adic bits, and every prescribed finite local asymptotic jet; only
the true cross-depth odd-numerator coherence remains outside its scope.
Independently,
(40aj)--(40al) show that bounded-congestion matching plus anti-concentration
of the adjacent coefficient rows would suffice without ergodicity or full
Fourier equality.  The strict refinement (40az)--(40bd) removes global
anti-concentration: matching plus positive mean defect at every fixed decimal
period already forces infinite common support and hence full support.  Under
ergodicity, even a fixed positive matched proportion suffices.  Neither
version's matching or fixed-period defect has been established.  The exact
carry form (40bi)--(40bl) shows what the latter now means arithmetically:
  linear density of nonzero centered carries in an eventually rational
  sevenfold-BBP stream for every fixed repunit multiplier.  The published
  irrationality exponent supplies only the sharp generic \(\Omega(\log N)\)
  lower bound (40bm), not the required \(\Omega(N)\).  The new exact
  recurrence (40bn)--(40bq), now with its generic one-step algebra
  `machine-checked` in T71, shows why local denominator information stalls:
  every two-adic and odd-LCM congruence is independent of the carry, while
  selecting the centered Archimedean lift remains uncontrolled.  The exact
  endpoint (40br)--(40bs) also shows that the proposed matching condition is
  not a weaker ergodic substitute for times-sixteen invariance.  Finally,
  (40bt) proves infinitely many fixed-amplitude excursions for every repunit
  multiple of pi, but no frequency, and (40bu) supplies every word only after
  a word-length-dependent integer multiplication.  Equations (40bv)--(40bz)
  further show that new odd-LCM primes are locally carry-blind and that no
  bounded-gap theorem can be the missing bridge: V1 requires arbitrarily long
  zero-carry runs, while the known irrationality exponent bounds their length
  only linearly.

T72 now gives the endpoint-safe `machine-checked` final target
(40ca)--(40cb): every decimal word occurs exactly when the real pi orbit
returns arbitrarily late and arbitrarily accurately to every repunit-grid
color.  The common-state formulas (40cc)--(40cf) express those colors through
one exact rational BBP phase and show why every fixed congruence is eventually
absorbed by the denominator.  The sparse stream (40cg) proves that uncolored
long zero blocks are insufficient.  Finally, the double-audited constructions
(40ch)--(40ck) show that exponentially close forcing can retain exact
denominator/two-adic data pointwise, or exact BBP forcing away from only
\(O(\log N)\) coherent resets, while all carries remain zero.  Those two
packages are distinct, and neither retains the exact selected BBP numerator
at every depth.  Thus the surviving arithmetic input is precisely that
selected cross-depth numerator correlation, not another height, valuation,
finite-asymptotic, fixed-difference, or density-one approximation estimate.

The latest exact reductions make that correlation more concrete.
(40ds)--(40dv) give every three-primary denominator epoch and exhibit
infinitely many complete shrinking grids in the isolated residual coordinate;
T73 machine-checks their universal period and residue-class arithmetic.
T74 then machine-checks the one-term folds behind the summed decimation
(40ec)--(40ef), and (40eg)--(40ei) identify the full period as one selected
Fourier coefficient of the synchronized complement.  Orthogonality gives no
bound for that coefficient: (40ep)--(40es) make the obstruction precise by
showing that ordinary block mixing leaves one ninth of the selected energy
and that one differencing step retains both hard dyadic precision and
exponential high-prime modulus.  The independently reconstructed full-phase
`experiment` (40ej), extended by (40eu)--(40ev), nevertheless finds
random-scale gaps on fourteen endpoint rows through \(5{,}491{,}685\) points.
Its directly sufficient `conjecture` (40ek) is now accompanied by the
correct all-color T72 argument (40em), machine-checked abstractly in T75 as
(40en); a single zero return is not enough.  The natural ninefold gap
recursion is falsified on every exact transition and by the primary-compatible
subwindow audit (40et).  No gap or all-mode Fourier decay theorem is known.
Independently,
(40dw)--(40ea) replace the dyadic forcing by exactly 28 odd-linear
selected-root coordinates and show that existing all-root or all-modulus
theorems do not apply.  The fixed-seven and modulo-three obstructions refute a
simultaneous-prime route, while (40eb) refutes the inference from even
excellent marginal forcing coverage to state hitting.  All branches passed
their stated disjoint checks; none is a full-phase return.

What remains is sharply isolated but still hard: establish (9)'s
all-frequency relative cancellation premise, maximal factor entropy, the
four-pole accumulated return (40aw), the Gauss cross-characteristic two-ray
estimate (40ap)--(40ar), or preferably the strictly weaker BBP alternatives
(40ak)+(40bl) or ergodicity+(40bc)+(40bl), by proving a pi-specific
cross-depth odd-numerator mechanism that upgrades logarithmic to positive
mean carry density while allowing the arbitrarily long zero-carry blocks that
V1 itself requires.  The exact, non-frequency formulation is now (40ca) or
(40cc): prove every colored shrinking return for the selected phase in
(40cd)--(40ce).  The newest arithmetic formulation is to prove joint
cancellation or direct target hitting for (40dv), equivalently prove
\(G_e^\pm\to0\) in (40ek), every fixed-mode decay behind it, or the analogous
statement for the actual 28-coordinate product in (40dx), with its generated
base-ten state.  This may follow from density of that exact rational coding
recurrence or from an equally strong direct mechanism for the single fixed
orbit of \(\pi\); none is currently proved.
