# Cross-index complementary-quotient attack

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL; none
is invented here.  
Route: the actual reduced-numerator split in
[`actual_numerator_phase_attack.md`](actual_numerator_phase_attack.md), the
general prime-band reduction in
[`general_seed_band_attack.md`](general_seed_band_attack.md), and T38/T46.

## Outcome and exact status

No complete proof that every finite decimal word occurs in \(\pi\) was
obtained. The canonical target remains a `conjecture`.

There is a material exact obstruction to the proposed cross-index repair of
the \(\exp(o(j))\) complementary-state bound.  Cross-index consistency is
controlled by a **gcd of the complementary moduli**, not by their individual
sizes.  For the exact Machin seeds this gcd has a persistent 3-primary part
of order \(\Theta(j)\).  Consequently, after any sufficiently late start
\(J\), there are at least \(\Theta(J)\) globally recurrence-consistent phase
translations which preserve every currently frozen base/high-prime
component at every later index.

More sharply, for every prescribed finite digit itinerary \(W\), one can
take \(J\) sufficiently large and choose one of these translations so that
the translated forced orbit follows \(W\), while retaining the exact same
forcing and all the frozen local components from \(J\) onward.  This is a
`proof sketch`, with every algebraic step displayed below.  It is a separator
for the current premises, not a counterexample involving the actual Machin
numerator and not a statement that V1 is false.

The positive structural result is an exact candidate-chain classification.
It identifies what a successful cross-index lemma would have to control: the
one actual initial quotient class, not merely overlap consistency or the
subexponential number of possible classes.

## 1. Normalized target and quantifiers

The canonical V1 statement is

\[
 \forall L\in\mathbb N\;\forall w\in\{0,\ldots,9\}^{L}\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+L-1}(\pi))=w.                 \tag{1}
\]

Digits are after the decimal point, leading zeroes are allowed, and \(L=0\)
is vacuous.  The target is finite contiguous occurrence, not a subsequence
claim and not normality.

## 2. Exact classification of cross-index alternatives

Let

\[
 x_j=\{y_j\}={b_j\over Q_j},\qquad
 y_j=10^jM_{3j},\qquad 0\le b_j<Q_j,                 \tag{2}
\]

with \(b_j/Q_j\) reduced. T38 gives the exact forced recurrence

\[
 x_{j+1}=\{10x_j+\Delta_j\}.                         \tag{3}
\]

For this separator, take exactly the factor split from equation (16) of the
actual-numerator report: let \(F_j\) contain the complete 5- and 239-primary
components and the certified primes \(B_j<p\le d_j\), and put

\[
 Q_j=F_jD_j,\qquad (F_j,D_j)=1.                      \tag{4}
\]

For all sufficiently large \(j\), one has \(B_j>3\), so this specific
\(F_j\) is prime to 3. Also \((D_j,10)=1\): the seed denominator is odd and
the complete 5-primary part has been put into \(F_j\). Knowing the frozen
local numerator data means knowing \(b_j\bmod F_j\). An arbitrarily enlarged
factor which also includes the complete 3-primary component is a different
split and is addressed explicitly in Section 6.

Consider an alternative phase \(\widetilde x_j=\widetilde b_j/Q_j\) on the
same denominator grid with
\(\widetilde b_j\equiv b_j\pmod {F_j}\). Reduction of this displayed
fraction is not required; cancellation in \(D_j\) does not alter a frozen
component. Its difference from the actual phase belongs to the subgroup

\[
 \theta_j:=\widetilde x_j-x_j
       \in {1\over D_j}\mathbb Z/\mathbb Z.          \tag{5}
\]

The alternative obeys the **same** forcing (3) exactly when

\[
 \theta_{j+1}=10\theta_j\pmod1.                     \tag{6}
\]

Therefore, on an interval \(J\le j\le K\), every consistent alternative is
of the form

\[
 \theta_j=10^{j-J}\theta_J,\qquad
 \theta_J\in {1\over g_{J,K}}\mathbb Z/\mathbb Z,
 \quad g_{J,K}=\gcd(D_J,D_{J+1},\ldots,D_K).         \tag{7}
\]

Indeed, multiplication by 10 preserves the reduced denominator of a
rational whose denominator is coprime to 10. Hence a reduced
\(\theta_J=a/q\) satisfies (5) at every index exactly when \(q\mid D_j\)
for every \(j\), which is equivalent to \(q\mid g_{J,K}\). This proves (7)
and shows why the pointwise estimate \(D_j=\exp(o(j))\) is not the right
cross-index statistic.

## 3. Exact persistent 3-primary denominator

Write

\[
 d=12j+3,\qquad a_j=\max\{a:3^a\le d\}.             \tag{8}
\]

The exact seed expansion from the companion reports is

\[
 {y_j\over10^j}=
 \sum_{\substack{1\le u\le d\\u\text{ odd}}}
 {4\chi_4(u)(4\cdot239^u-5^u)\over u5^u239^u}
 -{4\over(d+2)239^{d+2}}.                          \tag{9}
\]

For every odd \(u\), since \(239\equiv5\pmod9\),

\[
 4\cdot239^u-5^u\equiv3\cdot5^u\pmod9,
 \qquad v_3(4\cdot239^u-5^u)=1.                   \tag{10}
\]

Put \(h=3^{a_j}\). Because \(h\le d<3h\), the only odd \(u\le d\) with
\(v_3(u)=a_j\) is \(u=h\): another such \(u\) would be \(kh\) for an odd
integer \(1<k<3\). Thus the \(u=h\) summand in (9) has valuation
\(1-a_j\), every other common summand has valuation at least \(2-a_j\), and
the endpoint is 3-integral because \(d+2=12j+5\not\equiv0\pmod3\). The
least-valuation term is unique, so

\[
 \boxed{v_3(y_j)=1-a_j\qquad(j\ge1).}               \tag{11}
\]

This is an elementary unconditional calculation, retained as a
`proof sketch` because it has not been added to the verified Lean track. In
particular the actual reduced denominator has exact 3-primary part
\(3^{a_j-1}\).

For the specific high-prime factor just fixed, \(F_j\) is prime to 3 once
\(j\) is sufficiently large, so

\[
 3^{a_j-1}\mid D_j.                                 \tag{12}
\]

The exponents \(a_j\) are nondecreasing. For every sufficiently large start
\(J\), therefore,

\[
 q_J:=3^{a_J-1}\mid D_j\quad(j\ge J).               \tag{13}
\]

Moreover \(d/3<h\le d\), hence

\[
 {12J+3\over9}<q_J\le{12J+3\over3}.                \tag{14}
\]

So the persistent tail ambiguity is not merely nontrivial; it grows
linearly with the start index.

## 4. Recurrence-consistent translations preserve all frozen components

For every \(t\in\mathbb Z/q_J\mathbb Z\), define

\[
 \widetilde x_j^{(t)}=
 \left\{x_j+{10^{j-J}t\over q_J}\right\},
 \qquad j\ge J.                                    \tag{15}
\]

Equation (3) immediately gives

\[
 \widetilde x_{j+1}^{(t)}
   =\{10\widetilde x_j^{(t)}+\Delta_j\}.            \tag{16}
\]

On the \(Q_j\)-grid, its numerator is

\[
 \widetilde b_j^{(t)}\equiv
 b_j+10^{j-J}t{Q_j\over q_J}\pmod {Q_j}.           \tag{17}
\]

But \(Q_j/q_J=F_j(D_j/q_J)\), so

\[
 \widetilde b_j^{(t)}\equiv b_j\pmod {F_j}         \tag{18}
\]

at **every** later index. In the quotient coordinates of the companion
report, (17) changes only the coarse quotient by
\(10^{j-J}tD_j/q_J\pmod {D_j}\); the fine remainder is identical.

Thus the exact recurrence does not select the actual complementary quotient.
It leaves at least the \(q_J\)-element family (15), even after imposing all
currently certified local data simultaneously for the entire tail.

## 5. Arbitrary finite itinerary separator

The preceding ambiguity has direct archimedean content. The phases

\[
 \left\{x_J+{t\over q_J}\right\},qquad0\le t<q_J, \tag{19}
\]

form a shifted uniform grid of mesh \(1/q_J\). Put
\(R_{J,s}\) equal to the real cast of T46's
`sampledMachinForcingAccumulationRat J s`. An elementary induction on the
same affine recurrence (16) gives the alternative-phase iterate below; T46
then identifies this exact accumulation with its error telescope and bounds
it. Thus, for every \(s\ge0\),

\[
 \widetilde x_{J+s}^{(t)}
   =\{10^s\widetilde x_J^{(t)}+R_{J,s}\},
 \qquad0\le R_{J,s}<10^s\rho^J,
 \quad\rho={10\over625^3}.                         \tag{20}
\]

Fix an arbitrary decimal word \(W\) of length \(T\), and let \(k\) be its
base-10 value, including leading zeroes. Take the midpoint

\[
 \alpha_W={k+1/2\over10^T}                         \tag{21}
\]

of its decimal cylinder. At time \(0\le s<T\), the point
\(\{10^s\alpha_W\}\) is at distance at least
\(1/(2\cdot10^{T-s})\) from the boundary of its required one-digit cell.

Choose \(J\) beyond the point where \(B_J>3\), and so large that

\[
 q_J>2\cdot10^T,
 \qquad 10^T\rho^J<1/4.                            \tag{22}
\]

The grid (19) contains a point within \(1/(2q_J)<1/(4\cdot10^T)\) of
\(\alpha_W\), using distance on the circle. Multiplication by \(10^s\)
increases this circular distance by at most \(10^s\), so the first error is
less than \(1/(4\cdot10^{T-s})\). The correction in (20) is the exact
accumulated forcing, not the actual-orbit correction reused without proof;
T46 proves both \(R_{J,s}\ge0\) and
\(R_{J,s}<10^s\rho^J<1/(4\cdot10^{T-s})\).

The boundary set for the next decimal digit is
\(\{0,1/10,\ldots,9/10\}\) on the circle. The midpoint
\(\{10^s\alpha_W\}\) is at circular distance at least
\(1/(2\cdot10^{T-s})\) from this set. Thus the sum of the shifted initial
error and the positive forcing correction is strictly smaller than the
boundary guard. This remains valid if the perturbed representative wraps
through 0 or 1, because the estimate is on the circle and 0 is included in
the boundary set. Consequently the first \(T\) digit outputs of that
translated forced orbit are exactly \(W\).

This proves the separator:

> For every finite word \(W\), at every sufficiently large scale there is a
> recurrence-consistent complementary-quotient choice which follows \(W\)
> while preserving all currently frozen local components at every later
> index.

Taking \(W=55\ldots5\) gives an arbitrarily long cell-avoiding pulse. Taking
\(W\) to contain a finite de Bruijn word gives a pulse covering every word
of a prescribed shorter length. Hence the same local/cross-index premises
are compatible with opposite finite distribution behavior. They do not
identify the behavior of the actual quotient.

## 6. Why \(\exp(o(j))\) does not suffice

The failure is now precise rather than heuristic.

1. A pointwise upper bound on the number of candidates is not a mixing or
   occupancy bound. Even one consistently selected candidate can encode a
   non-disjunctive sequence.
2. Cross-index consistency replaces \(D_j\) by the gcd in (7). The exact
   seeds retain the growing divisor (13), so the overlap constraints do not
   collapse the candidate family.
3. The remaining family is archimedean: by (19)--(22), its members occupy
   every prescribed fixed-depth cylinder once \(J\) is large. An averaging,
   pigeonhole, or CRT argument can therefore prove only that **some**
   alternative has a desired itinerary, not that the actual one does.
4. Supplying the exact earlier phase would select the actual member, but
   propagating that selection is exactly the original coarse-carry/digit
   computation. It does not create a distribution estimate.

This does not rule out all future uses of the Machin formula. Enlarging the
specific factor (4) by the full 3-primary denominator and numerator component
removes this particular symmetry; the present claim must not be read as
applying to such an enlarged \(F_j\). Adding every residual prime component
eventually computes the complete
numerator. What remains missing is still a theorem about the archimedean
location or cancellation of that one complete numerator, not another count
of its possible CRT lifts.

## 7. Reproducible exact checks (`experiment`)

[`cross_index_quotient_check.py`](cross_index_quotient_check.py) imports the
exact `Fraction` seed constructor from the preceding experiment. It does not
evaluate \(\pi\) or read a digit table. SHA-256:
`9dbc89af57b4f157d8d0d930882a643cc9cec4c2ca2a9e636f58b48302335e9a`.

Commands:

```bash
python3 -m py_compile work/ultrapi-resume/cross_index_quotient_check.py
python3 work/ultrapi-resume/cross_index_quotient_check.py --max-j 80
```

Retained output:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
j_range=1..80
three_adic_valuation_checks=80
tail_divisibility_checks=3240
cross_index_recurrence_checks=1620
controlled_residue_checks=1620
translation_start=60 persistent_modulus=81
terminal_persistent_modulus=243
full_cylinder_depths=[(1, 10), (2, 100)]
full_forced_itinerary_depths=[(1, 10), (2, 100)]
all exact checks passed
```

The run checks (11) at every seed, all tail divisibilities (13) in the finite
range, every persistent translation over the final twenty transitions, and
literal equality of the controlled numerator residues. The cylinder rows
check both the static shifted grid and the genuinely forced alternative
orbits at depths one and two. Finite success is not a proof of (1) or of any
untested asymptotic.

## 8. Sharp remaining lemma

A useful next theorem must distinguish the actual coarse quotient from the
family (15). Sufficient forms remain:

- a discrepancy or exponential-sum estimate for the one actual quotient
  orbit, with a strict natural-scale bound such as T19;
- a genuinely archimedean estimate locating the actual quotient in
  prescribed cylinders infinitely often; or
- new exact numerator information which is then converted into distribution,
  rather than merely reducing the number of CRT candidates.

A cross-index lemma that only asserts recurrence consistency, overlapping
blocks, subexponential state count, or persistence of more local denominator
components is separated by (15)--(22).

## Bottom line

The cross-index route does not close the complementary phase. Its consistent
candidate space is exactly a gcd subgroup, and the actual Machin denominators
carry a growing persistent 3-primary subgroup. That subgroup can realize any
prescribed finite digit itinerary while preserving the current local data and
the exact forcing on the whole later tail. This is meaningful obstruction
work, but it is not a proof of V1, a `candidate resolution`, or a
`verified resolution`.
