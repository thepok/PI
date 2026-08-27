# Missing-word/transcendence attack

Audit date: **2026-08-12 UTC**  
Status: `literature-checked` applicability audit plus local `proof sketch`  
Target source: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target source SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

This route does **not** presently prove that every finite decimal word occurs
in \(\pi\).  Assuming that a word \(w\) is absent does place the decimal digit
stream of \(\pi\) in an explicit finite-state subshift with entropy strictly
below \(\log 10\).  That is the strongest unconditional symbolic consequence.
It does not make the one chosen digit stream automatic, Mahler, D-finite, or
periodic, and it does not by itself produce rational or algebraic
approximations good enough to contradict any known \(\pi\)-specific
transcendence measure.

The audit isolates a precise missing theorem.  A proof by this route would need
a genuinely \(\pi\)-specific assertion of the form

\[
  \pi\notin K_w
\]

for every forbidden-word survivor set \(K_w\), or a quantitative consequence
of \(\pi\in K_w\) that violates a known lower bound for a polynomial or linear
form at \(\pi\).  None of the inspected transcendence, Mahler, G-function,
Fourier, or Diophantine-approximation results supplies that implication.

The target remains a `conjecture`; this file contains no candidate resolution.

## 1. Exact reduction under an omitted word

Fix a decimal word \(w=w_0\cdots w_{m-1}\) of length \(m\geq1\).  Build the
usual prefix (KMP) automaton whose state is the longest suffix of the digits
already read that is a prefix of \(w\), and delete the transition that reaches
the complete word.  Let \(A_w\) be its adjacency matrix and let
\(\lambda_w=\rho(A_w)\).  Then the numbers whose nonterminating decimal
expansions avoid \(w\) form the graph-directed survivor set

\[
  K_w=\{x\in[0,1): T_{10}^n x\notin I_w\text{ for every }n\geq0\},
  \qquad T_{10}x=\{10x\},
\]

where \(I_w=[a/10^m,(a+1)/10^m)\) is the cylinder coded by \(w\), with the
usual harmless endpoint convention.  If \(w\) is absent from \(\pi\), then
\(\{\pi\}\in K_w\).

If \(a_n(w)\) counts length-\(n\) decimal strings avoiding \(w\), finite-state
Perron--Frobenius theory gives

\[
  a_n(w)=O_w(n^{m-1}\lambda_w^n),\qquad
  h_{\rm top}(K_w)=\log\lambda_w,
\]

and the equal-contraction graph-directed dimension formula gives

\[
  \dim_H K_w={\log\lambda_w\over\log10}<1. \tag{1}
\]

The elementary bounds

\[
  9\leq\lambda_w\leq(10^m-1)^{1/m}<10 \tag{2}
\]

are already enough for the applicability audit.  The lower bound follows by
discarding from the alphabet one digit occurring in \(w\); the upper bound
comes from splitting a survivor into aligned blocks of length \(m\), each of
which has at most \(10^m-1\) choices.  Thus omission creates a positive but
very small entropy gap

\[
  \delta_w=\log(10/\lambda_w)>0. \tag{3}
\]

For a single long forbidden word this gap is exponentially tiny in \(m\).
For example, the Guibas--Odlyzko correlation equation recorded in
[`ultrapi.md`](../../ultrapi.md) implies that the extremal values have scale

\[
  \delta_w\asymp10^{-m}.
\]

Numerically, for the unbordered and maximally bordered correlation
polynomials, respectively, the gaps \(\log(10/\lambda_w)\) are:

| \(m\) | unbordered | maximally bordered |
|---:|---:|---:|
| 1 | \(1.0536\cdot10^{-1}\) | \(1.0536\cdot10^{-1}\) |
| 2 | \(1.0153\cdot10^{-2}\) | \(9.2096\cdot10^{-3}\) |
| 4 | \(1.0004\cdot10^{-4}\) | \(9.0036\cdot10^{-5}\) |
| 8 | \(1.0000\cdot10^{-8}\) | \(9.0000\cdot10^{-9}\) |

These values are an `experiment`, computed from the exact correlation
equation; they illustrate scale only and are not used as proof evidence.

The reduction (1)--(3) is rigorous, but it is merely a reformulation of the
missing-word hypothesis.  It does not distinguish \(\pi\) from any other path
through the automaton.

## 2. Why the finite automaton is not a Mahler equation

There are two different automata here:

1. the finite graph accepting **all** strings that avoid \(w\); and
2. an automaton that, given the base-10 digits of an index \(n\), outputs the
   \(n\)-th digit of one **particular** infinite sequence.

Word avoidance supplies the first object only.  Automatic-number and Mahler
theorems require the second, equivalently a finite decimation kernel or a
functional equation relating values at \(z,z^{10},z^{10^2},\ldots\).  A path
in a finite graph can be arbitrarily complicated.  Indeed, concatenating all
finite words over any nine-digit subalphabet produces a path avoiding every
word containing the deleted digit while retaining at least \(9^n\) factors of
length \(n\).  This is incompatible with the \(O(n)\) factor complexity of an
automatic sequence.

Therefore one cannot apply the rational/transcendental dichotomy for
automatic numbers or standard Mahler-value theorems to \(\pi\) merely from
\(\pi\in K_w\).  The missing exact premise is a decimation relation for the
specific digit sequence of \(\pi\), and omission of \(w\) gives none.

The digit generating function

\[
  D_\pi(z)=\sum_{n\geq1}d_nz^n
\]

does not rescue the argument.  If it were D-finite over
\(\overline{\mathbb Q}(z)\), the finite-coefficient theorem of Bell--Chen
would make it rational; evaluating at \(z=1/10\) would then make
\(D_\pi(1/10)=\pi-3\) algebraic.  Thus \(D_\pi\) is not D-finite.  Moreover,
integer coefficients plus irrationality put it on the natural-boundary side
of P\'olya--Carlson.  Neither conclusion yields a contradiction: many
forbidden-word paths also have non-D-finite series and natural boundaries.

Status of this section: source premises are `literature-checked`; their
specialization is a `proof sketch`.

## 3. Transcendence and transcendence measures miss the survivor condition

Lindemann--Weierstrass proves that \(\pi\) is transcendental because
\(e^{i\pi}=-1\).  A quantitative transcendence measure bounds
\(|P(\pi)|\) from below in terms of the degree and height of a nonzero integer
polynomial \(P\).  The hypothesis \(\pi\in K_w\), however, gives only the
digit-by-digit inequalities defining a nested family of intervals.  It does
not supply a sequence of nonzero integer polynomials with anomalously small
values at \(\pi\).

At degree one, truncating after \(N\) digits gives

\[
  \left|\pi-{\lfloor10^N\pi\rfloor\over10^N}\right|<10^{-N}=q^{-1},
  \qquad q=10^N. \tag{4}
\]

This bound holds for every real number and is far weaker than the
\(q^{-2}\)-scale supplied infinitely often by continued fractions.  Avoiding
one word changes the set of allowed numerators in (4), but not the exponent.
Even the current `literature-checked` bound

\[
  \mu(\pi)\leq7.103205334137\ldots
\]

only forbids infinitely many rational approximations of exponent greater than
that number; (4) has exponent one.  A contradiction from the known
irrationality measure would require the omitted-word condition to manufacture
infinitely many \(p/q\) with

\[
  |\pi-p/q|<q^{-7.103205334137\ldots-\varepsilon}, \tag{5}
\]

and it supplies nothing remotely of this form.

The gap remains even if the best imaginable scalar result
\(\mu(\pi)=2\) were proved.  Fishman's Schmidt-game theorem puts badly
approximable points inside standard digit-restricted Cantor sets with full
relative Hausdorff dimension.  After deleting the countable algebraic points,
such survivor sets contain uncountably many transcendental numbers of exact
irrationality exponent two.  Hence no theorem depending only on
transcendence plus scalar rational-approximation quality can exclude
\(\pi\in K_w\).

The same obstruction applies a fortiori to broad Mahler S-number
classifications: generic Diophantine type coexists with missing digits.  A
usable transcendence measure would have to exploit a new polynomial family
whose smallness follows from the **specific defining identities of \(\pi\)**
and whose coefficient pattern also detects \(K_w\).  No such construction was
located.

## 4. G-functions and periods: exact quantifier mismatch

The identity

\[
  \pi=4\arctan(1)=4\int_0^1{dx\over1+x^2}
\]

makes \(\pi\) a period and a G-value.  Fischler--Rivoal prove strong lower
bounds for rational approximation to \(F(a/b)\) when \(F\) is one fixed
nonrational G-function and the rational argument \(a/b\) has sufficiently
large denominator relative to constants depending on \(F\).  Their digit
consequence controls long immediate repetitions in the expansion of
\(F(a/b^s)\); it does not prove occurrence of every word.

For \(4\arctan z\) at \(z=1\), the required small-rational-argument condition
is absent.  Replacing \(\arctan z\) by a sequence of Machin identities with
smaller rational arguments changes the function or the linear combination,
while the constants in the theorem depend on that fixed data.  There is no
uniform theorem that survives this variation.  Even if such a restricted
approximation bound were obtained for \(\pi\), a survivor path may avoid one
word without containing long powers, so the published repetition conclusion
would still not imply coverage.

The exact quantitative gap is therefore twofold:

- **applicability gap:** no fixed G-function/sufficiently-small rational-point
  presentation to which the published constants apply at \(\pi\);
- **combinatorial gap:** restricted rational approximation controls long
  repetitions, whereas one omitted word permits exponentially many
  nonrepetitive continuations.

## 5. Fourier methods: a support estimate is not point exclusion

The avoidance language has useful finite Fourier transforms.  Circle-method
work on missing-digit integers estimates sums over **all** admissible integers
of a given length.  The transfer matrix similarly counts or averages over all
paths in the subshift.  Neither estimates the one fixed point \(\pi\).

At the real-dynamical level, omission of \(w\) says that the empirical orbit
measures of \(T_{10}^n\{\pi\}\) assign zero mass to one cylinder.  Any weak
limit is a \(T_{10}\)-invariant measure supported on \(K_w\), hence has
entropy at most \(\log\lambda_w\).  To contradict this, one would need a
\(\pi\)-specific theorem proving full entropy, density, or sufficient
integer-frequency Fourier cancellation for the orbit.  Those statements are
already essentially the desired digit-distribution breakthrough.

Euler's identity does not provide an allowed Fourier character.  Characters
of \(\mathbb R/\mathbb Z\) have integer frequency
\(x\mapsto e^{2\pi ihx}\).  The map \(e^{ix}\) corresponds to the
noninteger frequency \(h=1/(2\pi)\), and along the decimal orbit it yields the
opposite of cancellation:

\[
  \sum_{0\leq j<N}e^{i10^j\pi}=N-2\qquad(N\geq1). \tag{6}
\]

The lacunary Mahler series

\[
  L_h(z)=\sum_{j\geq0}z^{h10^j},\qquad
  L_h(z)=z^h+L_h(z^{10}),
\]

also misses the target: the desired orbit sum would be its boundary value at
\(z=e^{2\pi^2i}\), where the terms have modulus one and the series does not
converge.  Standard Mahler value theorems instead use algebraic points
strictly inside the unit disk.  Thus neither (6) nor a boundary Mahler
continuation supplies the integer-frequency cancellation needed to exclude
\(K_w\).

## 6. Strong countermodels to all scalar upgrades

The obstruction is not merely that present constants are weak.

- For every nonempty \(w\), deleting one digit occurring in \(w\) leaves a
  nine-digit Cantor subset of \(K_w\).  It contains uncountably many
  transcendental, badly approximable points of irrationality exponent two.
- Automatic examples such as decimal affine images of the Thue--Morse number
  omit digits, are transcendental, have exact irrationality exponent two, and
  possess a Mahler functional equation.
- Generic paths in the avoidance subshift have entropy \(\log\lambda_w\), can
  have a natural-boundary digit series, and need not exhibit the repetitions
  targeted by Subspace-Theorem or G-function digit results.

Consequently the conjunction

\[
  \text{transcendental} + \mu=2 + \text{Mahler structure}
  + \text{natural boundary}
\]

does not imply even that every single digit occurs.  Any successful theorem
must use a property much more rigid and \(\pi\)-specific than all four.

## 7. The exact remaining proof obligations

A contradiction proof from an omitted word would be complete if any one of
the following currently missing inputs were established:

1. **Pointwise orbit input:** for every interval \(I\subset[0,1)\), the orbit
   \(\{10^n\pi\}\) enters \(I\); this is exactly V1/digit-density, not a
   simplification.
2. **Entropy input:** the orbit closure of \(\{\pi\}\) has topological entropy
   \(\log10\).  By (1), this excludes every \(K_w\); proving it is equivalent
   to maximal factor complexity and hence again essentially V1.
3. **Fourier input:** enough integer-frequency cancellation, uniformly at the
   natural frequency scale \(10^m\), to force every length-\(m\) cylinder to
   be hit.  Fixed-frequency or averaged-over-input estimates are insufficient.
4. **Transcendence-measure input:** from \(\pi\in K_w\), construct nonzero
   integer polynomials \(P_N\) for which the degree/height/small-value tradeoff
   violates an explicit lower bound at \(\pi\).  The survivor inequalities
   currently yield only the universal truncation scale (4).
5. **Uniform G-function input:** a theorem valid for a fixed representation of
   \(\pi\) that turns the absence of one arbitrary word into forbidden
   rational approximation, rather than merely ruling out long repetitions.

Items 1--3 are direct restatements or standard sufficient conditions for the
target.  Items 4--5 are the only genuinely alternative transcendence routes,
and the exact bridge from symbolic avoidance to anomalously small
\(\pi\)-specific forms is absent.

## 8. Literature and mathlib audit

Status: `literature-checked` as of **2026-08-12 UTC**.  This was a bounded
primary-source search, not a claim that the entire literature has been
exhausted.

- Lagarias, *On the Normality of Arithmetical Constants* (2001), gives the
  fixed-orbit/digit-density formulation and treats normality of constants such
  as \(\pi\) as conjectural: <https://arxiv.org/abs/math/0101055>.
- Guibas--Odlyzko, *String overlaps, pattern matching, and nontransitive
  games* (1981), supplies the exact correlation/avoidance generating
  function: <https://doi.org/10.1016/0097-3165(81)90005-4>.
- Mauldin--Williams, *Hausdorff dimension in graph directed constructions*
  (1988), supplies the graph-directed dimension theorem:
  <https://doi.org/10.1090/S0002-9947-1988-0961615-4>.
- Adamczewski--Bugeaud, *On the complexity of algebraic numbers I* (2007),
  is a low-complexity-to-transcendence theorem, not its converse and not a
  theorem excluding transcendental points from \(K_w\):
  <https://doi.org/10.4007/annals.2007.165.547>.
- Fischler--Rivoal, *Rational approximation to values of G-functions, and
  their expansions in integer bases* (2018), gives the fixed-function,
  small-rational-point and repetition statements audited above:
  <https://doi.org/10.1007/s00229-017-0933-8>.
- Zeilberger--Zudilin, *The irrationality measure of \(\pi\) is at most
  7.103205334137...* (2020), gives the current scalar bound used in (5):
  <https://doi.org/10.2140/moscow.2020.9.407>.
- Fishman, *Schmidt's game, badly approximable matrices and fractals* (2009),
  supplies the full-relative-dimension badly-approximable separator:
  <https://doi.org/10.1016/j.jnt.2009.02.005>.
- Chow--Varj\'u--Yu, *Counting rationals and Diophantine approximation in
  missing-digit Cantor sets* (2026), is an averaged/counting theorem inside a
  missing-digit set, not an exclusion theorem for \(\pi\):
  <https://doi.org/10.1016/j.aim.2026.110807>.
- Bell--Chen, *Power series with coefficients from a finite set* (2017), is
  the D-finite/rational input for the digit-series obstruction:
  <https://doi.org/10.1016/j.jcta.2017.05.002>.
- Bugeaud, *On the rational approximation to the Thue--Morse--Mahler
  numbers* (2011), proves the exact irrationality exponent two used in the
  automatic countermodel:
  <https://doi.org/10.5802/aif.2666>.
- Adamczewski--Faverjon, *M\'ethode de Mahler : relations lin\'eaires,
  transcendance et applications aux nombres automatiques* (2017), states the
  interior algebraic-point setting for standard Mahler value theorems:
  <https://doi.org/10.1112/plms.12038>.

The 2025--2026 search terms included fixed-number digit complexity,
forbidden-word subshifts, periods and G-values, transcendence measures for
\(\pi\), Mahler boundary values, and Fourier analysis on missing-digit sets.
No applicable theorem specializing to \(\pi\notin K_w\) was found.

The local mathlib search found finite Fourier infrastructure such as
`Mathlib/Analysis/Fourier/ZMod.lean` and polynomial Mahler **measure** in
`Mathlib/Analysis/Polynomial/MahlerMeasure.lean`.  The latter is not Mahler's
functional-equation method.  No library implementation of symbolic
subshifts, forbidden-word entropy, automatic-number transcendence, a
transcendence measure for \(\pi\), or the needed G-function digit theorem was
located.  Existing project modules T19, T30, T32, and T33 already formalize
the relevant Fourier/entropy reductions and countermodel boundary; no new
Lean infrastructure is justified by this negative applicability audit.

## Bottom line

The missing-word assumption gives a clean finite-state and fractal container,
but every inspected transcendence tool acts on the wrong invariant:
algebraicity, scalar approximation, decimation, fixed-function rational
values, or averages over all survivor paths.  The unresolved quantity is the
location of the single named point \(\pi\) relative to each \(K_w\).  Bridging
that pointwise gap would itself be the breakthrough.
