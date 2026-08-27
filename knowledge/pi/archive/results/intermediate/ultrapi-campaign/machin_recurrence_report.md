# Actual Machin numerator: recurrence, prime survival, and the remaining archimedean gap

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Route: the actual twelve-term forcing in T40, equation (11w) of
[`ultrapi.md`](../../ultrapi.md)

## Outcome and claim status

There is **no complete proof** here that every finite decimal word occurs in
\(\pi\). The target remains a `conjecture`.

This audit does, however, extract two route-specific facts that were not in
T40--T43:

1. the natural common numerator of the **actual** twelve Machin terms is an
   exponential-polynomial sequence annihilated by an explicit order-14
   constant-coefficient recurrence; and
2. every prime \(p>12\) survives in the reduced denominator of an explicitly
   chosen actual forcing increment. For primes entering one of three interior
   slots, its newly created \(p\)-component then follows an exact geometric
   progression \(c10^t\pmod p\) for about \(p/6\) consecutive orbit steps.

The recurrence and pulse derivations below are labeled `proof sketch`, and
the finite checks are separately labeled `experiment`. The admissible
interior-prime noncancellation theorem and the resulting valuation
\(v_p(\Delta_N)=-1\), excluding the Machin base \(p=239\), are
`machine-checked` in
[`T45T45MachinPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T45T45MachinPrimeSurvival.lean).
[`T47T47MachinAllPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T47T47MachinAllPrimeSurvival.lean)
now proves both endpoint cases, handles \(p=239\) at \(N=19\), and concludes
that every prime \(p>12\) divides the reduced denominator of some actual
forcing. Both modules are present in the shared import and axiom audit. Their
direct builds and audit use only the standard allowlisted axioms `propext`,
`Classical.choice`, and `Quot.sound`. After the T49--T50 integration, the
repository-wide `scripts/check.ps1` gate completed all 8,493 jobs and passed
the kernel build, exploit scan, and exact-allowlist axiom audit on 2026-08-12
UTC.

The related full-seed theorem is `machine-checked` in
[`T48T48MachinSeedUpperHalfPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T48T48MachinSeedUpperHalfPrimeSurvival.lean):
for \(d=12N+15\), every prime \(d/2<p\le d\) outside 239 and 317 has
valuation \(-1\), and hence exact reduced-denominator multiplicity one, in
\(10^{N+1}M_{3(N+1)}\). This validates the local arithmetic premise of the
same-denominator cofactor analysis, not its PNT/Jacobsthal layer and not the
actual numerator's archimedean phase.

Two subsequent modules close the arithmetic gaps identified by the
simultaneous-pulse audit. T49 is `machine-checked` in
[`T49T49MachinEndpointPulse.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T49T49MachinEndpointPulse.lean):
it proves the omitted class-5-modulo-12 endpoint-to-endpoint pulse through
the exact offset `t <= 2*N+1`. T50 is `machine-checked` in
[`T50T50MachinSeedLowerBandPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T50T50MachinSeedLowerBandPrimeSurvival.lean):
for `d = 12*N+15`, it proves exact seed-denominator multiplicity one for
every prime `d/5 < p <= d` outside the fixed set
`{5,11,19,233,239,317,13757}`. The apparent divisor of the extra endpoint is
fully discharged, not retained as a hypothesis.

T51 is `machine-checked` in
[`T51T51MachinSeedThirdBandPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T51T51MachinSeedThirdBandPrimeSurvival.lean).
It extends the seed result to \(d/7<p\le d/5\), isolates the three singular
exponents \(p,3p,5p\), records the five genuine coefficient exceptions, and
discharges the possible \(d+2=7p\) endpoint using \(p\equiv11\pmod {12}\).
It proves valuation \(-1\) and exact denominator multiplicity one, but no
archimedean residue statement. The subsequent T51-integrated full gate also
passed.

The broader arithmetic and its limitation are recorded in
[`actual_numerator_phase_attack.md`](actual_numerator_phase_attack.md). A
general-band `proof sketch` puts all but sublinear logarithmic prime mass into
the actual reduced denominator. Exact quotient reciprocity then identifies
the small complementary quotient with the actual archimedean cell index, so
this does not produce cancellation or coverage.

The advance is structural, not a resolution. Exact telescoping compresses the
whole pulse to powers of one fixed rational starting point plus an
exponentially tiny real correction. This is substantially stronger than
control of one CRT component, but the resulting short exponential orbit at a
large composite denominator is not covered by the finite-field estimates
located in the literature audit.

The corrected reduction is now `machine-checked` in
[`T46T46MachinFixedModulusTelescoping.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T46T46MachinFixedModulusTelescoping.lean).
T46 proves the exact rational iterate, fixed-initial-denominator
representation, error telescope, nonnegativity, generic geometric bound, and
the explicit \(t\le2N+1\) pulse bound. It does not assert that later reduced
denominators stay unchanged or prove any cancellation estimate.

## 1. Exact normalization of the T40 window

Put

\[
 r=r_N:=12N+5,
 \qquad
 W_q(r):=\sum_{j=0}^{5}
   \frac{(-1)^j}{(r+2j)q^{r+2j}}.
\]

Expanding the Taylor indices in T40 gives exactly

\[
 \boxed{\displaystyle
 \Delta_N=10^{N+1}\bigl(16W_5(r)+4W_{239}(r+2)\bigr).}
 \tag{1}
\]

The plus sign on the \(239\)-window is important: that six-term Taylor window
begins at an odd Taylor index, and T40 subtracts four times the window.

Define

\[
 P(r):=\prod_{j=0}^{5}(r+2j)
\]

and the integer polynomial

\[
 U_q(r):=\sum_{j=0}^{5}(-1)^j q^{10-2j}
   \prod_{\substack{0\le i<6\\i\ne j}}(r+2i).
 \tag{2}
\]

### Lemma 1 (`proof sketch`): exact six-term numerator

For every positive \(q,r\),

\[
 \boxed{\displaystyle
 W_q(r)=\frac{U_q(r)}{q^{r+10}P(r)}.}
 \tag{3}
\]

**Proof.** Use \(q^{r+10}P(r)\) as a common denominator. The \(j\)-th
summand is multiplied by
\(q^{10-2j}\prod_{i\ne j}(r+2i)\), which is precisely the \(j\)-th
summand in (2). \(\square\)

For \(r=12N+5\), define

\[
 B_N:=5^{r+10}239^{r+12}\prod_{j=0}^{6}(r+2j)
 \tag{4}
\]

and

\[
 \begin{aligned}
 A_N:=\;&16\,239^{r+12}(r+12)U_5(r)\\
       &+4\,5^{r+10}rU_{239}(r+2).
 \end{aligned}
 \tag{5}
\]

Equations (3)--(5) give the exact natural common-denominator presentation

\[
 16W_5(r)+4W_{239}(r+2)=\frac{A_N}{B_N},
 \qquad
 \Delta_N=\frac{10^{N+1}A_N}{B_N}.
 \tag{6}
\]

This presentation need not be reduced. In particular, no conclusion below
silently identifies \(A_N\) with the numerator in lowest terms.

## 2. A constant-coefficient recurrence for the actual numerator

The polynomial \(U_q(r)\) has degree exactly five. Its leading coefficient is

\[
 q^{10}-q^8+q^6-q^4+q^2-1
   =\frac{q^{12}-1}{q^2+1}\ne0
 \qquad(q>1).
\]

With \(r=12N+5\), set

\[
 \begin{aligned}
 \mathcal P(N)&:=16\,239^{17}(12N+17)U_5(12N+5),\\
 \mathcal Q(N)&:=4\,5^{15}(12N+5)U_{239}(12N+7).
 \end{aligned}
\]

Both are integer polynomials of degree exactly six, and (5) becomes

\[
 \boxed{\displaystyle
 A_N=(239^{12})^N\mathcal P(N)+(5^{12})^N\mathcal Q(N).}
 \tag{7}
\]

For a sequence \(f\), let

\[
 (\mathcal D_cf)_N:=f_{N+1}-cf_N.
\]

### Lemma 2 (`proof sketch`): order-14 annihilator

The natural common numerator in (5) satisfies

\[
 \boxed{\displaystyle
 \mathcal D_{239^{12}}^7
 \mathcal D_{5^{12}}^7A=0.}
 \tag{8}
\]

Equivalently, its characteristic polynomial is

\[
 (X-239^{12})^7(X-5^{12})^7.
\]

**Proof.** If \(R\) is a degree-six polynomial, then

\[
 \mathcal D_c(c^NR(N))
   =c^{N+1}\bigl(R(N+1)-R(N)\bigr),
\]

so seven applications kill the term. The two difference operators commute;
apply this observation to the two summands of (7). \(\square\)

The full displayed numerator \(C_N:=10^{N+1}A_N\) in (6) similarly obeys

\[
 \boxed{\displaystyle
 \mathcal D_{10\cdot239^{12}}^7
 \mathcal D_{10\cdot5^{12}}^7C=0.}
 \tag{9}
\]

This is genuine structure of the actual twelve-term expression, but it does
not by itself yield distribution: \(A_N\) and \(C_N\) are integers, so their
fractional parts are identically zero, while division by the moving
\(B_N\), followed by reduction, destroys the constant-coefficient recurrence.

## 3. Exact survival of primes in the reduced denominator

Write

\[
 a_k:=r+2k\qquad(0\le k\le6).
\]

Suppose first that \(p=a_k>12\) is prime and \(p\ne239\). Since
\(a_6-a_0=12<p\), among all linear denominators in (1), only the term or
terms having linear denominator exactly \(p\) contribute a negative
\(p\)-adic valuation.

At the endpoints there is only one such term:

\[
 p\frac{\Delta_N}{10^{N+1}}
 \equiv
 \begin{cases}
   16\,5^{-p}, & k=0,\\
   -4\,239^{-p}, & k=6
 \end{cases}
 \pmod p,
 \tag{10}
\]

and these residues are nonzero.

For an interior slot \(1\le k\le5\), the base-5 term with index \(k\) and
the base-239 term with index \(k-1\) share the exponent \(p\). Their exact
combined residue is

\[
 \begin{aligned}
 p\frac{\Delta_N}{10^{N+1}}
 &\equiv16(-1)^k5^{-p}+4(-1)^{k-1}239^{-p}\\
 &\equiv4(-1)^k\left(4\cdot5^{-1}-239^{-1}\right)\\
 &\equiv
 4(-1)^k\frac{951}{5\cdot239}\pmod p,
 \end{aligned}
 \tag{11}
\]

using Fermat's theorem. Here

\[
 951=4\cdot239-5=3\cdot317.
\]

For a prime greater than 12, the only possible interior slots are

\[
 \begin{array}{c|c}
 k& p\pmod{12}\\ \hline
 1&7\\
 3&11\\
 4&1.
 \end{array}
\]

The slots \(k=2,5\) would give a number divisible by 3. The only remaining
possible exceptional prime from (11) is 317, but
\(317\equiv5\pmod{12}\), so it cannot occupy an interior slot. Thus (11) is
always nonzero in the stated interior case.

### Lemma 3 (`proof sketch`): prime-survival law

If \(p=a_k>12\) is prime and \(p\ne239\), then

\[
 \boxed{v_p(\Delta_N)=-1.}
 \tag{12}
\]

Equivalently, \(p\) occurs to the first power in the denominator of
\(\Delta_N\) in lowest terms.

**Proof.** All terms have valuation at least \(-1\), and (10) or (11) says
that multiplication by \(p\) leaves a nonzero residue. The exterior factor
\(10^{N+1}\) is a \(p\)-unit. \(\square\)

In terms of the common numerator, the interior computation is equivalently

\[
 \begin{aligned}
 A_N\equiv{}&4(-1)^k5^{r+10-p}239^{r+12-p}
 \prod_{\substack{0\le i\le6\\i\ne k}}(r+2i)\\
 &\hspace{32mm}\cdot(4\cdot239^p-5^p)\pmod p.
 \end{aligned}
 \tag{13}
\]

Every prime \(p>12\), except temporarily \(239\), can be placed into an
explicit window:

\[
 \begin{array}{c|c|c}
 p\pmod{12}&k&N\\ \hline
 1&4&(p-13)/12\\
 5&0&(p-5)/12\\
 7&1&(p-7)/12\\
 11&3&(p-11)/12.
 \end{array}
 \tag{14}
\]

The omitted base prime also survives. For \(p=239\), take \(N=19\), so
\(r=233\). In \(W_{239}(235)\), the final term has the unique smallest
valuation \(-245\); the term whose linear denominator is 239 has valuation
only \(-240\), and every other term has larger valuation. Hence

\[
 v_{239}(\Delta_{19})=-245.
 \tag{15}
\]

Combining (12)--(15):

\[
 \boxed{\text{Every prime }p>12\text{ divides the reduced denominator of
 at least one actual }\Delta_N.}
 \tag{16}
\]

This is much more specific than a loose product-grid statement: it is a
noncancellation theorem for the actual signed Machin numerator. It still does
not order the resulting rational residue on the real unit interval.

## 4. A long fresh-prime pulse in the actual rational orbit

Let

\[
 y_n:=10^n M_{3n}\in\mathbb Q,
\]

where \(M_K\) is T36's rational lower Machin approximant. T38 gives the
unwrapped recurrence

\[
 y_{n+1}=10y_n+\Delta_n.
 \tag{17}
\]

Choose an interior prime

\[
 p=r_N+2k,
 \qquad k\in\{1,3,4\},
 \qquad p>12,
 \qquad p\ne239.
 \tag{18}
\]

The largest base-5 exponent in \(M_{3N}\) is \(r-2\), and the largest
base-239 exponent is \(r\). Both are less than \(p\), so \(y_N\) is
\(p\)-integral. By (11) and (17),

\[
 \boxed{\displaystyle
 py_{N+1}\equiv c_{N,p}:=
 4(-1)^k10^{N+1}\,951\,(5\cdot239)^{-1}\pmod p,}
 \tag{19}
\]

and \(c_{N,p}\ne0\).

At the next forcing index the smallest linear denominator is \(r+12>p\).
The next possible odd multiple of \(p\) is therefore \(3p\). Thus
\(\Delta_n\) is
\(p\)-integral for \(n>N\) as long as

\[
 12n+17<3p.
 \tag{20}
\]

Multiplying (17) by \(p\) then kills the forcing term modulo \(p\).

### Lemma 4 (`proof sketch`): fresh-prime geometric pulse

Under (18),

\[
 \boxed{\displaystyle
 py_{N+1+t}\equiv10^t c_{N,p}\pmod p}
 \tag{21}
\]

through the exact ranges

\[
 \begin{cases}
 0\le t\le2N,&k=1,\\
 0\le t\le2N+1,&k=3\text{ or }4.
 \end{cases}
 \tag{22}
\]

**Proof.** Condition (20) need only be checked at \(n=N+t\). Substituting
\(p=12N+5+2k\) gives (22). Induction in (17), using
\(p\Delta_n\equiv0\pmod p\), yields (21). \(\square\)

Consequently \(v_p(y_{N+1+t})=-1\) throughout the pulse. If
\(\operatorname{ord}_p(10)\) exceeds the pulse length, its displayed
\(p\)-components are also pairwise distinct.

This supplies infinitely many actual pulses (for example, Dirichlet's
theorem supplies primes in each of the progressions \(1,7,11\pmod{12}\)).
It is the strongest route-specific recurrence found in this audit.

## 5. Telescoping compresses the full phase to one fixed denominator

The first version of this audit treated the complementary CRT term as a
freely changing weight. That was too coarse. The coboundary from T38 gives a
much cleaner exact identity.

For any starting index \(n\) and \(t\ge0\), unroll (17):

\[
 y_{n+t}=10^t y_n+R_{n,t},
 \qquad
 R_{n,t}:=\sum_{u=0}^{t-1}10^{t-1-u}\Delta_{n+u}.
 \tag{23}
\]

Using \(\Delta_j=10s_j-s_{j+1}\), the remainder telescopes exactly:

\[
 \boxed{R_{n,t}=10^t s_n-s_{n+t}.}
 \tag{24}
\]

Every forcing increment is positive, so \(R_{n,t}\ge0\). T38's geometric
bound \(0\le s_j<\rho^j\), where

\[
 \rho=\frac{10}{625^3}<1,
\]

therefore gives

\[
 0\le R_{n,t}<10^t\rho^n.
 \tag{25}
\]

For a fresh-prime pulse take \(n=N+1\) and \(t\le2N+1\). Then

\[
 R_{N+1,t}<10\rho\,(100\rho)^N,
 \qquad 100\rho\approx4.096\cdot10^{-6}.
 \tag{26}
\]

Thus the entire actual pulse is exponentially close to the pure powers of
one fixed rational \(y_{N+1}\). If

\[
 y_{N+1}=a/Q
\]

in lowest terms, the relevant model phase is

\[
 e(h10^t a/Q),
 \tag{27}
\]

with the same composite modulus \(Q\) throughout the pulse. Moreover,

\[
 |e(hy_{N+1+t})-e(h10^t a/Q)|
 \le2\pi|h|R_{N+1,t},
 \tag{28}
\]

so for any fixed decimal depth the total perturbation over the
\(O(N)\)-term pulse is exponentially small.

This correction removes the purported arbitrary-weight obstruction. It does
not finish the proof. The located finite-field theorems bound a projection
such as \(\sum e_p(c10^t)\); (27) has one large, generally composite modulus
whose cofactor contains substantial powers of the Machin bases, and 10 need
not be a unit modulo it. The interval has only \(T\asymp N\) terms. A new
estimate must control this exact fixed-denominator segment rather than only
its \(p\)-projection.

Known unconditional multiplicative-order results also do not say that 10 has
order comparable to every pulse prime. Pappalardi's density-one rank-one
bound is about \(p^{1/2+o(1)}\), not the linear-sized order requested by a
naive distinctness argument over a \(\asymp p/6\) pulse. The corrected
frontier is therefore a short, fixed-composite-modulus exponential-orbit
problem, not an arbitrary changing-weight problem.

## 6. Exact failure test: the forcing sequence alone cannot select \(\pi\)

Let \(s_N\) be T38's sampled Machin error, so

\[
 \Delta_N=10s_N-s_{N+1}.
\]

For **any** real seed \(\theta\), define

\[
 w_N(\theta):=\{10^N\theta-s_N\}.
\]

Then the same complete actual forcing sequence obeys

\[
 w_{N+1}(\theta)=\{10w_N(\theta)+\Delta_N\}.
 \tag{25}
\]

For \(\theta=\pi\), this is the actual rational Machin orbit. But for
\(\theta=1/3\), since \(10^N\equiv1\pmod3\) and \(s_N\to0\),

\[
 w_N(1/3)=1/3-s_N\longrightarrow1/3
\]

for all sufficiently large \(N\). It eventually avoids the decimal cell
\([0,1/10)\).

Therefore no argument using only the forcing sequence, even its full exact
twelve-term numerator at every \(N\), can prove all-cell recurrence. It must
also exploit the actual initial phase and its correlation with the full
forcing tail. T38 already shows that this correlation is a moving-coordinate
encoding of the original \(\{10^N\pi\}\) problem.

## 7. Exact computational checks (`experiment` only)

All checks used Python integer arithmetic and `fractions.Fraction`; no
floating-point values of \(\pi\) were involved.

- Equation (6) was checked for \(0\le N<20\).
- The order-14 operator in (8) was applied at 26 consecutive positions; every
  resulting integer was exactly zero.
- For \(0\le N<1000\), all 1,793 occurrences of a prime \(p>12\),
  \(p\ne239\), among the seven window exponents were checked in the reduced
  denominator of \(\Delta_N\). Every exponent was exactly one.
- Formula (11) was checked at every eligible interior prime in that range,
  with no zero or mismatched residue.
- Formula (21), including the cutoff (22), was checked directly with exact
  rational Machin approximants in 21 small prime cases.

A separate exact-LCD analysis in
[`experiments/REPORT.md`](experiments/REPORT.md) found and proved at
`proof sketch` status infinite extra-cancellation progressions, including
\(19\mid g_{7+57t}\) and five residue classes modulo 203 on which
\(29\mid g_N\). These concern cancellation in the natural term LCD and do
not contradict the prime-survival theorem here, whose primes occupy the
linear-denominator slot itself.

These tests falsify indexing and sign mistakes; they provide zero proof of a
statement beyond the finite range.

## 8. Primary-source compatibility audit (`literature-checked`)

The fuller search log is
[`literature_report.md`](literature_report.md). The following sources are the
closest to the new recurrence and pulse.

- Fischler--Rivoal,
  [*Rational approximation to values of G-functions, and their expansions in
  integer bases*](https://arxiv.org/abs/1512.06534), gives restricted rational
  approximation and equal-digit repetition bounds for suitable G-function
  values. It does not give prescribed decimal-cell coverage for \(\pi\).
- Huang--Kauers,
  [*D-finite Numbers*](https://arxiv.org/abs/1611.05901), studies limits of
  P-recursive sequences. Classification as recurrence/D-finite data is not a
  digit-distribution theorem.
- Chen--Ye--Zheng,
  [*Distribution modulo one of linear recurrent sequences*](https://arxiv.org/abs/2604.14036),
  concerns fractional parts of real linear-recurrent sequences. The sequence
  in (8) is integer-valued, while \(A_N/B_N\) and the actual orbit are not
  fixed constant-coefficient recurrent sequences.
- Kerr,
  [*Incomplete exponential sums over exponential functions*](https://arxiv.org/abs/1302.4170),
  bounds sums of the pure form \(\sum e_p(ag^n)\), including when \(g\) is not
  primitive. It controls the prime projection of (27), not the full short
  orbit at the fixed composite denominator \(Q\).
- Pappalardi,
  [*On the Order of Finitely Generated Subgroups of
  \(\mathbb Q^*(\bmod p)\) and Divisors of \(p-1\)*](https://www.sciencedirect.com/science/article/pii/S0022314X9690044X),
  gives the density-one rank-\(r\) lower bound
  \(p^{r/(r+1)}\) times a subexponential factor, and an almost-linear bound
  under GRH. For rank one, the unconditional scale is not linear, and in any
  case it does not bound the full composite-modulus orbit (27).

No searched theorem specializes to the short fixed-composite-modulus
archimedean estimate required by (27).

## 9. Precise next lemma for this route

T45 formalizes the fixed interior residue 951, noncancellation of the two
singular terms, integrality of the ten regular terms, and
\(v_p(\Delta_N)=-1\) for admissible interior primes \(p\ne239\). T47 adds
both endpoints and the exceptional \(v_{239}(\Delta_{19})=-245\), then proves
the universal reduced-denominator survival theorem for every prime above 12;
the axiom audit is clean. The pulse range remains a suitable small formal
target. The telescoping estimate (23)--(28) is formalized by T46, but these
status upgrades do not change the status of V1. T48 additionally formalizes
the full-seed upper-half survival input; T49 formalizes the fourth long pulse,
T50 formalizes the complete two-band seed input without an endpoint hole, and
T51 formalizes the third band including its endpoint closure.
The remaining analytic task still
concerns the selected complete numerator, not denominator survival.

The next result with actual resolution leverage would have to be of the
following form. Write the fixed pulse origin as \(y_{N+1}=a_N/Q_N\) in lowest
terms. For every fixed decimal depth \(m\), prove a nontrivial bound, uniformly
for \(1\le |h|\le2\cdot10^m\), on

\[
 \left|\sum_{t<T} e_{Q_N}(h a_N10^t)\right|,
 \qquad T\asymp N,
 \tag{29}
\]

for infinitely many pulses, strongly enough that a finite Fourier minorant
forces a hit in every interval of length \(10^{-m}\). Equations (26)--(28)
then transfer that bound to the actual rational Machin orbit with an
exponentially small error.

A bound only for the projection modulo the fresh prime \(p\) is insufficient.
Conversely, a bound for (29) with error smaller than its main-term cell count
would be an actual breakthrough: it would turn the exact pulse into
prescribed-cell coverage and, through T41, into V1.

## Bottom line

The actual twelve-term numerator is not arithmetically featureless. It has an
explicit order-14 recurrence, a universal prime-survival law, and long exact
fresh-prime geometric pulses. These are meaningful, inspectable advances on
the route that survived the T43/product-grid separators.

They stop at a sharper boundary than first reported: telescoping controls the
full pulse up to an exponentially tiny error, but no cancellation theorem is
known for the resulting \(O(N)\)-term powers-of-10 segment at its fixed large
composite denominator. No complete proof of disjunctivity of \(\pi\) is
claimed.
