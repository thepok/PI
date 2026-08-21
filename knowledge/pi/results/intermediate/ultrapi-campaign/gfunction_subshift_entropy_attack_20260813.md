# G-function value versus a proper decimal finite-type subshift

Audit date: **2026-08-13 UTC**  
Status: `literature-checked` bounded primary-source audit, with local
`proof sketch` reductions and an `experiment` checker  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The canonical source is Marcel's local human-authored problem root; it has no
external source URL, and this report does not invent one.  The source's exact
normalization is retained: every **finite** decimal word, with leading zeros
allowed, must occur contiguously in the fractional decimal expansion of
\(\pi\).  The infinite-word and subsequence readings recorded in that source
are not substituted for this target.

## Verdict

The proposed first step is exact and useful:

> If a decimal word \(w\) is absent from \(\pi\), then its digit path belongs
> to a proper finite-type subshift whose entropy is strictly less than
> \(\log 10\).

For \(|w|=m\), the entropy deficit supplied by the elementary aligned-block
argument is

\[
 \delta_m=\log 10-{1\over m}\log(10^m-1)
          =-{1\over m}\log(1-10^{-m})>0.                 \tag{1}
\]

The audit found no current theorem that transfers the fact that \(\pi\) is a
fixed G-function value, E-function zero, period, or logarithm of an algebraic
number into exclusion from a prescribed positive-entropy subshift.  The main
obstruction is not merely a missing constant in a transcendence estimate.  It
is a quantifier mismatch:

* a finite automaton describes the **set of all legal paths** in the survivor;
* G-, Mahler-, D-finite-, and automatic-sequence theorems require an equation
  for the **one selected path** formed by the digits of the number.

Membership in a finite-type subshift supplies no such selected-path equation.
Indeed, every one-word survivor contains a full nine-symbol shift and hence
uncountably many freely chosen paths.

One unconditional conclusion sharpens the mismatch.  If the selected digit
generating series of \(\pi\) were D-finite, Bell--Chen's theorem would make it
rational and the digits eventually periodic, contradicting the irrationality
of \(\pi\).  Thus the selected digit series is **not** D-finite.  This does not
exclude it from any finite-type subshift; it explains why applying G-function
coefficient theorems to that series cannot be the missing bridge.

The canonical statement therefore remains a `conjecture`.  This audit gives
an exact entropy reduction, an exact degree--height ledger, and a strong
counterexample to several tempting strengthenings, but not a
`candidate resolution`.

## 1. Exact finite-type and candidate-count consequences

Write

\[
 \pi=3+\theta,\qquad
 \theta=0.d_1d_2\ldots=\sum_{n\geq1}d_n10^{-n}.
\]

Fix \(w\in\{0,\ldots,9\}^m\).  Its survivor is

\[
 X_w=\{x\in\{0,\ldots,9\}^{\mathbb N}:w
       \text{ occurs at no position of }x\}.                 \tag{2}
\]

This is the subshift defined by one forbidden pattern.  A prefix automaton can
use states \(0,\ldots,m-1\), where the state is the length of the longest
suffix equal to a prefix of \(w\); a transition reaching state \(m\) is
deleted.  If \(A_w\) is its nonnegative integer adjacency matrix and
\(R_w(N)\) is the number of legal length-\(N\) prefixes, then exactly

\[
 R_w(N)=e_0^{\mathsf T}A_w^N\mathbf 1.                       \tag{3}
\]

The companion checker implements this automaton independently of the
aligned-block estimate below and compares it with brute-force enumeration in
small bases.

Choose a digit \(c\) occurring in \(w\).  Every word over the other nine
digits avoids \(w\), so

\[
 9^N\leq R_w(N).                                               \tag{4}
\]

Write \(N=qm+r\), \(0\leq r<m\).  In each of the \(q\) disjoint aligned
length-\(m\) blocks, all words except \(w\) are possible; allowing an arbitrary
remainder only enlarges the set.  Hence

\[
 R_w(N)\leq10^r(10^m-1)^q.                                   \tag{5}
\]

Consequently

\[
 \log9\leq h(X_w)\leq{1\over m}\log(10^m-1)<\log10.           \tag{6}
\]

The relative candidate count also decays exponentially:

\[
 {R_w(N)\over10^N}\leq(1-10^{-m})^{\lfloor N/m\rfloor}.       \tag{7}
\]

Covering the survivor real numbers by their legal decimal cylinders gives

\[
 {\log9\over\log10}
 \leq \dim_{\mathrm H}X_w
 \leq {\log(10^m-1)\over m\log10}<1,                          \tag{8}
\]

where the lower bound uses the embedded full nine-shift.  In particular, the
survivor has Lebesgue measure zero but positive Hausdorff dimension.  These
metric statements do not decide whether the named point \(\pi\) belongs to
it.

If \(p_\pi(n)\) denotes the number of distinct length-\(n\) factors in the
digits of \(\pi\), then a missing word of length \(m\) gives
\(p_\pi(m)\leq10^m-1\).  Factor submultiplicativity then yields the same strict
entropy bound as (6).  Thus the canonical conjecture is equivalent to maximal
factor entropy \(\log10\), not merely positive entropy.

Status of this section: local `proof sketch`.  Equations (3)--(7) are also
covered by the finite `experiment` checker; finite checks are not used as a
proof.

## 2. Why an SFT automaton is not a digit automaton

There are three different finite-state objects here.

1. The legal-prefix language of \(X_w\) is regular.
2. The subshift \(X_w\) is the set of all infinite paths through that regular
   graph; the graph generally branches forever.
3. An automatic sequence is one selected output word computed from the base
   expansion of the index.

The transfer matrix in (3) gives rational generating functions for aggregate
counts and can be packaged into functional systems.  It does not give a
functional equation for

\[
 D_\pi(z)=\sum_{n\geq1}d_nz^n.                               \tag{9}
\]

This distinction can be made unconditional.  Bell--Chen, Theorem 1.3, proves
that a D-finite power series over a characteristic-zero field whose
coefficients lie in a finite set is rational.  Applied hypothetically to
(9), its hypotheses on the coefficients are automatic.  A rational series
with coefficients in a finite set has an eventually periodic coefficient
word: after the constant-coefficient recurrence begins, its finite set of
state vectors must eventually repeat.  The associated base-10 real would be
rational.  Therefore

\[
 \pi\text{ irrational}\quad\Longrightarrow\quad
 D_\pi(z)\text{ is not D-finite}.                             \tag{10}
\]

Every G-function is D-finite, so \(D_\pi\) is not a G-function either.  The
fixed G-function that evaluates to \(\pi\) in Section 4 is a different
function.  Confusing these two series would silently replace a value theorem
by a coefficient theorem.

The 2023 Bell--Chen--Nguyen--Zannier height theorem strengthens rationality
conclusions for D-finite series with sublinear coefficient height and
denominator growth.  Decimal digits have height zero, so again D-finiteness
would force rationality.  But neither regular-language membership nor a
finite entropy deficit supplies D-finiteness of the selected series.

Status: the cited implications are `literature-checked`; their specialization
to (9)--(10) is a local `proof sketch`.

## 3. A selected-path separator inside every one-word survivor

The gap is not only cardinality.  There is a structured survivor with strong
Diophantine properties for every forbidden word.

Let \((t_n)_{n\geq0}\) be Thue--Morse,

\[
 t_{2n}=t_n,\qquad t_{2n+1}=1-t_n,
\]

and choose distinct decimal digits \(a,b\neq c\), where \(c\) is any digit
occurring in \(w\).  Define

\[
 \tau_{10}=\sum_{n\geq0}t_n10^{-n-1},\qquad
 \eta_w={a\over9}+(b-a)\tau_{10}.                             \tag{11}
\]

There are no carries: the digits of \(\eta_w\) are exactly
\(a+(b-a)t_n\in\{a,b\}\).  They omit \(c\), hence the path avoids \(w\).
Its selected digit word is 2-automatic, and its generating function

\[
 T(z)=\sum_{n\geq0}t_nz^n
\]

satisfies the selected-path Mahler equation

\[
 T(z)=(1-z)T(z^2)+{z\over1-z^2}.                              \tag{12}
\]

Bugeaud recalls Mahler's transcendence theorem for the
Thue--Morse--Mahler number and proves that its irrationality exponent is
exactly two in every integer base \(b\geq2\).
Rational affine transformations preserve that exponent, so \(\eta_w\) has
the same property.  Thus all of the following can coexist:

\[
 \begin{gathered}
 \text{omission of a prescribed word},\quad
 \text{selected-path automatic/Mahler structure},\\
 \text{transcendence},\quad
 \text{optimal scalar irrationality exponent }2.
 \end{gathered}                                                \tag{13}
\]

This rules out any route that uses only those four properties.  It does not
rule out a theorem special to G-values.  In fact \(T(z)\) is nonrational and
Mahler; Bell--Coons--Rowland's version of Bézivin's theorem says that a
D-finite Mahler function is rational.  Hence this particular digit
generating function is not D-finite and is not itself a G-function.  No claim
is made that the **number** \(\eta_w\) cannot be represented as a value of
some unrelated G-function.

Status: (11)--(12) are local `proof sketch` identities and finite prefixes are
covered by the `experiment` checker.  Bugeaud's irrationality-exponent result
and the Bell--Coons--Rowland theorem are `literature-checked`.

## 4. The exact G-function representation of pi and its boundary

Machin's identity gives a fixed rational-coefficient G-function

\[
 H(z)=16\arctan(2z)-4\arctan(10z/239),\qquad H(1/10)=\pi.      \tag{14}
\]

The checker verifies the rational tangent calculation

\[
 \tan(2\arctan(1/5))={5\over12},\quad
 \tan(4\arctan(1/5))={120\over119},\quad
 \tan(4\arctan(1/5)-\arctan(1/239))=1.                       \tag{15}
\]

The relevant angle lies between \(0\) and \(\pi/2\), so (15) is Machin's
identity.  The Taylor coefficients of \(\arctan z\) are rational with the
required exponential denominator/height bounds, and it satisfies a rational
linear differential equation; hence (14) is a fixed nonrational G-function
evaluated strictly inside its disk of convergence.

Fischler--Rivoal's corrected 2018 paper is the closest direct result.  For a
fixed nonrational G-function \(F\), it gives rational-approximation estimates
for \(F(a/b)\) and a bound on long immediate repetitions in its base-\(b\)
expansion, provided \(b\) is sufficiently large relative to the fixed
\(F,a\) and other parameters.  The paper does not verify the required
threshold for the particular pair \((H,10)\).

Replacing \(H\) by a rescaled family \(H_r\) so that \(H_r(10^{-r})=\pi\)
does not make the theorem uniform: its effective constants change with the
function \(H_r\).  More importantly, even a successful threshold check would
only restrict immediate powers.  The Thue--Morse path above avoids a digit
while having extremely limited powers, so repetition control does not imply
escape from a forbidden-word subshift.

The value relation (14) likewise gives no equation for the digit series (9).
Composition, diagonal, and coefficient-height theorems for G- or D-finite
functions operate on Taylor coefficients of the function being represented;
base expansion after evaluation introduces floors and carries and is not
preserved by those closure operations.

Status: source applicability is `literature-checked`; the specialization and
threshold ledger are a local `proof sketch`.

## 5. Exact auxiliary-polynomial cost

The missing-word hypothesis says that for every \(n\),

\[
 a_n=\lfloor10^n\theta\rfloor\in A_w(n),                      \tag{16}
\]

where \(A_w(n)\) is the set of zero-padded length-\(n\) integers avoiding
\(w\), with \(|A_w(n)|=R_w(n)\).

### 5.1 Multiplying over every candidate prefix

The direct language polynomial is

\[
 B_n(X)=\prod_{a\in A_w(n)}(10^n(X-3)-a)\in\mathbb Z[X].      \tag{17}
\]

Its exact cost is

\[
 \deg B_n=R_w(n),\qquad
 \operatorname{lc}(B_n)=10^{nR_w(n)},\qquad
 \log H(B_n)\geq nR_w(n)\log10\geq n9^n\log10.               \tag{18}
\]

At \(X=\pi\), the selected factor is
\(10^n\theta-a_n=\{10^n\theta\}<1\), but the other
\(R_w(n)-1\) factors can each have size comparable with \(10^n\).  The only
uniform upper bound obtained from the selected factor is

\[
 0<|B_n(\pi)|<(10^n)^{R_w(n)-1},                              \tag{19}
\]

which is large.  Normalizing every factor by \(10^n\) destroys integrality;
clearing the denominators restores exactly the leading coefficient in (18).
The entropy saving changes the exponential base of \(R_w(n)\) but does not
make this integer polynomial small.

### 5.2 Multiplying genuinely small selected tails

Let \(A_n=\lfloor10^n\pi\rfloor\), \(x_n=10^n\pi-A_n\), and
\(F(Z)=Z(1-Z)\).  Then

\[
 P_N(X)=\prod_{n=1}^N F(10^nX-A_n)\in\mathbb Z[X]             \tag{20}
\]

has

\[
 0<P_N(\pi)\leq4^{-N},\qquad \deg P_N=2N.                    \tag{21}
\]

Since \(0<A_n<4\cdot10^n\), the coefficient \(\ell^1\)-norm of the \(n\)-th
quadratic factor is at most \(30\cdot10^{2n}\).  Therefore exactly

\[
 H(P_N)\leq30^N10^{N(N+1)},\qquad
 \log H(P_N)=O(N^2).                                         \tag{22}
\]

Cijsouw's polynomial measure for the fixed logarithm
\(i\pi=\operatorname{Log}(-1)\), transferred to integer polynomials in
\(\pi\), has the shape

\[
 |P(\pi)|>
 \exp[-C D^2(D+\log H)(1+\log D)^2].                         \tag{23}
\]

Substitution of (21)--(22) yields only

\[
 |P_N(\pi)|>\exp[-O(N^4\log^2N)],                             \tag{24}
\]

which is compatible with the much larger upper bound \(4^{-N}\).  Moreover,
the smallness in (21) is universal and never used word omission.  This ledger
does not exclude every possible auxiliary construction; it isolates why the
two direct constructions fail.  A viable construction would need to compress
all regular-language constraints while retaining integrality and smallness at
a cost far below (18) or (22)--(24).

Status: local `proof sketch`; the degree, leading coefficient, and
coefficient-norm computations are also covered by the finite `experiment`
checker.  The Cijsouw input is `literature-checked` in the frozen predecessor
report cited below.

## 6. What the 2024--2026 complexity results do and do not say

The bounded update searched G-function values, E-function zeros, Mahler
functions, D-finite finite-valued series, automatic sequences, irrationality
measures, subword complexity, finite-type subshifts, and restricted-numerator
approximation.  The most relevant boundaries are:

| Primary theorem | Output | Why it stops before the target |
|---|---|---|
| [Adamczewski--Bugeaud, *On the complexity of algebraic numbers I*](https://arxiv.org/abs/math/0511674), Theorems 1--2 | Irrational algebraic expansions have superlinear complexity; automatic irrational numbers are transcendental. | \(\pi\) is already transcendental, and a one-word survivor has exponential complexity. |
| [Adamczewski, *On the expansion of some exponential periods in an integer base*](https://arxiv.org/abs/1205.0961), Theorem 1 | Irrationality exponent two implies \(p(n)-n\to\infty\). | Still linear-scale complexity, and the required exponent is not known for \(\pi\). |
| [Bell--Chen, *Power Series with Coefficients from a Finite Set*](https://arxiv.org/abs/1606.04986), Theorem 1.3 | D-finite plus finite coefficient alphabet implies rational. | It proves (10) once D-finiteness is hypothesized; SFT membership does not imply D-finiteness. |
| [Bell--Coons--Rowland, *The rational-transcendental dichotomy of Mahler functions*](https://arxiv.org/abs/1210.2070), Theorem 1 | A D-finite Mahler function is rational. | It separates the Thue--Morse digit function from G-functions; it supplies no equation for \(D_\pi\). |
| [Bell--Chen--Nguyen--Zannier, *D-finiteness, rationality, and height III*](https://arxiv.org/abs/2306.02590), Theorem 1.1 | D-finite series with sublinear coefficient height and denominator growth are rational with restricted denominators. | Decimal digits satisfy the height condition, but selected-path D-finiteness is absent. |
| [Fischler--Rivoal, *Rational approximation to values of G-functions, and their expansions in integer bases*](https://www.imo.universite-paris-saclay.fr/~fischler/approxG.pdf), Theorems 2--3 | Effective rational separation and immediate-repetition bounds after a function-dependent large-base threshold. | The \((H,10)\) threshold is not established; repetitions do not detect arbitrary missing words. |
| [Bugeaud--Kaneko--Kim, *On irrationality exponent of real numbers with low complexity expansion*](https://arxiv.org/abs/2510.17177v3), Theorem 1.3 (20 March 2026 version) | If \(\mu(\xi)=2\), then \(\limsup p(n)/n\geq4/3\); its \(\mu>2\) bound is nontrivial only for \(\mu<2.2\). | Even the best case is linear and exponentially below \(10^n\); \(\mu(\pi)=2\) is not known. |
| [Fischler--Rivoal, *Transcendence of values of logarithms of E-functions*](https://doi.org/10.1007/s00208-026-03374-z), consequence after Theorem 3 | Since \(\pi\) is a simple zero of \(\sin z\), \(|\pi-a/b|\geq\exp(-cb^d)\). | At \(b=10^N\) this is far weaker than universal decimal truncation and is numerator-language blind. |
| [Adamczewski--Faverjon, *A Liouville-Type Inequality for Values of Mahler M-Functions*](https://arxiv.org/abs/2604.08208), Theorems 1.1--1.2 | Polynomial degree--height separation for Mahler values; no such value is a U-number. | A survivor path need not be Mahler, and the estimate has no forbidden-language input. |
| [Nguyen, *Transcendence and measures via the refined Diophantine exponent*](https://arxiv.org/abs/2605.30606v2), Theorems A--B | Strong near-periodicity of the selected word implies transcendence or measures. | Positive-entropy SFT membership does not imply the required selected-word recurrence. |

Zeilberger--Zudilin's available bound
\(\mu(\pi)\leq7.103205334137\ldots\) does not put \(\pi\) in the narrow
near-two regime of the 2026 linear-complexity estimate.  Even an eventual
proof of \(\mu(\pi)=2\) would give only the linear conclusion in the table,
whereas disjunctivity needs \(p_\pi(n)=10^n\) at every \(n\).

No inspected 2024--2026 primary theorem had the pointwise form

\[
 \xi\text{ is this fixed G/E/period value}
 \quad\Longrightarrow\quad
 \text{the base-10 digits of }\xi\text{ escape every proper SFT}. \tag{25}
\]

The absence of such a result is a bounded-search finding, not an exhaustive
novelty claim.

## 7. mathlib audit

The local mathlib search on 2026-08-13 used the terms `subshift`, `shift of
finite type`, `topological entropy`, `subword complexity`, `G-function`,
`Mahler function`, `automatic sequence`, `P-recursive`, `D-finite`, and
`holonomic`.

`Mathlib/Dynamics/SymbolicDynamics/Basic.lean` contains
`MulSubshift.ofForbidden` / `Subshift.ofForbidden`, occurrence cylinders, and
`languageOn`; its SHA-256 is
`c3113c110c17101ac09ac6ac332053ee09c1b02b7c78dbdedbc4f6f6afcc8eca`.
Generic topological-entropy infrastructure is also present.  The search found
no formalized G-function, Mahler-function, automatic-sequence, or D-finite
theorem connecting a special value to its positional digit word, and no
ready specialization proving (6).  Thus mathlib can encode the survivor, but
does not contain the missing arithmetic bridge.

This is a search report, not a claim that no differently named declaration
exists anywhere in the library.

## 8. Frozen inputs, primary-source pins, and checker

Frozen local inputs used by this update:

| File | SHA-256 |
|---|---|
| `special_values_digit_complexity_literature.md` | `b08859d7fa8e68402e26393a76dffb010b19a3dbb442053b6765e87f1b67ece9` |
| `subshift_log_algebraic_bridge.md` | `b4e4fb05397f75e1e4af7bbd6d4d32e80d489893fead9773de51a57a28aca896` |
| `subexponential_candidate_avoidance.md` | `aaec73cba088f84c9630603856385e8d1efe581a35f4ff73818dda7629b64aee` |

Freshly fetched or reverified primary/source PDFs on 2026-08-13 UTC:

| Source/version | SHA-256 |
|---|---|
| [Fischler--Rivoal, corrected `approxG.pdf`](https://www.imo.universite-paris-saclay.fr/~fischler/approxG.pdf) | `4e6954c62da62ab760181f9204a7f0fec50afaea6089004b874723b6dedc4d40` |
| [Adamczewski--Bugeaud, arXiv:math/0511674](https://arxiv.org/pdf/math/0511674) | `e3bd2934800e94dd27930d43d47abc44f760de7e90320d1d014b372b681be9a0` |
| [Adamczewski, arXiv:1205.0961](https://arxiv.org/pdf/1205.0961) | `28ed9d10ddcadc20e103a0ff177c19d2d8c80b5b264441baa071ce5f13e4a7e3` |
| [Bell--Chen, arXiv:1606.04986](https://arxiv.org/pdf/1606.04986) | `9550237fb012dea45349573f50ef19aa0adbbe9d4e68121255206756851da1db` |
| [Bell--Coons--Rowland, arXiv:1210.2070](https://arxiv.org/pdf/1210.2070) | `30481c3b4cf0ae925bb7bf11b908e00d3df0a77779090c615ebdfa82bd764aa0` |
| [Bell--Chen--Nguyen--Zannier, arXiv:2306.02590v1](https://arxiv.org/pdf/2306.02590v1) | `2d50018f9c9f255d3886814fb4875dacc7f3c7e936fc31ed0c2bab2bd8a4ac05` |
| [Bugeaud--Kaneko--Kim, arXiv:2510.17177v3](https://arxiv.org/pdf/2510.17177v3) | `c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01` |
| [Zeilberger--Zudilin, arXiv:1912.06345](https://arxiv.org/pdf/1912.06345) | `b922ee68a427ad5b74617bd2ac6b6a549824eb2d5a8c97eed0d34b2de984155f` |
| [Adamczewski, Mahler survey author PDF](https://adamczewski.perso.math.cnrs.fr/Mahler_selecta_new.pdf) | `2862813f5fc24f3a4e5d4af48603053c2657bb4722d9583c5af9f477a3ea55b0` |

The Cijsouw, Bugeaud Thue--Morse, Fischler--Rivoal 2026,
Adamczewski--Faverjon 2026, and Nguyen 2026 pins are inherited from the frozen
`subshift_log_algebraic_bridge.md`; that file records their exact URLs and
PDF hashes rather than silently treating mutable search snippets as sources.

The exact checker is
[`gfunction_subshift_entropy_attack_20260813_check.py`](gfunction_subshift_entropy_attack_20260813_check.py),
SHA-256
`c150a72f596794655ed00d911def69db88b92c578c69a463cb7ea05086baa6d7`.
It uses only the Python standard library and checks:

* KMP automaton counts against exhaustive enumeration in small bases;
* both bounds (4)--(5) for all 1,110 decimal words of lengths one through
  three and prefix lengths zero through eight;
* the strict entropy deficits in (1);
* the degree and leading coefficient of a concrete instance of (17);
* the coefficient-cost bound in (22);
* Machin's rational tangent identity;
* 1,024 coefficients of (12), the Thue--Morse recurrence, and an explicit
  mapped survivor for all 1,110 tested decimal words.

Its output is explicitly labeled `experiment`; it neither reads a prefix of
\(\pi\) nor promotes the canonical claim.

## 9. The exact missing theorem

This route can resume only with genuinely new input of one of these forms:

1. **Selected-digit bridge:** derive a nontrivial functional/differential
   equation for \(D_\pi\) from the fixed value identity (14), despite floors
   and carries.
2. **Restricted-numerator G-value estimate:** for every forbidden \(w\),
   separate \(H(1/10)\) from rationals \(a/10^n\) with
   \(a\in A_w(n)\) at a scale stronger than the universal truncation error.
3. **Compressed auxiliary form:** encode all memberships (16) in an integer
   auxiliary object whose degree, height, and value beat the ledger
   (18)--(24).
4. **Pointwise maximal-entropy theorem:** prove directly that the digit word
   of this particular G-/period value has entropy \(\log10\).

The fourth is essentially the canonical conjecture in entropy language; the
first three isolate possible arithmetic mechanisms rather than restating it.
No inspected theorem supplies any of them.  Accordingly, the G-function/SFT
attack has reached a precise obstruction and several falsified shortcuts, but
not a complete proof.
