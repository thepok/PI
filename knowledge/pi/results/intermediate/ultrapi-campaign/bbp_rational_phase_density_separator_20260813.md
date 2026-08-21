# BBP rational phases: an exponentially close zero-carry separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_centered_carry_recurrence_20260813.md](bbp_centered_carry_recurrence_20260813.md),
  SHA-256
  `3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6`;
- [bbp_fixed_period_carry_attack_20260813.md](bbp_fixed_period_carry_attack_20260813.md),
  SHA-256
  `bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55`;
- [bbp_fixed_period_carry_attack_20260813_independent_audit.md](bbp_fixed_period_carry_attack_20260813_independent_audit.md),
  SHA-256
  `ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91`;
- [bbp_all_depth_two_adic_attack.md](bbp_all_depth_two_adic_attack.md),
  SHA-256
  `9c1282724c7999fd67133a3f0e756015e564dc6b7a2a1ec44f2efe892b2653d9`;
- [bbp_all_depth_two_adic_independent_audit.md](bbp_all_depth_two_adic_independent_audit.md),
  SHA-256
  `846268c0b45dd82b96c6112054e344669eca62fe9a4308a56e6026f131a25007`;
- [bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
  SHA-256
  `d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`;
- [bbp_actual_odd_quotient_independent_audit.md](bbp_actual_odd_quotient_independent_audit.md),
  SHA-256
  `85f8e941bdb1d974d192e4f99f0aa1b10ea230b0b67c7a7fb5a067e1551f7c36`.

## Outcome and claim boundary

No positive lower density of nonzero centered carries was obtained.  Hence
the fixed-period target and canonical V1 remain a `conjecture`.  This report
is not evidence that every finite decimal word occurs in pi.

The material result is a sharp method separator, with status `proof sketch`.
Fix any \(P\geq1\), put \(q=10^P-1\), and let \(Q_{n,P}\) be the exact
reduced denominator of the rational BBP phase \(q10^nB_{7n}\).  There is a
rational centered phase sequence with all of the following properties.

1. At every sufficiently large depth its reduced denominator is exactly
   \(Q_{n,P}\), and its numerator over the raw denominator has the same exact
   two-adic valuation \(v_2(7n+1)\) as the BBP centered numerator.
2. Every centered carry is zero.
3. Its positive rational forcing differs from the exact sevenfold BBP
   forcing by relative error

   \[
   O\!\left(\exp\bigl(-(42+\log 5-o(1))n\bigr)\right). \tag{1}
   \]

There is also one coherent version whose denominator divides the exact raw
BBP denominator at every depth.  Its forcing equals the BBP forcing exactly
away from the transitions immediately preceding powers of two, hence on a
density-one set.  On the exceptional \(O(\log N)\) transitions below \(N\),
the relative error still tends to zero exponentially.  Every carry of this
coherent sequence is again zero.

These sequences deliberately change the selected BBP numerators.  They are
not alternate truncations of pi and are not counterexamples to V1.  Their
precise consequence is narrower: denominator height, exact two-adic order,
positivity, an arbitrary fixed asymptotic jet, and even density-one exactness
of the cross-depth forcing do **not** force positive carry density.  An
unconditional continuation must use the exact selected numerator correlation
at every depth, or use a different route.

The companion finite replay has status `experiment`.  The inherited dated
source searches in the frozen inputs are `literature-checked`.  Nothing here
is `machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Normalized target and quantifiers

Canonical V1 asks whether

\[
 \forall m\geq0\ \forall(w_0,\ldots,w_{m-1})\in\{0,\ldots,9\}^m\
 \exists r\geq0\ \forall i<m:\quad d_{r+i}(\pi)=w_i.       \tag{2}
\]

Leading zeroes are allowed, occurrence is contiguous, and the empty word is
vacuous.  This is distinct from the false suffix reading and from the weaker
subsequence reading.

The frozen adjacent-BBP route needs, for every fixed \(P\geq1\), positive
lower density of the nonzero centered carries of \(q\pi\).  The lower-density
constant may depend on \(P\), while the empirical subsequence in the parent
matching criterion must eventually work for every \(P\).  Every construction
below fixes one arbitrary \(P\) first.  It is a method separator for that
one-row implication and does not exchange these quantifiers.

## 2. Exact rational recurrence and its zero-carry orbit

Retain the frozen notation

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_m=\sum_{k=0}^m{a(k)\over16^k}.                   \tag{3}
\]

For \(q=10^P-1\), set

\[
 x_n=q10^nB_{7n},\qquad
 \delta_n=q10^{n+1}(B_{7n+7}-B_{7n})>0.             \tag{4}
\]

Then \(x_{n+1}=10x_n+\delta_n\).  If \(z_n\) is the nearest integer,
\(e_n=x_n-z_n\in[-1/2,1/2)\), and
\(\gamma_n=z_{n+1}-10z_n\), this becomes

\[
                  e_{n+1}=10e_n+\delta_n-\gamma_n. \tag{5}
\]

The seven-term forcing has an exact first-order rational form.  Put

\[
 \lambda={10\over16^7}={5\over2^{27}},\qquad
 R(n)=\sum_{j=1}^7{a(7n+j)\over16^j}.               \tag{6}
\]

Then

\[
 \delta_n=10q\lambda^nR(n),\qquad
 {\delta_{n+1}\over\delta_n}
 =\lambda{R(n+1)\over R(n)}.                        \tag{7}
\]

Here \(R(n)\) is a positive rational function.  Thus clearing the fixed
rational-function denominators in (7) gives a first-order
polynomial-coefficient recurrence for \(\delta_n\).  This exact finite
difference is not a density theorem.

There is a unique bounded all-zero-carry solution of the exact forcing:

\[
 \boxed{t_n=-q10^n(\pi-B_{7n}).}                    \tag{8}
\]

Indeed, telescoping gives

\[
 t_{n+1}-10t_n
 =q10^{n+1}(B_{7n+7}-B_{7n})=\delta_n.              \tag{9}
\]

Also \(t_n<0\) and \(t_n\to0\).  The difference of two solutions of (9)
is \(c10^n\), so boundedness forces \(c=0\).  Since \(B_{7n}\) is rational
and pi is irrational, every \(t_n\) is irrational.  Consequently a rational
phase cannot follow the exact BBP forcing with zero carries forever.  This
recovers infinitude, not positive density: it says only that a rational
orbit must be reset infinitely often.

The exact leading scales are

\[
 \begin{aligned}
 t_n&=-{q\over3136}\lambda^n n^{-2}(1+O(n^{-1})),\\
 \delta_n&={q(10-\lambda)\over3136}
             \lambda^n n^{-2}(1+O(n^{-1})).
 \end{aligned}                                      \tag{10}
\]

For (10), use \(a(k)=15/(64k^2)+O(k^{-3})\),
\(\sum_{j\geq1}16^{-j}=1/15\), and
\(\sum_{j=1}^716^{-j}=(1-16^{-7})/15\).  The constants agree because
\(10(1-16^{-7})=10-\lambda\).

## 3. Exact-denominator pointwise separator

Let \(Q_n=Q_{n,P}\) be the denominator of \(x_n\) in lowest terms.  The
audited all-depth and odd-quotient results give, for fixed \(P\),

\[
 \log Q_n=(42+27\log2+o(1))n,qquad
 \omega(Q_n)=o(n).                                  \tag{11}
\]

Here is the denominator ledger.  At \(m=7n\), the reduced denominator of
\(B_m\) has two-primary order \(28n-v_2(7n+1)\) and odd logarithm
\((42+o(1))n\).  Multiplication by \(10^n\) removes exactly \(n\)
two-primary powers.  Multiplication by fixed \(q\) costs \(O_P(1)\) in the
odd logarithm, while cancellation by \(5^n\) costs only \(O(\log n)\),
because the exponent of 5 in the raw least-common denominator is
\(O(\log n)\).  This proves (11), as well as

\[
 v_2(Q_n)=27n-v_2(7n+1).                            \tag{12}
\]

Kanold's audited Jacobsthal bound says that every interval of
\(2^{\omega(Q_n)}\) consecutive integers contains an integer coprime to
\(Q_n\).  Therefore one may choose \(A_n\in\mathbb Z\) such that

\[
 (A_n,Q_n)=1,qquad
 \left|{A_n\over Q_n}-t_n\right|
 \leq {2^{\omega(Q_n)}+1\over Q_n}
 =\exp(-(42+27\log2-o(1))n).                        \tag{13}
\]

Write

\[
 \widetilde e_n={A_n\over Q_n},\qquad
 \eta_n=\widetilde e_n-t_n.                         \tag{14}
\]

Equations (10)--(13) imply
\(-1/2<\widetilde e_n<0\) for every sufficiently large \(n\).  Its nearest
integer is zero, so its centered carry is identically zero.  Define its
rational forcing by

\[
 \widetilde\delta_n=\widetilde e_{n+1}-10\widetilde e_n.
                                                               \tag{15}
\]

Using (9),

\[
 \widetilde\delta_n-\delta_n=\eta_{n+1}-10\eta_n
 =O\!\left(\exp(-(42+27\log2-o(1))n)\right).       \tag{16}
\]

Division by (10) proves

\[
 \boxed{
 {\widetilde\delta_n\over\delta_n}
 =1+O\!\left(\exp(-(42+\log5-o(1))n)\right).}      \tag{17}
\]

The \(O\)-term in (17) is signed; its absolute value has the displayed
bound.  In particular
\(\widetilde\delta_n>0\) eventually.  The cancellation in the exponent is

\[
 (42+27\log2)-(27\log2-\log5)=42+\log5.             \tag{18}
\]

This separator also matches the exact raw LCM bookkeeping.  Let

\[
 D_n=2^{27n}L_{7n},\qquad \Lambda_n={D_{n+1}\over D_n},\qquad
 \widetilde S_n=D_n\widetilde e_n.                  \tag{19}
\]

Since \(Q_n\mid D_n\), the number \(\widetilde S_n\) is integral.  Equations
(12) and \((A_n,Q_n)=1\) give

\[
                    v_2(\widetilde S_n)=v_2(7n+1). \tag{20}
\]

Moreover

\[
 \widetilde J_n=D_{n+1}\widetilde\delta_n\in\mathbb Z,
 \qquad
 \widetilde S_{n+1}
 =10\Lambda_n\widetilde S_n+\widetilde J_n.         \tag{21}
\]

Thus (19)--(21) have the exact denominator update, centered interval, and
two-adic numerator order of the frozen recurrence, while every carry is
zero.  The changed datum is \(\widetilde J_n\), specifically its exact
selected residue, even though (17) makes it exponentially close to \(J_n\)
after normalization.

## 4. A coherent density-one-exact separator

The pointwise construction changes the forcing at every transition.  A
stronger coherent construction changes it only sparsely.

Choose a sufficiently large power of two \(N_0\), and put
\(N_j=2^jN_0\).  At each reset depth choose the coprime rational in (13),
and write its error as \(\eta_{N_j}\).  For
\(N_j\leq n<N_{j+1}\), define

\[
 \overline e_n=t_n+10^{n-N_j}\eta_{N_j}.            \tag{22}
\]

Although written using the irrational \(t_n\), every \(\overline e_n\) is
rational.  At the left endpoint this is \(A_{N_j}/Q_{N_j}\); thereafter
(9) gives the rational recursion

\[
 \overline e_{n+1}=10\overline e_n+\delta_n
 \quad(N_j\leq n<N_{j+1}-1).                       \tag{23}
\]

Also \(Q_{N_j}\mid D_{N_j}\), \(D_n\mid D_{n+1}\), and
\(D_{n+1}\delta_n\in\mathbb Z\).  Induction therefore shows that the
reduced denominator of \(\overline e_n\) divides \(D_n\) at every depth.

The expanding reset error remains small throughout a doubled block:

\[
 \max_{N_j\leq n<N_{j+1}}
 |10^{n-N_j}\eta_{N_j}|
 \leq\exp(-(42+27\log2-\log10-o(1))N_j)=o(1).       \tag{24}
\]

Together with \(t_n\to0\), this puts every \(\overline e_n\) in
\((-1/2,1/2)\) after increasing \(N_0\).  Take zero as its nearest integer.
Every centered carry is then zero.

Define \(\overline\delta_n=\overline e_{n+1}-10\overline e_n\).  Equation
(23) says

\[
 \overline\delta_n=\delta_n
 \quad\text{unless }n=N_j-1\text{ for some }j\geq1. \tag{25}
\]

There are \(O(\log N)\) exceptional transitions below \(N\).  At an
exception \(n=N_{j+1}-1=2N_j-1\), (22) gives

\[
 \overline\delta_n-\delta_n
 =\eta_{N_{j+1}}-10^{N_{j+1}-N_j}\eta_{N_j}.        \tag{26}
\]

Consequently

\[
 \left|{\overline\delta_n-\delta_n\over\delta_n}\right|
 \leq\exp(-(c_0-o(1))n),                            \tag{27}
\]

where

\[
 c_0={42+27\log2-\log10\over2}
      -(27\log2-\log5)
    =21-14\log2+{\log5\over2}>12.1.                \tag{28}
\]

Thus the coherent forcing is eventually positive, is exponentially
relative-close everywhere, and is exactly the BBP forcing on a density-one
set.  Nonetheless its carry density is zero because every carry is zero.

The infinitely many exceptional resets are necessary.  If a rational
bounded zero-carry phase used the exact forcing after some final depth, its
difference from (8) would be \(c10^n\).  Boundedness would give \(c=0\),
making the rational phase equal the irrational \(t_n\).  The construction
shows that exponentially sparse resets already avoid that contradiction.

## 5. Why the direct height product loses the density factor

The separator above falsifies a general denominator-to-density lemma.  The
same obstruction appears directly in the height ledger.

Suppose the actual rational shadow has disjoint zero-carry blocks beginning
at \(n_i\) and having lengths \(h_i\).  Its centered phase has reduced
denominator \(Q_{n_i}\), so it is nonzero and

\[
                         |e_{n_i}|\geq Q_{n_i}^{-1}. \tag{29}
\]

Iteration across a zero block and the BBP tail give

\[
 |e_{n_i}|
 \leq {1\over2\,10^{h_i}}
 +{q5^{n_i}\over2^{27n_i}15(7n_i+1)^2}.             \tag{30}
\]

In the range allowed by the published irrationality measure, the second
term is eventually smaller than the first.  Multiplication of (29)--(30)
over \(K\) blocks can therefore yield at best

\[
 (\log10)\sum_{i=1}^K h_i
 \leq\sum_{i=1}^K\log Q_{n_i}+O_P(K)
 =(42+27\log2+o(1))\sum_{i=1}^Kn_i.                 \tag{31}
\]

Even if the zero blocks cover \(N-o(N)\) indices, the right side can be
\(O(KN)\).  Hence (31) is compatible with \(K=o(N)\), for example with
geometrically spaced resets.  Replacing the individual denominators by the
common nested denominator \(D_N\) only gives \(D_N^{-K}\), not \(D_N^{-1}\),
for a product of \(K\) nonzero rationals.  That exponent \(K\) is genuine.

Equivalently, multiplying the decimal approximations produces the integer
polynomial

\[
 \mathcal P_K(X)=\prod_{i=1}^K(q10^{n_i}X-z_{n_i}). \tag{32}
\]

It has degree \(K\) and

\[
 \log H(\mathcal P_K)=O_P\!\left(K+\sum_i n_i\right). \tag{33}
\]

The small-value exponent supplied by the gaps is only proportional to
\(\sum_i h_i\leq N\), whereas the ordinary height can be proportional to
\(KN\).  Thus the direct product has no favorable degree-height balance.
This ledger does not exclude an identity giving a new, genuinely shared
small-height factor; none is supplied by the LCM recurrence itself.

## 6. Fixed finite differences do not repair the loss

Equation (7) is already the strongest fixed-order recurrence for the scalar
forcing: it is first order after allowing rational coefficients.  The
irrational orbit (8) satisfies it with zero carries exactly.  Rationality is
a global boundary condition, not a local failure of that recurrence.

The coherent separator makes this quantitative.  Any fixed number of shifts
or finite differences of (25) agrees with the exact BBP identity away from
only \(O(\log N)\) neighboring indices below \(N\).  At every remaining
exception, (27) is exponentially small relative to the forcing.  Therefore
an averaging argument that uses only fixed-order differences, signs,
denominator heights, or finite asymptotic expansions cannot by itself yield
a positive Cesaro carry defect.  An exact arithmetic argument may still
detect the nonzero errors in (26); that exact selected-numerator information
is precisely what this separator does not retain.

## 7. Exact replay

The companion
[bbp_rational_phase_density_separator_20260813_check.py](bbp_rational_phase_density_separator_20260813_check.py)
has SHA-256
`72dfd913b3532bfe41e1df9a87ebbb3000f6fe1d179af4edbc0163d2a36cc3bc`.
It imports no prior checker and uses
only integers and `Fraction` for the structural assertions.  It:

- pins the canonical target and the frozen recurrence, valuation, and
  odd-denominator reports;
- reconstructs \(L_{7n},A_{7n},D_n,Q_{n,P}\) for \(P=1,2,4\);
- checks the exact forcing recurrence and its rational-function ratio;
- chooses coprime exact-\(Q_{n,P}\) separator phases from finite rigorous BBP
  tail proxies and verifies their centered range, denominator, raw-numerator
  two-adic valuation, integer recurrence, and zero carries;
- verifies exact positivity and the exact relative forcing errors through
  the retained finite depth; and
- constructs the power-of-two coherent separator, checks raw-denominator
  divisibility, identifies every exceptional reset, and verifies that all
  other transitions use the exact BBP forcing.

Replay from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_check.py
```

The retained run reports `status: PASS` and explicitly reports
`asserts_positive_carry_density: false` and `asserts_v1: false`.  Every
bounded row has status `experiment`; the asymptotic separator is the
`proof sketch` in Sections 2--6.

## Sharp handoff

The exact BBP forcing plus rationality does prove that nonzero carries occur
infinitely often, because the unique bounded all-zero solution (8) is
irrational.  The new separator shows why this does not scale to positive
density through height, product, or fixed-difference stability: rational
phases on the exact denominator grid can shadow (8) exponentially well, and
only \(O(\log N)\) exponentially small resets are enough to remain bounded
through depth \(N\).

What survives is fully explicit.  A successful continuation must use the
exact equality

\[
 J_{n,P}=q5^{n+1}H_n                               \tag{34}
\]

inside the selected centered representative at every depth, not just its
denominator, valuation, sign, size, asymptotic expansion, or density-one
occurrence.  No estimate controlling that exact cross-depth numerator
correlation is obtained here.  Positive carry density and canonical V1
remain a `conjecture`.
