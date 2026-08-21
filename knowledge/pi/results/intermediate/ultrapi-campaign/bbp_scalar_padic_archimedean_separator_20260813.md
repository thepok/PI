# BBP scalar accumulated phase: a p-adic/Archimedean separator

Audit date: **2026-08-13 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Provenance: the immutable local question was created from Marcel's request and
contains no external source URL; none is invented here.

## Normalized statement and scope

Canonical V1 says that for every \(m\geq0\) and every word
\((d_1,\ldots,d_m)\in\{0,\ldots,9\}^m\), there is an index \(n\geq0\)
at which those digits occur contiguously in the decimal expansion of pi.
Leading zeroes are allowed and the empty word is vacuous.  The assertion that
every infinite word occurs as a tail is false.  The assertion that every
infinite word occurs as a subsequence is equivalent to every digit recurring
infinitely often and remains open.

The independently audited one-character branch reduces V1 to

\[
 \liminf_{n\to\infty}\|R_n\|_{\mathbb T}=0,
 \qquad R_n=(10^n-16)B_n,                            \tag{1}
\]

where \(B_n\) is the rational BBP partial sum below.  This note attacks the
coefficient-specific accumulated phase left after the exact scalar recurrence

\[
 R_{n+2}-11R_{n+1}+10R_n=h_n.                       \tag{2}
\]

It does not replace (1) by normality, a metric statement, or a finite digit
search.

## Outcome and claim status

No proof of (1) or V1 was obtained.  Canonical V1 remains a `conjecture`.

The new conclusions have status `proof sketch`.

1. The exact four-pole tail has a two-scale coordinate \(G_n\).  Its first two
   Archimedean coefficients can be copied by one explicit rational four-pole
   proxy \(g_n\).  The resulting rational scalar orbit has the same two leading
   terms of both the \((5/8)^n\) and \(16^{-n}\) forcing scales as the actual
   BBP orbit.
2. The proxy also has, for every \(n\geq3\), exactly the same 2-primary
   denominator order as the actual rational phase \(R_n\).  It matches the
   two exceptional positive forcing values \(h_0,h_1\), has negative forcing
   from \(h_2\) onward, and is anchored at an integral initial phase.
   Nevertheless all its noninitial phases stay more than \(1/16\) from an
   integer.
3. Combining an arbitrary finite asymptotic jet of the same tail coordinate
   with the already audited Kanold lift gives a stronger asymptotic method
   separator.  For every prescribed finite jet order, the lifted tail retains,
   at every sufficiently large depth, the actual complete reduced denominator
   of \(B_n\), all the derived two-adic bits from the all-depth identity,
   eventual one-sided scalar forcing, and that finite two-scale jet, while its
   phases converge to circle distance \(1/3\), not zero.  A finite splice
   supplies the integral anchor and the exact \(h_0,h_1\); those spliced
   initial values are not claimed to retain the actual BBP denominators.

Thus neither exact dyadic order, the complete already-derived two-adic
coordinate, full denominator size, nor any fixed finite amount of
Archimedean forcing asymptotics can prove (1).  What survives this separator
is the **exact selected odd numerator coordinate**, equivalently a genuinely
non-asymptotic correlation among all four-pole tail values.  This is narrower
than the previous sign/summability separator and narrower than the previous
per-depth denominator separator.

The finite replay is an `experiment`.  The bounded source search is
`literature-checked` on the displayed date.  Nothing here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## 1. Exact BBP data and the scalar forcing

For \(k,n\geq0\), put

\[
 \begin{aligned}
 D(k)&=(2k+1)(4k+3)(8k+1)(8k+5),\\
 a(k)&={120k^2+151k+47\over D(k)},\\
 b_k&={a(k)\over16^k},\qquad
 B_n=\sum_{k=0}^n b_k,\qquad q_n=10^n-16,\\
 R_n&=q_nB_n.
 \end{aligned}                                      \tag{3}
\]

The parent audit proves the local identity

\[
 h_n=(10^{n+2}-16)b_{n+2}+(160-10^{n+1})b_{n+1},    \tag{4}
\]

with

\[
 h_0={20048317\over16336320}>0,\qquad
 h_1={258249\over17353600}>0,\qquad h_n<0\ (n\geq2). \tag{5}
\]

Let \(T_n=\pi-B_n\) and \(E_n=q_nT_n\).  Since the homogeneous sequence
\(q_n\pi\) is killed by the operator

\[
 (Lx)_n=11x_{n+1}-10x_n-x_{n+2},                   \tag{6}
\]

one has the exact identity

\[
                         h_n=(LE)_n.                \tag{7}
\]

This note does not use (7) as another derivative-orbit restatement.  It uses
the exact tail inside \(E_n\) to test which p-adic and Archimedean data can
possibly force the accumulated return.

## 2. A two-scale coordinate for the full tail

Set

\[
 \rho={5\over8},\qquad \sigma={1\over16},\qquad
 G_n=15\sum_{j\geq1}{a(n+j)\over16^j}.              \tag{8}
\]

Then, without approximation,

\[
 T_n={16^{-n}\over15}G_n,qquad
 E_n={\rho^n-16\sigma^n\over15}G_n.                \tag{9}
\]

Direct expansion of the four-pole rational function gives

\[
 a(n)={15\over64n^2}-{89\over512n^3}+O(n^{-4}).    \tag{10}
\]

The two exact geometric moments are

\[
 15\sum_{j\geq1}16^{-j}=1,qquad
 15\sum_{j\geq1}j16^{-j}={16\over15}.              \tag{11}
\]

Expanding \(a(n+j)\) and using (11) therefore gives

\[
 G_n={15\over64n^2}-{345\over512n^3}+O(n^{-4}).    \tag{12}
\]

The \(O(n^{-4})\) remainder is legitimate under the geometric sum: the
fixed-order rational expansion has a remainder bounded by a polynomial in
\(j\) times \(n^{-4}\), and every such polynomial is summable against
\(16^{-j}\).  Alternatively one may split at \(j=n\), use the uniform Taylor
bound below that point, and bound the remaining geometric tail directly.

Now define the explicit rational four-pole proxy

\[
 \boxed{
 g(n)={15(n+1)(8n-15)\over
 (2n+1)(4n+3)(8n+1)(8n+5)}.}                       \tag{13}
\]

It has exactly the same first two coefficients:

\[
 g(n)={15\over64n^2}-{345\over512n^3}+O(n^{-4}),
 \qquad G_n-g(n)=O(n^{-4}).                         \tag{14}
\]

The numerator in (13) was not fitted numerically.  The coefficient
\(-345/512\) follows from the exact first moment in (11), and solving for the
linear numerator gives
\((n+1)(120n-225)=15(n+1)(8n-15)\).  This factorization will also determine
the exact two-adic order.

## 3. An anchored coherent separator using the four poles

For \(n\geq3\), define

\[
 \varepsilon_n={\rho^n-16\sigma^n\over15}g(n)
 ={q_n g(n)\over15\,16^n}.                          \tag{15}
\]

Put \(\varepsilon_0=1/3\).  Let \(\varepsilon_1,\varepsilon_2\) be the
unique rational solution of

\[
 \begin{aligned}
 11\varepsilon_1-10\varepsilon_0-\varepsilon_2&=h_0,\\
 11\varepsilon_2-10\varepsilon_1-\varepsilon_3&=h_1.
 \end{aligned}                                      \tag{16}
\]

Exact reduction gives

\[
 \varepsilon_1={3095504003\over6847215375},qquad
 \varepsilon_2={25814204941\over62603112000}.       \tag{17}
\]

Define

\[
 R_n^*={q_n\over9}-\varepsilon_n,qquad
 h_n^*=R_{n+2}^*-11R_{n+1}^*+10R_n^*
       =11\varepsilon_{n+1}-10\varepsilon_n-\varepsilon_{n+2}. \tag{18}
\]

Every value is rational.  Moreover \(R_0^*=-2\), so the associated product
of rational roots of unity is correctly anchored.  Equations (16)--(17)
give \(h_0^*=h_0\) and \(h_1^*=h_1\); direct exact reduction gives
\(h_2^*<0\).

For \(n\geq3\), \(g(n)>0\), \(g(n)<n^{-2}\), and \(g\) is strictly
decreasing.  The last assertion follows after putting the difference over
its positive denominator.  Its numerator, divided by 15, is

\[
 \begin{aligned}
 P(n)={}&8192n^5+17920n^4-33792n^3-122248n^2\\
       &-115688n-36645.
 \end{aligned}
\]

Writing \(n=m+3\) turns this into

\[
 8192m^5+140800m^4+918528m^3+2753144m^2
 +3491560m+1045851>0.                               \tag{19}
\]

Also

\[
 {q_{n+1}\over16q_n}< {10\over11}\qquad(n\geq2).  \tag{20}
\]

Equations (15), (19), and (20) imply
\(\varepsilon_{n+1}/\varepsilon_n<10/11\) for \(n\geq3\), hence

\[
 h_n^*< -\varepsilon_{n+2}<0\qquad(n\geq3).         \tag{21}
\]

Together with the exact splice, the separator has the same sign pattern as
the actual forcing: \(h_0^*,h_1^*>0\) and \(h_n^*<0\) for every \(n\geq2\).
If \(C_n^*=R_{n+1}^*-10R_n^*\), then

\[
 C_n^*=16+10\varepsilon_n-\varepsilon_{n+1}\downarrow16
 \quad(n\geq2),                                    \tag{22}
\]

so it also retains the exact one-sided-total-variation architecture.

It nevertheless fails the required return uniformly.  Since
\(q_n/9\equiv1/3\pmod1\), equations (17) give

\[
 {1\over16}<\varepsilon_i-{1\over3}<{1\over2}
 \quad(i=1,2).                                      \tag{23}
\]

For \(n\geq3\), (13) gives

\[
 0<\varepsilon_n<{\rho^n\over15n^2}<{1\over24}.   \tag{24}
\]

Consequently

\[
 \boxed{\|R_n^*\|_{\mathbb T}>{1\over16}
        \quad\hbox{for every }n\geq1.}             \tag{25}
\]

Thus exact endpoint forcing, the all-depth sign pattern, rational roots of
unity, and the much sharper coefficient data below still do not imply the
partial-product return.

## 4. Exact agreement of the 2-primary phase orders

The independently audited all-depth BBP identity gives

\[
 v_2(B_n)=v_2(n+1)-4n.                              \tag{26}
\]

For the separator, (13) has

\[
 v_2(g(n))=v_2(n+1),                               \tag{27}
\]

because \(D(n)\), 15, and \(8n-15\) are odd.  More explicitly, for
\(n\geq3\),

\[
 R_n^*=q_n\left(
 {1\over9}-{(n+1)(8n-15)\over D(n)16^n}
 \right).                                          \tag{28}
\]

After taking the bracket over the common denominator \(9D(n)16^n\), its
numerator is

\[
 D(n)16^n-9(n+1)(8n-15).                           \tag{29}
\]

The two terms in (29) have unequal valuations \(4n\) and \(v_2(n+1)\).
Therefore

\[
 v_2(R_n^*)=v_2(q_n)+v_2(n+1)-4n=v_2(R_n)          \tag{30}
\]

for every \(n\geq3\).  In particular, the actual and separator roots of
unity have the same exact 2-primary order at every one of those depths.
Equation (25) proves that this exact order synchronization has no
Archimedean return consequence.

## 5. Agreement of both forcing scales

Let

\[
 \bar E_n={\rho^n-16\sigma^n\over15}g(n).
\]

For \(n\geq3\), this is exactly \(\varepsilon_n\).  Equations (9) and
(14) give the scale-separated estimate

\[
 E_n-\bar E_n
 =O(\rho^n n^{-4})+O(\sigma^n n^{-4}).              \tag{31}
\]

Applying the fixed finite operator \(L\) preserves both bounds.  Hence

\[
 \boxed{
 h_n-h_n^*
 =O(\rho^n n^{-4})+O(\sigma^n n^{-4}).}             \tag{32}
\]

Thus the actual and separator forcing have identical \(n^{-2}\) and
\(n^{-3}\) coefficients at each of the two exponential scales.  For
orientation, the leading coefficients are

\[
 h_n^{(\rho)}\sim-{225\over4096}{\rho^n\over n^2},
 \qquad
 h_n^{(\sigma)}\sim {2385\over1024}{\sigma^n\over n^2}. \tag{33}
\]

The separator is not merely another geometric perturbation: (13) uses the
same four linear poles, (30) matches every exact dyadic phase order, and
(32) matches two terms of both Archimedean scales.  It deliberately changes
the exact odd numerator data, which is precisely the information left alive.

## 6. Full-denominator lift and arbitrary finite asymptotic jets

The previous independently audited denominator work permits a stronger
general no-go.  Write the actual reduced BBP partial sum as

\[
 B_n={P_n\over2^{K_n}R_n^{\mathrm{odd}}},qquad
 K_n=4n-v_2(n+1),\qquad (P_n,2R_n^{\mathrm{odd}})=1. \tag{34}
\]

The corrected odd-quotient audit proves

\[
 \log R_n^{\mathrm{odd}}=(6+o(1))n,qquad
 \omega(R_n^{\mathrm{odd}})=o(n).                  \tag{35}
\]

Its Kanold lift is pointwise in the target value.  Therefore, for **any**
real target sequence \(\beta_n\), and at every sufficiently large depth, it
supplies rational values \(\widehat B_n\) with the same complete reduced
denominator as \(B_n\), and with all the derived two-adic bits preserved,
such that

\[
 |\widehat B_n-\beta_n|
 =O\left({2^{\omega(R_n^{\mathrm{odd}})}
             \over R_n^{\mathrm{odd}}}\right)
 =\exp((-6+o(1))n).                                 \tag{36}
\]

The target need not be constant; the proof chooses one nearby coprime
numerator independently at each depth.

The rational function \(a(n)\) has a full asymptotic expansion with rational
coefficients.  The geometric moments
\(15\sum j^r16^{-j}\) are rational for every fixed \(r\).  Consequently, for
every fixed \(J\geq2\), there is an explicit rational Laurent polynomial

\[
 g_J(n)=\sum_{r=2}^J c_r n^{-r},\qquad c_r\in\mathbb Q, \tag{37}
\]

such that \(G_n-g_J(n)=O(n^{-J-1})\).  Take

\[
 \bar\varepsilon_n^{(J)}
 ={\rho^n-16\sigma^n\over15}g_J(n),qquad
 \beta_n={1\over9}-{\bar\varepsilon_n^{(J)}\over q_n}. \tag{38}
\]

After an irrelevant finite splice, every quantity is rational and
\((q_n\beta_n)\bmod1\to1/3\).  Apply (36) with this varying \(\beta_n\), and
put \(\widehat R_n=q_n\widehat B_n\).  Since

\[
 6-\log 10>\log 16,                                 \tag{39}
\]

the lift error satisfies

\[
 |\widehat R_n-q_n\beta_n|
 \leq\exp(-(6-\log10+o(1))n)
 =o(16^{-n}n^{-A})                                  \tag{40}
\]

for every fixed \(A\).  It is smaller than even the secondary BBP scale.
Thus the scalar forcing of \(\widehat R_n\) agrees with the actual \(h_n\)
through the prescribed \(J\)-term expansion at **both** exponential scales,
while

\[
 \|\widehat R_n\|_{\mathbb T}\longrightarrow{1\over3}. \tag{41}
\]

Choose the lift only from a sufficiently large depth \(N\) onward.  Before
\(N\), take the Section 3 values, in particular through \(R_3^*\).  This
preserves the integral anchor and the exact \(h_0,h_1\), while the complete
denominator and derived-two-adic conclusions are asserted only for
\(n\geq N\).  The two forcing values that straddle the splice need not match
the BBP forcing and need not have its sign.  Since the dominant coefficient
in (33) is negative, the lifted forcing is one-sided for every sufficiently
large \(n\).  These finite qualifications affect neither (40) nor (41).

This arbitrary-finite-jet construction is a method separator, not a
counterexample to pi.  It changes the odd numerator coordinate selected by
the exact BBP sum.  Its consequence is precise: the eventual complete
denominator/derived-two-adic data together with any fixed finite forcing jet
do not, by themselves, imply (1).

## 7. What remains after the separator

The following routes are now explicitly insufficient.

- Repeating \(h_n<0\), summability, or the exact total variation.
- Using only that all phases are rational roots of unity whose orders grow.
- Synchronizing the exact 2-primary order with the two leading
  Archimedean scales.
- Eventually keeping the complete actual denominator and all currently
  derived two-adic bits while estimating only a fixed finite asymptotic jet.
- Applying more fixed-order differences merely to improve the decay order:
  Section 6 matches any prescribed finite order.

The next scalar attack must use data excluded by the construction.  The
cleanest surviving target is an estimate involving the actual odd numerator
coordinate \(c_n\bmod R_n^{\mathrm{odd}}\), coupled across depths by the
**exact**, not asymptotic, four-pole tail.  Equivalently, a successful
argument must rule out the persistent low-frequency Fejer bias through a
nonzero exponential-sum or correlation estimate for those selected odd
coordinates.  Denominator size or another finite tail expansion cannot do
that.

## 8. Dated literature and mathlib audit

Status: bounded `literature-checked` search on **2026-08-13 UTC**.

The primary sources and their checked boundaries are:

| source | exact relevance and boundary | local pin |
|---|---|---|
| Bailey--Borwein--Plouffe, [*On the Rapid Computation of Various Polylogarithmic Constants*](https://www.davidhbailey.com/dhbpapers/bbp.pdf) | Supplies the exact four-pole series.  It gives digit extraction in base 16, not a decimal prescribed return or the separator above. | SHA-256 `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4` |
| Lagarias, [*On the Normality of Arithmetical Constants*](https://arxiv.org/abs/math/0101055v2) | Gives the BBP/G-function dynamical framework and states the digit-distribution implication only under a dichotomy hypothesis.  It does not control the selected odd numerator coordinate. | SHA-256 `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` |
| Kanold, [*Über eine zahlentheoretische Funktion von Jacobsthal*](https://eudml.org/doc/161543) | The bound \(j(q)\leq2^{\omega(q)}\) is used only through the independently audited full-denominator lift.  It supplies no BBP return. | source scope audited in `bbp_short_orbit_return_independent_audit.md` |
| Bailey--Crandall, [*On the Random Character of Fundamental Constant Expansions*](https://www.davidhbailey.com/dhbpapers/bcrandom.pdf) | Its rational-perturbation mechanism remains conditional on Hypothesis A.  No coefficient-specific accumulated-phase theorem applicable here is proved. | SHA-256 `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` in the parent audit |

Fresh exact web/arXiv queries included `BBP partial sums denominators 2-adic
valuation pi`, `p-adic BBP formula pi denominators`, `hypergeometric BBP
partial sums congruences`, `BBP normality pi orbit fractional parts`, and
`lacunary sequence q^n alpha prescribed accumulation zero special constants
pi`.  They returned BBP-formula families, generic or metric lacunary results,
G-function rational-approximation results, and unrelated hypergeometric
supercongruences.  No primary source found in this bounded search proves (1),
an exponential-sum estimate for the selected odd coordinate, or the new
separator statement.

A repository/mathlib search for `padicValRat`, `padicValNat`, `denom`,
`Equidistrib`, `lacunary`, and `hypergeometric` found the existing AllMath
two-adic BBP track and generic valuation/density infrastructure, but no
theorem converting exact rational denominator order or a finite asymptotic
jet into a prescribed expanding-orbit return.  No new formal infrastructure
was invented.

## 9. Exact replay

The companion
[`bbp_scalar_padic_archimedean_separator_20260813_check.py`](bbp_scalar_padic_archimedean_separator_20260813_check.py),
SHA-256
`5c75450eda7f1998136a7e7583bb5c8925a791dfd8d1af4f76a57f94ec323350`,
uses `Fraction` arithmetic throughout.  It pins the
canonical target, the corrected scalar audit, the all-depth two-adic audit,
the short-orbit lift audit, the actual odd-quotient audit, and the primary BBP
and Lagarias sources.  It independently checks the Laurent coefficients,
geometric moment transfer, endpoint splice, all scalar identities, exact
2-primary order matching, the uniform gap, and finite full-denominator lifts.
It imports no prior checker.

Run:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_scalar_padic_archimedean_separator_20260813_check.py \
  --max-depth 90 --lift-depth 64
```

Retained output:

```text
status: PASS
claim_label: experiment
pinned_artifacts: 11
c0_scanned_text_artifacts: 11
asymptotic_coefficients: a=(15/64,-89/512),G=g=(15/64,-345/512)
coefficient_checks: 176
scalar_checks: 91
valuation_checks: 176
separator_checks: 90
full_denominator_lift_checks: 240
maximum_finite_lift_offset: 7
minimum_finite_lifted_gap: 0.333302668432
maximum_tail_proxy_n4_scaled_error: 0.905791897058
maximum_finite_coprime_distance: 7.485122789631
matched_actual_endpoint_forcing: h_0,h_1
uniform_unlifted_gap_lower_bound: 1/16
asserts_fixed_return: false
asserts_v1: false
all exact finite checks passed
```

Every finite loop is an `experiment`; the all-index statements are the
rational identities, asymptotic argument, and audited dependencies above.

## Sharp handoff

The fixed return (1) is still unproved.  The useful advance is a stronger
negative localization of the method: even a coherent rational scalar orbit
can share exact BBP endpoint forcing, the full sign pattern, both leading
two-scale jets, and every exact 2-primary phase order while avoiding zero by
a fixed gap.  After the audited lift, the same obstruction persists
asymptotically with the actual complete denominator, all derived two-adic
bits, and an arbitrarily long fixed asymptotic jet.  The finite anchor splice
is separate and is not claimed to preserve those denominator data.

Therefore the next scalar work should not spend effort on another
denominator bound, p=2 calculation, higher fixed difference, or finite
asymptotic expansion.  It should target the selected odd numerator residues
across depths—ideally a genuinely nonzero exponential-sum estimate or an
exact four-pole correlation that contradicts the persistent Fejer-bias
alternative.  No such estimate is proved here, so V1 remains a `conjecture`.
