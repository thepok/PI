# T72: metric calibration of the coupled terminal decimal ray

Claim label: **proof sketch**.  The T55, T61, and T67 interfaces cited below
are machine-checked.  The metric argument is a paper-level proof sketch, with
finite identities replayed by `verify_note.py`; it has not been formalized in
Lean.

## 1. Provenance, normalized scope, and exclusions

The immutable statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.  It records no external
source URL: the question was formulated by this system on 2026-07-22.  A
byte-exact copy is delivered as `canonical_statement.txt`; its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical question concerns the single fixed value `pi`.  This note does
not answer it.  Its probability space is

\[
 ([0,1),\mathcal B,\lambda),\qquad
 x_j(\alpha)=10^j\alpha\pmod 1,\quad j\geq0,                 \tag{1.1}
\]

where one value of `alpha` supplies **every** phase.  No phases are replaced
by independent random variables.  This is sibling A14 in the canonical file.

The canonical quantifiers remain

\[
 \forall A\geq1\ \exists n_0\geq1\ \forall n\geq n_0\
 \exists N\geq1:\quad A n Q_\pi(n,N)\leq N^2,              \tag{1.2}
\]

with ordered pairs, diagonal included, and strict circle distance.  Nothing
below changes or proves (1.2).  There is no conclusion about `pi`, C1, C2,
normality, FSFS for `pi`, decimal factor complexity, or pair correlation.

The checked inputs and their exact roles are:

| item | SHA-256 | role used here |
|---|---|---|
| T55 `SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | terminal shell, weights, coefficients, endpoint budget, and strict threshold |
| T61 `DirectLabelAdjacentPhaseVariance.lean` | `2eaecb2df11027d6ed5911a16fe571b042afbe42e18daf57eaaffc668f74dbdb` | direct frequencies, exact remainder, adjacent variance, and threshold implication |
| T67 `TerminalRayStrength.lean` | `e9fc18166d2b31c52adbfe73bfcbb10ccd8d93c785fb39144b88db75ed493dff` | empirical defect identity, primitive rays, qualified UPRID, and UPRID-to-threshold implication |

The T60 note is unverified.  It was used only to identify notation worth
checking; no T60 assertion is a premise.

Exact audit locators in the accumulated checked library are:

| module | declarations / source lines |
|---|---|
| T26 `SharedResonanceChain.lean` (`7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2`) | `GeometricResonanceChain.nodeCoefficient`, lines 142--146; `nodeResidual`, lines 149--152 |
| T38 `FixedStratumFejerSpike.lean` (`853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014`) | `commonDepth`, lines 35--40; `stratumDelta`, lines 336--346; `stratumOrder`, lines 349--354; `FSFS`, lines 399--411 |
| T55 | `terminalShell`, lines 225--230; `terminalCorrelation`, lines 292--295; generic Fejer identity, lines 541--548; top-shell premise, lines 568--578 |
| T61 | direct variance, lines 116--126; exact margin, lines 344--353; mass-minus-half-variance identity, lines 295--300 |
| T67 | empirical endpoint identity, lines 90--128; qualified UPRID, lines 181--192; UPRID-to-threshold, lines 271--284 |

T38 and T26 are transitive checked dependencies of T55.  The report does not
redeclare their objects; equations (3.2)--(3.5) are a line-by-line audit of
these locators under the explicitly marked random sibling substitution.

### Quantifier ambiguities resolved

1. All natural parameters, chain skeletons, and candidate families are fixed
   before `alpha` is sampled.  An `alpha`-dependent choice from an unrestricted
   family is not covered.
2. A random analogue replaces every occurrence of `pi` in a node coefficient
   by the same `alpha`; it does not randomize separate labels.
3. `ell` is both the T55 depth and the number of orbit samples in its block.
   The T67 empirical sample length is the incoming chain shift `s`, a different
   parameter.
4. `R=ceil(delta^(-1))` is the Fejer order and `H=R-1` is the positive Fourier
   cutoff.  The terminal shell is exactly `(floor(H/10),H]`.
5. The almost-everywhere statement is for each predetermined schedule.  It is
   not a single full-measure set uniform over all schedules.

## 2. Exact-form finite T55 objects

T55's public chain predicates are typed with `initialCoefficient h r`, which
contains `Real.pi`.  They cannot literally be instantiated with a random
`alpha`.  Here **exact-form** means that every finite sum, shell, weight,
cutoff, endpoint, and normalization is copied from the checked interface after
the explicitly stated sibling substitution `pi -> alpha`.  The generic finite
identities used below hold for every real `beta`; no randomized Lean chain is
asserted.

Write

\[
 e(y)=\exp(2\pi i y),\qquad
 F_H(y)=\frac1{H+1}\left|\sum_{r=0}^{H}e(ry)\right|^2.
                                                                    \tag{2.1}
\]

For `R>=1`, put `H=R-1` and

\[
 w_R(u)=1-u/R,\quad
 \mathcal S_H=\{1,\ldots,\lfloor H/10\rfloor\},\quad
 \mathcal T_H=\{u:\lfloor H/10\rfloor<u\leq H\}.             \tag{2.2}
\]

These are literally T55's `triangularWeight`, `pairingSourceShell`, and
`terminalShell`.  For `ell>=1`, define

\[
 D_j=10^\ell-10^j\quad(0\leq j<\ell),\qquad
 B_{\beta,\ell}(u)=\sum_{j=0}^{\ell-1}e(\beta uD_j).           \tag{2.3}
\]

Let

\[
 \nu_{10}(u)=\max\{a\geq0:10^a\mid u\}.
\]

Induction in T55's displayed predecessor recurrence gives, independently of
the T60 note,

\[
 \Gamma_{\beta,\ell,R}(u)=
 \sum_{a=0}^{\nu_{10}(u)}w_R(u/10^a)
 e\!\left((u/10^a-u)10^\ell\beta\right).                    \tag{2.4}
\]

Indeed, the `a=0` term is `w_R(u)`.  One recurrence step multiplies the old
coefficient at `u/10` by `e(-9(u/10)10^ell beta)`; its exponent telescopes to
the exponent in (2.4).  Consequently the exact-form T55 terminal correlation is

\[
 T_{\ell,R}(\beta)=
 \sum_{u\in\mathcal T_H}\Gamma_{\beta,\ell,R}(u)
 B_{\beta,\ell}(u)                                           \tag{2.5}
\]

and has the completely flattened coupled expansion

\[
 \boxed{T_{\ell,R}(\beta)=
 \sum_{u\in\mathcal T_H}\sum_{a=0}^{\nu_{10}(u)}
 \sum_{j=0}^{\ell-1}w_R(u/10^a)e(\beta n_{u,a,j}),}          \tag{2.6}
\]

where

\[
 n_{u,a,j}=10^\ell(u/10^a)-10^j u\in\mathbb Z.              \tag{2.7}
\]

No two labels in (2.6) are identified, even when their numerical frequencies
coincide.

The endpoint budget retained by T55 is

\[
 B_{\rm end}(\beta,\ell,R)=
 2\sum_{u\in\mathcal S_H}|\Gamma_{\beta,\ell,R}(u)|.         \tag{2.8}
\]

The random sibling's exact-form top-shell premise is

\[
 \boxed{\Re T_{\ell,R}(\beta)>
 \frac{\ell}{8R\delta^2}-\frac\ell2+B_{\rm end}(\beta,\ell,R).}
                                                                    \tag{2.9}
\]

The generic checked identities `stratumFejerSum_eq_endpoint_add_topShell` and
`norm_endpointSum_le_endpointBudget` give

\[
 S_{\ell,H}(\beta)=\ell+2\Re(E_{\rm end}(\beta)+T_{\ell,R}(\beta)),
 \qquad \Re E_{\rm end}(\beta)\geq-B_{\rm end}(\beta,\ell,R). \tag{2.10a}
\]

Substituting (2.9) in (2.10a) proves, for every real `beta`, the strict Fejer
threshold

\[
 \boxed{\frac{\ell}{4R\delta^2}<
 S_{\ell,H}(\beta):=\sum_{j=0}^{\ell-1}F_H(\beta D_j).}      \tag{2.10}
\]

The terminal theorem below refutes eventual (2.10), and hence eventual (2.9),
on an explicit random-orbit schedule.

## 3. Chain and schedule quantifiers

For comparison with the checked types, fix natural data

\[
 h,r,M,D,K,d\geq0,\quad \sigma=(\sigma_0,\ldots,\sigma_{d-1}),
 \quad k<d.                                                   \tag{3.1}
\]

Assume `h,r>=1`, every `sigma_i>=1`, and fix this data before sampling
`alpha`.  The randomized initial and node coefficients are

\[
 c_\alpha=h(10^r-1)\alpha,\qquad
 \beta_{\alpha,k}=C_k\alpha,
\quad C_k=h(10^r-1)\prod_{i<k}(10^{\sigma_i}-1)\in\mathbb N_{\geq1}.
                                                                    \tag{3.2}
\]

The outgoing adjacent factor is

\[
 U_k=10^{\sigma_k}-1\geq9.                                  \tag{3.3}
\]

For `1<=ell<min(M-sum_{i<k}sigma_i,M-sum_{i<=k}sigma_i)`, the
exact-form T38 values are

\[
 \delta_{k,\ell}=\min\left(E(D,k),
   \min\left(E(D,k+1)/U_k,\frac1{2U_k10^\ell}\right)\right),
 \qquad R_{k,\ell}=\lceil\delta_{k,\ell}^{-1}\rceil,        \tag{3.4}
\]

where `E(D,k)` is T38's positive `nodeErrorThreshold`.  Thus

\[
 0<\delta_{k,\ell}\leq\frac1{2U_k10^\ell},\qquad
 H_{k,\ell}=R_{k,\ell}-1.                                  \tag{3.5}
\]

Equations (3.2)--(3.5) copy the corresponding node coefficient, adjacent
factor, common-depth condition, stratum delta, and stratum order after the
random sibling substitution.  They do not construct the checked
`GeometricResonanceChain`, whose type fixes `pi`.  Intersecting with any
separately defined random-chain resonance event can only decrease every
exceptional-set bound below.

For T61/T67, fix `k+1<d`, set `q=k+1`, and distinguish:

\[
 s=\sigma_k\quad\hbox{(incoming empirical sample length)},
 \qquad U_q=10^{\sigma_q}-1\quad\hbox{(outgoing delta factor)}. \tag{3.6}
\]

The preceding and adjacent coefficients are `C_k alpha` and
`C_q alpha=(10^s-1)C_k alpha`; T61 at node `q` uses
`delta_(q,ell),R_(q,ell)`, whose third minimum contains `U_q`, not the
incoming factor.

## 4. Exact Haar moments of the Fejer top-shell statistic

Let `alpha` be uniform, `C` be any fixed nonzero integer, `ell>=1`, and
`H>=0`.  The Fourier expansion

\[
 F_H(y)=\sum_{|u|\leq H}\left(1-\frac{|u|}{H+1}\right)e(uy) \tag{4.1}
\]

and `int e(n alpha) d alpha = 1_(n=0)` give

\[
 \boxed{\mathbb E S_{\ell,H}(C\alpha)=\ell.}                 \tag{4.2}
\]

This uses linearity, not independence.

### 4.1 Complete equal-frequency classification

For `0<=j<j'<ell`, put

\[
 s_0=\ell-j,\quad t_0=\ell-j',\quad g=\gcd(s_0,t_0),
\]

\[
 A_{j,j'}=\frac{10^{s_0}-1}{10^g-1},\qquad
 B_{j,j'}=10^{j'-j}\frac{10^{t_0}-1}{10^g-1}.               \tag{4.3}
\]

The repunit gcd identity gives

\[
 \gcd(D_j,D_{j'})=10^j(10^g-1),\quad
 \gcd(A_{j,j'},B_{j,j'})=1.                                \tag{4.4}
\]

Therefore every positive collision, and no other one, is

\[
 \boxed{uD_j=u'D_{j'}\iff
 u=qB_{j,j'},\quad u'=qA_{j,j'}\quad(q\geq1).}               \tag{4.5}
\]

For `j=j'`, equality means `u=u'`.  If `u=10^b v`, `10 not divides v`, then

\[
 \nu_{10}(uD_j)=b+j.                                        \tag{4.6}
\]

Thus an equality requires matching decimal valuations and matching primitive
cofactors.  It never occurs twice on one primitive ray.  The first
off-diagonal example is exactly T55's

\[
 10(10^2-1)=11(10^2-10)=990.                                \tag{4.7}
\]

### 4.2 Exact variance and tails

Orthogonality and (4.5) give

\[
 \boxed{\begin{aligned}
 \operatorname{Var}S_{\ell,H}(C\alpha)
 ={}&\frac{\ell H(2H+1)}{3(H+1)}\\
 &+4\sum_{0\leq j<j'<\ell}
 \sum_{q=1}^{\lfloor H/A_{j,j'}\rfloor}
 \left(1-\frac{qB_{j,j'}}{H+1}\right)
 \left(1-\frac{qA_{j,j'}}{H+1}\right).
 \end{aligned}}                                             \tag{4.8}
\]

For `Q=floor(H/A)`, an inner sum is exactly

\[
 Q-\frac{(A+B)Q(Q+1)}{2(H+1)}
 +\frac{ABQ(Q+1)(2Q+1)}{6(H+1)^2}.                          \tag{4.9}
\]

Since a proper divisor `g` of `s_0` is at most `s_0/2`, one has
`A_(j,j')>=10^(s_0/2)`.  Hence, with

\[
 C_{10}=\frac4{10(1-10^{-1/2})^2}<0.856,
\]

\[
 \operatorname{Var}S_{\ell,H}
 \leq\frac{\ell H(2H+1)}{3(H+1)}+C_{10}H.                  \tag{4.10}
\]

Consequently, for every `t>0`,

\[
 \lambda(|S_{\ell,H}-\ell|\geq t)
 \leq \operatorname{Var}(S_{\ell,H})/t^2,                 \tag{4.11}
\]

and nonnegativity also gives, for `T>0`,

\[
 \boxed{\lambda(S_{\ell,H}>T)\leq
 \min\left(1,\frac\ell T,
 \frac{\operatorname{Var}S_{\ell,H}}{(T-\ell)^2}
 \ \text{when }T>\ell\right).}                            \tag{4.12}
\]

This displays both the covariance-sensitive and covariance-free tails.

## 5. Moments of the exact-form terminal correlation

Equation (2.6) also permits an exact moment audit.  For a finite real-weighted
polynomial

\[
 P(\alpha)=\sum_{\lambda\in L}a_\lambda e(Cn_\lambda\alpha),
 \quad C\in\mathbb Z\setminus\{0\},                         \tag{5.1}
\]

define the equal-frequency class mass

\[
 A_m=\sum_{\lambda:n_\lambda=m}a_\lambda.                   \tag{5.2}
\]

Haar orthogonality gives the exact universal formulas

\[
 \mathbb EP=A_0,\qquad
 \mathbb E|P-A_0|^2=\sum_{m\ne0}A_m^2,\qquad
 \operatorname{Var}(\Re P)=\frac12\sum_{m\geq1}(A_m+A_{-m})^2.
                                                                    \tag{5.3}
\]

Apply this to (2.6), with labels `(u,a,j)` and weights `w_R(u/10^a)`.
The zero classes are exactly

\[
 n_{u,a,j}=0\iff a+j=\ell.                                  \tag{5.4}
\]

Therefore

\[
 \boxed{\mathbb ET_{\ell,R}(C\alpha)=
 \sum_{u\in\mathcal T_H}
 \sum_{a=1}^{\min(\ell,\nu_{10}(u))}w_R(u/10^a).}           \tag{5.5}
\]

Its complex centered second moment and real-part variance are exactly (5.3)
with these class masses.  This is a finite displayed formula, not an
independence approximation.

For the promised decimal-valuation classification, write `u=10^b v` with
`10 not divides v`.  For a nonzero terminal frequency,

\[
 |n_{u,a,j}|=
 v10^{b+\min(j,\ell-a)}(10^{|\ell-a-j|}-1),                 \tag{5.6}
\]

and its sign is the sign of `ell-a-j`.  Thus two labels contribute covariance
to `Re T` exactly when the decimal exponents in (5.6) agree and the remaining
primitive cofactors agree; opposite signs are combined by `A_m+A_(-m)`.
The separate zero-frequency predecessor classes are exactly (5.4).  An
independent-phase model would wrongly erase both kinds of coupling.

For completeness, each coefficient in the endpoint budget satisfies

\[
 \mathbb E\Gamma_{C\alpha,\ell,R}(u)=w_R(u),\qquad
 \mathbb E|\Gamma_{C\alpha,\ell,R}(u)|^2
 =\sum_{a=0}^{\nu_{10}(u)}w_R(u/10^a)^2,                    \tag{5.7}
\]

because its internal frequencies are distinct.  Hence its exact expectation
and useful bounds are

\[
 \mathbb EB_{\rm end}=
 2\sum_{u\in\mathcal S_H}\int_0^1|\Gamma_{C\alpha,\ell,R}(u)|d\alpha,
                                                                    \tag{5.8}
\]

\[
 2\sum_{u\in\mathcal S_H}w_R(u)
 \leq\mathbb EB_{\rm end}
 \leq2\sum_{u\in\mathcal S_H}
 \left(\sum_{a=0}^{\nu_{10}(u)}w_R(u/10^a)^2\right)^{1/2}. \tag{5.9}
\]

Also `0<=B_end<=2 sum_(u in S_H) sum_(a<=nu10(u)) w_R(u/10^a)`, so its
variance is at most the square of that deterministic upper bound.  The norm
prevents a simpler orthogonality identity; (5.8) is the exact expectation,
not an omitted term.

## 6. Exact-form T61/T67 UPRID statistic

At a preceding node coefficient `beta_0=C alpha`, let `s>=1` be the incoming
shift and

\[
 \widehat\mu_{C\alpha,s}(m)=\frac1s\sum_{r=0}^{s-1}e(m10^rC\alpha),
\quad d_{C\alpha,s}(m)=\widehat\mu(10m)-\widehat\mu(m).      \tag{6.1}
\]

T67's checked endpoint identity is

\[
 s d_{C\alpha,s}(m)=e(10^s mC\alpha)-e(mC\alpha).           \tag{6.2}
\]

For `m_(u,j)=uD_j`, define

\[
 Z_{u,j}(\alpha)=s|d_{C\alpha,s}(m_{u,j})|,
\quad
 V_{s,\ell,R}(\alpha)=
 \sum_{u\in\mathcal T_H}\sum_{j<\ell}w_R(u)Z_{u,j}(\alpha)^2.
                                                                    \tag{6.3}
\]

This is the exact-form random sibling of T61's `directAdjacentVariance` after
T67's rewrite.  Put

\[
 A_{\ell,R}=\ell\sum_{u\in\mathcal T_H}w_R(u)               \tag{6.4}
\]

and let `P_rem(beta_1,ell,R)` be (2.6) restricted to `a>=1`; this is T61's
checked exact `predecessorRemainder`.  With

\[
 \beta_1=(10^s-1)C\alpha,
\]

The random sibling of T67's exact-remainder margin is

\[
 \mathcal M(\alpha)=\ell+2A_{\ell,R}
 -2|P_{\rm rem}(\beta_1,\ell,R)|
 -2B_{\rm end}(\beta_1,\ell,R)
 -\frac{\ell}{4R\delta^2}.                                  \tag{6.5}
\]

The random sibling's qualified UPRID event, with no quantifier suppressed, is

\[
 \boxed{\exists\eta\in\mathbb R:\quad
 0\leq\eta,\quad A_{\ell,R}\eta^2<\mathcal M(\alpha),\quad
 \forall u\in\mathcal T_H\ \forall j<\ell:\ Z_{u,j}(\alpha)\leq\eta.}
                                                                    \tag{6.6}
\]

For the interface-shaped schedule, use `C=C_k`, `s=sigma_k`, and the shell,
delta, and order at `q=k+1`, exactly as in Section 3.  This matches every
finite T67 argument but is not asserted to inhabit T67's fixed-`pi` chain type.

The exact-form UPRID implication needs no chain axiom.  From (6.6),

\[
 V\leq A_{\ell,R}\eta^2<\mathcal M(\alpha).                 \tag{6.6a}
\]

The generic T61 identities give

\[
 \Re C_{\rm direct}=A_{\ell,R}-V/2,\qquad
 T=C_{\rm direct}+P_{\rm rem}.                              \tag{6.6b}
\]

Combining (6.6a)--(6.6b), `Re P_rem>=-|P_rem|`, and (2.10a)
gives

\[
 S\geq\ell-2B_{\rm end}+2A_{\ell,R}-V-2|P_{\rm rem}|
 >\frac\ell{4R\delta^2}.                                    \tag{6.6c}
\]

Thus (6.6) implies the exact-form strict threshold by direct algebra.  The
checked T67 theorem proves the same implication inside its fixed-`pi` type; it
is used here as an interface audit, not as a randomized instantiation.

### 6.1 Expectation, covariance, and variance

On the schedules considered here, (3.5) gives `R>=180`, so the shell and
labeled domain are nonempty.  For every label, `m_(u,j)>0`, so with
`K_s=10^s-1`,

\[
 Z_{u,j}=2|\sin(\pi K_s C m_{u,j}\alpha)|.
\]

Multiplication by the nonzero integer `K_s C m_(u,j)` preserves Haar measure.
Thus each individual label has the exact law

\[
 \mathbb EZ_{u,j}=\frac4\pi,\quad
 \mathbb EZ_{u,j}^2=2,\quad
 \operatorname{Var}Z_{u,j}=2-\frac{16}{\pi^2},              \tag{6.7a}
\]

\[
 \lambda(Z_{u,j}\leq\eta)=\frac2\pi\arcsin(\eta/2)
 \quad(0\leq\eta\leq2).                                    \tag{6.7b}
\]

For the UPRID maximum `Z_max=max_(u in T_H,j<ell) Z_(u,j)`, its exact coupled
moments are the one-dimensional integrals

\[
 \mathbb EZ_{\max}=\int_0^1\max_{u,j}Z_{u,j}(\alpha)d\alpha,
 \quad
 \operatorname{Var}Z_{\max}=\int_0^1Z_{\max}(\alpha)^2d\alpha
 -(\mathbb EZ_{\max})^2,                                    \tag{6.7c}
\]

with `4/pi<=E Z_max<=2` and
`lambda(Z_max<=eta)<=2 pi^(-1) arcsin(eta/2)`.  Equality is not asserted:
the labels are coupled through their integer frequencies.

Let

\[
 h_0=\lfloor H/10\rfloor,\quad L=h_0+1,\quad N_H=H-h_0.
\]

Then

\[
 \sum_{u\in\mathcal T_H}w_R(u)=\frac{N_H(N_H+1)}{2R},
\quad A_{\ell,R}=\frac{\ell N_H(N_H+1)}{2R}.                \tag{6.7}
\]

Since `10^s-1` is nonzero and not divisible by ten,

\[
 \boxed{\mathbb EV_{s,\ell,R}=2A_{\ell,R}
 =\frac{\ell N_H(N_H+1)}R.}                                \tag{6.8}
\]

For individual squared defects `X_(u,j)=Z_(u,j)^2`, direct expansion gives

\[
 \boxed{\operatorname{Cov}(X_{u,j},X_{u',j'})
 =2\,\mathbf1_{uD_j=u'D_{j'}}.}                             \tag{6.9}
\]

They are generally dependent, despite being uncorrelated outside the exact
collision classes.  Multiplication by `10^s-1` neither changes equality nor
the decimal valuation `nu10(u)+j`.

Using (4.3), a cross-depth collision lies in the terminal shell exactly when

\[
 \left\lceil\frac L{B_{j,j'}}\right\rceil\leq q\leq
 \left\lfloor\frac H{A_{j,j'}}\right\rfloor.                \tag{6.10}
\]

Thus

\[
 \boxed{\begin{aligned}
 \operatorname{Var}V_{s,\ell,R}={}&
 \frac{\ell N_H(N_H+1)(2N_H+1)}{3R^2}\\
 &+4\sum_{0\leq j<j'<\ell}
 \sum_{q=\lceil L/B_{j,j'}\rceil}^{\lfloor H/A_{j,j'}\rfloor}
 \left(1-\frac{qB_{j,j'}}R\right)
 \left(1-\frac{qA_{j,j'}}R\right),
 \end{aligned}}                                             \tag{6.11}
\]

where a reversed inner interval contributes zero.  For `p<=Q`, that inner sum
is

\[
 Q-p+1-\frac{A+B}{2R}[Q(Q+1)-(p-1)p]
 +\frac{AB}{6R^2}[Q(Q+1)(2Q+1)-(p-1)p(2p-1)].               \tag{6.12}
\]

The same count as Section 4 gives

\[
 \operatorname{Var}V\leq
 \frac{\ell N_H(N_H+1)(2N_H+1)}{3R^2}+C_{10}H,             \tag{6.13}
\]

and therefore

\[
 \lambda(|V-2A_{\ell,R}|\geq t)\leq\operatorname{Var}(V)/t^2.
                                                                    \tag{6.14}
\]

The remainder polynomial in (6.5) has exact expectation, complex second
moment, and real variance from (5.3) after restricting to `a>=1`.  Its norm
has exact expectation `int_0^1 |P_rem|` and upper bound
`sqrt(E|P_rem|^2)`.  Thus every random term in the UPRID margin has an explicit
finite moment formula or displayed one-dimensional integral.

## 7. Almost-everywhere refutation of the terminal schedule

### Theorem 7.1 (predetermined coupled top-shell schedule)

For each `t>=1`, fix before sampling `alpha`:

* an integer `C_t != 0`;
* a depth `ell_t>=1`;
* a real `delta_t>0` and integer `U_t>=9` such that
  `delta_t<=1/(2 U_t 10^(ell_t))`;
* `R_t=ceil(delta_t^(-1))` and `H_t=R_t-1`.

Let

\[
 E_t=\left\{\alpha:\frac{\ell_t}{4R_t\delta_t^2}<
 \sum_{j=0}^{\ell_t-1}F_{H_t}
   (C_t\alpha(10^{\ell_t}-10^j))\right\}.                  \tag{7.1}
\]

Then

\[
 \boxed{\lambda(E_t)\leq4R_t\delta_t^2
 \leq4\delta_t+4\delta_t^2
 \leq\frac2{U_t10^{\ell_t}}+
       \frac1{U_t^2 10^{2\ell_t}}.}                         \tag{7.2}
\]

If the last bounds are summable, then for Lebesgue-almost every `alpha`, only
finitely many events `E_t` occur.  Moreover, for every `T>=1`,

\[
 \boxed{\lambda(\exists t\geq T:E_t)\leq
 \sum_{t\geq T}\left(\frac2{U_t10^{\ell_t}}+
 \frac1{U_t^2 10^{2\ell_t}}\right).}                       \tag{7.3}
\]

**Proof.**  Every `C_t(10^(ell_t)-10^j)` is a nonzero integer, so Haar
orthogonality gives expectation `ell_t` by (4.2), while the Fejer statistic is
nonnegative.  Markov at the literal threshold gives the first inequality.
Since `R_t=ceil(1/delta_t)`,
`R_t<=1/delta_t+1`; substitution gives the next two inequalities.  The first
Borel--Cantelli lemma proves the almost-everywhere assertion.  It requires no
independence.  The union bound proves (7.3).  QED.

The sharper, fully coupled alternative is also explicit:

\[
 \lambda(E_t)\leq
 \frac{\operatorname{Var}S_{\ell_t,H_t}}
 {(\ell_t/(4R_t\delta_t^2)-\ell_t)^2}                       \tag{7.4}
\]

whenever the denominator is positive, with the exact variance (4.8).

### 7.2 Exact-form chain schedule

The theorem applies to every predetermined interface-shaped chain-skeleton schedule by
taking `C_t=C_(k_t)` and `U_t=U_(k_t)` from (3.2)--(3.4).  For T61 UPRID at
`q_t=k_t+1`, take `C_t=C_(q_t)` and the **outgoing** `U_t=U_(q_t)`.

An entirely explicit infinite interface schedule is:

\[
 h=r=D=K=1,\quad d=2,\quad k=0,\quad q=1,\quad
 \sigma=[2,3],\quad M_t=t+6,\quad\ell_t=t.                  \tag{7.5}
\]

The shifts are distinct, at least one, avoid `{r}={1}`, and have sum five;
`K<=M_t-5`.  At node `q=1`, the residuals are `t+4` and `t+1`, so
`1<=ell_t=t<commonDepth=t+1`.  The incoming empirical length is `s=2`,
the adjacent coefficient is

\[
 C_q=1(10^1-1)(10^2-1)=891,                                 \tag{7.6}
\]

and the outgoing factor is `U_q=10^3-1=999`.  In exact interface form,

\[
 \delta_t=\min\left(E(1,1),
   \min\left(E(1,2)/999,\frac1{1998\,10^t}\right)\right),
 \quad R_t=\lceil\delta_t^{-1}\rceil,\quad H_t=R_t-1.       \tag{7.7}
\]

Thus `H_t>=1998*10^t-1`: shell size grows at least exponentially, top-shell
depth and T55 sample length equal `t`, and the T67 incoming sample length is
the fixed value two.  Equations (7.2)--(7.3) become

\[
 \lambda(E_t)\leq\frac2{999\,10^t}+
 \frac1{999^2 10^{2t}},                                    \tag{7.8}
\]

\[
 \lambda(\exists t\geq T:E_t)\leq
 \frac{2\,10^{1-T}}{8991}+
 \frac{100\,10^{-2T}}{98\,802\,099}.                      \tag{7.9}
\]

The combinatorial fields of the chain skeleton are fixed.  No checked random
chain is claimed.  Intersecting with any additional random-chain resonance
event would not enlarge (7.8).  Hence almost every `alpha` eventually has no
exact-form random T55 threshold on this fixed skeleton.

The generic algebra following (2.9) and (6.6) says that the random exact-form
top-shell and UPRID events each imply the same threshold.  Taking contrapositives,
for almost every `alpha`, on schedule (7.5)--(7.7):

\[
 \boxed{\text{the exact-form random T55 top-shell premise and
 T61-qualified UPRID are both
 eventually false.}}                                       \tag{7.10}
\]

This is a refutation of the proposed eventual random-baseline schedule, not a
claim that no exceptional `alpha` or no adaptively selected chain can satisfy
one finite threshold.

### 7.3 Admissible family growth

If a predetermined finite family `C_t` of candidate nonzero coefficients or
chain skeletons is allowed at stage `t`, a union bound gives

\[
 \lambda(\exists C\in\mathcal C_t:E_{t,C})\leq
 |\mathcal C_t|\left(\frac2{U_t10^{\ell_t}}+
 \frac1{U_t^2 10^{2\ell_t}}\right).                        \tag{7.11}
\]

Therefore summability of the right side is an explicit sufficient joint
growth condition; it is not claimed necessary.  For `ell_t=t`, `U_t>=9`, and
some fixed `epsilon>0`, any family with
`|mathcal C_t|=O(10^((1-epsilon)t))` (where this denotes the cardinality
`|\mathcal C_t|`) is admissible.  No assertion is made for a family
growing as fast as `10^t` or for a coefficient selected after observing
`alpha`.  This is the remaining maximal-selection boundary.

## 8. Sparse primitive rays

For every primitive base `v` with `10 not divides v`, the terminal interval
`(H/10,H]` contains exactly one element `10^a v` when `v<=H`, and none when
`v>H`.  Indeed, the largest power not exceeding `H` is greater than `H/10`;
two powers differ by a factor at least ten and cannot both lie in the interval.
Thus the literal shell is a transversal of primitive decimal rays, not an
average along each ray.

UPRID itself excludes a sparse bad label **conditional on UPRID holding**, due
to its pointwise maximum in (6.6).  The almost-everywhere theorem proves that
UPRID is eventually false on the displayed schedule.  It does **not** prove a
uniform primitive-ray maximal inequality and does **not** exclude sparse
primitive-ray concentration in the orbit.  T67's sparse-ray separators are
abstract arrays, not orbit witnesses.  The exact answer requested by the
agenda is therefore:

```text
SPARSE PRIMITIVE-RAY CONCENTRATION IS NOT EXCLUDED.
```

## 9. Terminal verdict

The terminal verdict is the permitted negative outcome:

```text
PROOF SKETCH: RIGOROUS ALMOST-EVERYWHERE REFUTATION OF THE EVENTUAL
EXACT-FORM RANDOM T55 TOP-SHELL AND T61-QUALIFIED-UPRID SCHEDULE
(7.5)--(7.7), WITH EXPLICIT TAILS; NO STATEMENT ABOUT PI FOLLOWS.
```

The underlying reason is normalization, not an iid heuristic.  The exact
coupled Fejer sum has mean `ell`, while T55 asks it to exceed a quantity of
order `ell*R`; T38 forces `R` to grow at least like `10^ell`.  Equal-frequency
and decimal-valuation collisions increase the variance by the explicitly
listed positive covariance classes, but they do not alter the first-moment
summable obstruction.

## 10. Replay

From a directory containing only the delivered files, run

```text
python3 verify_note.py
```

The script hash-checks the canonical statement and checks, with exact rational
arithmetic, the primitive-ray partition, collision parametrization, Fejer and
UPRID moment formulas against direct frequency dictionaries, the terminal
correlation zero and covariance classes, the explicit chain arithmetic, and
the exceptional-tail summation.
