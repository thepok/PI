# T54: exact multiplier-ten signed pairing at one T38 stratum

Claim label: **proof sketch**. The T26, T34, and T38 inputs listed below are
kernel-checked. The new finite identities in this prose note are proved by the
displayed algebra but have not been formalized in Lean. T28 is used only in
the conditional-payoff paragraph of Section 11.

## 1. Provenance, normalized question, and scope

The canonical statement is the local, system-formulated question in
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its verified SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\},
\]

the canonical question is

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \ \forall n\geq n_0\ \exists N\geq1:
 \qquad AnQ_\pi(n,N)\leq N^2.                    \tag{1.1}
\]

Pairs in (1.1) are ordered, the diagonal is included, and `N` may depend on
`A,n`. This note does not change any of those quantifiers or conventions. It
does not prove (1.1), FSFS, adjacent compatibility, C1, or C2.

The only established mathematical inputs used are these kernel-checked
files:

| item | file | SHA-256 | interface used |
|---|---|---|---|
| T26 | `t26/SharedResonanceChain.lean` | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | genuine chain, node coefficient, residual, and adjacent node |
| T34 | `t34/MixedProductBridge.lean` | `0ba1b2af1d381d87f062deb4fa7df230564b51ac13c43e8e8150a0234c66559d` | common legal pair domain, joint-good predicate, and conditional mixed-sum bridge |
| T38 | `t38/FixedStratumFejerSpike.lean` | `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014` | stratum radius/order, literal one-dimensional expansion, and exact FSFS threshold |
| T28 | `t28/AdjacentNodeCompatibility.lean` | `f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd` | conditional payoff in Section 11 only |

The adjacent-program signed-pairing lead is motivation only. No assertion
from that unverified note is a premise here. In particular, the pairing map,
telescoping identity, bounds, and threshold comparison below are all derived
again from T38's literal finite sum.

## 2. Literal legal T38 data

Fix a T26 geometric resonance chain and an adjacent node `k : Fin d` of the
form required by T34 and T38. Put

\[
 \beta:=\operatorname{chain.nodeCoefficient}(k),\qquad
 U:=\operatorname{chain.adjacentFactor}(k).                 \tag{2.1}
\]

Thus `beta` is the actual fixed node coefficient, not a free averaging
variable. Fix a legal stratum

\[
 1\leq\ell<\operatorname{commonDepth}(\operatorname{chain},k). \tag{2.2}
\]

For clarity, the T38 quantities used below are

\[
 \tau_t=\frac{1}{8\,\operatorname{densityDenominator}(D,t)^2},
 \qquad \eta_t=\operatorname{inverseError}(\tau_t),          \tag{2.3}
\]

\[
 \delta=\min\left\{\eta_k,\frac{\eta_{k+1}}{U},
                    \frac{1}{2U10^\ell}\right\},
 \qquad R=\left\lceil\delta^{-1}\right\rceil.              \tag{2.4}
\]

Here (2.3)-(2.4) are just T38's `nodeErrorThreshold`, `stratumDelta`,
and `stratumOrder` unfolded. For legal data T38 proves `delta > 0` and
`R >= 1`. Set

\[
 H:=R-1,\qquad
 e(x):=\exp(2\pi i x),\qquad
 w(u):=1-\frac{|u|}{R}\quad (|u|\leq H).                    \tag{2.5}
\]

T38's theorem `stratumFejerSum_eq_lacunaryExpansion`, followed only by
distributivity, gives the exact real quantity

\[
 \begin{aligned}
 E_{\ell,R}(\beta)
   &:=\sum_{j=0}^{\ell-1}F_{R-1}
       \bigl(\beta(10^\ell-10^j)\bigr)\\
   &=\sum_{u=-H}^{H}w(u)F_u,                                \tag{2.6}\\
 F_u&:=\sum_{j=0}^{\ell-1}X_{u,j},\\
 X_{u,j}&:=e\bigl(\beta u(10^\ell-10^j)\bigr)\\
   &=e(\beta u10^\ell)e(-\beta u10^j).                     \tag{2.7}
 \end{aligned}
\]

No estimate has entered (2.6). The analytic clause in T38's `ExpandedFSFS`
is literally

\[
 \boxed{\quad \Theta_{\ell,R,\delta}
 :=\frac{\ell}{4R\delta^2}<E_{\ell,R}(\beta).\quad}         \tag{2.8}
\]

The legality conjuncts `1 <= D`, (2.2), and the definitions (2.3)-(2.4)
remain in force separately from the strict inequality (2.8).

## 3. Zero frequency, signs, and multiplicity

At zero frequency every one of the `ell` labeled stratum terms equals one:

\[
 F_0=\ell.                                                   \tag{3.1}
\]

For `1 <= u <= H`, real `beta` gives

\[
 w(-u)=w(u),\qquad F_{-u}=\overline{F_u}.                   \tag{3.2}
\]

Consequently, preserving the two signed copies of each nonzero frequency,

\[
 \boxed{\quad E_{\ell,R}(\beta)
   =\ell+2\operatorname{Re}\sum_{u=1}^{H}w(u)F_u.\quad}     \tag{3.3}
\]

Equation (3.3) aggregates conjugates; it does not identify or cancel their
two occurrences in (2.6). If `R=1`, then `H=0`, the sum in (3.3) is empty,
and all later primitive-orbit sums are empty as well.

## 4. Exact multiplier-ten orbit partition

Assume only for the notation in this section that `H >= 1`. Define the
positive primitive roots

\[
 \mathcal P_H:=\{a\in\mathbb N:1\leq a\leq H,\ 10\nmid a\}. \tag{4.1}
\]

For `a in P_H`, define

\[
 Q_a:=\max\{q\in\mathbb N:a10^q\leq H\},
 \qquad u_{a,q}:=a10^q\quad(0\leq q\leq Q_a).               \tag{4.2}
\]

The maximum exists because `q=0` is allowed and powers of ten eventually
exceed `H`. Its cutoff boundary is exactly

\[
 u_{a,Q_a}\leq H<10u_{a,Q_a}.                              \tag{4.3}
\]

Repeatedly divide a positive integer `u <= H` by ten until it is no longer
divisible by ten. This produces a unique pair `(a,q)` with `a in P_H` and
`u=u_(a,q)`. Uniqueness follows because if `a10^q=a'10^(q')` and neither
`a` nor `a'` is divisible by ten, cancellation of the smaller power forces
`q=q'`, then `a=a'`. Hence the labeled frequencies partition exactly as

\[
 \sum_{u=1}^{H}w(u)F_u
 =\sum_{a\in\mathcal P_H}\sum_{q=0}^{Q_a}w(u_{a,q})F_{u_{a,q}}. \tag{4.4}
\]

There is no collision in the orbit coordinates `(a,q)`. Numerical collisions
of the full integer frequencies `u(10^ell-10^j)` can nevertheless occur and
must not be quotiented. For example, when `ell=2`,

\[
 10(10^2-1)=11(10^2-10)=990.                               \tag{4.5}
\]

Thus `(u,j)=(10,0)` and `(11,1)` are distinct labeled summands with the same
phase whenever both are within the cutoff. Every sum below remains over
labeled `(a,q,j)` coordinates, so (4.5) and all higher collisions retain
their full multiplicity.

## 5. The explicit signed pairing map

Extend (2.7) only as notation to the auxiliary endpoint `j=ell`:

\[
 X_{u,\ell}=e\bigl(\beta u(10^\ell-10^\ell)\bigr)=1.        \tag{5.1}
\]

For a sign `epsilon in {-1,1}`, `a in P_H`, `0 <= q < Q_a`, and
`0 <= j < ell`, define the nonlocal multiplier-ten pairing map

\[
 \mathfrak p(\epsilon,a,q,j+1)
   :=(\epsilon,a,q+1,j).                                    \tag{5.2}
\]

It is a bijection from the labeled set

\[
 \{(\epsilon,a,q,t):\epsilon=\mathord\pm1,\ a\in\mathcal P_H,
     0\leq q<Q_a,\ 1\leq t\leq\ell\}                      \tag{5.3}
\]

to

\[
 \{(\epsilon,a,q+1,j):\epsilon=\mathord\pm1,\ a\in\mathcal P_H,
     0\leq q<Q_a,\ 0\leq j<\ell\}.                        \tag{5.4}
\]

The inverse subtracts one from the orbit index and adds one to the stratum
index. Hence (5.2) has no coordinate collisions. On the original range
`0 <= j < ell`, its interior part pairs `j=1,...,ell-1` at frequency `u`
with `j=0,...,ell-2` at frequency `10u`; (5.1) exposes the two endpoints
rather than discarding either one.

For any signed nonzero `u` satisfying `|10u| <= H`, set

\[
 \rho_u:=e(-9\beta u10^\ell).                               \tag{5.5}
\]

The exact phase equality associated with (5.2) is

\[
 \begin{aligned}
 \rho_uX_{10u,j}
 &=e\bigl(-9\beta u10^\ell
       +10\beta u(10^\ell-10^j)\bigr)\\
 &=e\bigl(\beta u(10^\ell-10^{j+1})\bigr)
 =X_{u,j+1}.                                                \tag{5.6}
 \end{aligned}
\]

Thus this is a signed pairing: `rho_u F_(10u)` is subtracted from `F_u`.
The factor `rho_u` is essential. Omitting it would silently lose the outer
phase `e(beta u 10^ell)` in T38's expansion.

## 6. Exact one-step telescope and every endpoint

Sum (5.6) over the complete range `0 <= j < ell`. The right side is indexed
by `1 <= j+1 <= ell`, while `F_u` is indexed by `0 <= j < ell`. Therefore

\[
 \begin{aligned}
 F_u-\rho_uF_{10u}
 &=\sum_{j=0}^{\ell-1}X_{u,j}
   -\sum_{j=0}^{\ell-1}X_{u,j+1}\\
 &=X_{u,0}-X_{u,\ell}\\
 &=e\bigl(\beta u(10^\ell-1)\bigr)-1.                     \tag{6.1}
\end{aligned}
\]

This proves, rather than assumes, the exact telescoping identity

\[
 \boxed{\quad F_u-\rho_uF_{10u}
 =e\bigl(\beta u(10^\ell-1)\bigr)-1.\quad}                 \tag{6.2}
\]

The lower boundary is the actual original term `j=0`. The upper boundary is
the auxiliary value `j=ell`, exactly `1`. When `ell=1`, the interior pairing
range is empty and (6.2) still holds. No stratum term has been inserted into
T38's sum: the auxiliary upper endpoint occurs once with a minus sign solely
because of finite telescoping.

## 7. Triangular weights and the exact orbit telescope

For a fixed primitive root `a`, abbreviate

\[
 w_{a,q}:=1-\frac{a10^q}{R},\quad
 F_{a,q}:=F_{u_{a,q}},\quad
 \rho_{a,q}:=\rho_{u_{a,q}},                                \tag{7.1}
\]

and define cumulative coefficients

\[
 \Gamma_{a,0}:=w_{a,0},\qquad
 \Gamma_{a,q}:=w_{a,q}+\rho_{a,q-1}\Gamma_{a,q-1}
 \quad(1\leq q\leq Q_a).                                  \tag{7.2}
\]

This recursion retains the nonconstant triangular weights. Iterating it gives
the explicit, nonrecursive formula

\[
 \boxed{\quad
 \Gamma_{a,q}=\sum_{p=0}^{q}w_{a,p}
 e\bigl(\beta(u_{a,p}-u_{a,q})10^\ell\bigr).\quad}          \tag{7.3}
\]

Indeed,

\[
 \prod_{t=p}^{q-1}\rho_{a,t}
 =e\left(-9\beta10^\ell\sum_{t=p}^{q-1}a10^t\right)
 =e\bigl(\beta(u_{a,p}-u_{a,q})10^\ell\bigr),              \tag{7.4}
\]

with the empty product equal to one when `p=q`.

Put

\[
 b_{a,q}:=e\bigl(\beta u_{a,q}(10^\ell-1)\bigr)-1.          \tag{7.5}
\]

Applying (6.2) successively along the finite orbit gives

\[
 \boxed{\quad
 \sum_{q=0}^{Q_a}w_{a,q}F_{a,q}
 =\sum_{q=0}^{Q_a-1}\Gamma_{a,q}b_{a,q}
  +\Gamma_{a,Q_a}F_{a,Q_a}.\quad}                          \tag{7.6}
\]

Here and below a sum from `q=0` to `Q_a-1` is empty when `Q_a=0`. For a
direct coefficient check, replace each `b_(a,q)` in (7.6) by
`F_(a,q)-rho_(a,q)F_(a,q+1)`. The coefficient of `F_(a,0)` is
`Gamma_(a,0)=w_(a,0)`. For `1 <= q <= Q_a`, its coefficient is

\[
 \Gamma_{a,q}-\rho_{a,q-1}\Gamma_{a,q-1}=w_{a,q}.          \tag{7.7}
\]

This verifies every weight and multiplicity in (7.6). The final term
`Gamma_(a,Q_a)F_(a,Q_a)` is the exact Fourier-cutoff boundary: by (4.3),
its successor frequency `10u_(a,Q_a)` is outside `[-H,H]` and cannot legally
be paired in T38's expansion.

## 8. Global identity and the one remaining correlation

Define the fully explicit endpoint sum

\[
 \mathcal B:=
 \sum_{a\in\mathcal P_H}\sum_{q=0}^{Q_a-1}
 \Gamma_{a,q}
 \left[e\bigl(\beta u_{a,q}(10^\ell-1)\bigr)-1\right],     \tag{8.1}
\]

and define the single terminal-orbit correlation

\[
 \mathcal C:=
 \sum_{a\in\mathcal P_H}\Gamma_{a,Q_a}F_{a,Q_a}.           \tag{8.2}
\]

Combining (3.3), (4.4), and (7.6) yields the exact global identity

\[
 \boxed{\quad
 E_{\ell,R}(\beta)=\ell+2\operatorname{Re}(\mathcal B+\mathcal C).
 \quad}                                                     \tag{8.3}
\]

There are no hidden sums in the remaining term. Multiplying (7.3) by the
literal definition of `F_(a,Q_a)` gives

\[
 \boxed{\quad
 \mathcal C=
 \sum_{a\in\mathcal P_H}
 \left(\sum_{p=0}^{Q_a}w_{a,p}e(\beta u_{a,p}10^\ell)\right)
 \left(\sum_{j=0}^{\ell-1}e(-\beta u_{a,Q_a}10^j)\right).
 \quad}                                                     \tag{8.4}
\]

Equivalently, with every range and multiplicity flattened,

\[
 \mathcal C=
 \sum_{a\in\mathcal P_H}\sum_{p=0}^{Q_a}
 \sum_{j=0}^{\ell-1}w_{a,p}
 e\bigl(\beta(u_{a,p}10^\ell-u_{a,Q_a}10^j)\bigr).         \tag{8.5}
\]

Even if two phases in (8.5) have the same integer frequency, both labeled
triples `(a,p,j)` remain in the sum. Thus (8.3)-(8.5) preserve the numerical
collisions discussed in (4.5).

## 9. Universal bounds for every noncorrelation term

Since `a10^p <= H=R-1`, every `w_(a,p)` is positive. From (7.3) and the
triangle inequality,

\[
 \begin{aligned}
 |\Gamma_{a,q}|&\leq W_{a,q}:=\sum_{p=0}^{q}w_{a,p}\\
 &=(q+1)-\frac{a(10^{q+1}-1)}{9R}.                          \tag{9.1}
 \end{aligned}
\]

Also `|e(x)-1| <= 2`. Therefore the endpoint sum has the universal bound

\[
 |\mathcal B|\leq\mathfrak B_R,                             \tag{9.2}
\]

where

\[
 \boxed{\quad
 \mathfrak B_R:=2\sum_{a\in\mathcal P_H}
 \sum_{q=0}^{Q_a-1}
 \left[(q+1)-\frac{a(10^{q+1}-1)}{9R}\right].\quad}         \tag{9.3}
\]

Thus all terms other than the one correlation (8.4) are bounded explicitly:

\[
 \boxed{\quad
 \ell+2\operatorname{Re}\mathcal C-2\mathfrak B_R
 \leq E_{\ell,R}(\beta)
 \leq\ell+2\operatorname{Re}\mathcal C+2\mathfrak B_R.
 \quad}                                                     \tag{9.4}
\]

For scale only, not as a closing estimate, the residual itself satisfies

\[
 \begin{aligned}
 |\mathcal C|
 &\leq\ell\sum_{a\in\mathcal P_H}W_{a,Q_a}
 =\ell\sum_{u=1}^{R-1}\left(1-\frac uR\right)\\
 &=\frac{\ell(R-1)}2.                                      \tag{9.5}
 \end{aligned}
\]

The equality in the middle again uses the collision-free orbit partition,
not a claim that the phases are distinct.

## 10. Literal comparison with T38's threshold

Substituting (8.3) into T38's strict inequality (2.8) shows that, for the
fixed legal tuple, its analytic FSFS clause is exactly equivalent to

\[
 \boxed{\quad
 \operatorname{Re}\mathcal C>
 \frac{\ell}{8R\delta^2}-\frac\ell2-
 \operatorname{Re}\mathcal B.\quad}                        \tag{10.1}
\]

Using only the proved universal endpoint bound (9.2), the following is a
fully explicit sufficient condition:

\[
 \boxed{\quad
 \operatorname{Re}\mathcal C>
 \frac{\ell}{8R\delta^2}-\frac\ell2+\mathfrak B_R.
 \quad}                                                     \tag{10.2}
\]

Indeed, (9.4) and (10.2) give

\[
 E_{\ell,R}(\beta)
 \geq\ell+2\operatorname{Re}\mathcal C-2\mathfrak B_R
 >\frac{\ell}{4R\delta^2}=\Theta_{\ell,R,\delta},          \tag{10.3}
\]

which is exactly T38's displayed threshold, with the strict direction
preserved. Writing (10.2) without abbreviating the remaining sum gives the
required frontier

\[
 \begin{aligned}
 \operatorname{Re}\sum_{\substack{1\leq a\leq R-1\\10\nmid a}}
 &\left(\sum_{p=0}^{Q_a}
   \left(1-\frac{a10^p}{R}\right)e(\beta a10^{p+\ell})\right)
 \left(\sum_{j=0}^{\ell-1}e(-\beta a10^{Q_a+j})\right)\\
 &>\frac{\ell}{8R\delta^2}-\frac\ell2
 +2\sum_{\substack{1\leq a\leq R-1\\10\nmid a}}
   \sum_{q=0}^{Q_a-1}
   \left[(q+1)-\frac{a(10^{q+1}-1)}{9R}\right],             \tag{10.4}
 \end{aligned}
\]

where in every occurrence

\[
 Q_a=\max\{q\geq0:a10^q\leq R-1\}.                         \tag{10.5}
\]

Conversely, (9.4) shows that

\[
 \operatorname{Re}\mathcal C\leq
 \frac{\ell}{8R\delta^2}-\frac\ell2-\mathfrak B_R          \tag{10.6}
\]

is sufficient to rule out the strict T38 spike for that same tuple. Neither
(10.2) nor (10.6) follows from T26, T34, or T38. In particular, the triangle
bound (9.5) has no favorable sign and cannot replace the missing lower bound
in (10.2).

## 11. Exact status and conditional payoff

The signed map (5.2) and telescope (6.2) pair every eligible interior term
along each multiplier-ten orbit. The zero frequency is (3.1), the two signs
are retained by (3.2)-(3.3), all triangular weights and outer-phase mismatches
are in (7.2)-(7.4), the lower and upper stratum endpoints are in (6.1), and
the Fourier-cutoff endpoint of each orbit is precisely (8.2). Numerical
frequency collisions remain labeled with multiplicity by (4.5) and (8.5).
Thus no boundary or collision has been discarded.

What remains is exactly the terminal-orbit correlation (8.4), with sufficient
inequality (10.2), or equivalently its fully expanded form (10.4). T26's
nodewise resonance does not state a lower bound for this weighted collection
of terminal orbit multipliers. T34 supplies the exact downstream mixed-sum
interface, not a bound for (8.4). T38 deliberately leaves the fixed-stratum
spike as a hypothesis. Therefore these kernel-checked inputs do not discharge
the remaining correlation inequality.

Conditionally, if (10.2) is proved for legal data, then (10.3) establishes
T38's FSFS analytic clause for that tuple. T38 then supplies a legal
`JointGoodPair` and its zero-cutoff `MixedSumLowerBound`; T34 converts that
premise into an `AdjacentPairCompatible` witness. Only if `1 <= h`, `1 <= r`,
and T28's additional `ExponentEightLowerBound` and
`ExponentEightClosingBounds` hypotheses also hold does T28 give its pairwise
contradiction. (The inequalities on `h,r` hold for chains returned by T26's
literal-A1-failure theorem, but they are not silently assumed for the generic
legal tuple fixed in Section 2.) A canonical-A1 consequence would further
require T28's uniform coherent-selection hypothesis. None of those T28
hypotheses is asserted here, and no unconditional fixed-pi, FSFS,
compatibility, C1, or C2 claim is made.

SIGNED PAIRING REDUCES TO ONE CORRELATION TERM
