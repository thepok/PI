# T57: the first-sign stopping rule can stop in T55's terminal shell

Claim label: **proof sketch**.  The established research input is the
kernel-checked T55 module.  The finite algebra in this note is written out for
inspection but is not itself formalized.  The T56 note is motivation only and
none of its claims is used as a premise.

## 1. Provenance, normalized statement, and scope

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.  It records no external
source URL; it says that the question was formulated by this system on
2026-07-22.  Its verified SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For real `x`, let `||x||_(R/Z)` be distance to the nearest integer and let

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\]

The canonical question is

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \ \forall n\geq n_0\ \exists N\geq1:
 \qquad AnQ_\pi(n,N)\leq N^2.                    \tag{1.1}
\]

The pairs are ordered, the diagonal is included, and `N` may depend on
`A,n`.  Infinitely many `n`, one fixed `A`, a prescribed `N`, unordered
pairs, or removal of the diagonal are different statements.  T57 changes
none of these conventions.  It proves no instance of (1.1), no fixed-`pi`
cancellation, and no C1, C2, T28, or general FSFS conclusion.

The sole checked research artifact used is

| item | file | SHA-256 | interface used |
|---|---|---|---|
| T55 | `TheoryLib/PiLacunaryNearReturnSparsity/T55SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | literal signed range, phase transport, one-step telescope, orbit coefficient, endpoint and terminal sums, signed aggregation, and strict threshold |

The conclusion is a same-domain refutation of the proposed universal
localization.  The cost is strictly discretely convex and its minimizer is
indeed found by the first nonnegative finite difference, but that set can be
empty.  In an explicit legal T55 tuple, the unique fallback minimizer is the
last orbit vertex, which lies in T55's original terminal shell.  Thus the
minimizing rule does not always produce a lower-orbit block.

## 2. Literal signed range and positive orbit coordinates

Fix real `beta`, natural `ell`, and natural `R` with

\[
 1\leq\ell,\qquad 1\leq R,\qquad H:=R-1.          \tag{2.1}
\]

T55's signed Fourier range is every integer `-H <= u <= H`.  Write

\[
 e(x):=\exp(2\pi i x),\qquad
 X_{u,j}:=e\!\left(\beta u(10^\ell-10^j)\right),\qquad
 F_u:=\sum_{j=0}^{\ell-1}X_{u,j}.                 \tag{2.2}
\]

The value `X_(u,ell)=1` is an auxiliary telescope endpoint, not an extra
stratum summand.  For `1 <= u <= H`, put

\[
 w(u):=1-\frac uR>0.                              \tag{2.3}
\]

T55 keeps the two labels `u` and `-u`, then uses conjugacy.  Its exact signed
aggregation is

\[
 E_{\ell,R}(\beta)
 =\ell+2\operatorname{Re}\sum_{u=1}^{H}w(u)F_u.  \tag{2.4}
\]

Thus the factor two below represents both signs; negative frequencies have
not been deleted.

If `H=0`, the positive range is empty and there is no stopping problem.
Assume henceforth that `H>=1`.  Define the primitive roots

\[
 \mathcal P_H:=\{a:1\leq a\leq H,\ 10\nmid a\}.  \tag{2.5}
\]

For `a in P_H`, set

\[
 u_{a,q}:=a10^q,\qquad
 Q_a:=\max\{q\geq0:u_{a,q}\leq H\}.              \tag{2.6}
\]

Then

\[
 u_{a,Q_a}\leq H<10u_{a,Q_a}.                    \tag{2.7}
\]

Repeated division by ten gives a unique representation `u=u_(a,q)` for
every `1<=u<=H`.  This is only a collision-free parametrization of the
frequency label `u`.  The full integer frequencies
`u(10^ell-10^j)` may collide and are always retained with multiplicity.

Abbreviate, for `0<=q<=Q_a`,

\[
 w_{a,q}:=1-\frac{u_{a,q}}R,
 \qquad W_{a,q}:=\sum_{p=0}^q w_{a,p}
 =(q+1)-\frac{a(10^{q+1}-1)}{9R}.                \tag{2.8}
\]

Every displayed weight is at least `1/R`, since `u_(a,q)<=R-1`.

## 3. T55 phase transport and an exact stopped identity

For `0<=q<Q_a`, define

\[
 \rho_{a,q}:=e(-9\beta u_{a,q}10^\ell),\qquad
 b_{a,q}:=e\!\left(\beta u_{a,q}(10^\ell-1)\right)-1.       \tag{3.1}
\]

T55's checked phase transport and telescope say

\[
 \rho_{a,q}X_{u_{a,q+1},j}=X_{u_{a,q},j+1}
 \quad(0\leq j<\ell),                                      \tag{3.2}
\]

\[
 F_{u_{a,q}}-\rho_{a,q}F_{u_{a,q+1}}=b_{a,q}.               \tag{3.3}
\]

The lower endpoint in (3.3) is `j=0`; the upper endpoint is the one auxiliary
value `j=ell`, with a minus sign.  For `ell=1` the interior cancellation range
is empty and the identity remains valid.

Define the accumulated coefficients

\[
 \Gamma_{a,0}:=w_{a,0},\qquad
 \Gamma_{a,q}:=w_{a,q}+\rho_{a,q-1}\Gamma_{a,q-1}
 \quad(1\leq q\leq Q_a).                           \tag{3.4}
\]

This is T55's `orbitCoefficient` along the unique predecessor chain.  The
nonrecursive phase-preserving formula is

\[
 \Gamma_{a,q}=\sum_{p=0}^q w_{a,p}
 e\!\left(\beta(u_{a,p}-u_{a,q})10^\ell\right).             \tag{3.5}
\]

Fix a stopping vertex `s` with `0<=s<=Q_a`.  Substituting (3.3) and using
`Gamma_(a,q)-rho_(a,q-1)Gamma_(a,q-1)=w_(a,q)` gives the exact identity

\[
 \boxed{
 \sum_{q=0}^{Q_a}w_{a,q}F_{u_{a,q}}
 =\sum_{q=0}^{s-1}\Gamma_{a,q}b_{a,q}
  +\Gamma_{a,s}F_{u_{a,s}}
  +\sum_{q=s+1}^{Q_a}w_{a,q}F_{u_{a,q}}.}          \tag{3.6}
\]

The first sum is empty at `s=0`; the last is empty at `s=Q_a`.  Terms in the
last sum are untouched original T55 labels.  Expanding all labels gives

\[
 \Gamma_{a,s}F_{u_{a,s}}
 =\sum_{p=0}^{s}\sum_{j=0}^{\ell-1}w_{a,p}
 e\!\left(\beta(u_{a,p}10^\ell-u_{a,s}10^j)\right),         \tag{3.7}
\]

and

\[
 \Gamma_{a,q}b_{a,q}
 =\sum_{p=0}^{q}w_{a,p}\left[
 e\!\left(\beta(u_{a,p}10^\ell-u_{a,q})\right)
 -e\!\left(\beta(u_{a,p}-u_{a,q})10^\ell\right)\right].   \tag{3.8}
\]

These are sums over labels `(a,p,q,j)`.  Equal numerical frequencies add
their coefficients; no quotient or support image is used.

## 4. The retained-correlation cost and its closed form

If the middle term of (3.6) is retained for later phase-sensitive analysis,
while endpoint and untouched-tail terms are bounded using

\[
 |\Gamma_{a,q}|\leq W_{a,q},\qquad |b_{a,q}|\leq2,
 \qquad |F_{u_{a,q}}|\leq\ell,                    \tag{4.1}
\]

the exact phase-blind remainder cost is

\[
 \boxed{K_a(s):=
 2\sum_{q=0}^{s-1}W_{a,q}
 +\ell\sum_{q=s+1}^{Q_a}w_{a,q}.}                 \tag{4.2}
\]

Both sums include their stated endpoints and are empty under the conventions
already given.  Summing the two geometric progressions yields

\[
 \begin{aligned}
 K_a(s)={}&s(s+1)
 -\frac{2a}{9R}\left(\frac{10(10^s-1)}9-s\right)\\
 &+\ell\left[Q_a-s-
 \frac{a(10^{Q_a+1}-10^{s+1})}{9R}\right].       \tag{4.3}
 \end{aligned}
\]

No phase or collision assumption enters (4.2)-(4.3).

## 5. Finite difference and strict discrete convexity

For exactly `0<=s<Q_a`, moving the stop from `s` to `s+1` adds the endpoint
charge `2W_(a,s)` and removes the tail charge `ell*w_(a,s+1)`.  Therefore

\[
 \boxed{\Delta_a(s):=K_a(s+1)-K_a(s)
 =2W_{a,s}-\ell w_{a,s+1}.}                       \tag{5.1}
\]

For exactly `0<=s<Q_a-1`, a second subtraction gives

\[
 \begin{aligned}
 \Delta_a(s+1)-\Delta_a(s)
 &=2(W_{a,s+1}-W_{a,s})
   -\ell(w_{a,s+2}-w_{a,s+1})\\
 &=2w_{a,s+1}+\frac{9\ell u_{a,s+1}}R>0.          \tag{5.2}
 \end{aligned}
\]

Indeed, `w_(a,s+1)>=1/R>0`, while all other factors are nonnegative.  Thus
`K_a` is strictly discretely convex whenever its domain has at least three
points.  For `Q_a<=1`, the second-difference assertion is vacuous and the
one available difference gives the complete comparison.

## 6. Complete first-sign minimizer classification

If `Q_a=0`, the only legal stop is `s=0`.

Suppose `Q_a>=1` and define

\[
 S_a:=\{s\in\{0,\ldots,Q_a-1\}:\Delta_a(s)\geq0\}.          \tag{6.1}
\]

Strict increase in (5.2) gives all cases:

1. If `S_a` is empty, every adjacent difference is negative and the unique
   minimizer is `s=Q_a`.
2. If `S_a` is nonempty, let `m_a=min S_a`.  Every difference before `m_a`
   is negative and every difference after it is strictly positive.
3. If `Delta_a(m_a)>0`, the unique minimizer is `s=m_a`.
4. If `Delta_a(m_a)=0`, the two and only two minimizers are
   `s=m_a` and `s=m_a+1`.

This includes both boundaries.  In particular, `Delta_a(0)>0` gives the
unique minimizer `0`, `Delta_a(0)=0` gives the tie `{0,1}`, and
`Delta_a(Q_a-1)=0` gives the tie `{Q_a-1,Q_a}`.  Thus the correct rule is
"first nonnegative difference, with a two-point tie at zero, and last-vertex
fallback if there is no nonnegative difference."

## 7. The support condition needed for a strict lower block

Equation (2.7) gives the exact support dichotomy

\[
 \begin{cases}
 s<Q_a &\Longrightarrow u_{a,s}\leq H/10,\\
 s=Q_a &\Longrightarrow H/10<u_{a,s}\leq H.
 \end{cases}                                                \tag{7.1}
\]

With integer endpoints this is T55's partition

\[
 \operatorname{pairingSourceShell}(R)=Icc(1,\lfloor H/10\rfloor),
 \qquad
 \operatorname{terminalShell}(R)=Ioc(\lfloor H/10\rfloor,H). \tag{7.2}
\]

Consequently, a minimizing retained vertex is strictly lower than T55's
terminal shell only if a minimizer can be chosen with `s<Q_a`.  For a
nontrivial orbit, the last comparison needed for that conclusion is

\[
 \Delta_a(Q_a-1)=2W_{a,Q_a-1}-\ell w_{a,Q_a}\geq0.          \tag{7.3}
\]

Strict positivity in (7.3) would force every minimizer below the terminal
vertex; equality would permit the lower endpoint of the tie.  T55's literal
domain does not imply (7.3).

## 8. An explicit legal T55 tuple

Take

\[
 M=5,\quad D=2,\quad B=1,\quad K=4,\quad d=1,
 \quad h=1,\quad r=0,\quad F=\{0\},                         \tag{8.1}
\]

and define a geometric resonance chain with the one-term shift list `[1]`.
This is a literal inhabitant of T55's chain type:

* the list has length one and no duplicate;
* its shift is at least `B=1` and avoids `{0}`;
* `K=4=M-1`, so the final-residual condition is equality;
* `initialCoefficient(1,0)=(10^0-1)pi=0`, so every geometric phase is one;
* at node `0`, the checked chain inequality is `5/2<5`;
* at node `1`, `densityDenominator(2,1)=8*2^2=32`, and the inequality is
  `4/32<4`.

These are all nodes `k<=d`.  Let `k` be the unique member of `Fin 1`, namely
`k=0`, and choose

\[
 \ell=3.                                                    \tag{8.2}
\]

The node residuals are `5` and `4`, hence T38's `commonDepth` is `4` and
`1<=ell<commonDepth` is literal.  The adjacent factor is

\[
 U=10^1-1=9,                                                \tag{8.3}
\]

and the phase in T55 is

\[
 \beta=\operatorname{chain.nodeCoefficient}(0)=0.           \tag{8.4}
\]

For `D=2`, the two T38 correlation thresholds are

\[
 \operatorname{nodeTau}(2,0)=\frac1{32},\qquad
 \operatorname{nodeTau}(2,1)=\frac1{8192}.                  \tag{8.5}
\]

Both lie strictly between zero and `1/2`.  Since `arccos` is strictly
decreasing and `arccos(1/2)=pi/3`, their inverse errors `eta_0,eta_1` satisfy

\[
 \eta_0>\frac16,\qquad \eta_1>\frac16.                     \tag{8.6}
\]

T38's literal stratum radius is therefore

\[
 \begin{aligned}
 \delta
 &=\min\left\{\eta_0,\frac{\eta_1}{9},
                  \frac1{2\cdot9\cdot10^3}\right\}\\
 &=\frac1{18000},                                           \tag{8.7}
 \end{aligned}
\]

because `eta_0>1/6>1/18000` and
`eta_1/9>1/54>1/18000`.  Hence

\[
 R=\lceil\delta^{-1}\rceil=18000,\qquad H=17999.           \tag{8.8}
\]

No chain-existence hypothesis, fixed-`pi` assertion, or T28 premise is being
assumed here.  The value `r=0` is allowed by T55's top-shell and threshold
declarations; it would not meet the separate positive-`r` premise in T55's
conditional T28 theorem.

## 9. Exact endpoint refutation of lower localization

In the legal tuple of Section 8, choose the primitive root

\[
 a=181.                                                     \tag{9.1}
\]

It is not divisible by ten, and

\[
 u_{a,0}=181,\qquad u_{a,1}=1810\leq17999,
 \qquad u_{a,2}=18100>17999.                                \tag{9.2}
\]

Thus `Q_a=1`.  The exact weights are

\[
 w_{a,0}=\frac{17819}{18000},\qquad
 w_{a,1}=\frac{1619}{1800},\qquad W_{a,0}=w_{a,0}.          \tag{9.3}
\]

The domain of differences contains only `s=0`, and (5.1) gives

\[
 \begin{aligned}
 \Delta_a(0)
 &=2\frac{17819}{18000}-3\frac{1619}{1800}\\
 &=-\frac{3233}{4500}<0.                                   \tag{9.4}
 \end{aligned}
\]

Hence `S_a` is empty and Section 6 gives the unique minimizer

\[
 \boxed{s=1=Q_a.}                                           \tag{9.5}
\]

The exact two costs are

\[
 K_a(0)=3w_{a,1}=\frac{1619}{600},\qquad
 K_a(1)=2W_{a,0}=\frac{17819}{9000},                        \tag{9.6}
\]

and their difference is exactly (9.4).  Thus forcing the lower stop `s=0`
increases the stated deterministic remainder majorant by `3233/4500`.

The terminal-shell boundary is

\[
 \left\lfloor\frac H{10}\right\rfloor=1799.                \tag{9.7}
\]

The selected frequency `1810` therefore lies in
`Ioc(1799,17999)`, T55's original terminal shell, not in its lower source
shell `Icc(1,1799)`.  This is the first failed assertion required by the
proposed strict reduction: inequality (7.3) is false by the exact deficit
`3233/4500`.

## 10. Phases, endpoint remainder, and collisions in the refutation

The phase has not been changed to manufacture (9.4); it is the literal T55
phase (8.4).  At `beta=0`, all transport phases and labeled phases equal one.
Consequently

\[
 b_{a,0}=0,\qquad
 \Gamma_{a,1}=w_{a,0}+w_{a,1}=\frac{34009}{18000},
 \qquad F_{u_{a,1}}=3.                                     \tag{10.1}
\]

The retained terminal term is therefore the nonzero positive number

\[
 \Gamma_{a,1}F_{u_{a,1}}=\frac{34009}{6000}.               \tag{10.2}
\]

At the forced lower stop `s=0`, the exact remainder in (3.6) is the untouched
tail

\[
 w_{a,1}F_{u_{a,1}}=3w_{a,1}=\frac{1619}{600}=K_a(0).       \tag{10.3}
\]

At the minimizing terminal stop `s=1`, the exact endpoint remainder is
`Gamma_(a,0)b_(a,0)=0`; the phase-blind cost `K_a(1)=2W_(a,0)` is a valid but
non-sharp bound obtained from `|b_(a,0)|<=2`.  Thus no endpoint or tail has
been silently dropped, and the support failure is not a remainder-sign
artifact.

If `Gamma_(a,1)` is kept as T55's single orbit coefficient, its three block
labels have integer frequencies

\[
 1810(1000-1)=1808190,\quad
 1810(1000-10)=1791900,\quad
 1810(1000-100)=1629000.                                  \tag{10.4}
\]

Under the fully expanded `(p,j)` convention of (3.7), the retained term has
six labels, with frequencies

\[
 179190,\quad162900,\quad0,\quad
 1808190,\quad1791900,\quad1629000.                         \tag{10.5}
\]

The endpoint expansion (3.8) has one negative zero-frequency label, which
cancels the retained `p=0,j=2` constituent when the stopped identity is
collected as a Fourier polynomial.  Its positive label restores the missing
original `u=181,j=0` frequency.  This is ordinary finite telescoping, not
deletion of either label; at the literal phase `beta=0` the complete endpoint
remainder has the already checked value zero.

Global numerical collisions are still possible.  For example, on this same
`ell=3` domain,

\[
 110(1000-1)=109890=111(1000-10),                          \tag{10.6}
\]

although the labels `(110,0)` and `(111,1)` are distinct.  Equations
(3.6)-(3.8) retain both labels.  In the original positive-frequency
polynomial their triangular coefficients are positive and collection adds
them.  In the stopped expansion, endpoint labels can have negative signs as
just displayed, and those signs are retained as well.  The refutation does
not assume collision-free collection: at `beta=0` the complete endpoint
remainder is exactly zero while the complete retained value (10.2) is
strictly positive.

## 11. Strict comparison with T55's literal threshold

For the tuple of Section 8, T55's strict T38 threshold is

\[
 \Theta=\frac{\ell}{4R\delta^2}
 =\frac{3\cdot18000}{4}=13500.                              \tag{11.1}
\]

Equivalently, T55 requires the positive-frequency real part to exceed

\[
 B:=\frac{\ell}{8R\delta^2}-\frac\ell2
 =\frac{13497}{2}.                                         \tag{11.2}
\]

Because `beta=0`, every one of the three Fejer kernels has value `R=18000`.
Thus the actual stratum sum is

\[
 E_{3,18000}(0)=54000>13500.                               \tag{11.3}
\]

This numerical comparison is only for the displayed legal tuple, not a
general FSFS claim.

T55's endpoint differences all vanish at this phase, so its exact identity
gives

\[
 \operatorname{Re}(\operatorname{terminalCorrelation})
 =\frac{E_{3,18000}(0)-3}{2}
 =\frac{53997}{2}.                                         \tag{11.4}
\]

For completeness, T55's phase-blind `endpointBudget` is also strictly within
the available slack.  At `beta=0`, an orbit coefficient at a source frequency
`u` is a positive sum of `nu_10(u)+1` weights, each strictly below one.  Since
the source shell is `1<=u<=1799`, the total number of predecessor labels is

\[
 1799+\left\lfloor\frac{1799}{10}\right\rfloor
 +\left\lfloor\frac{1799}{100}\right\rfloor
 +\left\lfloor\frac{1799}{1000}\right\rfloor
 =1799+179+17+1=1996.                                     \tag{11.5}
\]

Therefore

\[
 \operatorname{endpointBudget}<2\cdot1996=3992.            \tag{11.6}
\]

The literal T55 top-shell right side is consequently bounded by

\[
 B+\operatorname{endpointBudget}
 <\frac{13497}{2}+3992=\frac{21481}{2}
 <\frac{53997}{2}.                                         \tag{11.7}
\]

The final strict margin in this estimate is greater than

\[
 \frac{53997-21481}{2}=16258.                              \tag{11.8}
\]

Thus the example does not refute T55's hypothesis or threshold.  It refutes
the proposed universal *localization of the minimizing retained block* even
in a tuple where T55's existing endpoint budget is comfortably inside the
strict threshold slack.  The first obstruction is support inequality (7.3),
not a later threshold deficit.

## 12. Verdict

The stopped cost (4.2), finite difference (5.1), strict discrete convexity
(5.2), and first-nonnegative minimizer rule of Section 6 are valid, including
all ties and endpoint cases.  The endpoint fallback is essential rather than
formal bookkeeping: Sections 8-10 give legal T55 data and a nontrivial orbit
for which the unique minimizer is `s=Q_a`, the retained term is nonzero, and
its frequency remains in T55's unchanged terminal shell.

Therefore the first-sign rule does **not** universally yield the explicitly
smaller lower-orbit block demanded by T57.  Because that support conclusion
already fails, no universal lower-block estimate implying T55's
`TopShellCorrelationHypothesis` can be stated from this stopping rule, and it
would be misleading to promote the exact decomposition (3.6) into a strict
support reduction.  All signs, phases, endpoints, cutoff inequalities, tail
terms, collision multiplicities, cost constants, and the literal strict T55
threshold have been retained above.

**EXACT SAME-DOMAIN REFUTATION OF STRICT LOWER-BLOCK LOCALIZATION**
