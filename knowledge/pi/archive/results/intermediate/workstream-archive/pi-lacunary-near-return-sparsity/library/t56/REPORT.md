# T56: stopped multiplier-ten orbits and the phase-blind barrier

Claim label: **proof sketch**. The only imported research result is the
kernel-checked T55 module. The stopping identity and optimization below are
finite algebra derived from T55's checked declarations, but this prose note is
not itself kernel-checked. T28 is mentioned only in the conditional-payoff
paragraph of Section 12.

## 1. Provenance, normalized question, and scope

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with verified SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

It asks whether, for the ordered and diagonal-inclusive count

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\},
\]

one has

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \ \forall n\geq n_0\ \exists N\geq1:
 \qquad AnQ_\pi(n,N)\leq N^2.                    \tag{1.1}
\]

Thus `N` may depend on `A,n`; infinitely many `n`, one fixed `A`, prescribed
`N`, unordered pairs, or removal of the diagonal would be different readings.
This note changes none of these quantifiers. It does not prove (1.1), FSFS,
fixed-`pi` cancellation, adjacent compatibility, C1, or C2.

The sole research input is

| item | file | SHA-256 | checked interface used |
|---|---|---|---|
| T55 | `TheoryLib/PiLacunaryNearReturnSparsity/T55SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | literal signed pairing, phase transport, one-step telescope, endpoints, signed aggregation, exact stratum identity, and strict T38 threshold |

In particular, the unverified T54 note is not a premise. All definitions and
identities needed below are reconstructed from T55's checked declarations.

## 2. Literal T55 stratum and Fourier ranges

Fix real `beta`, natural `ell`, and natural `R` with

\[
 \ell\geq1,\qquad R\geq1,\qquad H:=R-1.          \tag{2.1}
\]

For the later T38 comparison, these become

\[
 \beta=\operatorname{chain.nodeCoefficient}(k),\quad
 \delta=\operatorname{stratumDelta}(\operatorname{chain},k,\ell)>0,
 \quad R=\lceil\delta^{-1}\rceil,                \tag{2.2}
\]

under T55's literal legality conditions

\[
 1\leq D,\qquad 1\leq\ell<
 \operatorname{commonDepth}(\operatorname{chain},k).       \tag{2.3}
\]

Write

\[
 e(x):=\exp(2\pi i x),\qquad
 w(u):=1-\frac{|u|}{R}\quad (|u|\leq H),          \tag{2.4}
\]

and, for every integer `u`,

\[
 X_{u,j}:=e\!\left(\beta u(10^\ell-10^j)\right)
 \quad(0\leq j\leq\ell),\qquad
 F_u:=\sum_{j=0}^{\ell-1}X_{u,j}.                \tag{2.5}
\]

The value at `j=ell` is auxiliary notation, not an added T38 summand:

\[
 X_{u,\ell}=1.                                    \tag{2.6}
\]

T55's signed Fourier range is literally
`signedFrequenciesZero (R-1)`, namely all integers `-H <= u <= H`.
Its exact stratum identity and signed conjugate aggregation give

\[
 \begin{aligned}
 E_{\ell,R}(\beta)
  &:=\sum_{j=0}^{\ell-1}F_{R-1}
       \!\left(\beta(10^\ell-10^j)\right)\\
  &=\ell+2\operatorname{Re}
       \sum_{u=1}^{H}\left(1-\frac uR\right)F_u. \tag{2.7}
 \end{aligned}
\]

The first term is exactly the zero-frequency contribution. The factor two
retains the two labels `u` and `-u`; it uses `F_{-u}=conj(F_u)` only after
both signed occurrences have been included.

## 3. T55's complete signed pairing and its boundaries

Before orbit notation, T55's label-level source is exactly

\[
 (\epsilon,u,t):\quad \epsilon\in\{-1,1\},\quad
 1\leq u,\quad10u\leq H,\quad1\leq t\leq\ell,    \tag{3.1}
\]

and its target is exactly

\[
 (\epsilon,v,j):\quad \epsilon\in\{-1,1\},\quad
 1\leq v\leq H,\quad10\mid v,\quad0\leq j<\ell. \tag{3.2}
\]

The checked bijection and inverse are

\[
 (\epsilon,u,t)\longmapsto(\epsilon,10u,t-1),
 \qquad
 (\epsilon,v,j)\longmapsto(\epsilon,v/10,j+1).   \tag{3.3}
\]

Thus the stratum boundaries `t=1`, `t=ell`, `j=0`, and `j=ell-1`, and
the Fourier boundaries `10u<=H`, `v<=H`, are all present in the domains.
In T55's literal Finset notation, the positive frequencies with a legal
successor and the unpaired cutoff shell are

\[
 \operatorname{pairingSourceShell}(R)=Icc(1,H/10),\qquad
 \operatorname{terminalShell}(R)=Ioc(H/10,H),               \tag{3.4}
\]

and T55 checks the exact disjoint partition

\[
 Icc(1,H)=Icc(1,H/10)\mathbin\cup Ioc(H/10,H).               \tag{3.5}
\]

For a signed integer `u` with `|10u|<=H`, define T55's indispensable
transport phase

\[
 \rho_u:=e(-9\beta u10^\ell).                    \tag{3.6}
\]

Its checked phase transport is

\[
 \rho_uX_{10u,j}=X_{u,j+1}\qquad(0\leq j<\ell). \tag{3.7}
\]

Summing over the complete displayed range gives T55's exact one-step
telescope

\[
 \boxed{
 F_u-\rho_uF_{10u}=X_{u,0}-X_{u,\ell}
 =e\!\left(\beta u(10^\ell-1)\right)-1.}         \tag{3.8}
\]

The lower endpoint `j=0` is an original stratum term. The upper endpoint
`j=ell` is exactly one and appears once with a minus sign from telescoping.
For `ell=1` the interior cancellation range is empty, although the
source-target pairing still contains its boundary label; (3.8) remains exact.

## 4. Collision-free orbit coordinates, not collision-free phases

If `H=0`, there are no positive frequencies; Section 9 handles this edge
case. Assume in Sections 4-8 that `H>=1`. Define

\[
 \mathcal P_H:=\{a\in\mathbb N:1\leq a\leq H,\ 10\nmid a\}. \tag{4.1}
\]

For each `a in P_H`, put

\[
 u_{a,q}:=a10^q,\qquad
 Q_a:=\max\{q\geq0:u_{a,q}\leq H\}.              \tag{4.2}
\]

The cutoff boundary is exactly

\[
 u_{a,Q_a}\leq H<10u_{a,Q_a}.                   \tag{4.3}
\]

Repeated division by ten gives every `1<=u<=H` a unique representation
`u=u_(a,q)` with `a in P_H` and `0<=q<=Q_a`. Hence

\[
 \sum_{u=1}^{H}\left(1-\frac uR\right)F_u
 =\sum_{a\in\mathcal P_H}\sum_{q=0}^{Q_a}w_{a,q}F_{a,q},   \tag{4.4}
\]

where

\[
 w_{a,q}:=1-\frac{a10^q}{R}>0,
 \qquad F_{a,q}:=F_{u_{a,q}}.                   \tag{4.5}
\]

Uniqueness of `(a,q)` does not make the full phase frequencies distinct.
T55 checks the numerical collision

\[
 10(10^2-1)=11(10^2-10)=990,                    \tag{4.6}
\]

while also checking that the labels `(10,0)` and `(11,1)` differ. All sums
below remain over labeled orbit and stratum coordinates. Thus both terms in
(4.6), and every analogous collision, retain their multiplicity.

## 5. Orbitwise stopping selector

An orbitwise stopping selector is any function choosing

\[
 \sigma_a\in\{0,\ldots,Q_a\}\qquad(a\in\mathcal P_H).      \tag{5.1}
\]

The convention is that the edges `q=0,...,sigma_a-1` are telescoped and the
vertex `q=sigma_a` is retained. Every used edge is legal because
`q<sigma_a<=Q_a` implies `10u_(a,q)=u_(a,q+1)<=H`.

Abbreviate

\[
 \rho_{a,q}:=e(-9\beta u_{a,q}10^\ell),\qquad
 b_{a,q}:=e\!\left(\beta u_{a,q}(10^\ell-1)\right)-1.      \tag{5.2}
\]

Define accumulated coefficients by

\[
 \Gamma_{a,0}:=w_{a,0},\qquad
 \Gamma_{a,q}:=w_{a,q}+\rho_{a,q-1}\Gamma_{a,q-1}
 \quad(1\leq q\leq Q_a).                         \tag{5.3}
\]

Since

\[
 \prod_{t=p}^{q-1}\rho_{a,t}
 =e\!\left(\beta(u_{a,p}-u_{a,q})10^\ell\right),           \tag{5.4}
\]

with empty product one, the nonrecursive coefficient is

\[
 \boxed{
 \Gamma_{a,q}=\sum_{p=0}^{q}w_{a,p}
 e\!\left(\beta(u_{a,p}-u_{a,q})10^\ell\right).}           \tag{5.5}
\]

This is T55's `orbitCoefficient` evaluated along the unique predecessor
chain of `u_(a,q)`.

## 6. Exact partial-telescoping identity

Fix one orbit and write `s=sigma_a`. Multiply (3.8) at edge `q` by
`Gamma_(a,q)`, then use

\[
 \Gamma_{a,0}=w_{a,0},\qquad
 \Gamma_{a,q}-\rho_{a,q-1}\Gamma_{a,q-1}=w_{a,q}.          \tag{6.1}
\]

Every coefficient then matches, giving

\[
 \boxed{
 \begin{aligned}
 \sum_{q=0}^{Q_a}w_{a,q}F_{a,q}
  ={}&\sum_{q=0}^{s-1}\Gamma_{a,q}b_{a,q}
     +\Gamma_{a,s}F_{a,s}\\
    &+\sum_{q=s+1}^{Q_a}w_{a,q}F_{a,q}.
 \end{aligned}}                                             \tag{6.2}
\]

The first sum is empty at `s=0`; the last is empty at `s=Q_a`. Terms
`q>s` are untouched original T55 Fourier terms, not absorbed into a renamed
correlation. At `s=Q_a`, (4.3) says the retained block has no legal successor;
choosing `s=Q_a` on every orbit recovers exactly T55's existing terminal
shell `(R-1)/10<u<=R-1` and is not a strict reduction.

For complete inspection of frequencies, (5.5) gives

\[
 \Gamma_{a,s}F_{a,s}
 =\sum_{p=0}^{s}\sum_{j=0}^{\ell-1}w_{a,p}
 e\!\left(\beta(u_{a,p}10^\ell-u_{a,s}10^j)\right),        \tag{6.3}
\]

while

\[
 \Gamma_{a,q}b_{a,q}
 =\sum_{p=0}^{q}w_{a,p}\left[
 e\!\left(\beta(u_{a,p}10^\ell-u_{a,q})\right)
 -e\!\left(\beta(u_{a,p}-u_{a,q})10^\ell\right)
 \right],                                                   \tag{6.4}
\]

and the untouched tail is

\[
 \sum_{q=s+1}^{Q_a}\sum_{j=0}^{\ell-1}w_{a,q}
 e\!\left(\beta u_{a,q}(10^\ell-10^j)\right).              \tag{6.5}
\]

Equations (6.3)-(6.5) are labeled sums. Equal integer phase frequencies may
be collected by adding all their coefficients, but they may not be
deduplicated, deleted, or assigned multiplicity one.

## 7. Exact stopped global identity

Define the selected stopped correlations and the remainder by

\[
 \mathcal C_\sigma:=\sum_{a\in\mathcal P_H}
       \Gamma_{a,\sigma_a}F_{a,\sigma_a},                   \tag{7.1}
\]

\[
 \mathcal A_\sigma:=\sum_{a\in\mathcal P_H}\left(
   \sum_{q=0}^{\sigma_a-1}\Gamma_{a,q}b_{a,q}
   +\sum_{q=\sigma_a+1}^{Q_a}w_{a,q}F_{a,q}\right).         \tag{7.2}
\]

Summing (6.2), then applying T55's complete signed aggregation (2.7), gives
the stopped-orbit identity

\[
 \boxed{
 E_{\ell,R}(\beta)=\ell+2\operatorname{Re}
   (\mathcal C_\sigma+\mathcal A_\sigma).}                  \tag{7.3}
\]

This accounts for the zero label, both nonzero signs, every triangular
weight, every lower and upper stratum endpoint, every untouched tail, every
stopping fiber, and the Fourier cutoff.

## 8. Phase-blind majorants and exact optimization

Put

\[
 W_{a,q}:=\sum_{p=0}^{q}w_{a,p}
 =(q+1)-\frac{a(10^{q+1}-1)}{9R}.                           \tag{8.1}
\]

The phase-blind inequalities are exactly

\[
 |\Gamma_{a,q}|\leq W_{a,q},\qquad
 |b_{a,q}|\leq2,\qquad |F_{a,q}|\leq\ell.                  \tag{8.2}
\]

If the stopped correlation is retained but every term in
`A_sigma` is charged labelwise, its orbit cost is

\[
 K_a(s):=2\sum_{q=0}^{s-1}W_{a,q}
       +\ell\sum_{q=s+1}^{Q_a}w_{a,q}.                      \tag{8.3}
\]

It has the closed form

\[
 \begin{aligned}
 K_a(s)={}&s(s+1)
 -\frac{2a}{9R}\left(\frac{10(10^s-1)}9-s\right)\\
 &+\ell\left[Q_a-s-
 \frac{a(10^{Q_a+1}-10^{s+1})}{9R}\right].                 \tag{8.4}
 \end{aligned}
\]

The exact adjacent difference is

\[
 K_a(s+1)-K_a(s)=2W_{a,s}-\ell w_{a,s+1}.                   \tag{8.5}
\]

This records the possible tradeoff if `C_sigma` is to be attacked by a later
phase-sensitive estimate: advancing one edge adds endpoint cost `2W_(a,s)`
and removes untouched-block cost `ell*w_(a,s+1)`.

For the phase-blind architecture under review, the selected block must also
be charged by (8.2). Its full orbit cost is therefore

\[
 \begin{aligned}
 P_a(s)&:=K_a(s)+\ell W_{a,s}\\
 &=\ell W_{a,Q_a}+2\sum_{q=0}^{s-1}W_{a,q}.                 \tag{8.6}
 \end{aligned}
\]

Consequently

\[
 \boxed{P_a(s+1)-P_a(s)=2W_{a,s}>0.}                        \tag{8.7}
\]

Strict positivity follows from `u_(a,p)<=R-1`, which gives every
`w_(a,p)>=1/R>0`. Hence the unique optimum for this uncollected labelwise cost
on every nontrivial orbit is

\[
 \boxed{\sigma_a=0.}                                       \tag{8.8}
\]

Thus a coefficient-only treatment should not telescope even one edge. Its
exact optimized positive-frequency budget is

\[
 \begin{aligned}
 P^*_{\ell,R}
 &=\ell\sum_{a\in\mathcal P_H}W_{a,Q_a}
  =\ell\sum_{u=1}^{R-1}\left(1-\frac uR\right)\\
 &=\boxed{\frac{\ell(R-1)}2}.                              \tag{8.9}
 \end{aligned}
\]

The orbit partition proves the middle equality without assuming distinct
phase frequencies. Combining (7.3) with the fully phase-blind charge gives

\[
 \ell(2-R)\leq E_{\ell,R}(\beta)\leq\ell R.                 \tag{8.10}
\]

Nonnegativity of the Fejer kernels can improve the left side only to zero;
it cannot yield T38's required strict positive lower bound.

For completeness, collision collection does not produce a hidden better
coefficient norm. Before taking a real part, summing the complex identity
(6.2) over all primitive roots and using (4.4) gives

\[
 \boxed{\mathcal C_\sigma+\mathcal A_\sigma
 =\sum_{u=1}^{R-1}\left(1-\frac uR\right)F_u.}              \tag{8.11}
\]

In the original positive-frequency polynomial, define

\[
 c_m:=\sum_{\substack{1\leq u\leq R-1,\ 0\leq j<\ell\\
          u(10^\ell-10^j)=m}}
       \left(1-\frac uR\right).                              \tag{8.12}
\]

Every `c_m` is nonnegative, and every labeled `(u,j)` occurs once, including
all collisions. Therefore

\[
 \sum_m|c_m|=\sum_m c_m
 =\ell\sum_{u=1}^{R-1}\left(1-\frac uR\right)
 =P^*_{\ell,R}.                                             \tag{8.13}
\]

The complex stopped identity (8.11) holds in the variable `beta`. After
collecting equal integer frequencies, uniqueness of a finite Fourier
polynomial (equivalently, integration against `e(-m beta)` on `[0,1]`)
returns exactly the coefficients (8.12). Thus the fully collision-collected
coefficient norm is `P*_(ell,R)` for every selector. Immediate stopping is
uniquely optimal for the explicit uncollected cost (8.6); after maximal legal
collision collection all selectors tie, and none improves (8.9).

## 9. Edge cases

If `R=1`, then `H=0`, `P_H` is empty, and T55 gives

\[
 E_{\ell,1}(\beta)=\ell.                                   \tag{9.1}
\]

There is no selector or residual correlation to optimize. If `Q_a=0`, the
only legal choice is `sigma_a=0`, (6.2) reads
`w_(a,0)F_(a,0)=Gamma_(a,0)F_(a,0)`, and both other sums are empty. If
`ell=1`, every block has only `j=0`; the auxiliary endpoint `j=1` in (3.8)
is still exactly one, so all identities and costs above remain valid.

## 10. T55's literal strict threshold

For data satisfying (2.2)-(2.3), T55's checked strict T38 target is

\[
 \boxed{
 \Theta_{\ell,R,\delta}:=
 \frac{\ell}{4R\delta^2}<E_{\ell,R}(\beta).}                \tag{10.1}
\]

Equivalently, the positive-frequency sum in (2.7) must satisfy

\[
 \operatorname{Re}\sum_{u=1}^{R-1}
 \left(1-\frac uR\right)F_u
 >\frac{\ell}{8R\delta^2}-\frac\ell2.                       \tag{10.2}
\]

The right side is a lower bound. The optimized quantity (8.9) is only an
absolute coefficient radius and supplies no sign. A legal family below makes
the quantitative mismatch exact.

## 11. Exact legal factor-four family

For every integer `t>=1`, set

\[
 U:=10^t-1,
\quad M:=t+2,
\quad D:=2,
\quad K:=2,
\quad d:=1,
\quad h:=1,
\quad r:=0,                                                \tag{11.1}
\]

and take forbidden set `{r}={0}`, lower shift bound `B=1`, and the one-term
shift list `[t]`. This explicitly inhabits T55's required type

\[
 \operatorname{GeometricResonanceChain}
 (\operatorname{initialCoefficient}(1,0))\ M\ 2\ 1\ 2\ 1\ \{0\}.
                                                               \tag{11.2}
\]

Indeed, the list has length one and no duplicate, `1<=t`, `t` avoids `{0}`,
and the final residual is

\[
 M-t=2=K.                                                   \tag{11.3}
\]

Moreover

\[
 \operatorname{initialCoefficient}(1,0)
 =(10^0-1)\pi=0,                                           \tag{11.4}
\]

so every geometric phase at both nodes equals one. The two node-resonance
fields reduce exactly to

\[
 \frac{t+2}{\operatorname{densityDenominator}(2,0)}
 =\frac{t+2}{2}<t+2,
 \qquad
 \frac{2}{\operatorname{densityDenominator}(2,1)}
 =\frac2{32}<2.                                            \tag{11.5}
\]

Thus no chain existence is being assumed. Choose its only adjacent index
`k=0` and choose `ell=1`. The two residuals are `t+2` and `2`, so

\[
 \operatorname{commonDepth}=2,
 \qquad1=\ell<2,                                           \tag{11.6}
\]

which is T55's literal depth condition. Its adjacent multiplier is exactly
`U=10^t-1>=9`.

Let `eta_i=inverseError(nodeTau(2,i))`. Since

\[
 \operatorname{densityDenominator}(2,0)=2,
 \quad \operatorname{densityDenominator}(2,1)=32,
\]

one has

\[
 \operatorname{nodeTau}(2,0)=\frac1{32},
 \qquad \operatorname{nodeTau}(2,1)=\frac1{8192}.           \tag{11.7}
\]

Both numbers lie strictly between zero and `1/2`. Since `arccos` is strictly
decreasing on this interval and `arccos(1/2)=pi/3`, T55's unfolded inverse
error gives

\[
 \eta_0>\frac16,\qquad\eta_1>\frac16.                       \tag{11.8}
\]

T55's literal stratum radius at `ell=1` is therefore

\[
 \begin{aligned}
 \delta
 &=\min\left\{\eta_0,\frac{\eta_1}{U},
                 \frac1{2U10}\right\}\\
 &=\boxed{\frac1{20U}},                                   \tag{11.9}
 \end{aligned}
\]

because `U>=9`, `1/(20U)<1/6`, and
`eta_1/U>1/(6U)>1/(20U)`. Hence T55's literal integral order is

\[
 R=\left\lceil\delta^{-1}\right\rceil
  =\boxed{20U}.                                             \tag{11.10}
\]

On this exact legal family the strict target and optimized phase-blind scales
are

\[
 \Theta_{1,R,\delta}
 =\frac1{4R\delta^2}=\frac R4=5U,
 \qquad
 1+2P^*_{1,R}=R.                                           \tag{11.11}
\]

Thus the coefficient-envelope scale satisfies

\[
 \boxed{\frac{1+2P^*_{1,R}}{\Theta_{1,R,\delta}}=4.}        \tag{11.12}
\]

More directly, (10.2) requires a positive-frequency lower bound

\[
 \operatorname{Re}\sum_{u=1}^{R-1}
 \left(1-\frac uR\right)F_u>\frac{R-4}{8},                 \tag{11.13}
\]

whereas coefficient-only information supplies merely the symmetric radius

\[
 \left|\sum_{u=1}^{R-1}
 \left(1-\frac uR\right)F_u\right|\leq\frac{R-1}{2}.        \tag{11.14}
\]

The uncertainty radius exceeds the required positive excess by the explicit
factor

\[
 \boxed{\frac{(R-1)/2}{(R-4)/8}
 =\frac{4(R-1)}{R-4}>4.}                                   \tag{11.15}
\]

At the smallest member `t=1`, these values are

\[
 U=9,\quad R=180,\quad\Theta=45,\quad
 \frac{(R-1)/2}{(R-4)/8}=\frac{179}{44}.                   \tag{11.16}
\]

For transparency, `beta=0` makes the actual Fejer sum equal to `R`, so this
family is not a counterexample to FSFS. It is an exact obstruction to the
specified phase-blind proof architecture: after phases are discarded, its
sharp coefficient envelope has scale `R=4Theta`, while its guaranteed lower
bound is only `2-R`, or zero after adding Fejer nonnegativity, strictly below
`Theta=R/4`. Equation (11.15) quantifies the uncertainty radius, not a
multiplicative deficit in that lower bound. Recovering the actual value `R`
uses phase information (`beta=0`) and is outside that architecture.

## 12. Verdict and conditional payoff only

The optimization (8.7) proves that orbitwise stopping cannot improve the
fully coefficient-only estimate: immediate stopping is uniquely optimal for
the uncollected labelwise cost, while (8.11)-(8.13) prove that every selector
ties after complete legal collision collection. Immediate stopping retains
the entire original positive Fourier range, so it is not a smaller residual
and cannot honestly be called `STRICT REDUCTION`. On the exact legal family,
the optimized phase-blind guaranteed lower bound is zero while T55 requires
the strict positive bound `R/4`; its uncertainty radius exceeds the required
positive excess by the explicit factor (11.15), and its total envelope scale
is four times the threshold. Therefore `SUFFICIENT` is unavailable without
phase-sensitive input.

This is only a barrier for stopping plus coefficient magnitudes and triangle
inequalities. It is not a claim that FSFS fails, and it is not a claim about
cancellation for the fixed positive multiples of `pi` arising from T26's
failure-of-A1 route. In particular, the family has `r=0`; it is legal for the
T55/T38 theorem types but does not satisfy T55's later positive-`r` premise
for the conditional T28 contradiction. If a future phase-sensitive argument
does establish T55's strict threshold for a positive-`h`, positive-`r` chain,
then T55 supplies FSFS and its T34 mixed-sum consequence; only with T28's
separate exponent-eight and closing hypotheses would the conditional T28
contradiction follow. None of those hypotheses or conclusions is asserted
here.

PHASE-BLIND BARRIER
