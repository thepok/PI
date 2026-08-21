# T58: one adjacent T26 pullback of T55's terminal coefficients

Claim label: **proof sketch**. The T26 and T55 inputs cited below are
machine-checked. The coefficient expansion, variance reduction, and exact
arithmetic in this note are given for inspection but are not separately
formalized.

## 1. Provenance and exact scope

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. It records no external
source URL; it says that the question was formulated by this system on
2026-07-22. Its verified SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For real `x`, let `||x||_(R/Z)` be distance to the nearest integer and set

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
`A,n`. Infinitely many `n`, one fixed `A`, prescribed `N`, unordered pairs,
or removal of the diagonal are different statements. T58 changes none of
these quantifiers. It proves no instance of (1.1), no fixed-`pi` estimate, and
no unconditional C1, C2, FSFS, or T28 statement.

The only research inputs used as established are:

| item | file | SHA-256 | interface used |
|---|---|---|---|
| T26 | `TheoryLib/PiLacunaryNearReturnSparsity/T26SharedResonanceChain.lean` | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | geometric-chain coefficients, residuals, shifts, and node resonance ranges |
| T55 | `TheoryLib/PiLacunaryNearReturnSparsity/T55SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | literal shell decomposition, exact complex coefficients, endpoints, signed aggregation, collisions, and strict threshold |

The T57 note, SHA-256
`f92fe204dc9cc42996f73752dc42a207610e566248001da6f3817977a73c86dd`,
is an unverified proof sketch. Its endpoint warning motivated retaining phases,
but no claim from T57 is a premise here. No literature or novelty claim is
made; this is an internal finite reduction of the two checked interfaces.

## 2. Adjacent nodes and all index ranges

Fix T26 data with `1<=D`

\[
 \mathcal C:\operatorname{GeometricResonanceChain}
  (\operatorname{initialCoefficient}(h,r))\ M\ D\ 1\ K\ d\ \{r\}.
                                                               \tag{2.1}
\]

T55's checked positivity interface then gives `delta>0` and `1<=R`. Thus the
signed aggregation used below has its required `R` premise; no empty or
negative cutoff convention is being inserted.

Fix natural numbers `k,q` with

\[
 q=k+1<d.                                                     \tag{2.2}
\]

Thus `q` is a noninitial node and is also a legal T55 node in `Fin d`. Let

\[
 s_-:=\mathcal C.\mathrm{shifts}[k],\qquad
 U_-:=10^{s_-}-1,                                            \tag{2.3}
\]

and write

\[
 \beta_0:=\mathcal C.\operatorname{nodeCoefficient}(k),
 \qquad
 \beta:=\mathcal C.\operatorname{nodeCoefficient}(q).       \tag{2.4}
\]

The subscript on `s_-` is important: it is the incoming shift from `k` to
`q`. T55's stratum at `q` also uses the outgoing shift
`s_+ = C.shifts[q]` in its radius. These two shifts are not identified.

Choose a legal T55 stratum

\[
 1\leq\ell<\operatorname{commonDepth}(\mathcal C,q),          \tag{2.5}
\]

and put, exactly as in T55,

\[
 \delta:=\operatorname{stratumDelta}(\mathcal C,q,\ell),
 \qquad R:=\operatorname{stratumOrder}(\mathcal C,q,\ell)
       =\lceil\delta^{-1}\rceil,
 \qquad H:=R-1.                                               \tag{2.6}
\]

T55's signed Fourier range is every integer

\[
 -H\leq u\leq H.                                              \tag{2.7}
\]

The zero label contributes `ell`. The two labels `u` and `-u` remain in the
signed sum; conjugacy later produces the explicit factor two. The positive
source and terminal ranges are exactly

\[
 \mathcal S=\{u:1\leq u\leq\lfloor H/10\rfloor\},\qquad
 \mathcal T=\{u:\lfloor H/10\rfloor<u\leq H\}.               \tag{2.8}
\]

In Lean these are `Icc 1 ((R-1)/10)` and
`Ioc ((R-1)/10) (R-1)`. Every T55 frequency block has precisely

\[
 0\leq j<\ell.                                                \tag{2.9}
\]

The auxiliary value `j=ell` occurs only as the upper telescope endpoint; it
is not an additional block summand.

## 3. The genuine adjacent T26 coefficient step

T26 defines

\[
 \operatorname{nodeCoefficient}(a)
 =c\prod_{t\in\operatorname{take}(a,\mathcal C.\mathrm{shifts})}
       (10^t-1),
 \qquad c=\operatorname{initialCoefficient}(h,r).             \tag{3.1}
\]

Because `q=k+1<d`, the literal list identity is

\[
 \operatorname{take}(k+1,\mathcal C.\mathrm{shifts})
 =\operatorname{take}(k,\mathcal C.\mathrm{shifts})
    \mathbin{++}[s_-].                                        \tag{3.2}
\]

Substitution in (3.1), with no estimate, gives

\[
 \boxed{\beta=U_-\beta_0=(10^{s_-}-1)\beta_0.}               \tag{3.3}
\]

For every integer `m`, define the preceding-node character

\[
 \chi_0(m):=e(\beta_0m),\qquad e(x):=\exp(2\pi i x).          \tag{3.4}
\]

Then (3.3) gives the exact adjacent autocorrelation identity

\[
 \boxed{
 e(\beta m)=
 \chi_0(10^{s_-}m)\,\overline{\chi_0(m)}.}                   \tag{3.5}
\]

Both factors in (3.5) are retained. In particular, (3.5) is not replaced by
the uninformative absolute bound `1`.

## 4. Pulling back T55's literal terminal coefficients

For `1<=v<=H`, write

\[
 w_R(v):=1-\frac vR>0.                                       \tag{4.1}
\]

For a positive integer `u`, let `nu_10(u)` be the largest `a>=0` such that
`10^a` divides `u`. Iterating T55's checked recurrence for
`orbitCoefficient`, including its transport phase at every predecessor,
gives the finite identity

\[
 \boxed{
 \Gamma_\beta(u)=
 \sum_{a=0}^{\nu_{10}(u)}
 w_R(u/10^a)\,
 e\!\left(\beta\left(\frac{u}{10^a}-u\right)10^\ell\right).}
                                                               \tag{4.2}
\]

Indeed, one predecessor step contributes T55's exact factor
`e(-9 beta (u/10) 10^ell)`, and products of consecutive factors telescope
to the exponent in (4.2). No norm bound has entered.

T55's literal block is

\[
 F_\beta(u)=\sum_{j=0}^{\ell-1}
 e\!\left(\beta u(10^\ell-10^j)\right).                      \tag{4.3}
\]

Multiplying (4.2) and (4.3), define the integer frequency

\[
 m_{u,a,j}:=\frac{u}{10^a}10^\ell-u10^j.                     \tag{4.4}
\]

T55's checked flattened terminal sum is therefore exactly

\[
 \operatorname{terminalCorrelation}(\beta,\ell,R)
 =\sum_{u=\lfloor H/10\rfloor+1}^{H}
   \sum_{a=0}^{\nu_{10}(u)}
   \sum_{j=0}^{\ell-1}
   w_R(u/10^a)e(\beta m_{u,a,j}).                             \tag{4.5}
\]

Applying (3.5) term by term gives the requested adjacent T26 pullback:

\[
 \boxed{
 \operatorname{terminalCorrelation}(\beta,\ell,R)
 =\sum_{u=\lfloor H/10\rfloor+1}^{H}
   \sum_{a=0}^{\nu_{10}(u)}
   \sum_{j=0}^{\ell-1}
   w_R(u/10^a)
   \chi_0(10^{s_-}m_{u,a,j})
   \overline{\chi_0(m_{u,a,j})}.}                            \tag{4.6}
\]

The domain in (4.6) is a labeled triple sum. Distinct triples are never
identified if their numerical frequencies agree. For example, T55 checks

\[
 10(10^2-1)=11(10^2-10)=990,                                 \tag{4.7}
\]

while retaining `(u,j)=(10,0)` and `(11,1)` as distinct labels. Equations
(4.5)-(4.6) use the same multiplicity convention.

## 5. Direct labels versus genuine predecessor labels

Separate (4.6) at predecessor depth `a=0`:

\[
 C_0:=\sum_{u\in\mathcal T}\sum_{j=0}^{\ell-1}
 w_R(u)\chi_0(10^{s_-}m_{u,0,j})
       \overline{\chi_0(m_{u,0,j})},                          \tag{5.1}
\]

\[
 C_+:=\sum_{u\in\mathcal T}
 \sum_{a=1}^{\nu_{10}(u)}\sum_{j=0}^{\ell-1}
 w_R(u/10^a)\chi_0(10^{s_-}m_{u,a,j})
       \overline{\chi_0(m_{u,a,j})}.                         \tag{5.2}
\]

The `a`-sum in (5.2) is empty when `10` does not divide `u`. Thus

\[
 \operatorname{terminalCorrelation}(\beta,\ell,R)=C_0+C_+   \tag{5.3}
\]

is an exact coefficient split, not a support quotient.

Define the explicit positive masses

\[
 A_0:=\ell\sum_{u\in\mathcal T}w_R(u),                       \tag{5.4}
\]

\[
 X:=\ell\sum_{u\in\mathcal T}
       \sum_{a=1}^{\nu_{10}(u)}w_R(u/10^a).                  \tag{5.5}
\]

Every phase in (5.2) has modulus one, so the only estimate in this split is

\[
 \operatorname{Re}C_+\geq-|C_+|\geq-X.                      \tag{5.6}
\]

## 6. One explicit adjacent phase-variance inequality

For the direct frequency

\[
 m_{u,j}:=m_{u,0,j}=u(10^\ell-10^j),                         \tag{6.1}
\]

define the fully ranged weighted variance

\[
 \boxed{
 V_-:=\sum_{u=\lfloor H/10\rfloor+1}^{H}
       \sum_{j=0}^{\ell-1}w_R(u)
       \left|\chi_0(10^{s_-}m_{u,j})-\chi_0(m_{u,j})\right|^2.}
                                                               \tag{6.2}
\]

For unit complex numbers `z,y`,

\[
 \operatorname{Re}(z\overline y)=1-\frac12|z-y|^2.          \tag{6.3}
\]

Apply (6.3) to every labeled pair in (5.1). The result is the exact identity

\[
 \boxed{\operatorname{Re}C_0=A_0-\frac12V_-.}               \tag{6.4}
\]

This is phase variance at the preceding T26 node: it compares the two genuine
factors at indices `m` and `10^s_- m` whose product is the adjacent-node
phase. It is not coefficient energy and not a synthetic phase.

T55's endpoint range is the complete source shell

\[
 1\leq v\leq\lfloor H/10\rfloor.                             \tag{6.5}
\]

Its exact endpoint is

\[
 E:=\sum_{v=1}^{\lfloor H/10\rfloor}
 \Gamma_\beta(v)
 \left[e\!\left(\beta v(10^\ell-1)\right)-1\right],         \tag{6.6}
\]

where the final `1` is exactly the auxiliary upper endpoint `j=ell`. T55's
checked budget is

\[
 B_{\rm end}:=2\sum_{v=1}^{\lfloor H/10\rfloor}
                 |\Gamma_\beta(v)|,
 \qquad \operatorname{Re}E\geq-B_{\rm end}.                 \tag{6.7}
\]

For complete phase visibility, (4.2) and (3.5) also give

\[
 B_{\rm end}=2\sum_{v=1}^{\lfloor H/10\rfloor}
 \left|\sum_{a=0}^{\nu_{10}(v)}w_R(v/10^a)
 \chi_0(10^{s_-}n_{v,a})\overline{\chi_0(n_{v,a})}\right|, \tag{6.8}
\]

with

\[
 n_{v,a}:=(v/10^a-v)10^\ell.                                \tag{6.9}
\]

Finally set

\[
 \Theta:=\frac{\ell}{4R\delta^2}.                           \tag{6.10}
\]

The one additional premise tested in this note is the following strict,
quantitative inequality:

\[
 \boxed{
 \text{(DLAPV)}\qquad
 V_-<\ell+2A_0-2X-2B_{\rm end}-\Theta.}                     \tag{6.11}
\]

Its name is the **Direct-Label Adjacent Phase-Variance bound**. Every term and
range in (6.11) is displayed in (2.8)-(2.9), (5.4)-(5.5), and
(6.2), (6.5)-(6.10).

## 7. Quantitative payoff from DLAPV

T55's exact signed aggregation and terminal decomposition give

\[
 S_{\ell,R}(\beta)
 :=\sum_{j=0}^{\ell-1}
   \operatorname{fejerKernel}(R-1,
     \beta(10^\ell-10^j))
 =\ell+2\operatorname{Re}(E+C_0+C_+).                        \tag{7.1}
\]

The factor two in (7.1) is the retained multiplicity of the positive and
negative signed frequencies. Combining (5.6), (6.4), and (6.7) yields the
displayed unconditional lower estimate

\[
 \boxed{
 S_{\ell,R}(\beta)
 \geq \ell-2B_{\rm end}+2A_0-V_--2X.}                       \tag{7.2}
\]

If DLAPV holds, its strict inequality substituted into (7.2) gives

\[
 \boxed{
 \frac{\ell}{4R\delta^2}=\Theta
 <S_{\ell,R}(\beta).}                                       \tag{7.3}
\]

Equation (7.3) is T55's literal strict T38 threshold. No FSFS or T28
conclusion is asserted here: those are only the already checked conditional
payoffs once all of their separate legality premises are supplied.

DLAPV is not T55's `TopShellCorrelationHypothesis` under another name. It
controls only the direct labels `a=0` by a positive square difference and
uses the worst-case bound `-X` for all genuine predecessor labels `a>=1`.
The full top-shell hypothesis may instead use favorable predecessor phases.
Section 9 gives a literal example where the full hypothesis holds but DLAPV
fails, proving that the two conditions are not equivalent.

## 8. Literal test where DLAPV holds

Take the following exact inhabitant of T26's chain structure and T55's chain
type:

\[
 h=1,\ r=0,\ M=5,\ D=2,\ B_{\rm chain}=1,\ K=2,\ d=2,
 \quad F=\{0\},\quad \mathcal C.\mathrm{shifts}=[2,1].       \tag{8.1}
\]

The list has length two, has no duplicate, every shift is at least one, and
both shifts avoid `{0}`. Its final residual condition is equality:

\[
 K=2=5-(2+1).                                                \tag{8.2}
\]

Because

\[
 \operatorname{initialCoefficient}(1,0)
 =1(10^0-1)\pi=0,                                            \tag{8.3}
\]

all geometric phases are one. The residual lengths are `5,3,2`; the density
denominators are `2,32,8192`. Hence every required T26 node inequality is
literal:

\[
 \frac52<5,\qquad \frac3{32}<3,\qquad \frac2{8192}<2.       \tag{8.4}
\]

Use the noninitial T55 node `q=1` and `ell=1`. Its incoming shift is `s_-=2`,
while its outgoing shift is `s_+=1`; thus `U_-=99` and the outgoing factor
used in `delta` is `9`. The two residuals at `q,q+1` are `3,2`, so

\[
 1\leq\ell=1<\operatorname{commonDepth}(\mathcal C,1)=2.    \tag{8.5}
\]

At nodes `1,2`, both `nodeTau` values are below `1/2`. Since `arccos` is
strictly decreasing and `arccos(1/2)=pi/3`, both inverse-error terms exceed
`1/6`. Consequently the third entry in T55's literal minimum is smallest:

\[
 \delta=\min\left\{\eta_1,\frac{\eta_2}{9},
                    \frac1{2\cdot9\cdot10}\right\}
       =\frac1{180},
 \qquad R=180,\quad H=179.                                  \tag{8.6}
\]

Thus every range is explicit:

\[
 \mathcal S=\{1,\ldots,17\},\qquad
 \mathcal T=\{18,\ldots,179\},\qquad j=0.                  \tag{8.7}
\]

At `beta_0=beta=0`, all complex factors in (6.2) are one, so

\[
 V_-=0.                                                      \tag{8.8}
\]

The exact finite sums are

\[
 B_{\rm end}=\frac{1543}{45},\qquad
 A_0=\frac{1467}{20},\qquad
 X=\frac{323}{20},\qquad
 \Theta=45.                                                  \tag{8.9}
\]

For example, only `10` is divisible by ten in the source shell, so

\[
 \frac12B_{\rm end}
 =\sum_{v=1}^{17}w_R(v)+w_R(1)=\frac{1543}{90}.              \tag{8.10}
\]

In the terminal shell, the extra predecessors are `2,...,17`, together with
the second predecessor `1` of `u=100`; this gives `X=323/20`. Substitution
in the right side of DLAPV gives

\[
 1+2\frac{1467}{20}-2\frac{323}{20}
   -2\frac{1543}{45}-45
 =\frac{82}{45}>0.                                          \tag{8.11}
\]

Therefore the literal test satisfies

\[
 V_-=0<\frac{82}{45}.                                       \tag{8.12}
\]

The lower bound (7.2) is consequently

\[
 S_{1,180}(0)\geq\frac{2107}{45}>45=\Theta.                 \tag{8.13}
\]

The actual value is `S_(1,180)(0)=180`. This test verifies the constants and
shows that DLAPV is nonvacuous on the literal checked interface. It is not a
fixed-`pi` example.

## 9. Literal test proving DLAPV is not a renamed top-shell hypothesis

Keep every parameter in (8.1) except reverse the shifts:

\[
 \mathcal C.\mathrm{shifts}=[1,2].                           \tag{9.1}
\]

The residuals are `5,4,2`, so the complete T26 inequalities are

\[
 \frac52<5,\qquad \frac4{32}<4,\qquad \frac2{8192}<2.       \tag{9.2}
\]

At `q=1, ell=1`, the incoming shift is now `1` and the outgoing shift is `2`.
Thus

\[
 \delta=\frac1{1980},\qquad R=1980,\qquad H=1979,            \tag{9.3}
\]

with source shell `1<=u<=197` and terminal shell `198<=u<=1979`. Again
`beta_0=beta=0` and `V_-=0`. Direct summation gives

\[
 B_{\rm end}=\frac{204983}{495},\qquad
 A_0=\frac{16047}{20},\qquad
 X=\frac{3743}{20},\qquad
 \Theta=495.                                                 \tag{9.4}
\]

Here the DLAPV right side is negative:

\[
 1+2A_0-2X-2B_{\rm end}-\Theta
 =-\frac{45448}{495}<0.                                     \tag{9.5}
\]

Therefore DLAPV fails. Nevertheless, at zero phase the full T55 terminal
correlation retains every direct and predecessor label positively:

\[
 \operatorname{Re}\operatorname{terminalCorrelation}(0,1,1980)
 =A_0+X=\frac{1979}{2}.                                     \tag{9.6}
\]

T55's top-shell right side is

\[
 \frac{\Theta}{2}-\frac12+B_{\rm end}
 =247+B_{\rm end},                                          \tag{9.7}
\]

and the exact strict margin in (9.6)-(9.7) is

\[
 \frac{1979}{2}-247-\frac{204983}{495}
 =\frac{325109}{990}>0.                                     \tag{9.8}
\]

Thus T55's full top-shell hypothesis holds while DLAPV fails on one legal
chain. DLAPV is a proper stronger covariance premise on a proper component,
not an equivalent rewriting of the old hypothesis.

## 10. The one remaining gap and terminal status

T26 controls, at each node `a<=d`, only the magnitude

\[
 \left|\sum_{n=0}^{M_a-1}e(\beta_a10^n)\right|
 >\frac{M_a}{\operatorname{densityDenominator}(D,a)},
 \qquad
 M_a=M-\sum\operatorname{take}(a,\mathcal C.\mathrm{shifts}). \tag{10.1}
\]

It does not give an argument for that sum, a prefix bound over `j<ell`, or a
multiharmonic estimate at the collision-bearing frequencies
`u(10^ell-10^j)` in (6.2). T55 supplies the exact decomposition but no upper
bound for `V_-`. The two zero-phase tests show both that DLAPV can hold and
that it is not equivalent to T55's old full-shell premise; they do not prove
DLAPV for the positive-`r`, prescribed-`K` chains returned by T26's canonical
failure theorem. In particular, the test chains have `r=0` and are literal
interface tests only.

The single residual premise is therefore precisely the following proposition.
It is stated on T26's canonical-output subdomain, not on every inhabitant of
the bare chain structure.

> **Direct-Label Adjacent Phase-Covariance Gap.** For every
> `A,n,d,N,r,h` in `N` with `1<=A`, `1<=n`, and `2<=d`, define
> `D=initialDensity(A,n)`, `K=chainLengthRequest(D,d)`, and
> `L=iterationLengthThresholdAux(D,1,K,1,d)`. For every
> `C : GeometricResonanceChain(initialCoefficient(h,r), N-r, D, 1, K, d,
> {r})` satisfying
> `N=16*A*n*L`, `1<=r<=N-1`, and `1<=h<=256*A*n`, there exist natural
> numbers `k,ell` such that `k+1<d`, with `q=k+1`,
> `1<=ell<commonDepth(C,q)`, and (DLAPV) holds after instantiating
> `s_- = C.shifts[k]`, `beta_0=C.nodeCoefficient(k)`,
> `beta=C.nodeCoefficient(q)`, `delta=stratumDelta(C,q,ell)`,
> `R=stratumOrder(C,q,ell)`, and every labeled sum exactly as in
> (2.6), (2.8), (5.4)-(5.5), and (6.2), (6.5)-(6.11).

These quantifiers match the tuple returned at each requested depth by T26's
canonical failure-of-A1 theorem. The universal quantifier over its returned
chain witnesses is deliberate; the existential quantifier is only over the
noninitial adjacent node and legal stratum. The `r=0`, small-`K` test chains
in Sections 8-9 lie outside this quantified subdomain, so Section 9 proves
properness of DLAPV without refuting the named gap.

If that one premise is supplied, (7.2)-(7.3) give the quantitative T55
threshold. T26 and T55 alone do not currently supply it, and no broader
top-shell assumption is silently substituted.

OPEN WITH ONE NAMED PHASE-COVARIANCE GAP
