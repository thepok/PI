# T60: audit of the terminal decimal-ray condition

Claim label: **proof sketch**. The cited Lean interfaces are machine-checked.
All new finite identities and counterexamples below are proved in the note, but
they have not been formalized. The T58 note was read as motivation only; no
claim from T58 is a premise.

## 1. Provenance, immutable question, and scope

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. It records no external
source URL and says that the question was formulated by this system on
2026-07-22. Its SHA-256 was recomputed as

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For real `x`, let `||x||_(R/Z)` be distance to the nearest integer. The
canonical count is

\[
 Q_\pi(n,N)=\#\{(i,j)\in\{0,\ldots,N-1\}^2:
   \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

The canonical assertion, called A1 in the source file, is

\[
 \forall A\in\mathbb N_{\geq1}\ \exists n_0\geq1\
 \forall n\geq n_0\ \exists N\geq1:\quad
 A n Q_\pi(n,N)\leq N^2.                         \tag{1.2}
\]

Pairs are ordered, the diagonal is included, the distance is circular and
strict, and `N` may depend on both `A` and `n`. This note does not replace
`forall n >= n0` by infinitely many `n`, prescribe `N`, remove the diagonal,
or replace the circle distance by ordinary distance.

No assertion below proves (1.2), normality of pi, C1, C2, FSFS, or pair
correlation for pi. Artificial streams, general circle sequences, and
invariant measures are explicitly labeled as sibling counterexamples.

The checked interfaces used are:

| interface | SHA-256 | exact role |
|---|---|---|
| `PiLacunaryNearReturnSparsity/T4ClusterNearReturns.lean` | `894a6b785720fb456b3392a1ecf569ea4d9049b10eaba8d413c36851b84f77fd` | empirical probability measures, ordered closed pair counts, product convergence |
| `PiLacunaryNearReturnSparsity/T6CylinderCollision.lean` | `ff8327cfcc73207141b84d6f35ecb4e66345d82c227facd2d37e1034340c44f6` | half-open cylinder energy and its factor-three small-ball comparison |
| `PiLacunaryNearReturnSparsity/T7FiniteCylinderEnergy.lean` | `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c` | pi cylinder counts, ordered diagonal-inclusive normalization, exact A1 equivalence |
| `PiDigits/T26WeylCancellationV1.lean` | `3825d0dcb5bd4d22ffa3cd8853db1bbf79c2ad1faa4ff0f1db96dbf7efc11871` | fixed-frequency Weyl predicate and continuous equidistribution implication |
| `PiLacunaryNearReturnSparsity/T26SharedResonanceChain.lean` | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | canonical-output chain quantifiers and adjacent node coefficients |
| `PiLacunaryNearReturnSparsity/T38FixedStratumFejerSpike.lean` | `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014` | `commonDepth`, `stratumDelta`, `stratumOrder`, and the strict Fejer threshold |
| `PiLacunaryNearReturnSparsity/T55SignedMultiplierTenPairing.lean` | `025f3f7095f18bc542797113073d2bb20921895582dd49eb553b415952f31ffd` | literal shell, coefficients, labels, endpoints, and signed aggregation |
| `PiPositiveLowerBlockDensity/T23T23FiniteCylinderEnergyCriterion.lean` | `8e8f560806f13a8e56bd4432aef2b689309837c8a1adb2bab72cf7c9349e6aa6` | exact word-frequency/cylinder-energy identification |
| `PiLacunaryNearReturnSparsity/T2NormalOrbitNearReturns.lean` | `1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174` | normal decimal orbit implies the weak near-return target |
| `PiLacunaryNearReturnSparsity/T5LagDiscrepancy.lean` | `b6d1fad76f87627cefefcb921722476a694c78f1a8983d9e7a70765074d0854d` | exact quantitative lag-discrepancy sufficient condition |
| `PiPositiveDecimalFactorEntropy/T6T6PairCorrelationConditional.lean` | `9e83797e1ac488dd02a6c607f7f1d99ca2c50eb6c65bd331d7f254bc60775da4` | fixed-pi full pair-correlation predicate and diagonal restoration |
| `PiPositiveDecimalFactorEntropy/T16T16MicroscopicFullEntropy.lean` | `bcb6ada3167623b8f3d5ce65bb4d10337526424fe13bb36511f4b7267a2bab9f` | checked C3-to-microscopic-count transfer |

There is a naming collision: the Weyl module and the shared-chain module are
both item T26. They are never denoted merely by `T26` below.

## 2. Empirical Fourier normalization and exact invariance defect

Write `e(t)=exp(2*pi*i*t)`. For real `beta` and `N>=1`, set

\[
 x_j(\beta)=10^j\beta\pmod1,\qquad
 \mu_{\beta,N}=\frac1N\sum_{j=0}^{N-1}\delta_{x_j(\beta)},
\tag{2.1}
\]

and use the positive-sign Fourier convention

\[
 \widehat\mu_{\beta,N}(h)
 =\int e(hx)\,d\mu_{\beta,N}(x)
 =\frac1N\sum_{j=0}^{N-1}e(h10^j\beta),\quad h\in\mathbb Z.
\tag{2.2}
\]

This is exactly `circleEmpiricalMean ... (fourier h) N` in the Weyl T26
module for positive `N`. Directly shifting the finite sum gives

\[
 \boxed{
 \widehat\mu_{\beta,N}(10h)-\widehat\mu_{\beta,N}(h)
 =\frac{e(h10^N\beta)-e(h\beta)}N.}
\tag{2.3}
\]

More generally, if `S_N(h)=sum_{j<N} e(h10^j beta)`, then

\[
 \widehat\mu_{\beta,N}(10^r h)
 =\frac{S_{N+r}(h)-S_r(h)}N,
\qquad
 |\widehat\mu_{\beta,N}(10^r h)-\widehat\mu_{\beta,N}(h)|
 \leq\frac{2r}{N}.                                           \tag{2.4}
\]

Consequently every weak empirical limit `nu` along `N -> infinity` is
invariant under `T(x)=10x mod 1` and satisfies

\[
 \boxed{\widehat\nu(10h)=\widehat\nu(h)\quad(h\in\mathbb Z).} \tag{2.5}
\]

For the pi orbit this is the content of the checked empirical-invariance
interface. Equation (2.3) also proves the generic statement without invoking
pi. Notice what (2.5) does not say: it identifies coefficients on a decimal
ray but does not say that any of them is zero.

Every nonzero integer has a unique representation

\[
 h=10^r u,\qquad r\geq0,\quad 10\nmid u.                     \tag{2.6}
\]

Thus fixed-frequency Weyl cancellation is

\[
 \forall u\neq0\ (10\nmid u)\ \forall r\geq0:\quad
 \widehat\mu_{\beta,N}(10^r u)\longrightarrow0,             \tag{2.7}
\]

where `u,r` are fixed before `N -> infinity`. It is not a uniform assertion
for moving `u=u_N` or `r=r_N`.

## 3. Independent reconstruction of T55 in empirical variables

Fix a shared-chain object

\[
 \mathcal C:\operatorname{GeometricResonanceChain}
  (\operatorname{initialCoefficient}(h,r))\ M\ D\ 1\ K\ d\ \{r\},
\tag{3.1}
\]

and adjacent indices `q=k+1<d`. Put

\[
 s=\mathcal C.\mathrm{shifts}[k],\quad
 \beta_0=\mathcal C.\operatorname{nodeCoefficient}(k),\quad
 \beta=\mathcal C.\operatorname{nodeCoefficient}(q).         \tag{3.2}
\]

The list identity `take(k+1)=take(k)++[s]` in the checked definition gives,
without an estimate,

\[
 \boxed{\beta=(10^s-1)\beta_0.}                              \tag{3.3}
\]

Choose `1<=ell<commonDepth(C,q)`, and put exactly as in T38/T55

\[
 \delta=\operatorname{stratumDelta}(\mathcal C,q,\ell),\quad
 R=\operatorname{stratumOrder}(\mathcal C,q,\ell)
   =\lceil\delta^{-1}\rceil,\quad H=R-1.                    \tag{3.4}
\]

The positive source and terminal shells are literally

\[
 \mathcal S_H=\{1,\ldots,\lfloor H/10\rfloor\},\qquad
 \mathcal T_H=\{u:\lfloor H/10\rfloor<u\leq H\}.           \tag{3.5}
\]

T55's frequency block is

\[
 B_{\beta,\ell}(u)=\sum_{j=0}^{\ell-1}
 e(\beta u(10^\ell-10^j)).                                  \tag{3.6}
\]

Factoring its terminal phase proves the first required empirical identity:

\[
 \boxed{B_{\beta,\ell}(u)
 =\ell e(u10^\ell\beta)\widehat\mu_{\beta,\ell}(-u).}      \tag{3.7}
\]

In particular `|B|=ell*|mu_hat|`; dropping the factor `ell` would change the
T55 threshold.

Let `w_R(v)=1-v/R`. If `nu_10(u)` is the number of trailing decimal zeros of
`u`, induction on T55's checked predecessor recurrence gives

\[
 \Gamma_{\beta,\ell,R}(u)
 =\sum_{a=0}^{\nu_{10}(u)}w_R(u/10^a)
 e((u/10^a-u)10^\ell\beta).                                 \tag{3.8}
\]

The induction starts at `10 not divides u`, where T55's definition is just
`w_R(u)`. One predecessor step multiplies the old coefficient by
`e(-9(u/10)10^ell beta)`; multiplying the consecutive factors telescopes to
the exponent in (3.8).

Multiplying (3.7) and (3.8), and retaining every label, gives

\[
 \boxed{
 \operatorname{terminalCorrelation}(\beta,\ell,R)
 =\ell\sum_{u\in\mathcal T_H}\widehat\mu_{\beta,\ell}(-u)
   \sum_{a=0}^{\nu_{10}(u)}w_R(u/10^a)
     e((u/10^a)10^\ell\beta).}                              \tag{3.9}
\]

No equal numerical phases are merged. T55's checked collision
`10(10^2-1)=11(10^2-10)=990` therefore still contributes with both labels.

### 3.1 Primitive decimal rays

For each positive primitive `v` with `10 not divides v` and `v<=H`, let

\[
 r_H(v)=\max\{a:10^a v\leq H\},\qquad h_H(v)=10^{r_H(v)}v.
\tag{3.10}
\]

The map `v -> h_H(v)` is a bijection from primitive `v<=H` to `T_H`, because
`h_H(v)<=H<10h_H(v)`. Reindexing (3.9) gives

\[
 \boxed{
 \frac{\operatorname{terminalCorrelation}(\beta,\ell,R)}\ell
 =\sum_{\substack{1\leq v\leq H\\10\nmid v}}
  \widehat\mu_{\beta,\ell}(-h_H(v))
  \sum_{a=0}^{r_H(v)}w_R(10^a v)e(10^{a+\ell}v\beta).}       \tag{3.11}
\]

The label weight has exact total mass

\[
 \sum_{\substack{v\leq H\\10\nmid v}}
 \sum_{a=0}^{r_H(v)}w_R(10^a v)
 =\sum_{t=1}^{H}(1-t/R)=\frac{R-1}{2}.                      \tag{3.12}
\]

The first equality is the unique factorization (2.6), not an asymptotic.
The replay script checks the finite bijection and (3.12) for several cutoffs.

## 4. Direct labels are finite invariance defects

For a direct label put

\[
 m_{u,j}=u(10^\ell-10^j),\qquad
 u\in\mathcal T_H,\quad 0\leq j<\ell.                       \tag{4.1}
\]

Equation (3.3) gives

\[
 e(\beta m_{u,j})
 =e(\beta_0 10^s m_{u,j})\overline{e(\beta_0m_{u,j})}.       \tag{4.2}
\]

Define the finite empirical invariance defect

\[
 d_{\beta_0,s}(m)=
 \widehat\mu_{\beta_0,s}(10m)-\widehat\mu_{\beta_0,s}(m).
\tag{4.3}
\]

The checked chain has `s>=1`, and (2.3) says exactly

\[
 s d_{\beta_0,s}(m)
 =e(\beta_0 10^s m)-e(\beta_0m).                            \tag{4.4}
\]

For unit complex numbers `z,y`,
`Re(z*conj(y))=1-|z-y|^2/2`. Therefore, with

\[
 V= s^2\sum_{u\in\mathcal T_H}\sum_{j=0}^{\ell-1}
       w_R(u)|d_{\beta_0,s}(m_{u,j})|^2,                    \tag{4.5}
\]

and

\[
 A_0=\ell\sum_{u\in\mathcal T_H}w_R(u),                    \tag{4.6}
\]

the direct part `C_0=sum w_R(u)e(beta*m_{u,j})` satisfies the exact identity

\[
 \boxed{\operatorname{Re}C_0=A_0-\frac12V.}                 \tag{4.7}
\]

This derives the direct-label phase condition solely from the empirical
Fourier invariance defect. It is not a bound on
`|mu_hat(h)|`, and replacing (4.5) by Weyl cancellation changes the statement.

Let

\[
 X=\ell\sum_{u\in\mathcal T_H}
       \sum_{a=1}^{\nu_{10}(u)}w_R(u/10^a),                 \tag{4.8}
\]

with an empty inner sum when `10 not divides u`. Every omitted predecessor
phase has modulus one, so its real contribution is at least `-X`. Let

\[
 B_{\rm end}=2\sum_{v=1}^{\lfloor H/10\rfloor}
 |\Gamma_{\beta,\ell,R}(v)|,                                \tag{4.9}
\]

which is exactly T55's `endpointBudget`. T55 keeps both telescope endpoints,
and its checked bound gives `Re(endpointSum)>=-B_end`.

The checked signed aggregation, including zero frequency `ell` and both signs,
now gives

\[
 \boxed{
 S_{\ell,R}(\beta):=\sum_{j=0}^{\ell-1}
  \operatorname{fejerKernel}(R-1,\beta(10^\ell-10^j))
 \geq \ell-2B_{\rm end}+2A_0-V-2X.}                        \tag{4.10}
\]

The factor two is the multiplicity of positive and negative signed
frequencies. The auxiliary `j=ell` occurs only in the endpoint term; it is not
part of the `j<ell` block sum.

## 5. A derived budget and the audited minimal uniform hypothesis

Put

\[
 \Theta=\frac{\ell}{4R\delta^2}.                            \tag{5.1}
\]

The direct computation first gives the conservative sufficient budget

\[
 \boxed{\mathsf{DIB}:\quad
 V<\ell+2A_0-2X-2B_{\rm end}-\Theta.}                       \tag{5.2}
\]

`DIB` means **Direct-label empirical Invariance-defect Budget**. Substitution
of (5.2) in (4.10) gives, with no further analytic premise,

\[
 \boxed{\Theta<S_{\ell,R}(\beta),}                          \tag{5.3}
\]

which is T38/T55's literal strict threshold. After deriving (5.2), comparison
with the unverified T58 note shows that it is algebraically the same inequality
called DLAPV there. This note does not use that occurrence as a premise and
does not claim (5.2) as a new or minimal hypothesis. In fact Section 6.2 shows
that (5.2) is strictly stronger than T55's threshold because it replaces the
actual predecessor and endpoint real parts by the worst-case bounds `-X` and
`-B_end`.

To obtain a genuinely different anti-diluting hypothesis, define

\[
 \Lambda=\ell+2A_0-2X-2B_{\rm end}-\Theta.                  \tag{5.4}
\]

The third entry in `stratumDelta`, together with `ell>=1`, gives `R>=20`, so
the terminal shell is nonempty and `A_0>0`. Define

\[
 \boxed{\mathsf{UPRID}:\quad
 \Lambda>0\quad\hbox{and}\quad
 s\max_{\substack{u\in\mathcal T_H\\0\leq j<\ell}}
 |d_{\beta_0,s}(m_{u,j})|<\sqrt{\Lambda/A_0}.}              \tag{5.5}
\]

`UPRID` means **Uniform Primitive-Ray Invariance Defect**. It uses a supremum
on the unchanged labeled terminal domain, so one sparse bad ray or one
top-boundary label cannot be diluted. Since

\[
 \sum_{u\in\mathcal T_H}\sum_{j<\ell}w_R(u)=A_0,
\]

equation (4.5) gives

\[
 V\leq A_0s^2\max_{u,j}|d_{\beta_0,s}(m_{u,j})|^2<\Lambda.   \tag{5.6}
\]

Thus `UPRID => DIB => (5.3)`. The constant
`sqrt(Lambda/A_0)` is the largest bound obtainable from only the supremum and
the exact total weight `A_0`: increasing it would allow an abstract labeled
family with every defect at the larger bound and `V>=Lambda`. This is the
precise sense in which (5.5), rather than (5.2), is the audited minimal
uniform hypothesis.

The intended quantified research hypothesis is not an assertion about every
bare chain. It is:

1. For every natural `A,n,d,N,r,h` with `1<=A`, `1<=n`, and `2<=d`, define
   `D=initialDensity(A,n)`, `K=chainLengthRequest(D,d)`, and
   `L=iterationLengthThresholdAux(D,1,K,1,d)`.
2. Assume `N=16*A*n*L`, `1<=r<=N-1`, and `1<=h<=256*A*n`.
3. For every
   `C : GeometricResonanceChain(initialCoefficient(h,r),N-r,D,1,K,d,{r})`,
   there exist `k,ell` with `k+1<d` and
   `1<=ell<commonDepth(C,k+1)` for which `UPRID` in (5.5) holds with all
   quantities defined by (3.2)-(5.4).

These are the literal parameter bounds returned by the checked shared-chain
theorem if canonical A1 fails. `UPRID` is not Weyl's criterion: it requires a
chain-dependent moving-frequency bound at scale `1/s` on one finite labeled shell,
whereas Weyl fixes a frequency before the prefix tends to infinity. It is not
pair correlation: it contains no pair count or `s/N` limit. It is not a
renamed T55 conclusion: it is a pointwise upper bound on empirical invariance
defects, while T55's conclusion is a lower bound on a phase-sensitive linear
sum with predecessor and endpoint terms.

This quantified hypothesis alone is not claimed to prove A1. It supplies the
T55 threshold on a canonical-output chain. T55's later payoffs still retain
their separate legality and T28 closing assumptions.

## 6. Exact strictness test for `DIB`

Both examples in this section are reconstructed directly from the checked
T26/T38/T55 definitions. They use `r=0`, so they are interface tests outside
the canonical-output domain in Section 5 and make no fixed-pi claim.

Take

\[
 h=1,\,r=0,\,M=5,\,D=2,\,B=1,\,K=2,\,d=2,\,F=\{0\}.
\tag{6.1}
\]

Since `initialCoefficient(1,0)=0`, every geometric phase equals one.

### 6.1 `DIB` is nonvacuous

Use shifts `[2,1]`. The residual lengths are `5,3,2`, and the node inequalities
are

\[
 5/2<5,\qquad 3/32<3,\qquad 2/8192<2.                       \tag{6.2}
\]

At node `q=1`, take `ell=1`. The incoming shift is `2`; the outgoing adjacent
factor is `9`. The third entry of `stratumDelta` is `1/180`, while each of the
first two entries is larger (use `nodeTau<1/2`, hence
`arccos(nodeTau)>pi/3`). Thus

\[
 \delta=1/180,\quad R=180,\quad H=179,\quad
 \mathcal S_H=\{1,\ldots,17\},\quad
 \mathcal T_H=\{18,\ldots,179\}.                            \tag{6.3}
\]

All invariance defects in (4.5) are zero. Exact summation gives

\[
 V=0,\quad A_0=1467/20,\quad X=323/20,\quad
 B_{\rm end}=1543/45,\quad \Theta=45.                       \tag{6.4}
\]

The right side of (5.2) is `82/45>0`; hence `DIB` holds.

### 6.2 T55 top shell does not imply `DIB`

Reverse the shifts to `[1,2]`. The residual lengths are `5,4,2`, so the three
node inequalities are

\[
 5/2<5,\qquad 4/32<4,\qquad 2/8192<2.                       \tag{6.5}
\]

At the same node and stratum,

\[
 \delta=1/1980,\quad R=1980,\quad H=1979,\quad
 \mathcal S_H=\{1,\ldots,197\},\quad
 \mathcal T_H=\{198,\ldots,1979\}.                         \tag{6.6}
\]

Again `V=0`, but now

\[
 A_0=16047/20,\quad X=3743/20,\quad
 B_{\rm end}=204983/495,\quad \Theta=495.                   \tag{6.7}
\]

The `DIB` right side is `-45448/495`, so its strict inequality fails. On the
other hand, all terminal phases are positive and

\[
 \operatorname{Re}\operatorname{terminalCorrelation}(0,1,1980)
 =A_0+X=1979/2.                                               \tag{6.8}
\]

T55's top-shell right side is

\[
 1980/8-1/2+B_{\rm end}=327248/495,                          \tag{6.9}
\]

and the exact margin in (6.8)-(6.9) is `325109/990>0`.
Therefore the top-shell premise holds while `DIB` fails. The script
`verify_note.py` reproduces every rational value in (6.4) and (6.7)-(6.9).

## 7. Global properties and literal quantifiers

For a circle sequence `x=(x_j)`, let

\[
 \mu_N=N^{-1}\sum_{j<N}\delta_{x_j}\quad(N\geq1).           \tag{7.1}
\]

We compare the following properties.

**Weyl (`W`).** For every fixed `h in Z\{0}`,
`mu_hat_N(h)->0`.

**Equidistribution (`EQ`).** For every continuous complex `f`,
`int f dmu_N -> int f dm`, where `m` is Haar probability measure.

**Interval discrepancy (`DISC`).**

\[
 D_N=\sup_{0\leq a<b\leq1}
 |\mu_N([a,b))-(b-a)|\longrightarrow0.                       \tag{7.2}
\]

**Fixed-level decimal collision (`BC_m`).** Put `q=10^m`, let
`I_a=[a/q,(a+1)/q)` for `0<=a<q`, and put

\[
 p_{a,m}(N)=\mu_N(I_a),\quad
 C_m(N)=\sum_{a=0}^{q-1}p_{a,m}(N)^2,\quad
 X_m(N)=qC_m(N)-1.                                           \tag{7.3}
\]

The property is `X_m(N)->0` for every fixed `m>=1`.

**Weak near-return target (`A1_x`).** With strict distance, ordered pairs, and
diagonal retained, define

\[
 Q_x(n,N)=\#\{(i,j)<N:\operatorname{dist}(x_i,x_j)<10^{-n}\}.
\tag{7.4}
\]

Then `A1_x` has exactly the quantifiers in (1.2), with `Q_x` in place of
`Q_pi`.

**Full pair correlation (`PPC_x`).** For every fixed real `s>0`,

\[
 \frac1N\#\{(i,j)<N:i\neq j,
  \operatorname{dist}(x_i,x_j)<s/N\}\longrightarrow2s.      \tag{7.5}
\]

The checked fixed-pi `PiDecimalShiftPairCorrelationC3` is precisely (7.5) for
`x_j=10^j*pi mod 1`. It omits the diagonal; the checked bridge adds exactly
`N` diagonal pairs when passing to `Q_pi`.

Finally, T5's `lagCircularIntervalDiscrepancy` is not (7.2). It is the
unnormalized supremum error for the lag orbit
`10^j(10^r-1)pi`, in strict circular intervals of radius `rho`. Its checked
sufficient hypothesis is

\[
 \forall A\geq1\ \exists n_d\geq1\ \forall n\geq n_d\
 \exists N\geq1:\quad 8An\leq N,\quad
 \sum_{r=1}^{N-1}D_{N,r}(10^{-n})\leq\frac{N^2}{8An}.        \tag{7.6}
\]

The checked theorem says (7.6) implies canonical A1. Fixed-frequency Weyl has
no rate or all-lags uniformity that would imply (7.6).

## 8. Exact Walsh/block-collision identity

Let `G_m=(Z/10Z)^m`, `q=10^m`, and let `w_j in G_m` be the length-`m` word at
start `j<N`. Set

\[
 n_w=\#\{j<N:w_j=w\},\qquad p_w=n_w/N.                       \tag{8.1}
\]

Thus `sum_w p_w=1`. Let `zeta=e(1/10)` and, for `kappa in G_m`, define the
digitwise Walsh character and unnormalized transform

\[
 \chi_\kappa(w)=\zeta^{\sum_{r=1}^m\kappa_rw_r},\qquad
 \widehat p_W(\kappa)=\sum_w p_w\overline{\chi_\kappa(w)}.   \tag{8.2}
\]

The zero coefficient is one. Character orthogonality is

\[
 \sum_{\kappa\in G_m}\chi_\kappa(w)\overline{\chi_\kappa(v)}
 =q\,1_{w=v}.                                                 \tag{8.3}
\]

Expanding (8.3) proves Parseval with the present normalization:

\[
 \sum_w p_w^2=\frac1q\sum_\kappa|\widehat p_W(\kappa)|^2.   \tag{8.4}
\]

Also

\[
 \sum_w(p_w-q^{-1})^2
 =\sum_wp_w^2-q^{-1}.                                        \tag{8.5}
\]

Combining (8.4)-(8.5) gives the requested exact identity:

\[
 \boxed{
 q\sum_w(p_w-q^{-1})^2
 =q\left(\sum_wp_w^2-q^{-1}\right)
 =\sum_{\kappa\neq0}|\widehat p_W(\kappa)|^2.}              \tag{8.6}
\]

The middle quantity is excess ordered collision mass. In unnormalized counts,

\[
 \boxed{
 \sum_w n_w^2-\frac{N^2}{q}
 =N^2\sum_w(p_w-q^{-1})^2
 =\frac{N^2}{q}\sum_{\kappa\neq0}|\widehat p_W(\kappa)|^2.}\tag{8.7}
\]

The diagonal is included because `sum_w n_w^2` counts all ordered pairs with
equal words. In particular it is at least `N`, exposing the finite occupancy
obstruction when `q>N`.

For the pi digit stream, the checked T23 theorem identifies `sum p_w^2`
exactly with `normalizedPiCylinderCollisionEnergy`; T7 identifies the latter
with ordered equal half-open-cylinder pairs. Thus (8.6) has the same `N^2`
normalization as the kernel interface.

## 9. Endpoint and carry audit

Every circle point uses its unique representative in `[0,1)`. The level-`m`
cylinders are

\[
 I_a=[a/q,(a+1)/q),\qquad 0\leq a<q.                         \tag{9.1}
\]

The circle point `1=0` belongs to `I_0`, not the last cylinder. Decimal
rationals use the terminating-zero code. For the pi orbit no point is on a
decimal boundary: `fract(10^j*pi)=a/q` would make pi rational. This is the
strict-boundary fact used by the checked T7 code/cylinder theorem.

If another convention changes exactly `B` of the `N` word labels, then direct
counting gives

\[
 \|p-p'\|_1\leq2B/N,\quad
 |\widehat p_W(\kappa)-\widehat p'_W(\kappa)|\leq2B/N,       \tag{9.2}
\]

and at most `2BN-B^2` ordered pairs touch a changed index, so

\[
 |C_m(p)-C_m(p')|\leq(2BN-B^2)/N^2\leq2B/N.                 \tag{9.3}
\]

Walsh characters are digitwise characters of `(Z/10Z)^m`. They are not
ordinary characters of `Z/10^mZ`, because the latter group includes carries.
This prevents coefficientwise identification with T55's circle Fourier
frequencies.

For comparison, label a word by
`a(w)=sum_{r=1}^m w_r*10^(m-r)` and define the cyclic transform

\[
 \widetilde p(t)=\sum_{a=0}^{q-1}p_a e(-ta/q),\quad
 t\in\mathbb Z/q\mathbb Z.                                  \tag{9.4}
\]

Cyclic Parseval gives another exact total-energy identity

\[
 \boxed{q\sum_a(p_a-q^{-1})^2
 =\sum_{t=1}^{q-1}|\widetilde p(t)|^2
 =\sum_{\kappa\neq0}|\widehat p_W(\kappa)|^2.}              \tag{9.5}
\]

This is equality of total nonconstant energy, not equality of individual
Walsh and cyclic coefficients.

## 10. Quantified comparison with T55's ordinary top shell

Use the negative-sign ordinary coefficient in this section,

\[
 \widehat\mu^-(t)=\int e(-tx)\,d\mu(x),                     \tag{10.1}
\]

so its sign matches (9.4). Write each `x in I_a` uniquely as
`x=(a+theta)/q`, `0<=theta<1`. Then

\[
 |\widehat\mu^-(t)-\widetilde p(t)|
 \leq\min(2,2\pi|t|/q).                                     \tag{10.2}
\]

Indeed, subtract term by term and use
`|e(-t*theta/q)-1|<=min(2,2*pi*|t|/q)`.

Let `S` be a set of distinct frequencies in `{1,...,q-1}`. Minkowski and
(9.5) yield

\[
 \boxed{
 \|\widehat\mu^-\|_{2,S}
 \leq\sqrt{q\sum_a(p_a-q^{-1})^2}
 +\frac{2\pi}{q}\left(\sum_{t\in S}t^2\right)^{1/2}.}       \tag{10.3}
\]

Take `mu=mu_(beta,ell)` and `S=T_H`. This requires the explicit scale
separation

\[
 H<q=10^m.                                                    \tag{10.4}
\]

Let `Gamma_u=Gamma_(beta,ell,R)(u)`. From (3.7), Cauchy-Schwarz, and (10.3),

\[
 \boxed{
 |\operatorname{terminalCorrelation}(\beta,\ell,R)|
 \leq\ell\|\Gamma\|_{2,\mathcal T_H}
 \left(\sqrt{q\sum_a(p_a-q^{-1})^2}+E_{H,q}\right),}        \tag{10.5}
\]

where

\[
 E_{H,q}=\frac{2\pi}{q}
   \left(\sum_{u\in\mathcal T_H}u^2\right)^{1/2}.           \tag{10.6}
\]

Therefore any real lower bound
`Re terminalCorrelation >= L>0` implies

\[
 \boxed{
 q\sum_a(p_a-q^{-1})^2\geq
 \left(\max\left\{0,
 \frac{L}{\ell\|\Gamma\|_{2,\mathcal T_H}}-E_{H,q}
 \right\}\right)^2.}                                       \tag{10.7}
\]

This is the proved one-way comparison to block collision. It retains the T55
coefficient norm, quantization error, shell endpoints, and the scale condition
`H<10^m`. No T55-specific converse is asserted: a converse would also have to
control the phases and the coefficient vector `Gamma`, not only shell energy.

If `H>=q`, cyclic aliasing makes `p_tilde(q)=1`, while the residue-zero term is
absent from (9.5). Hence no version of (10.3) with zero error can hold on the
unchanged domain.

## 11. Counterexamples and non-comparisons

### 11.1 Block uniformity does not control an aliased top shell

Fix `q=10^m` and `0<theta<1`. Put one point at

\[
 x_a=(a+\theta)/q,\qquad 0\leq a<q.                          \tag{11.1}
\]

Every level-`m` cylinder has mass `1/q`, so the three quantities in (8.6) are
zero. Nevertheless `|mu_hat(q)|=1`. Taking `H=q` puts this frequency in the
literal shell `(H/10,H]`. This is a finite synthetic orbit and proves that
(10.4) cannot be deleted.

An invariant version uses a cyclic decimal de Bruijn word `B` of order `m`.
Its periodic shift measure gives every length-`m` word exactly once, but every
orbit point has denominator dividing `10^(10^m)-1`; the Fourier coefficient at
that denominator is one.

### 11.2 General measure-level shell decay does not control block collision

Fix `H` and choose `M>H` with `gcd(M,10)=1`. Let

\[
 \nu_M=M^{-1}\sum_{a=0}^{M-1}\delta_{a/M}.                  \tag{11.2}
\]

Multiplication by ten permutes its support, so `nu_M` is invariant. Its
Fourier coefficients are one when `M` divides `h` and zero otherwise. Thus
all frequencies `1<=h<=H` vanish. If `q=10^m>M`, at most `M` decimal
cylinders are occupied; Cauchy-Schwarz gives

\[
 q\sum_a(p_a-q^{-1})^2=q\sum_ap_a^2-1\geq q/M-1>0.          \tag{11.3}
\]

This proves general measure-level non-comparison, even on invariant measures.
It is not presented as a T55-specific converse to (10.7), because `nu_M` is
not here realized as the particular finite empirical measure
`mu_(beta,ell)` with its corresponding T55 coefficient vector.

### 11.3 Normality does not control an adaptive moving shell

Let `beta` be base-10 normal. For every `L`, its digit stream contains a block
of `2L` zeros beginning at some position `r_L+1`. For `0<=j<L`,

\[
 \{10^{r_L+j}\beta\}<10^{-L},
\]

and hence

\[
 |\widehat\mu_{\beta,L}(10^{r_L})-1|\leq2\pi10^{-L}.        \tag{11.4}
\]

With `H_L=2*10^(r_L)`, this bad frequency lies in `(H_L/10,H_L]` with
triangular weight close to `1/2`. Thus fixed-frequency Weyl cancellation and
normality do not imply uniform cancellation on arbitrary adaptive T55-shaped
shells. This is exactly the quantifier mismatch between fixed `h` in (2.7)
and moving `h=h_L` in (11.4).

### 11.4 Sparse-ray and bulk-shell dilution on the unchanged domain

For `H_k=M_k` with `M_k -> infinity` and `gcd(M_k,10)=1`, use the invariant
measures `nu_(M_k)` from (11.2). The literal terminal shell contains the one
frequency `M_k` with coefficient one, so the shell supremum is one. But the
unweighted normalized `L2` average is `O(1/H_k)`. T55's literal triangular
weight at `u=H_k` is

\[
 w_{H_k+1}(H_k)=1/(H_k+1),                                  \tag{11.5}
\]

so after normalization by the exact total weight `H_k/2`, this one ray has
mass `2/(H_k(H_k+1))`. Both sparse-ray and top-boundary dilution therefore
occur without changing the shell or weight. A supremum norm excludes this;
the normalized T55 weight and any normalized `L1` or `L2` average do not.

A single non-atomic invariant example also has a persistent ray. Let `nu` be
the decimal Bernoulli measure with independent digits `0,1`, each of
probability `1/2`. Then

\[
 \widehat\nu(1)=\prod_{n=1}^\infty\frac{1+e(10^{-n})}{2},
 \qquad
 |\widehat\nu(1)|=\prod_{n=1}^\infty\cos(\pi10^{-n})>0.      \tag{11.6}
\]

The product is positive because the sum of `1-cos(pi*10^-n)` converges.
Invariance gives `nu_hat(10^r)=nu_hat(1)` for every `r`.

Nevertheless its normalized triangular Fourier energy tends to zero. Indeed,
the normalized Fejer identity is

\[
 \frac1{H+1}\sum_{|h|\leq H}
  (1-|h|/(H+1))|\widehat\nu(h)|^2
 =\iint \frac{F_H(x-y)}{H+1}\,d\nu(x)d\nu(y).               \tag{11.7}
\]

The normalized kernel is at most one and tends to zero off the diagonal.
Because `nu` has no atoms, `(nu x nu)(diagonal)=0`; dominated convergence
proves that (11.7) tends to zero. Its positive-frequency part contains the
literal T55 weighted `L2` average. Cauchy-Schwarz gives the corresponding
weighted `L1` dilution. Thus even one invariant measure exhibits a persistent
primitive decimal ray hidden by the bulk norm.

### 11.5 Weak near return does not imply Weyl or normality

Take an explicit binary-normal stream over digits `{0,1}` and interpret it as
a decimal expansion. Its decimal orbit is generic for the invariant Bernoulli
measure in (11.6). At level `n`, exactly `2^n` cylinders have mass `2^-n`, so

\[
 C_n(\nu)=2^{-n}.                                             \tag{11.8}
\]

The checked factor-three cylinder/small-ball comparison gives closed
small-ball mass at most `3*2^-n`. For each fixed `A` and all sufficiently
large `n`, `3*A*n*2^-n<1`. Weak convergence of empirical products and
Portmanteau then supplies a sufficiently large `N` for the strict ordered
pair count, with its diagonal included, satisfying `A1_x`.

The orbit is not equidistributed: cylinders beginning with digits `2,...,9`
have zero limiting mass. Hence `A1_x` does not imply Weyl, discrepancy decay,
or normality. This is a deterministic sibling orbit, not the pi orbit.

### 11.6 Weyl and weak near return do not imply full pair correlation

Start from any base-10 normal digit stream. At positions `P_k` growing so fast
that all earlier modifications are `o(P_k)`, replace
`L_k=floor(P_k^(3/4))` consecutive digits by zeros. The modified set of digit
positions has asymptotic density zero. For each fixed word length, only starts
within that fixed distance of a modified position can change, also a
density-zero set. The resulting stream remains normal, hence its decimal
orbit satisfies Weyl, interval discrepancy decay, every fixed-level collision
limit, and `A1_x`.

At `N_k=P_k+L_k`, at least `floor(L_k/2)` orbit points beginning in the zero
island lie within `10^(-L_k/2)` of zero. For large `k` this is less than
`1/N_k`. Therefore the ordered off-diagonal pair count at `s=1` is at least

\[
 \lfloor L_k/2\rfloor(\lfloor L_k/2\rfloor-1),              \tag{11.9}
\]

and division by `N_k` tends to infinity rather than `2`. Thus neither Weyl
nor the weak target implies full pair correlation, even for a genuine decimal
orbit.

## 12. Implication diagram and classifications

For decimal orbits, with all limits taken as stated in Section 7,

```text
W  <=>  EQ  <=>  DISC  <=>  [X_m(N) -> 0 for every fixed m]
|                                      |
| checked normal-orbit route           | same normality property
v                                      v
A1_x  <----------------------------- full PPC_x
 ^
 |
quantitative all-lag discrepancy (7.6)
```

Here are the proofs and non-arrows.

1. `W=>EQ` is the checked Weyl T26 theorem. `EQ=>W` follows by testing the
   continuous character `e(hx)`. `EQ<=>DISC` follows by approximating
   half-open interval indicators from above and below; Haar gives their
   endpoints mass zero.
2. `EQ` gives `p_(a,m)(N)->1/10^m` for every fixed half-open cylinder, hence
   fixed-level collision excess tends to zero. Conversely, (8.6) says zero
   excess forces every one of the finitely many level-`m` probabilities to be
   uniform. Doing this for every `m` gives convergence on the decimal cylinder
   algebra and therefore `EQ`.
3. The checked normal-orbit theorem gives `W/EQ=>A1_x` for decimal orbits.
   Section 11.5 disproves the converse.
4. Full PPC gives A1 directly: use `s=1` and `N=10^n`. Eventually the
   off-diagonal count is less than `3N`; restoring the `N` diagonal pairs gives
   `Q_x(n,N)<=4N`. Since `4An<=10^n` for all sufficiently large `n`, (1.2)
   follows. This is the normalization implemented by the checked fixed-pi C3
   interfaces. Section 11.6 disproves the converse.
5. The exact T5 all-lag discrepancy condition implies A1 by its checked
   theorem. No converse is used or asserted.

The terminal audit has three objects that must not be merged:

1. The invariant-measure terminal ray condition is

   \[
   \mathsf{RI}(\nu):\quad
   \widehat\nu(10h)=\widehat\nu(h)\quad\hbox{for every }h\in\mathbb Z.
   \tag{12.1}
   \]

   On the explicitly stated domain of invariant empirical limits, `RI` is
   **strictly weaker than equidistribution/normality**. Haar satisfies it, but
   so does the non-Haar Bernoulli measure (11.6), whose coefficient is nonzero
   on the whole ray `10^r`. This is the requested ternary classification of
   the invariant terminal phase condition.
2. The finite quantity in (4.5) is not merely `RI`: it multiplies the endpoint
   defect by `s^2` and evaluates moving frequencies. Weak convergence to an
   invariant measure gives `d=O(1/s)` from (4.4), but supplies no `o(1/s)`
   bound after this scaling. Therefore the classification of `RI` is not
   silently transferred to `DIB` or `UPRID`.
3. T55's literal finite top-shell lower bound is a chain-indexed proposition,
   not an asymptotic digit property until a quantifier closure and shell
   schedule are specified. It cannot honestly be labeled weaker, equivalent,
   stronger, or incomparable with normality on the bare finite domain.
   Section 11.3 establishes only that normality does not control arbitrary
   moving-frequency cancellation; Section 6.2 establishes only that one
   non-equidistributed bare chain can satisfy the top-shell premise.

Thus no fixed-pi genericity claim has been hidden in the classification.
`UPRID` in Section 5 is the audited anti-diluting intermediate hypothesis that
links finite empirical invariance defects to T55's threshold without being
Weyl's criterion, pair correlation, DLAPV under another name, or the T55
conclusion itself.

## 13. Replay and terminal status

From a directory containing only the delivered files, run

```text
python3 verify_note.py
```

The script checks the primitive-ray partition and total weight `(R-1)/2`; the
bare-chain fields, residuals, density denominators, legal stratum, delta
minimum bounds, and resulting orders in both zero-phase tests; all rational
strict margins; and both the collision and numerically evaluated Walsh sides
of a nonuniform instance of (8.6).

The terminal status is:

```text
PROOF SKETCH: INVARIANT CONDITION CLASSIFIED; FINITE TOP-SHELL CLOSURE AND
FIXED-PI HYPOTHESES REMAIN OPEN
```
