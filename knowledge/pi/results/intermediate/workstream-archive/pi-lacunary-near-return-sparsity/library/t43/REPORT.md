# T43: aggregate primitive correlation at a fixed T26 stratum

Claim label: **proof sketch**. The three formal inputs named below are
kernel-checked, but the deductions newly written in this note have not been
formalized in Lean. Every finite identity needed for the terminal verdict is
displayed here.

## 1. Provenance, normalized statement, and scope

There is no external source URL: this is the local, system-formulated question
in the byte-identical delivered file `canonical_statement.txt`. Its SHA-256 is

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
 \forall n\geq n_0\ \exists N\geq1:
 \qquad AnQ_\pi(n,N)\leq N^2.                    \tag{1.1}
\]

The pairs are ordered, the diagonal is included, and `N` may depend on `A,n`.
This note does not replace eventual `n` by infinitely many `n`, prescribe `N`,
remove the diagonal, change strict circle distance, or replace fixed `pi` by a
generic real.

The only kernel-checked inputs used are:

| item | delivered-library file | SHA-256 | interface used |
|---|---|---|---|
| T10 | `t10/LongLagResonance.lean` | `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947` | the explicit long-lag sum and its bound |
| T26 | `t26/SharedResonanceChain.lean` | `7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2` | chain parameters, node coefficients, residuals, and node resonance |
| T38 | `t38/FixedStratumFejerSpike.lean` | `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014` | the fixed stratum, radius, order, Fejer expansion, and expanded-FSFS equivalence |

Definitions unfolded in (2.1)-(2.4), such as `densityDenominator` and
`iterationLengthThresholdAux`, are transitive kernel-checked definitions
appearing in T26's theorem types; no theorem from an additional note is used.

The T40 note (SHA-256
`351c1b183e4c3fb00471a70674452e1a58803f3786fd3c914adb3371fa995d38`)
is an unverified proof sketch. Its classwise `PCC_(1/4)` terminology is
motivation only. All facts about that condition used below are re-derived from
its displayed definition.

Recorded interpretation issues are:

1. `nu_10` below is the exponent of divisibility by the composite integer 10;
   no valuation inequality is used.
2. A collision means equality of integer frequencies, not merely equality of
   their phases at one real number.
3. The second moment integrates a free coefficient over `[0,1]`; it gives no
   estimate at a T26 coefficient.
4. The finite separator in Section 8 deliberately changes the fixed-pi
   coefficient. It can refute only an implication from the abstract interface.

## 2. Every T10/T26 parameter substitution

Write

\[
 e(x):=\exp(2\pi i x).
\]

Assume temporarily the literal negation of (1.1), solely to invoke T26's
necessary-only theorem. T26 returns `A>=1`; for arbitrarily large `n>=1` and
each requested depth `d`, set

\[
 D_0:=131072A^2n^2,\qquad D_{q+1}:=8D_q^2,                 \tag{2.1}
\]

\[
 K:=2D_d^2.                                                \tag{2.2}
\]

For completeness, T26's recursive requested length is

\[
 \begin{aligned}
 T(D,B,K,q,0)&:=K,\\
 T(D,B,K,q,t+1)&:=\max\{8D^2,\ 16(B+q+R)D^2\},\\
 R&:=T(8D^2,B,K,q+1,t),
 \end{aligned}                                             \tag{2.3}
\]

and the actual substitutions are

\[
 L:=T(D_0,1,K,1,d),\qquad N:=16AnL.                        \tag{2.4}
\]

There are

\[
 1\leq r\leq N-1,\qquad 1\leq h\leq256An,                \tag{2.5}
\]

and one T26 chain with a list of distinct shifts
`(s_0,...,s_{d-1})`, each `s_q>=1` and different from `r`. Define

\[
 M_q:=N-r-\sum_{t<q}s_t,                                   \tag{2.6}
\]

\[
 \beta_q:=h(10^r-1)\pi\prod_{t<q}(10^{s_t}-1).             \tag{2.7}
\]

The empty product is 1. Thus

\[
 \beta_0=h(10^r-1)\pi,\qquad
 \beta_{q+1}=U_q\beta_q,\qquad U_q:=10^{s_q}-1\geq9,       \tag{2.8}
\]

and T26 retains at every node `0<=q<=d` the strict inequality

\[
 \boxed{\quad \frac{M_q}{D_q}<
 \left|\sum_{x=0}^{M_q-1}e(\beta_q10^x)\right|.\quad}      \tag{2.9}
\]

At `q=0`, (2.9) is precisely T10's resonance after substituting
`M_0=N-r`, `D_0=131072A^2n^2`, and (2.7). T26 also gives

\[
 M_q\geq M_d\geq K=2D_d^2\geq2D_q^2,                      \tag{2.10}
\]

where the last inequality uses the monotonicity of the kernel-checked density
denominators. Equations (2.1)-(2.10) list every parameter later used.

Fix from now on one genuine consecutive pair `q,q+1` with `q<d`. Its T38
common depth is

\[
 M_*:=\min(M_q,M_{q+1})=M_{q+1},                            \tag{2.11}
\]

because `s_q>=1`. Fix one genuine stratum

\[
 1\leq\ell<M_*.                                             \tag{2.12}
\]

Put

\[
 \tau_q:=\frac1{8D_q^2},\qquad
 \eta_q:=\frac{\arccos(\tau_q)}{2\pi},                    \tag{2.13}
\]

and use the actual T38 radius and integral order

\[
 \delta:=\min\left\{\eta_q,\frac{\eta_{q+1}}{U_q},
             \frac1{2U_q10^\ell}\right\}>0,
 \qquad R:=\lceil\delta^{-1}\rceil.                        \tag{2.14}
\]

In particular,

\[
 \delta\leq\frac1{2U_q10^\ell},\quad U_q\geq9,\quad
 \ell\geq1\quad\Longrightarrow\quad R\geq180.            \tag{2.15}
\]

This is an actual T26 consecutive-node domain and an actual legal T38 fixed
stratum. No inverse witness or compatibility assertion is assumed.

## 3. Exact T38 frequency domain and normalization

T38's stratum consists of exactly

\[
 \mathcal J_\ell:=\{(j,\ell-j):0\leq j<\ell\}.              \tag{3.1}
\]

The denominator at `j` is

\[
 Q_j:=10^\ell-10^j=10^j(10^{\ell-j}-1)>0.                 \tag{3.2}
\]

The Fejer normalization used by T38 is

\[
 F_{R-1}(x)=\frac1R\left|\sum_{v=0}^{R-1}e(vx)\right|^2
 =\sum_{|u|\leq R-1}\left(1-\frac{|u|}{R}\right)e(ux).    \tag{3.3}
\]

Thus the signed support and weights are exactly

\[
 \mathcal U_R:=\{u\in\mathbb Z:|u|\leq R-1\},\qquad
 w(u):=1-\frac{|u|}{R}.                                    \tag{3.4}
\]

T38's proved expansion, flattened using its phase factorization, is

\[
 \begin{aligned}
 E_{\ell,R}(\beta_q)
 &:=\sum_{j=0}^{\ell-1}F_{R-1}(\beta_qQ_j)\\
 &=\sum_{u\in\mathcal U_R}w(u)
     \sum_{j=0}^{\ell-1}e(\beta_q\lambda(u,j)),\\
 \lambda(u,j)&:=uQ_j.                                      \tag{3.5}
 \end{aligned}
\]

The left side shows that `E` is real and nonnegative. The analytic inequality
in expanded FSFS is exactly

\[
 \boxed{\qquad \frac{\ell}{4R\delta^2}<E_{\ell,R}(\beta_q).\qquad} \tag{3.6}
\]

The legal-data conjuncts (2.12)-(2.14) remain separate from (3.6).

## 4. Decimal classes and every collision

### 4.1 Zero and nonzero classes

Since all `Q_j` are positive,

\[
 \lambda(u,j)=0\iff u=0.                                   \tag{4.1}
\]

The zero frequency therefore has multiplicity exactly `ell`: the points
`(0,j)`, `0<=j<ell`, all collide, and no nonzero point joins them.

For `u!=0`, uniquely write

\[
 u=\varepsilon10^am,
 \quad\varepsilon\in\{-1,1\},\quad a=\nu_{10}(|u|),
 \quad m\geq1,\quad10\nmid m.                              \tag{4.2}
\]

Because `10^(ell-j)-1` is `-1 mod 10`, (3.2) gives

\[
 \nu_{10}(|\lambda(u,j)|)=a+j.                              \tag{4.3}
\]

For two nonzero points, (4.2)-(4.3) give the complete criterion

\[
 \boxed{
 \lambda(u,j)=\lambda(u',j')\iff
 \begin{cases}
 \varepsilon=\varepsilon',\\
 a+j=a'+j',\\
 m(10^{\ell-j}-1)=m'(10^{\ell-j'}-1).
 \end{cases}}                                               \tag{4.4}
\]

Necessity follows by sign, exact powers of 10, and cancellation. Multiplying
the last line by the common signed power of 10 proves sufficiency. Together,
(4.1) and (4.4) include zero/zero, zero/nonzero, both signs, and all valuation
classes.

### 4.2 Off-diagonal parametrization

Orient two different indices as `0<=j<j'<ell`, and set

\[
 s:=\ell-j,\qquad t:=\ell-j',\qquad g:=\gcd(s,t),           \tag{4.5}
\]

\[
 A_{j,j'}:=\frac{10^s-1}{10^g-1},\qquad
 B_{j,j'}:=10^{j'-j}\frac{10^t-1}{10^g-1}.                 \tag{4.6}
\]

The Euclidean identity

\[
 10^s-1=10^{s-t}(10^t-1)+(10^{s-t}-1)                      \tag{4.7}
\]

reduces the pair of exponents exactly as the ordinary Euclidean algorithm;
hence

\[
 \gcd(10^s-1,10^t-1)=10^{\gcd(s,t)}-1.                    \tag{4.8}
\]

All repunits in (4.8) are coprime to 10, so

\[
 \gcd(Q_j,Q_{j'})=10^j(10^g-1),\quad
 \frac{Q_j}{\gcd(Q_j,Q_{j'})}=A_{j,j'},\quad
 \frac{Q_{j'}}{\gcd(Q_j,Q_{j'})}=B_{j,j'},                 \tag{4.9}
\]

with `gcd(A,B)=1` and `A>B`. Therefore the positive solutions of
`uQ_j=u'Q_(j')` are exactly

\[
 u=qB_{j,j'},\qquad u'=qA_{j,j'}\qquad(q\geq1).             \tag{4.10}
\]

Restoring the cutoff and signs, every nonzero off-diagonal collision is

\[
 ((u,j),(u',j'))=
 ((\varepsilon qB_{j,j'},j),(\varepsilon qA_{j,j'},j')),
\quad \varepsilon=\pm1,
\quad1\leq q\leq\left\lfloor\frac{R-1}{A_{j,j'}}\right\rfloor, \tag{4.11}
\]

or the reversal of the two complete frequency-index points. No other
off-diagonal collision exists by (4.9)-(4.10).

For an exact multiplicity formula, for every positive integer `v` define

\[
 \mu_v:=\sum_{j=0}^{\ell-1}
  \mathbf1_{\{Q_j\mid v,\ 1\leq v/Q_j\leq R-1\}},          \tag{4.12}
\]

\[
 c_v:=\sum_{j=0}^{\ell-1}
  \mathbf1_{\{Q_j\mid v,\ 1\leq v/Q_j\leq R-1\}}
  \left(1-\frac{v/Q_j}{R}\right).                         \tag{4.13}
\]

Then the positive frequency `v` has collision multiplicity `mu_v`, weight
`c_v`, the negative frequency has the same data, and the zero frequency has
multiplicity and weight `ell`. This records every multiplicity, including
fibers containing more than two points.

## 5. Exact diagonal/off-diagonal second moment

Grouping (3.5) with (4.12)-(4.13) gives the finite identity

\[
 E_{\ell,R}(\beta)=\ell+
   \sum_{v>0}c_v\{e(v\beta)+e(-v\beta)\}.                   \tag{5.1}
\]

Only finitely many `c_v` are nonzero. Character orthogonality is

\[
 \int_0^1e((v-v')\beta)\,d\beta=\mathbf1_{\{v=v'\}}.       \tag{5.2}
\]

Applying (5.2) term by term to (5.1) yields

\[
 \boxed{\int_0^1|E_{\ell,R}(\beta)|^2\,d\beta
 =\ell^2+2\sum_{v>0}c_v^2.}                                \tag{5.3}
\]

Expanding each square separates identical points from distinct colliding
points:

\[
 \begin{aligned}
 \int_0^1|E|^2
 ={}&\ell^2+2\ell\sum_{u=1}^{R-1}\left(1-\frac uR\right)^2\\
 &+2\!\!\sum_{\substack{(u,j)\ne(u',j')\\
       1\leq u,u'\leq R-1\\uQ_j=u'Q_{j'}}}
 \left(1-\frac uR\right)\left(1-\frac{u'}R\right).
                                                               \tag{5.4}
 \end{aligned}
\]

The last sum is ordered; the outer factor 2 accounts for the corresponding
negative frequencies. The diagonal is exactly

\[
 2\ell\sum_{u=1}^{R-1}\left(1-\frac uR\right)^2
 =\frac{\ell(R-1)(2R-1)}{3R}.                              \tag{5.5}
\]

Using (4.11), the exact resolved identity is

\[
 \boxed{
 \begin{aligned}
 \int_0^1|E_{\ell,R}(\beta)|^2\,d\beta
 ={}&\ell^2+\frac{\ell(R-1)(2R-1)}{3R}\\
 &+4\sum_{0\leq j<j'<\ell}
   \sum_{q=1}^{\lfloor(R-1)/A_{j,j'}\rfloor}
   \left(1-\frac{qB_{j,j'}}R\right)
   \left(1-\frac{qA_{j,j'}}R\right).
 \end{aligned}}                                             \tag{5.6}
\]

The factor 4 is 2 for the two orderings of each positive collision and 2 for
its positive/negative copies. If `Q=floor((R-1)/A)` then each inner sum is

\[
 Q-\frac{(A+B)Q(Q+1)}{2R}
  +\frac{ABQ(Q+1)(2Q+1)}{6R^2}.                             \tag{5.7}
\]

These formulas also cover empty sums. They determine an average over free
`beta`; they do not locate a spike at the fixed value (2.7).

## 6. The exact aggregate primitive-class criterion

Let

\[
 \mathcal M_R:=\{m:1\leq m\leq R-1,\ 10\nmid m\},\qquad
 \mathcal A_R(m):=\{a\geq0:10^am\leq R-1\}.                \tag{6.1}
\]

For each primitive class define

\[
 S_m:=\sum_{a\in\mathcal A_R(m)}\left(1-\frac{10^am}{R}\right), \tag{6.2}
\]

\[
 C_m(\beta):=\sum_{a\in\mathcal A_R(m)}
 \left(1-\frac{10^am}{R}\right)
 \sum_{j=0}^{\ell-1}
 \cos(2\pi\beta10^amQ_j).                                  \tag{6.3}
\]

The classes partition `1,...,R-1`; pairing positive and negative frequencies
in (3.5) therefore gives two exact identities:

\[
 \sum_{m\in\mathcal M_R}S_m
 =\sum_{u=1}^{R-1}\left(1-\frac uR\right)=\frac{R-1}{2},    \tag{6.4}
\]

\[
 \boxed{E_{\ell,R}(\beta)=\ell+
 2\sum_{m\in\mathcal M_R}C_m(\beta).}                     \tag{6.5}
\]

Substitution of (6.5) into (3.6) shows that the analytic part of T38's
expanded FSFS is equivalent, not merely implied, to the single weighted
aggregate criterion

\[
 \boxed{\operatorname{APC}(\beta,\ell,R,\delta):\quad
 \sum_{m\in\mathcal M_R}C_m(\beta)>
 \underbrace{\frac{\ell}{8R\delta^2}-\frac\ell2}_{
 \text{exact threshold}}.}                                 \tag{6.6}
\]

No normalization is hidden: (6.2) contains the Fejer weight, (6.3) contains
every valuation exponent and every stratum index, and (6.6) is strict because
T38's inequality is strict.

## 7. APC is strictly weaker on the finite scalar interface

Re-define the T40-motivated classwise condition here, without using any claim
from that note:

\[
 \operatorname{PCC}_{1/4}(\beta,\ell,R):\quad
 C_m(\beta)\geq\frac\ell4S_m
 \quad\hbox{for every }m\in\mathcal M_R.                    \tag{7.1}
\]

If (7.1) holds, then by (6.4)

\[
 \sum_mC_m(\beta)\geq\frac\ell4\frac{R-1}{2}
 =\frac{\ell(R-1)}8.                                       \tag{7.2}
\]

Since `R=ceil(delta^(-1))`,

\[
 \delta^{-1}\leq R
 \Longrightarrow
 \frac\ell{8R\delta^2}-\frac\ell2
 \leq\frac{\ell R}{8}-\frac\ell2
 =\frac{\ell(R-4)}8
 <\frac{\ell(R-1)}8.                                      \tag{7.3}
\]

Thus classwise PCC implies APC at every legal T38 scalar tuple.

The converse fails in the following exact finite scalar model, chosen to have
the large order and third-radius normalization occurring in T38:

\[
 \ell=3,\quad U=9,\quad R=18000,\quad
 \delta=\frac1{18000}=\frac1{2U10^\ell},\quad
 \beta=\frac14.                                            \tag{7.4}
\]

Here `R=ceil(delta^(-1))` and

\[
 Q_0=999,\qquad Q_1=990,\qquad Q_2=900.                    \tag{7.5}
\]

Because `R` is divisible by 4, complete fourth-root blocks in (3.3) give

\[
 F_{R-1}(999/4)=0,\qquad F_{R-1}(990/4)=0,\qquad
 F_{R-1}(900/4)=R.                                         \tag{7.6}
\]

Thus

\[
 E_{3,R}(1/4)=R=18000>
 \frac3{4R\delta^2}=\frac{3R}{4}=13500,                   \tag{7.7}
\]

so APC holds. On the other hand choose the primitive class `m=R-1=17999`.
It is not divisible by 10, `A_R(m)={0}`, and `S_m=1/R`. Reducing the three
integer products modulo 4 gives

\[
 999m\equiv1,\qquad990m\equiv2,\qquad900m\equiv0\pmod4,
\]

hence

\[
 C_m(1/4)=\frac1R\left(0-1+1\right)=0
 <\frac34\frac1R=\frac\ell4S_m.                            \tag{7.8}
\]

Therefore PCC fails while APC holds. This proves strict weakness on the
displayed finite scalar interface, even with `R>=180` and with `delta` equal to
T38's third-radius entry. The tuple is not claimed to arise from an actual
fixed-pi T26 chain; strict non-equivalence restricted to realizable chain
tuples is not asserted.

## 8. Uniform finite refutation of the resonance-only interface

We now test (6.6) after all substitutions in Section 2. Take any numeric T26
tuple `A,n,d,N,r,h,(s_q)` supplied there, retaining its actual `D_q`, `M_q`,
`U_q`, `delta`, and `R`. Change only the coefficient source by defining

\[
 \beta_0^*:=\frac14,\qquad
 \beta_q^*:=\frac{\prod_{t<q}U_t}{4}.                       \tag{8.1}
\]

Every `U_t=10^(s_t)-1` is odd, and (8.1) retains the exact successor relation

\[
 \beta_{q+1}^*=U_q\beta_q^*.                               \tag{8.2}
\]

Write the odd numerator of `beta_q^*` as `P_q`. Directly from powers of 10,
for every `M>=2`,

\[
 \begin{aligned}
 \sum_{x=0}^{M-1}e(P_q10^x/4)
 &=e(P_q/4)+e(10P_q/4)+\sum_{x=2}^{M-1}1\\
 &=\pm i-1+(M-2)=M-3\pm i,
 \end{aligned}                                             \tag{8.3}
\]

and hence

\[
 \left|\sum_{x=0}^{M-1}e(\beta_q^*10^x)\right|^2
 =(M-3)^2+1.                                                \tag{8.4}
\]

For every substituted node, (2.10) and `D_q>=D_0>=131072` imply
`M_q>=2D_q^2>=8`. Therefore

\[
 \left|\sum_{x<M_q}e(\beta_q^*10^x)\right|
 >M_q-3\geq\frac{M_q}{2}\geq\frac{M_q}{D_q}.              \tag{8.5}
\]

Thus the synthetic coefficients satisfy every T10/T26 node-resonance
inequality (2.9), with the actual substituted thresholds, lengths, shifts,
and successor factors.

Now use the numerically legal inherited stratum `ell=1` at any consecutive
pair `q,q+1`; its depth inequality holds because `M_{q+1}>=K>1`. Its sole
denominator is `Q_0=9`. By (3.3),

\[
 E_{1,R}(\beta_q^*)=F_{R-1}(9P_q/4)
 =\frac1R\left|\sum_{v=0}^{R-1}\zeta^v\right|^2,
 \qquad \zeta\in\{i,-i\}.                                 \tag{8.6}
\]

Writing `R=4a+b`, `0<=b<4`, complete blocks sum to zero and the four possible
squared norms of the remaining partial block are

\[
 b=0,1,2,3:\qquad 0,1,2,1.                                 \tag{8.7}
\]

Consequently

\[
 E_{1,R}(\beta_q^*)\leq\frac2R.                            \tag{8.8}
\]

On the other hand the actual T38 radius in (2.14) satisfies

\[
 \delta\leq\frac1{20U_q},
\]

so its exact FSFS threshold obeys

\[
 \frac1{4R\delta^2}\geq\frac{100U_q^2}{R}
 \geq\frac{8100}{R}>\frac2R.                              \tag{8.9}
\]

Equations (8.8)-(8.9) show that APC fails at every consecutive node of this
synthetic interface model despite every substituted resonance inequality
(8.5).

The model does **not** satisfy the fixed-pi identity

\[
 \beta_0=h(10^r-1)\pi.                                     \tag{8.10}
\]

Therefore it proves exactly

\[
 \{\text{T10/T26 resonance bounds, lengths, density updates, and
 successor relations}\}\not\Longrightarrow\operatorname{APC}, \tag{8.11}
\]

as an abstract interface implication. It does not prove that APC fails at an
actual fixed-pi coefficient. The narrower fixed-pi estimate still needed is,
for an actual coefficient (2.7) and some legal consecutive node and stratum,

\[
 \sum_{m\in\mathcal M_R}\sum_{a\in\mathcal A_R(m)}
 \left(1-\frac{10^am}{R}\right)
 \sum_{j=0}^{\ell-1}\cos(2\pi\beta_q10^am(10^\ell-10^j))
 >\frac\ell{8R\delta^2}-\frac\ell2.                        \tag{8.12}
\]

The resonance inequalities and successor identities alone do not force
(8.12). Whether the additional arithmetic identity (8.10) can force it is
open; none of T10, T26, or T38 asserts (8.12). In particular, this note asserts
no unconditional FSFS instance, adjacent compatibility, canonical (1.1), C1,
or decimal-complexity conclusion.

ABSTRACT INTERFACE REFUTED
