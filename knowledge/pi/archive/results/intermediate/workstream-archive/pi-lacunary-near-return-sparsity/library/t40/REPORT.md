# T40: decimal-valuation collisions in the fixed-stratum Fejer expansion

Claim label: **proof sketch**.  The inputs explicitly identified below are
kernel-checked, but this note itself is prose and is not a new Lean theorem.

## 1. Pins, scope, and quantifiers

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

Its canonical question is whether

\[
 \forall A\geq 1\ \exists n_0\geq 1\ \forall n\geq n_0\
 \exists N\geq 1:\qquad A n Q_\pi(n,N)\leq N^2,
\]

where ordered pairs are counted and the diagonal is included.  This note does
not prove or refute that statement.  In particular, it does not replace the
eventual quantifier by infinitely many `n`, prescribe `N`, remove the diagonal,
or replace circle distance by ordinary distance.

The two principal kernel-checked inputs are:

| input | SHA-256 | exact interface used |
|---|---|---|
| `TheoryLib/PiLacunaryNearReturnSparsity/T10LongLagResonance.lean` | `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947` | `lagExponentialSum` at lines 34-38 and the necessary-only theorem at lines 829-894 |
| `TheoryLib/PiLacunaryNearReturnSparsity/T38FixedStratumFejerSpike.lean` | `853f10a83b0dbf91955f7587c07cd4651e5954b19f78942703df15073456a014` | fixed-stratum domain at lines 42-94, denominator identity at lines 96-105, `stratumDelta` and `stratumOrder` at lines 329-394, `FSFS` at lines 396-411, the expansion at lines 622-676, and `fsfs_iff_expandedFSFS` at lines 678-718 |

For identification of T38's actual node coefficient, this note also uses the
kernel-checked definition in
`T26SharedResonanceChain.lean` (SHA-256
`7278999f1ff89d11e7ee408b21e5a300fbdc3e78cf5a6776a2274fc9a761f1c2`):
the adjacent factor used below is defined and proved positive in
`T28AdjacentNodeCompatibility.lean`, lines 60-65 and 245-256 (SHA-256
`f94c5c2060be43f0800e83adb782b5f3d20ee3fff7beadd2d28c9e92cc818dbd`).

Fix natural numbers `M,D,K,d,h,r` and a chain of T38's full type

```text
GeometricResonanceChain (initialCoefficient h r) M D 1 K d {r}.
```

If `s_q` denotes entry `q` of `chain.shifts`, then T26's exact definitions give

\[
 \beta_k=\operatorname{nodeCoefficient}(k)
 =h(10^r-1)\pi\prod_{q<k}(10^{s_q}-1).                       \tag{1.1}
\]

Hereafter also fix a node `k : Fin d` and an integer `ell` satisfying

\[
 1\leq D,\qquad 1\leq\ell<\operatorname{commonDepth}(k).
\]

Set

\[
 \beta=\beta_k,\qquad
 \delta=\operatorname{stratumDelta}(k,\ell)>0,\qquad
 R=\left\lceil\delta^{-1}\right\rceil\geq1.
\]

These are local fixed-node, fixed-stratum quantities.  No universal or
existential assertion about which T10/T26 chain has the estimate introduced in
Section 6 is implicit.

### Recorded interpretation issues

1. By "10-adic valuation" this note means the decimal divisibility exponent
   \(\nu_{10}(n)=\max\{a:10^a\mid n\}\) for a nonzero integer `n`.  Since 10 is
   composite, this is only the named divisibility statistic; no nonarchimedean
   valuation law is used.
2. A transported-frequency collision means equality of the integer
   multipliers.  It is stronger than equality of their phase values at one
   particular `beta`.
3. The integral in Section 5 averages over a free real `beta` in `[0,1]`.
   T26 builds a chain from one finite T10 resonance, and T38 quantifies over a
   node of that chain with its particular fixed-pi coefficient `beta_k`.
   Averaging cannot silently replace evaluation at that coefficient.
4. T38's `FSFS` is a conditional local predicate.  Even proving it once would
   not by itself prove uniform adjacent compatibility or canonical A1.

## 2. The exact T38 frequency domain

T38 proves that the actual common pair domain equals the union of denominator
strata and that the stratum of total length `ell` is

\[
 \{(j,\ell-j):0\leq j<\ell\}.
\]

On this stratum, T38's `pairDenominator_stratum` gives

\[
 D_j:=10^\ell-10^j=10^j(10^{\ell-j}-1)>0
 \qquad(0\leq j<\ell).                                      \tag{2.1}
\]

The Fourier support in `lacunaryExpansion beta ell R` is exactly

\[
 \mathcal U_R=\{u\in\mathbb Z:|u|\leq R-1\},
 \qquad w_R(u)=1-\frac{|u|}{R}.                             \tag{2.2}
\]

Flattening T38's proved phase factorization therefore gives the finite sum

\[
 E_{\ell,R}(\beta)
 =\sum_{u\in\mathcal U_R}w_R(u)
   \sum_{0\leq j<\ell}e^{2\pi i\beta\lambda(u,j)},
 \qquad \lambda(u,j):=uD_j.                                \tag{2.3}
\]

By `stratumFejerSum_eq_lacunaryExpansion`, this complex expression equals the
real nonnegative Fejer sum

\[
 E_{\ell,R}(\beta)=
 \sum_{j<\ell}F_{R-1}(\beta D_j).                           \tag{2.4}
\]

Consequently the analytic inequality in T38's FSFS is precisely

\[
 \frac{\ell}{4R\delta^2}<E_{\ell,R}(\beta).                 \tag{2.5}
\]

The other three FSFS conjuncts are the legal-data conditions already fixed in
Section 1.

## 3. Decimal valuation classes and all collisions

### 3.1 Zero frequency

Every `D_j` is positive.  Hence

\[
 \lambda(u,j)=0\quad\Longleftrightarrow\quad u=0.           \tag{3.1}
\]

Thus the zero frequency has multiplicity exactly `ell`: all `(0,j)` collide
with one another, and no nonzero `u` collides with them.  This remains true
when `R=1`, in which case zero is the entire Fourier support.

### 3.2 Nonzero valuation criterion

For `u != 0`, write uniquely

\[
 u=\varepsilon10^a m,
 \quad \varepsilon\in\{-1,1\},\quad a=\nu_{10}(|u|),
 \quad m\geq1,\quad10\nmid m.                              \tag{3.2}
\]

For a second nonzero frequency write
`u'=epsilon' 10^(a') m'` in the same way.  Because
`10^(ell-j)-1` is congruent to `-1` modulo 10, (2.1) gives

\[
 \nu_{10}(|\lambda(u,j)|)=a+j.                              \tag{3.3}
\]

It follows that, on the exact domain (2.2),

\[
\boxed{
 \lambda(u,j)=\lambda(u',j')
 \Longleftrightarrow
 \begin{cases}
  \varepsilon=\varepsilon',\\
  a+j=a'+j',\\
  m(10^{\ell-j}-1)=m'(10^{\ell-j'}-1).
 \end{cases}}                                               \tag{3.4}
\]

Necessity is direct.  Positivity of the denominators forces equal signs.
After writing out (2.1), unequal exponents `a+j` and `a'+j'` would make one
side, but not the other, divisible by 10.  Cancelling the common sign and
power of 10 gives the last identity.  Conversely, multiplying the last
identity by the common signed power of 10 proves equality.  Together with
(3.1), this treats every signed pair, including all zero/nonzero edge cases.

### 3.3 Complete off-diagonal parameterization

For a form with no hidden divisibility conditions, orient distinct indices as
`0 <= j < j' < ell` and put

\[
 s=\ell-j,\quad t=\ell-j',\quad g=\gcd(s,t),
\]

\[
 A_{j,j'}=\frac{10^s-1}{10^g-1},\qquad
 B_{j,j'}=10^{j'-j}\frac{10^t-1}{10^g-1}.                  \tag{3.5}
\]

The elementary repunit identity

\[
 \gcd(10^s-1,10^t-1)=10^{\gcd(s,t)}-1                     \tag{3.6}
\]

follows by applying the Euclidean algorithm to the exponents.  Since every
repunit in (3.6) is coprime to 10, (3.6) gives

\[
 \gcd(D_j,D_{j'})=10^j(10^g-1),
 \quad \frac{D_j}{\gcd(D_j,D_{j'})}=A_{j,j'},
 \quad \frac{D_{j'}}{\gcd(D_j,D_{j'})}=B_{j,j'},           \tag{3.7}
\]

with `gcd(A_(j,j'),B_(j,j'))=1` and `A_(j,j')>B_(j,j')`.
Therefore all positive solutions of `u D_j = u' D_(j')` are exactly

\[
 u=qB_{j,j'},\qquad u'=qA_{j,j'}\qquad(q\geq1).             \tag{3.8}
\]

Restoring signs and the cutoff, every nonzero off-diagonal collision is
exactly

\[
 ((u,j),(u',j'))
 =((\varepsilon qB_{j,j'},j),(\varepsilon qA_{j,j'},j')),
 \quad \varepsilon\in\{-1,1\},
 \quad1\leq q\leq
 \left\lfloor\frac{R-1}{A_{j,j'}}\right\rfloor,           \tag{3.9}
\]

or the reversal of these entire frequency-index points.  Reversing only
`u,u'` while retaining `j<j'` is not a collision.  Equations (3.1), (3.4), and (3.9)
classify all pairwise transported-frequency collisions on T38's actual
fixed-stratum domain.

### 3.4 The sharp first collision

Since `j<j'` implies `s>t`, the number `g` is a proper divisor of `s`.
Writing `s=ng` with `n>=2`,

\[
 A_{j,j'}=1+10^g+\cdots+10^{(n-1)g}\geq11.                 \tag{3.10}
\]

Equality requires `s=2,t=1`.  Thus there are no nonzero off-diagonal
collisions when `R<=11`, and the bound is sharp.  For every `ell>=2`,

\[
 10D_{\ell-2}=10(99\cdot10^{\ell-2})
 =11(90\cdot10^{\ell-2})=11D_{\ell-1}.                    \tag{3.11}
\]

Hence `(10,ell-2)` and `(11,ell-1)` collide as soon as `R>=12`.

This is not a remote edge case in T38.  Define

\[
 U=\operatorname{GeometricResonanceChain.adjacentFactor}(\texttt{chain},k).
\]

T28's kernel-checked `adjacentFactor_pos` gives `U>=1`, and the third entry in
T38's `stratumDelta` is

\[
 \frac1{2U10^\ell},\qquad U\geq1,
\]

so legal `ell>=1` gives `delta<=1/20` and therefore `R>=20`.  Consequently
every legal T38 stratum with `ell>=2` contains the explicit collision (3.11).
The unscaled-denominator injectivity proved in T38 cannot be promoted to
injectivity of `(u,j) |-> uD_j`.

## 4. Primitive classes versus collision classes

Let

\[
 \mathcal M_R=\{m:1\leq m\leq R-1,\ 10\nmid m\},
 \qquad
 \mathcal A_R(m)=\{a\geq0:10^am\leq R-1\}.                 \tag{4.1}
\]

These sets partition the positive Fourier indices by `u=10^a m`.  A single
primitive class has no internal off-diagonal frequency collision.  Indeed,
if the two primitive parts in (3.4) are the same `m`, its last equality makes
`10^(ell-j)-1=10^(ell-j')-1`, hence `j=j'`; then (3.3) gives `a=a'`.

The explicit collision (3.11), by contrast, crosses primitive classes:
`10=10^1*1` and `11=10^0*11`.  Thus valuation stratification diagonalizes
each primitive class separately but leaves exactly the cross-class families
(3.9).  This is the precise obstruction to a collision-free second-moment
argument.

## 5. Exact diagonal/off-diagonal second moment

For `n>0`, aggregate the positive-frequency coefficient by

\[
 c_n=\sum_{\substack{1\leq u\leq R-1,\ 0\leq j<\ell\\uD_j=n}}
       w_R(u).                                               \tag{5.1}
\]

The zero coefficient is `c_0=ell`, not `1`, because of (3.1).  Character
orthogonality

\[
 \int_0^1e^{2\pi i\beta(n-n')}\,d\beta
 =\begin{cases}1,&n=n',\\0,&n\ne n'\end{cases}             \tag{5.2}
\]

applied to the finite sum (2.3) yields the exact identity

\[
\boxed{
 \int_0^1|E_{\ell,R}(\beta)|^2\,d\beta
 =\ell^2+2\sum_{n>0}c_n^2.}                                \tag{5.3}
\]

Separating identical positive pairs from distinct colliding pairs gives

\[
 \int_0^1|E|^2
 =\ell^2+2\ell\sum_{u=1}^{R-1}w_R(u)^2
 +2\!\!\sum_{\substack{(u,j)\ne(u',j')\\
          1\leq u,u'\leq R-1\\uD_j=u'D_{j'}}}
       w_R(u)w_R(u').                                       \tag{5.4}
\]

The last sum is ordered; the displayed factor `2` accounts for the matching
negative frequencies.  The nonzero diagonal is exactly

\[
 2\ell\sum_{u=1}^{R-1}\left(1-\frac uR\right)^2
 =\frac{2\ell}{R^2}\sum_{v=1}^{R-1}v^2
 =\frac{\ell(R-1)(2R-1)}{3R}.                              \tag{5.5}
\]

Using the complete collision parameterization (3.9), the ordered factors can
instead be resolved into the following fully explicit unordered-index form:

\[
\boxed{
\begin{aligned}
 \int_0^1|E_{\ell,R}(\beta)|^2\,d\beta
 ={}&\ell^2+\frac{\ell(R-1)(2R-1)}{3R}\\
 &+4\sum_{0\leq j<j'<\ell}
   \sum_{q=1}^{\lfloor(R-1)/A_{j,j'}\rfloor}
   \left(1-\frac{qB_{j,j'}}R\right)
   \left(1-\frac{qA_{j,j'}}R\right).
\end{aligned}}                                               \tag{5.6}
\]

The factor `4` is exactly `2` for the two orderings of each positive
collision times `2` for its positive/negative copies.  If
`Q=floor((R-1)/A_(j,j'))`, the inner sum in (5.6) is, without asymptotic
notation,

\[
 Q-\frac{(A+B)Q(Q+1)}{2R}
 +\frac{ABQ(Q+1)(2Q+1)}{6R^2},                              \tag{5.7}
\]

where `A=A_(j,j')` and `B=B_(j,j')`.  Formula (5.6) also covers
`R=1` and `ell=1`: the corresponding sums are empty and the moment is
`ell^2` when only the zero mode remains.

The off-diagonal term is nonnegative.  It raises the average square, but it
does not identify the location of a spike, much less place one at the fixed
number `beta_k` of the T26 chain built from a finite T10 resonance.

## 6. One explicit sufficient primitive-correlation estimate

Define the positive weight and real correlation of primitive class `m` by

\[
 S_m=\sum_{a\in\mathcal A_R(m)}w_R(10^am),                  \tag{6.1}
\]

\[
 C_m(\beta)=\sum_{a\in\mathcal A_R(m)}w_R(10^am)
   \sum_{j<\ell}\cos(2\pi\beta\,10^amD_j).                 \tag{6.2}
\]

Pairing the positive and negative terms in (2.3) gives the exact identity

\[
 E_{\ell,R}(\beta)=\ell+2\sum_{m\in\mathcal M_R}C_m(\beta).
                                                                    \tag{6.3}
\]

We name the following local, pointwise inequality.

> **Primitive-Class Quarter-Correlation Estimate**
> `PCC_(1/4)(beta,ell,R)`: for every `m in M_R`,
> \[
> C_m(\beta)\geq\frac\ell4 S_m.                             \tag{6.4}
> \]

This is one quarter of the largest possible real contribution `ell*S_m` in
every primitive class separately.  It forbids cancellation in one class from
being hidden by excess in another and is therefore not the aggregate FSFS
inequality under a new name.

The classes partition `1,...,R-1`, so

\[
 \sum_{m\in\mathcal M_R}S_m
 =\sum_{u=1}^{R-1}\left(1-\frac uR\right)
 =\frac{R-1}{2}.                                            \tag{6.5}
\]

If (6.4) holds at T38's actual `beta=beta_k`, then (6.3)-(6.5) imply

\[
 E_{\ell,R}(\beta_k)
 \geq\ell+2\frac\ell4\frac{R-1}{2}
 =\frac{\ell(R+3)}4.                                       \tag{6.6}
\]

Since `R=ceil(delta^(-1))` and `delta>0`,

\[
 \delta^{-1}\leq R,
 \qquad
 \frac{\ell}{4R\delta^2}\leq\frac{\ell R}{4}
 <\frac{\ell(R+3)}4.                                       \tag{6.7}
\]

Equations (6.6)-(6.7) prove the strict analytic inequality (2.5), with the
constant `1/4` displayed.  Together with the three legal-data conjuncts,
`PCC_(1/4)(beta_k,ell,R)` is therefore sufficient for T38's FSFS at this
node and stratum.  For abstract `R=1`, (6.4) is vacuous and the same conclusion
holds because `E=ell` while `ell/(4 delta^2)<=ell/4`; actual legal T38 data
already have `R>=20`.

### 6.1 Not an aggregate renaming; the abstract converse fails

The distinction can be tested by an exact algebraic example.  Take

\[
 \ell=1,\quad R=2,\quad\delta=\tfrac12,\quad\beta=\tfrac1{36}.
\]

Then `D_0=9`, `w_R(1)=1/2`, and

\[
 C_1(\beta)=\tfrac12\cos(2\pi\cdot9/36)=0<\tfrac18
 =\frac\ell4S_1,                                            \tag{6.8}
\]

so `PCC_(1/4)` fails.  Nevertheless

\[
 E_{1,2}(\beta)=1>\frac1{4\cdot2\cdot(1/2)^2}=\frac12,     \tag{6.9}
\]

so the FSFS analytic inequality holds.  This is an exact counterexample to
the converse on the displayed abstract scalar domain.  It proves that (6.4)
is not algebraically the aggregate FSFS inequality under a new name.  It is
deliberately not an example of legal T38 chain data; strict non-equivalence
after restricting to realizable chain tuples is not claimed.  The example is
also not a statement about pi.

## 7. What remains at the fixed-pi coefficient

T10's necessary-only conclusion starts from a hypothetical failure of
canonical A1 and has the quantifier pattern

\[
 \exists A\ \forall n_0\ \exists n\ \forall K\ \exists N,r,h.
                                                                    \tag{7.1}
\]

For each requested `K`, the returned `N,r,h` may change.  In particular T10
does not supply one persistent harmonic or coefficient across all requested
lengths.  Each returned positive lag `r` and low positive harmonic `h` gives a
large sum with phase coefficient

\[
 \beta_0=h(10^r-1)\pi.                                     \tag{7.2}
\]

For each requested finite depth, T26 selects one such finite T10 resonance and
builds a chain that keeps that source while multiplying (7.2) by explicit
factors `10^s-1`, producing T38's `beta_k`.  This provenance matters: beta is
not a free point selected after inspecting (5.6).

Neither cited kernel-checked file supplies (6.4).  T10 controls one
low-harmonic lacunary sum at one resonance scale.  `PCC_(1/4)` simultaneously
requires a positive lower bound for every primitive `m` and every decimal
valuation `a` represented below `R`, after the denominator transport `D_j`.
T38 proves the exact expansion and the FSFS/expanded-FSFS equivalence.  The
new prose calculation (6.3)-(6.7), not a theorem in T38, proves that the
stronger pointwise estimate would be sufficient.  Neither file constructs it.

The exact second moment (5.6) cannot fill this gap.  It averages over all
`beta`, includes unavoidable cross-primitive collisions such as (3.11), and
does not transfer a generic spike to the prescribed fixed-pi node coefficient.
Thus valuation stratification identifies the missing cancellation statement
but does not establish it.

## Terminal verdict

**OPEN WITH ONE NAMED PRIMITIVE-CORRELATION ESTIMATE:
`PCC_(1/4)` AT AN ACTUAL T26/T38 NODE BUILT FROM A T10 RESONANCE.**

The note proves in prose the exact domain decomposition, all integer-frequency
collision identities, and the second-moment formula.  It also verifies with
explicit constants that the classwise `PCC_(1/4)` is sufficient for the
analytic part of FSFS and is not merely its aggregate inequality renamed; the
abstract counterexample does not claim realizability by a T38 chain.  The note
does **not** assert `PCC_(1/4)` for pi, FSFS for pi, unconditional adjacent
compatibility, or canonical A1.
