# T36: denominator-stratified boundary loss for the T34 bridge

## Status

**OPEN WITH ONE NAMED ESTIMATE: Fixed-Stratum Fejer Spike (FSFS).**

Claim label: **proof sketch**. The finite calculations in `verify_bound.py` are
**experiment** only. T24, T26, T28, and T34 are machine-checked dependencies;
the new analytic estimates in this note have not been formalized in Lean.

The canonical statement is vendored as `canonical_statement.txt`. Text-file
packaging adds one terminal LF which the immutable source lacks; the verifier
removes exactly that transport byte and checks the resulting source SHA-256:

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

It asks the ordered, diagonal-inclusive fixed-pi question A1. This note does
not prove or refute A1. In particular, none of the rational models in Section
8 is a T26 chain for pi.

## 1. Fixed T26/T34 domain

Fix natural numbers `M,D,K,d,h,r` satisfying

\[
  1\le D,\qquad 1\le d,\qquad 1\le h,\qquad 1\le r,
  \tag{1}
\]

and a genuine fixed-pi chain object of the exact T26/T34 type

\[
 \mathcal C:\operatorname{GeometricResonanceChain}
  (\operatorname{initialCoefficient}(h,r),M,D,1,K,d,\{r\}).
 \tag{2}
\]

Assume throughout the exact T26 nodewise-inverse length request

\[
  2\,\operatorname{densityDenominator}(D,d)^2\le K.       \tag{2a}
\]

Thus the initial coefficient is `h(10^r-1) pi`; it is not a freely selected
real phase. Fix `k : Fin d`, and abbreviate

\[
\begin{aligned}
 M_0&=\mathcal C.\operatorname{nodeResidual}(k),&
 M_1&=\mathcal C.\operatorname{nodeResidual}(k+1),\\
 \beta _0&=\mathcal C.\operatorname{nodeCoefficient}(k),&
 \beta _1&=\mathcal C.\operatorname{nodeCoefficient}(k+1),\\
 t&=\mathcal C.\operatorname{shiftAt}(k),& U&=10^t-1,\\
 D_0&=\operatorname{densityDenominator}(D,k),&
 D_1&=\operatorname{densityDenominator}(D,k+1),\\
 \tau_i&=(8D_i^2)^{-1},&
 E_i&=\operatorname{inverseError}(\tau_i)
       ={\arccos(\tau_i)\over2\pi}.
\end{aligned}
\tag{3}
\]

The machine-checked T28 transport identity is

\[
             \boxed{\beta _1=U\beta _0}.                 \tag{4}
\]

Since the chain has shift lower bound one, `t >= 1` and hence

\[
                         U\ge9.                            \tag{5}
\]

The exact T34 common domain is

\[
 \Omega=\{(j,s)\in\mathbb N^2:
  1\le s,\ j+s<M_0,\ j+s<M_1\}.             \tag{6}
\]

Put `L=min(M_0,M_1)`. Then (6) is exactly

\[
 \Omega=\{(j,s):1\le s,\ j+s<L\}.           \tag{7}
\]

No residual inequality has been dropped: (7) is just the conjunction in (6)
rewritten using the minimum. T34's ambient product-range clauses
`j<M_0` and `s<M_1` follow respectively from `j+s<M_0` and
`j+s<M_1` together with `j>=0` and `s>=1`, so (7) also retains those
clauses. T26's `final_residual`, its prefix-sum inequality, and (2a) give

\[
 M_0\ge K\ge2,\qquad M_1\ge K\ge2,
 \qquad\boxed{L\ge2}.                              \tag{8}
\]

Thus the denominator strata used below are nonempty in the intended T26
application. The boundary calculation does not silently assume that the separate T24
witnesses have a common index pair.

## 2. Exact denominator strata

For `(j,s) in Omega`, define

\[
 Q(j,s)=10^j(10^s-1).
 \tag{9}
\]

Stratify by `ell=j+s`. For each `1 <= ell < L`, the stratum is

\[
 \Omega_\ell=\{(j,\ell-j):0\le j<\ell\},
 \qquad |\Omega_\ell|=\ell,                  \tag{10}
\]

and

\[
 Q_{\ell,j}:=Q(j,\ell-j)=10^\ell-10^j.       \tag{11}
\]

Consequently

\[
 9\cdot10^{\ell-1}\le Q_{\ell,j}<10^\ell.   \tag{12}
\]

Different `ell` are separated by (12). At fixed `ell`, (11) is strictly
decreasing in `j`. Therefore `(j,s) -> Q(j,s)` is injective on `Omega`.
This also gives the exact cardinality

\[
 |\Omega|=\sum_{\ell=1}^{L-1}\ell={L(L-1)\over2}.         \tag{13}
\]

The `j=0` point is the cycle denominator `10^ell-1`; the remaining `ell-1`
points have positive preperiod.

## 3. Nearest errors and the exact bad partition

For `Q=Q(j,s)`, let

\[
 d_i(Q)=\|Q\beta_i\|_{\mathbb R/\mathbb Z}\in[0,1/2].   \tag{14}
\]

Nearest integers attain these distances. Replacing arbitrary T34 witnesses by
nearest integers can only decrease both node errors and the mixed budget.
Hence T34's `JointGoodPair` is equivalent on `Omega` to

\[
 d_0(Q)<E_0,\qquad d_1(Q)<E_1,\qquad
 Q\bigl(d_1(Q)+U d_0(Q)\bigr)<1.             \tag{15}
\]

Equation (4) gives the circle-distance transport inequality

\[
                  d_1(Q)\le U d_0(Q).         \tag{16}
\]

Partition the complement of (15) disjointly as

\[
\begin{aligned}
 \mathcal B_0&=\{Q:d_0\ge E_0\},\\
 \mathcal B_1&=\{Q:d_0<E_0,\ d_1\ge E_1\},\\
 \mathcal B_m&=\{Q:d_0<E_0,\ d_1<E_1,
                     Q(d_1+Ud_0)\ge1\}.
\end{aligned}                                      \tag{17}
\]

This is exactly T34's `boundaryLoss` predicate, not a larger informal
"boundary region".

Because `D_i >= 1`, one has `0 < tau_i <= 1/8`. Monotonicity of arccos and
`cos(pi/3)=1/2` give the useful explicit range

\[
                       {1\over6}<E_i<{1\over4}.      \tag{18}
\]

## 4. Fejer envelopes with all constants

Let `H_0,H_1` be T34's cutoffs and put

\[
 A_i=H_i+1,\qquad P=A_0A_1.                   \tag{19}
\]

T34's point weight is

\[
 W(Q)=F_{H_0}(Q\beta_0)F_{H_1}(Q\beta_1),    \tag{20}
\]

where `F_H` is normalized to have mean one and maximum `H+1`. No additional
theorem dependency is needed for the pointwise bound. From T34's displayed
Fejer definition, if `d=||x||` and `0<d<=1/2`, the finite geometric-series
identity and `|sin(pi d)|>=2d` give

\[
 F_H(x)={1\over H+1}
 \left|{\sin(\pi(H+1)x)\over\sin(\pi x)}\right|^2
 \le {1\over4(H+1)d^2}.                         \tag{20a}
\]

Together with the triangle-inequality bound `F_H(x)<=H+1`, this yields, for
`0<delta<=1/2`,

\[
 F_H(x)\le\min\left\{H+1,
             {1\over4(H+1)\delta^2}\right\}
 \quad\hbox{when }\|x\|_{\mathbb R/\mathbb Z}\ge\delta. \tag{21}
\]

The constant 4 is the best constant obtained from the global linear inequality
`|sin(pi x)| >= 2||x||`; equality occurs at distance `1/2`. Define

\[
 \rho_i(z)=\min\left\{1,{1\over4A_i^2z^2}\right\}
 \quad(z>0).                                      \tag{22}
\]

For a point in `B_0`, (21) gives

\[
 W(Q)\le B_0^*=P\rho_0(E_0).                   \tag{23}
\]

For a point in `B_1`, (16) also gives `d_0 >= E_1/U`, so

\[
 W(Q)\le B_1^*=P\rho_0(E_1/U)\rho_1(E_1).      \tag{24}
\]

This is sharper than discarding the transported left-node information.

### Optimized mixed-budget envelope

For `Q in B_m`, define

\[
 x_Q={UQ\over2A_0},\qquad y_Q={Q\over2A_1}.     \tag{25}
\]

The product of the two envelopes in (21) decreases when either positive
distance increases. Scale `(d_0,d_1)` down to the budget boundary while
preserving (16), and write

\[
 Ud_0={\lambda\over Q},\qquad
 d_1={1-\lambda\over Q}.                        \tag{26}
\]

Condition (16) is exactly `lambda >= 1/2`. Thus the optimized normalized
envelope is

\[
 m(x,y)=\max_{1/2\le\lambda\le1}
 \min\left\{1,{x^2\over\lambda^2}\right\}
 \min\left\{1,{y^2\over(1-\lambda)^2}\right\}. \tag{27}
\]

At the allowed endpoint `lambda=1`, the second minimum is defined to be one,
which is its continuous limiting value and corresponds to `d_1=0`. This
removes any division-by-zero convention from (27).

Direct optimization over the breakpoints `lambda=x` and `lambda=1-y` gives

\[
m(x,y)=
\begin{cases}
1,&x\ge1/2\text{ and }x+y\ge1,\\[2mm]
\left({x\over\max(1/2,1-y)}\right)^2,&x<1/2,\\[3mm]
\max\left\{
 \left({y\over1-x}\right)^2,
 \left({x\over1-y}\right)^2
\right\},&x\ge1/2\text{ and }x+y<1.
\end{cases}                                      \tag{28}
\]

The denominators in the last case are positive because `x+y<1`. Formula (28)
also handles `y>=1` through the first two cases. It is the exact maximum of
the relaxed two-distance envelope (27), not merely a choice of a half-budget
threshold. The restrictions `d_i<E_i` do not alter the maximum: by (5),
(12), and (18), points on (26) satisfy

\[
 d_0\le {1\over UQ}<{1\over6}<E_0,
 \qquad d_1\le {1\over2Q}<{1\over6}<E_1.        \tag{29}
\]

Therefore

\[
 W(Q)\le B_m^*(Q):=P\,m(x_Q,y_Q)\quad(Q\in\mathcal B_m). \tag{30}
\]

For comparison, optimizing only a binary split
`d_0 >= theta/(UQ)` or `d_1 >= (1-theta)/Q` gives

\[
 \theta_*={UA_1\over UA_1+A_0},\qquad
 P\min\left\{1,{Q^2(A_0+UA_1)^2\over4A_0^2A_1^2}\right\}. \tag{31}
\]

Equation (30) is never worse and can be strictly better. This records and
optimizes the threshold rather than fixing it at `1/2`.

## 5. The denominator-stratified upper bound

Define

\[
 \mathcal B(Q)=\max\{B_0^*,B_1^*,B_m^*(Q)\}.    \tag{32}
\]

The explicit candidate bound is

\[
\boxed{
 \operatorname{boundaryLoss}(\mathcal C,k,H_0,H_1)
 \le
 \sum_{\ell=1}^{L-1}\sum_{j=0}^{\ell-1}
   \mathcal B(10^\ell-10^j).}
                                                        \tag{DBL}
\]

**Proof sketch.** Equations (10)-(12) enumerate every common legal pair once.
The three classes in (17) are disjoint and exhaustive. Apply (23), (24), or
(30) according to its class, then bound that class-dependent envelope by the
maximum in (32) and sum. Every summand is nonnegative by T34's
`commonPairWeight_nonneg`. If `L<=1`, both sides are empty and zero. This
proves `(DBL)` as an elementary inequality, conditional only on the displayed
fixed setup. No T32 claim is used. `verify_bound.py` checks its finite indexing
and the optimization formula numerically, but those checks are not its proof.

A sharper class-count form, useful when arithmetic information is available,
is

\[
 \operatorname{boundaryLoss}\le
 B_0^*|\mathcal B_0|+B_1^*|\mathcal B_1|
   +\sum_{Q\in\mathcal B_m}B_m^*(Q).            \tag{33}
\]

Equation (33) and `(DBL)` are the same proved partition estimate before and
after forgetting class membership.

## 6. Transported-frequency injectivity

T34's exact expansion uses

\[
 (u,v)\longmapsto w=u+Uv,
 \quad |u|\le H_0,\quad |v|\le H_1.             \tag{34}
\]

The coefficients and supports are exactly

\[
 c_H(u)=1-{|u|\over H+1}\quad (|u|\le H),
 \qquad c_H(u)=0\quad (|u|>H),                  \tag{34a}
\]

so `c_H(u)>=0`, `c_H(0)=1`, and the coefficient attached to `(u,v)`
is precisely `c_{H_0}(u)c_{H_1}(v)`. There is no omitted normalization:

\[
 F_H(x)=\sum_{|u|\le H}c_H(u)e^{2\pi iux},
 \qquad \sum_{|u|\le H}c_H(u)=H+1.             \tag{34b}
\]

Suppose two pairs have the same transported frequency. Then

\[
 U(v-v')=u'-u,
 \qquad |u'-u|\le2H_0.                          \tag{35}
\]

If

\[
                         \boxed{U>2H_0},         \tag{36}
\]

and `v != v'`, the nonzero left side of (35) has absolute value at least `U`,
contradicting (35). Thus `v=v'`, and then `u=u'`. This proves injectivity.

The condition is optimal as a uniform condition when `H_1>=1`: if
`U<=2H_0`, two integers in `[-H_0,H_0]` can differ by `U`, and pairing them
with `v=1` and `v'=0` gives a collision. At equality, the explicit collision
is

\[
 (-H_0,1)\mapsto H_0,
 \qquad (H_0,0)\mapsto H_0.                     \tag{37}
\]

When `H_1=0`, injectivity is automatic and (36) is unnecessary. Thus no
cutoff edge case is hidden.

Injectivity removes frequency multiplicity from T34's double sum, but gives
no bound on the resulting fixed-pi exponential sums.

## 7. Why `(DBL)` does not close T34

T34 machine-checks

\[
 \operatorname{mixedProductSum}
 =\operatorname{commonGoodMass}+\operatorname{boundaryLoss}              \tag{38}
\]

and identifies `mixedProductSum` with the real part of its transported
double-frequency sum. Thus `(DBL)` would yield positive good mass only after
the additional strict estimate

\[
 \operatorname{mixedProductSum}>
 \sum_{\ell=1}^{L-1}\sum_{j=0}^{\ell-1}
   \mathcal B(10^\ell-10^j).                   \tag{39}
\]

Neither the separate nodewise T24 alternatives nor frequency injectivity
implies (39). Equation (39) is recorded only to show why the `(DBL)` route
stops; it is abandoned and is not a second surviving estimate. Section 9
replaces it with the single narrower target `(FSFS)`. In fact, (28) equals one whenever

\[
 x_Q\ge1/2\quad\hbox{and}\quad x_Q+y_Q\ge1,     \tag{40}
\]

so the mixed-budget contribution can attain the trivial pointwise cap `P`.
The perturbed model below shows that a mixed-budget failure can retain more
than 81 percent of this cap. Denominator stratification therefore does not,
by itself, extract cross-node compatibility from T24's nodewise information.

## 8. Exact model calculations

These are exact models of the algebra `beta_1=U beta_0`, the T24 denominator,
and T34's weights. They are not fixed-pi T26 chains because their coefficients
are rational rather than positive integral multiples of pi. They test the
bound and cannot refute canonical A1.

For all three models take `H_0=H_1=1`, so

\[
 F_1(x)=1+\cos(2\pi x),\qquad P=4.              \tag{41}
\]

### 8.1 Exact cycle

Take

\[
 U=9,\quad(j,s)=(0,1),\quad Q=9,\quad
 \beta_0={1\over9},\quad\beta_1=1,
 \quad(a_0,a_1)=(1,9),                          \tag{42}
\]

and residuals `(M_0,M_1)=(3,2)`. The common-domain inequalities are
`1=j+s<2<=3`. Both scaled errors are zero, so the mixed budget is zero and
the pair is jointly good. Its weight is the exact maximum

\[
                         F_1(1)F_1(9)=4.         \tag{43}
\]

It contributes zero to `boundaryLoss`, as required by `(DBL)`.

### 8.2 Genuine positive preperiod

Take

\[
 U=99,\quad(j,s)=(1,1),\quad Q=90,\quad
 \beta_0={1\over2},\quad\beta_1={99\over2},
 \quad(a_0,a_1)=(45,4455),                      \tag{44}
\]

and residuals `(M_0,M_1)=(5,3)`. Again both errors and the mixed budget are
zero, and the weight is exactly four. This is not just a representation with
`j>0`: every cycle denominator `10^a-1` is odd, so its product with either
coefficient in (44) has circle distance `1/2`. By (18), this exceeds both T24
tolerances. Hence the model has no T24 cycle approximation but has the exact
positive-preperiod approximation (44).

### 8.3 Large-denominator mixed failure

Take

\[
 U=9,\quad(j,s)=(0,6),\quad Q=999999,
 \quad\beta_0={11\over10Q},\quad
 \beta_1={99\over10Q},\quad(a_0,a_1)=(1,10).    \tag{45}
\]

With residuals `(M_0,M_1)=(8,7)`, the pair is legal. Its exact errors are

\[
                         e_0=e_1={1\over10}.     \tag{46}
\]

They are individually T24-good by (18), but

\[
 Qe_1+UQe_0=Q=999999,                           \tag{47}
\]

so the mixed budget fails. Nevertheless

\[
 W(Q)=\left({5+\sqrt5\over4}\right)^2
      ={15+5\sqrt5\over8}\approx3.272542486,    \tag{48}
\]

which is about `81.8%` of the maximum four. Here (40) holds and `(DBL)` gives
the valid cap `W(Q)<=4`. Replacing `s=6` by `s=m` leaves (46) and (48)
unchanged while the failed budget `Q=10^m-1` diverges. This refutes any
attempt to deduce the mixed budget from two fixed positive T24 error margins
and large pointwise Fejer weight alone. It is not a fixed-pi refutation.

## 9. The one surviving estimate

The obstruction can be narrowed to a one-node, one-stratum exponential-sum
estimate that is strictly more specific than either T32's JWMO or T34's mixed
sum.

For each `1<=ell<L`, define

\[
 \delta_{k,\ell}=
 \min\left\{E_0,{E_1\over U},{1\over2U10^\ell}\right\},
 \qquad R_{k,\ell}=\left\lceil\delta_{k,\ell}^{-1}\right\rceil. \tag{49}
\]

All quantities are positive. The sole open estimate is:

**Fixed-Stratum Fejer Spike (FSFS).** For at least one
`ell` with `1<=ell<L`,

\[
\boxed{
 \sum_{j=0}^{\ell-1}
 F_{R_{k,\ell}-1}
   \bigl(\beta_0(10^\ell-10^j)\bigr)
 > {\ell\over4R_{k,\ell}\delta_{k,\ell}^2}.}
                                                        \tag{FSFS}
\]

This is an unproved fixed-pi estimate because `beta_0=C pi` in (2).

### Why `(FSFS)` suffices

If every `d_0(Q_{ell,j})>=delta_{k,ell}`, (21), with
`H=R_{k,ell}-1`, bounds every summand by

\[
 {1\over4R_{k,\ell}\delta_{k,\ell}^2},          \tag{50}
\]

contradicting `(FSFS)`. Hence some `j` and nearest integer `a_0` satisfy

\[
 |Q_{\ell,j}\beta_0-a_0|<\delta_{k,\ell}.       \tag{51}
\]

Set `s=ell-j` and `a_1=Ua_0`. Equations (4), (12), and (49) give

\[
\begin{aligned}
 e_0&<E_0,\\
 e_1&=Ue_0<E_1,\\
 Q_{\ell,j}(e_1+Ue_0)
   &=2UQ_{\ell,j}e_0
     <2U10^\ell\delta_{k,\ell}\le1.
\end{aligned}                                      \tag{52}
\]

The last inequality is strict because (51) and `Q_{ell,j}<10^ell` are
strict. Also `s>=1` and `j+s=ell<L`, so all domain clauses hold. Thus this
single stratum estimate constructs a T34 `JointGoodPair` with the stronger
integer relation `a_1=Ua_0`.

At bridge cutoffs `H_0=H_1=0`, every common-pair weight is one. The pair from
(52) makes `commonGoodMass>0`; (38) and T34's exact double-frequency identity
then give its `MixedSumLowerBound`, and T34 produces an adjacent compatible
pair. T28's separate exponent-eight closing bounds are still required before
any A1 conclusion.

### Why this is strictly narrower than the old premises

`(FSFS)` contains neither `JointGoodPair`, `boundaryLoss`, nor
`mixedDoubleFrequencySum`. It concerns one prescribed denominator stratum and
only the one-node fixed-pi phases

\[
              C\pi(10^\ell-10^j).               \tag{53}
\]

Expanding its Fejer kernel turns it into finitely many explicit lacunary sums
`sum_j exp(-2 pi i u C pi 10^j)` with `|u|<R_{k,ell}`. It is stronger and more
specialized than JWMO because it forces the explicit scale
`e_0<1/(2U10^ell)` and the transported integer `a_1=Ua_0`. It is not T34's
mixed-sum hypothesis rewritten: it has no two-node product and no comparison
with an unknown boundary loss.

## 10. Verdict

`(DBL)` and the frequency-injectivity statement are established by the
displayed elementary arguments, and the exact models pass. The optimized
mixed envelope can equal the full pointwise cap, so these deterministic facts
do not establish compatibility from T24's nodewise alternatives. No genuine
T26 fixed-pi chain counterexample is supplied, so `REFUTED` would be false.
No exponent-eight closing bounds are proved, so no compatibility-to-A1
conclusion is asserted.

**OPEN WITH ONE NAMED ESTIMATE: Fixed-Stratum Fejer Spike `(FSFS)`.**

## Replay

From a directory containing only the delivered files, run

```sh
sh reproduce.sh
```

The script verifies the vendored statement hash, finite denominator strata,
frequency injectivity and its sharp boundary collision, all exact rational
model errors and budgets, the algebraic Fejer values, and sampled agreement
between (27) and (28). These computations test the formulas but are not proof
of `(DBL)`, `(FSFS)`, or canonical A1.
