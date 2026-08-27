# T21: optimized concentration versus the irrationality measure of pi

Status: `proof sketch` with kernel-checked T13 input and a source-pinned
irrationality theorem.

Verdict: **INSUFFICIENT**. The generalized concentration lemma below is a
rigorous prose proof, not a Lean theorem. Optimizing its threshold gives an
exact density-period-preperiod-error frontier, but after the literal T13
specialization the guaranteed error in the resulting rational approximation
to `pi` is still a positive constant divided by its denominator. This has
approximation exponent 1 and does not conflict with the published bound
`mu(pi) <= 7.103205334137...`. No part of this note asserts canonical A1.

## 0. Immutable statement, normalization, and scope

The canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, it counts ordered pairs, includes diagonal pairs, uses
strict distance on `R/Z`, and asks

```text
forall A>=1, exists n0>=1, forall n>=n0, exists N>=1,
  A*n*Q_pi(n,N) <= N^2.                                (A1)
```

The quantified integer `N` may depend on `A,n`; it is neither prescribed nor
universal. The statement's A2--A16 readings (infinitely many `n`, one fixed
`A`, prescribed `N`, omitted diagonals, unordered pairs, other constants or
bases, and finite or almost-everywhere analogues) are sibling statements and
are not substituted here. The local statement records no original external
source URL; its provenance is recorded in its line 5.

The accepted formal input is
`knowledge_library/t13/IteratedLagResonance.lean`, SHA-256

```text
14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13.
```

Its theorem
`DecimalFactorComplexity.IteratedLagResonance.literal_not_A1_implies_arbitrary_depth_resonance`
is at lines 629--702. T13 is `machine-checked`; the generalized inverse lemma
and comparisons in this note are only a `proof sketch` until formalized.

Write

```text
e(x) := exp(2*pi*i*x),
||x|| := inf_(a in Z) |x-a|,
S_M(beta) := sum_(0<=j<M) e(beta*10^j).                 (0.1)
```

All rational denominators below are positive but need not be reduced. This is
enough for the pinned irrationality theorem, which quantifies over every
integer numerator and every sufficiently large positive integer denominator.

## 1. Generalized concentration lemma for every 0<tau<delta

**Theorem 1 (weak finite concentration dichotomy).** Let `M>=2` be an integer,
let `beta` be real, and suppose

```text
0 < tau < delta <= 1,
|S_M(beta)| >= delta*M.                                (1.1)
```

Define

```text
rho(delta,tau) := (delta-tau)/(1-tau),
g0 := ceil(rho(delta,tau)*M),
epsilon(tau) := arccos(tau)/pi.                        (1.2)
```

Then `0<rho<=1`. If `g0>=2`, then for each integer
`ell` with `1<=ell<=g0-1`, define

```text
P_ell := floor((M-g0+ell)/ell).                        (1.3)
```

Exactly one of the following alternatives holds:

```text
C_ell: exists integers s,a,
       1 <= s <= P_ell,
       |beta-a/(10^s-1)| <= epsilon(tau)/(10^s-1);     (1.4)

P_ell: C_ell is false, and there exist integers j,s,a,
       1 <= j <= M-g0+ell-1,
       1 <= s <= P_ell,
       j+s <= M-g0+ell,
       |beta-a/(10^j*(10^s-1))|
         <= epsilon(tau)/(10^j*(10^s-1)).              (1.5)
```

The label `P_ell` in (1.5) is an alternative, not the numerical period bound
in (1.3). Its factor `10^j` is the decimal preperiod and is not canceled.

### Numbered proof

1. The sum is nonzero by (1.1). Rotate in its direction:

   ```text
   u := S_M(beta)/|S_M(beta)|,
   z_j := e(beta*10^j),
   x_j := Re(conj(u)*z_j).                              (1.6)
   ```

   Each `x_j<=1`, and the rotation gives the exact identity

   ```text
   sum_(0<=j<M) x_j = |S_M(beta)|.                     (1.7)
   ```

2. Let `G={j in {0,...,M-1}: x_j>=tau}` and `g=|G|`. Outside
   `G`, `x_j<tau`, hence certainly `x_j<=tau`. Therefore

   ```text
   delta*M <= sum_j x_j <= g+(M-g)*tau,
   g >= ((delta-tau)/(1-tau))*M = rho*M,
   g >= ceil(rho*M) = g0.                              (1.8)
   ```

   This proves the generalized good-index density. The hypothesis `g0>=2`
   is exactly what guarantees two good indices; it is equivalent to
   `rho*M>1`.

3. For each `j in G`, choose the unique `y_j in [-1/2,1/2)` such that
   `conj(u)*z_j=e(y_j)`. Since

   ```text
   cos(2*pi*y_j)=x_j>=tau>0,
   |y_j| <= arccos(tau)/(2*pi),                         (1.9)
   ```

   any `j,k in G` satisfy

   ```text
   ||(10^k-10^j)*beta||
     = ||y_k-y_j||
     <= |y_k-y_j|
     <= epsilon(tau).                                  (1.10)
   ```

4. List `G` as `b_0<...<b_(g-1)`. Fix `ell` as in the theorem. There must
   remain at least `g-1-ell` selected indices after `b_ell`, so

   ```text
   b_ell <= M-g+ell <= M-g0+ell.                       (1.11)
   ```

   The first `ell` positive consecutive gaps have sum
   `b_ell-b_0<=b_ell`. One of them, say from `j=b_v` to
   `j+s=b_(v+1)`, consequently obeys

   ```text
   1 <= s <= floor(b_ell/ell) <= P_ell,
   j <= b_ell-1 <= M-g0+ell-1,
   j+s <= b_ell <= M-g0+ell.                           (1.12)
   ```

5. Apply (1.10) to this pair. The circle-distance infimum is attained by
   some `a in Z`, so

   ```text
   |10^j*(10^s-1)*beta-a| <= epsilon(tau).             (1.13)
   ```

   Division by the positive integer `10^j*(10^s-1)` gives the approximation
   in (1.5), except that `j` may initially be zero.

6. Use excluded middle on `C_ell`. If it holds, this is (1.4). If it is
   false, then the pair extracted in Step 4 cannot have `j=0`, because
   (1.13) with `j=0` and `s<=P_ell` would establish `C_ell`. Thus `j>=1`
   and all of (1.5) holds. The alternatives are disjoint because (1.5)
   explicitly includes the negation of (1.4), and they are exhaustive by
   this construction. This proves Theorem 1.

## 2. Exact optimization and strict refinement

The parameter `ell` exposes the period-preperiod Pareto frontier rather than
hiding it behind one worst-case bound.

1. At `ell=1`, Theorem 1 gives

   ```text
   j <= M-g0,
   s <= M-g0+1,
   j+s <= M-g0+1.                                     (2.1)
   ```

   This gives the strongest start-position bound but a potentially long
   period.

2. At `ell=g0-1`, it gives

   ```text
   j <= M-2,
   s <= S_tau(M) := floor((M-1)/(g0-1)),
   j+s <= M-1.                                        (2.2)
   ```

   This is T19's short-period endpoint. Over all admissible integer `M`, its
   sharp uniform period bound is

   ```text
   S_tau(M) <= floor(2/rho)-1.                         (2.3)
   ```

   To prove (2.3), put `m=ceil(rho*M)>=2`. From `rho*M<=m`,

   ```text
   (M-1)/(m-1)
     <= (m/rho-1)/(m-1)
      = 1/rho+(1/rho-1)/(m-1)
     <= 2/rho-1.                                      (2.4)
   ```

   Taking floors gives (2.3). It is sharp: for
   `M=floor(2/rho)`, one has `ceil(rho*M)=2` and equality in (2.3).

3. T13 supplies a strict sum inequality. A useful strict version of Theorem 1
   uses `G={j:x_j>tau}`. If `|S_M(beta)|>delta*M`, then

   ```text
   g > rho*M,
   g >= g_strict := floor(rho*M)+1.                    (2.5)
   ```

   If `floor(rho*M)>=1`, all formulas (1.3)--(1.5) hold with `g0` replaced
   by `g_strict` and every approximation error made strict. In particular,

   ```text
   S_strict(M) := floor((M-1)/floor(rho*M)).            (2.6)
   ```

   For `0<rho<1`, its sharp uniform bound is

   ```text
   S_strict(M) <= ceil(2/rho)-2.                       (2.7)
   ```

   Indeed, with `m=floor(rho*M)>=1`, the strict inequality
   `M<(m+1)/rho` gives

   ```text
   (M-1)/m < 1/rho+(1/rho-1)/m <= 2/rho-1.
   ```

   Hence its floor is at most `ceil(2/rho)-2`. Equality is obtained at
   `M=ceil(2/rho)-1`. Formula (2.5), not a ceiling formula, must be used when
   `rho*M` is an integer.

4. For fixed `0<delta<1`, direct differentiation gives

   ```text
   d rho/d tau = (delta-1)/(1-tau)^2 < 0,
   d epsilon/d tau = -1/(pi*sqrt(1-tau^2)) < 0.        (2.8)
   ```

   Thus increasing `tau` improves the approximation error but worsens the
   guaranteed density, period, and preperiod bounds. The exact endpoints are

   ```text
   tau -> 0+:     rho -> delta, epsilon -> 1/2;
   tau -> delta-: rho -> 0,     epsilon -> arccos(delta)/pi. (2.9)
   ```

   The second error value is an infimum, not an attained value. Equivalently,
   a prescribed `0<rho<delta` determines the entire frontier by

   ```text
   tau = (delta-rho)/(1-rho),
   epsilon(rho) = arccos((delta-rho)/(1-rho))/pi.       (2.10)
   ```

   When `delta=1`, `rho=1` for every `tau<1`; equality
   `|S_M|=M` actually forces exact phase alignment, although Theorem 1 only
   needs its stated coarse conclusion.

## 3. Exact cycle and preperiod examples

These are algebraic checks, not evidence for A1.

1. **Fixed cycle `beta=1/9`.** Since `10^j=1 (mod 9)`, every summand is
   `e(1/9)` and `|S_M(1/9)|=M`. With `delta=1` and any `0<tau<1`,
   `rho=1`, `g0=M`, and the short-period bound is one. The cycle branch is
   exact with `(s,a)=(1,1)`.

2. **Least period two, `beta=1/99`.** For `M=2m`,

   ```text
   S_(2m)(1/99)=m*(e(1/99)+e(10/99)),
   |S_(2m)(1/99)|=2m*cos(pi/11).                       (3.1)
   ```

   The least exact period is two. For `M=2`,
   `delta=cos(pi/11)`, and `tau=delta/2`, one has `g0=2` and the theorem's
   period bound is one. Its coarser cycle conclusion holds with `a=0`, since
   `epsilon>=1/3` and `1/99<1/27<=epsilon/9`.

3. **Least period two, `beta=1/11`.** Here `10=-1 (mod 11)` and

   ```text
   |S_(2m)(1/11)|=2m*cos(2*pi/11).                     (3.2)
   ```

   For `M=2`, `delta=cos(2*pi/11)`, and `tau=delta/2`, again `g0=2` and
   the reported bound is one. The coarse cycle is `(s,a)=(1,1)`, because
   `|1/11-1/9|=2/99<1/27<=epsilon/9`.

4. **Exact preperiod `beta=1/20`.** Its orbit is

   ```text
   1/20, 1/2, 0, 0, ... (mod 1).                       (3.3)
   ```

   For `M=20`,

   ```text
   S_20(1/20)=17+e(1/20),
   |S_20(1/20)| >= 17+cos(pi/10) > 16.                 (3.4)
   ```

   Set `delta=4/5` and `tau=2/5`. Then `rho=2/3`; the weak count has
   `g0=ceil(40/3)=14`, while the strict count is also
   `floor(40/3)+1=14`. At the short-period endpoint the exact bound is
   `floor(19/13)=1`. Moreover

   ```text
   epsilon=arccos(2/5)/pi < 9/20,                      (3.5)
   |1/20-a/9|=|9-20a|/180 >= 1/20                     (3.6)
   ```

   for every integer `a`. For (3.5),
   `cos(9*pi/20)=sin(pi/20)<pi/20<1/5<2/5`; for (3.6), split into
   `a<=0` and `a>=1`. Thus the cycle branch is false. The preperiod branch
   has the exact zero-error witness

   ```text
   (j,s,a)=(2,1,45),
   10^2*(10^1-1)*(1/20)=45.                            (3.7)
   ```

   The rational `45/900` happens to reduce to `1/20`. This accidental
   cancellation in one example does not justify canceling `10^j` in the
   general theorem. It instead proves that a pure-cycle-only replacement of
   Theorem 1 with the same period and error bounds is false.

The exact rational orbit and integer calculations are replayed by
`verify_tradeoffs.py`.

## 4. Literal T13 specialization with every loss retained

Assume only the literal negation of canonical A1:

```text
not (forall A:N, 1<=A -> exists n0:N, 1<=n0 and
     forall n:N, n0<=n -> exists N:N, 1<=N and
     A*n*Q_pi(n,N)<=N^2).                              (4.1)
```

The kernel-checked T13 theorem gives the dependency order

```text
exists A>=1, forall n0>=1, exists n>=n0 with n>=1,
forall d>=0, forall K>=1, exists N,r,h,(s_t)_(t in Fin d). (4.2)
```

In particular, `A,n` are fixed before `d,K`. Every later witness may change
with `d,K`, and no cross-`K` coherence is supplied.

Fix such `A,n,d`. Define

```text
D0 := 131072*A^2*n^2 = 2^17*(A*n)^2,
D_i := densityDenominator(D0,i),
D := D_d,
H := 256*A*n.                                         (4.3)
```

T13's recursion and its closed form are

```text
D_(i+1)=8*D_i^2,
D_i=8^(2^i-1)*D0^(2^i)
   =2^(20*2^i-3)*(A*n)^(2^(i+1)).                     (4.4)
```

For every requested `K>=1`, T13 supplies witnesses with

```text
T_d(K) := iterationLengthThresholdAux(D0,1,K,1,d),
N = 16*A*n*T_d(K),
1 <= r <= N-1,
1 <= h <= H,
s_t>=1, the s_t pairwise distinct, and s_t != r,
L := N-r-sum_t s_t >= K,                              (4.5)
|sum_(0<=j<L) e(beta_T*10^j)| > L/D,                  (4.6)
beta_T := a0*pi,
a0 := h*(10^r-1)*prod_t(10^(s_t)-1).                  (4.7)
```

The circle coordinate is `a0*pi`, not `a0*pi^2`; the second `pi` visible
after expanding `e(x)` belongs to the definition of the exponential.

### Full depth and ambient-length loss

At recursion stage `i`, the second branch of `oneStepLengthThreshold` is
`16*(1+(i+1)+R)*D_i^2`. Since `R>=K>=1`, it strictly dominates
`8*D_i^2`. Put

```text
lambda_i := 16*D_i^2,
C_d := prod_(0<=i<d) lambda_i
     = 2^(40*(2^d-1)-2*d)*(A*n)^(4*(2^d-1)),
E_d := sum_(0<=i<d) (i+2)*prod_(0<=v<=i) lambda_v.     (4.8)
```

Empty products and sums give `C_0=1,E_0=0`. Exact unrolling yields

```text
T_d(K)=C_d*K+E_d,
N=16*A*n*(C_d*K+E_d).                                 (4.9)
```

Since `K<=L` and `L>=1`, define

```text
Gamma_d := 16*A*n*(C_d+E_d),
N <= Gamma_d*L.                                       (4.10)
```

These are the full density and depth losses; increasing `d` worsens all of
`D_d,C_d,E_d,Gamma_d`.

### Full coefficient loss

Because `L>=1`, the natural-number subtraction in (4.5) does not truncate:

```text
r+sum_t s_t+L=N.                                      (4.11)
```

The `d+1` integers `r,s_0,...,s_(d-1)` are distinct and positive. Therefore

```text
prod_(u=1)^(d+1)(10^u-1) <= a0
  < H*10^(r+sum_t s_t)
  = H*10^(N-L).                                       (4.12)
```

The first bound will put denominators beyond an existential irrationality
threshold; the second is the coefficient growth that cannot be suppressed.

### Optimized concentration parameters

Apply the strict form of Theorem 1 to (4.6), with

```text
delta=1/D,
tau=theta/D for an arbitrary 0<theta<1.                (4.13)
```

Then

```text
rho_(theta,D)=(1-theta)/(D-theta),
epsilon_(theta,D)=arccos(theta/D)/pi.                  (4.14)
```

The strict theorem applies exactly when

```text
floor(rho_(theta,D)*L)>=1,
equivalently L >= ceil((D-theta)/(1-theta)).           (4.15)
```

It is therefore enough to request `K` at least the ceiling in (4.15). Put

```text
g := floor(rho_(theta,D)*L)+1.                         (4.16)
```

For every `1<=ell<=g-1`, the specialized cycle-or-preperiod dichotomy has

```text
period s <= floor((L-g+ell)/ell),
preperiod j <= L-g+ell-1,
j+s <= L-g+ell,                                       (4.17)
```

and strict phase error `epsilon_(theta,D)`. At the short-period endpoint,

```text
s <= floor((L-1)/floor(rho_(theta,D)*L))
  <= ceil(2*(D-theta)/(1-theta))-2.                    (4.18)
```

At `theta=1/2`, the weak version recovers T19 literally:

```text
rho=1/(2*D-1), K>=2*D,
s<=floor((L-1)/(ceil(L/(2*D-1))-1))<=4*D-3.            (4.19)
```

The strict refinement permits `K>=2*D-1` and replaces the ceiling denominator
by `floor(L/(2*D-1))`. Thus the note retains T19's specialization while also
recording the one-index gain available from T13's strict inequality.

Finally, because `D>=D0>=131072`, every allowed threshold satisfies

```text
arccos(1/D)/pi < epsilon_(theta,D) < 1/2.              (4.20)
```

Even at depth zero, the possible improvement below `1/2` is less than
`1/(pi*sqrt(D^2-1)) <= 1/(pi*sqrt(131072^2-1)) < 0.0000025`, using
`arcsin x <= x/sqrt(1-x^2)`. Letting `theta` approach one improves the error
only to the unattained infimum `arccos(1/D)/pi`, while the density tends to
zero and the period bound diverges.

## 5. Rational approximations to pi, including the preperiod

For either inverse branch let

```text
Q := 10^j*(10^s-1),                                   (5.1)
```

where `j=0` in the cycle branch and `j>=1` in the preperiod branch. If `a` is
the inverse-theorem numerator, (4.7) and Theorem 1 give

```text
|a0*pi-a/Q| < epsilon_(theta,D)/Q,
|a0*Q*pi-a| < epsilon_(theta,D).                       (5.2)
```

Set

```text
q := a0*Q >= 1, p := a.                               (5.3)
```

Then the actual approximation to `pi` is

```text
|pi-p/q| < epsilon_(theta,D)/q.                        (5.4)
```

It would be wrong to use `Q` alone as the denominator for `pi`, to confuse
`a` with `a0`, or to delete `10^j`. Rational reduction may remove factors in
individual cases, but T13/T19 guarantees no such reduction. The unreduced
integer `q` is valid for the cited theorem.

Combining (4.12) with the `ell`-dependent bound in (4.17) gives the complete
denominator tradeoff

```text
q < H*10^(N-L+j+s)
  <= H*10^(N-g+ell),                                  (5.5)
```

for the extracted preperiod pair. Thus:

```text
ell=1:   q < H*10^(N-floor(rho*L)),
ell=g-1: q < H*10^(N-1) <= H*10^(Gamma_d*L-1).         (5.6)
```

The first endpoint saves roughly `rho*L` decimal powers but allows a long
period; the second gives the optimized short period but retains a preperiod
as large as `L-2`. Both remain exponential in `L`.

If the cycle branch occurs at the short-period endpoint, `j=0` gives the
slightly better bound

```text
q < H*10^(N-L+s)
  <= H*10^((Gamma_d-1)*L+S_strict(L)).                 (5.7)
```

This still has exponential growth because T13 permits `N-L` to be linear in
`L`. Hence even eliminating the preperiod entirely would not eliminate the
coefficient loss.

## 6. Pinned irrationality theorem

The retained source is Doron Zeilberger and Wadim Zudilin, *The irrationality
measure of pi is at most 7.103205334137...*, Moscow Journal of Combinatorics
and Number Theory 9 (2020), no. 4, 407--419,
DOI `10.2140/moscow.2020.9.407`.

The accepted T18 source pins, exact URLs, hashes, and locators are reproduced
in `SOURCE_PINS.md`. On printed p. 407 (PDF page 2), retained extract lines
27--34 define irrationality measure by the eventual inequality

```text
for every eta>0, all integers p and all sufficiently large q:
|pi-p/q| > q^(-(mu(pi)+eta)).                          (6.1)
```

The `World record` paragraph on printed p. 418 (PDF page 13), extract lines
676--691, concludes

```text
mu(pi) <= Mpi
       := 7.10320533413700172750577342281... .          (6.2)
```

The source gives no numerical denominator threshold. A convenient exact
consequence, taking exponent 8, is only

```text
exists Q8>=1, forall integers q>=Q8, forall p in Z,
|pi-p/q| > q^(-8).                                    (6.3)
```

No explicit value of `Q8` is asserted.

## 7. Final exponent comparison

1. After `A,n` have been fixed by T13, choose `d` so large that

   ```text
   prod_(u=1)^(d+1)(10^u-1) >= Q8.                    (7.1)
   ```

   This is permitted by the quantifier order (4.2). Equations (4.12) and
   (5.3) then ensure `q>=Q8` for every later `K` and either inverse branch.

2. Combining (5.4) and (6.3) gives only

   ```text
   q^(-8) < |pi-p/q| < epsilon_(theta,D)/q,
   hence q^7 > 1/epsilon_(theta,D).                    (7.2)
   ```

   This is compatible for all sufficiently large `q`. By (4.20), the
   guaranteed numerator error is essentially `1/2`, so (5.4) has exponent
   1, not an exponent exceeding `Mpi`.

3. Optimizing `theta` cannot change that exponent. Improving the period
   changes the factors inside `q` but not the constant numerator error in
   (5.4). In the preperiod branch `10^j` can be exponentially large in `L`;
   in the cycle branch the T13 coefficient `a0` can be exponentially large
   through `10^(N-L)`. Equations (4.4), (4.8), (5.5), and (5.7) retain every
   density, depth, coefficient, and preperiod loss.

4. For comparison, T18's bare circular-pigeonhole argument, which does not
   use concentration, gave an error `1/(q*(L+1))`. If one also had a
   hypothetical polynomial denominator bound `q<=c*L^C`, that error would
   have exponent `1+1/C`. Comparison with (6.2) could close only for

   ```text
   1+1/C > Mpi,
   C < 1/(Mpi-1)
     = 0.163848329730397... .                          (7.3)
   ```

   T13 supplies only the exponential bounds (5.5)--(5.7), not any polynomial
   bound. More generally, if an improved inverse theorem supplied numerator
   error `O(L^(-B))` and `q=O(L^C)`, the exact closing comparison would be

   ```text
   1+B/C > Mpi,
   equivalently B > C*(Mpi-1).                         (7.4)
   ```

   Current concentration has `B=0`, so no finite `C` closes it.

## 8. Weakest explicit improvements that would close

The following are alternative sufficient thresholds. None is proved here.

1. **Approximation-error threshold.** Against the convenient exponent-8
   consequence (6.3), it would suffice for arbitrarily large generated `q`
   to strengthen (5.2) to

   ```text
   |q*pi-p| <= q^(-7).                                 (8.1)
   ```

   More sharply relative to (6.2), it suffices for some fixed `eta>0` to
   have `|q*pi-p|=O(q^(-(Mpi-1+eta)))`. The present bound is the constant
   `epsilon_(theta,D)>arccos(1/D)/pi`, so it is far weaker.

2. **Resonance-density threshold through this method.** To make
   `epsilon(tau)<=q^(-7)`, one needs

   ```text
   tau >= cos(pi*q^(-7)).                              (8.2)
   ```

   Since the concentration proof requires `tau<delta`, a necessary strict
   improvement of its normalized resonance density is

   ```text
   delta > cos(pi*q^(-7)).                             (8.3)
   ```

   Asymptotically this asks `1-delta` to be at most about
   `(pi^2/2)*q^(-14)`, whereas T13 gives the tiny fixed density
   `delta=1/D_d`. Using the sharper exponent `Mpi+eta` replaces `7` by
   `Mpi-1+eta`.

3. **Preperiod/coefficient threshold with a `1/L` error.** No bound on `j`
   alone, even `j=0`, can close the present constant-error estimate (5.4).
   If a strengthened inverse theorem also supplied T18's numerator error
   `1/(L+1)`, then the exact exponent-8 sufficient condition would be

   ```text
   q=a0*10^j*(10^s-1) <= (L+1)^(1/7).                 (8.4)
   ```

   Solved for the preperiod, this is

   ```text
   j <= (1/7)*log_10(L+1)-log_10(a0)-log_10(10^s-1).  (8.5)
   ```

   Thus a logarithmic preperiod bound is insufficient unless the T13
   coefficient and period factors are controlled simultaneously. Equations
   (4.12) and (5.5) show exactly where current bounds fail (8.4).

## 9. Verdict and non-claims

**INSUFFICIENT.** The generalized lemma proves the exact frontier

```text
rho=(delta-tau)/(1-tau),
epsilon=arccos(tau)/pi,
period/preperiod bounds (1.3)--(1.5),
```

including the strict T13 gain and all ceiling/floor edge cases. But T13 has
`delta=1/D_d`, so the optimized error remains essentially `1/2`. After
retaining the coefficient `a0`, depth loss, ambient-length loss, and the
preperiod `10^j`, it yields only `|pi-p/q|<epsilon/q`. This is compatible with
the pinned irrationality measure and gives no contradiction.

This note does not prove or assume the premise `not A1`, does not prove A1,
does not claim cross-window coherence, and does not promote the prose lemma to
`machine-checked`. The precise closing thresholds are (8.1), (8.3), and the
combined condition (8.4); they identify stronger arithmetic error or
near-unit resonance density, rather than suppression of the preperiod, as the
necessary next frontier.
