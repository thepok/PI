# T19: A finite cycle-or-preperiod inverse dichotomy

Status: `proof sketch` (complete prose proof, not Lean-formalized).

Verdict for the candidate dichotomy in Theorem 1: **PROVED**.

## 0. Source, scope, and quantifiers

The immutable canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It defines the ordered, diagonal-inclusive quantity `Q_pi(n,N)` and records
the exact canonical quantifiers. The local statement records no external
source URL; its provenance is given in its line 5, and no URL is invented
here. The finite theorem below concerns an arbitrary real `beta`, so by itself
it is a sibling statement of type A13, not a statement about `Q_pi`.

Write

```text
e(x) := exp(2*pi*i*x),
||x|| := inf_{a in Z} |x-a|,
S_M(beta) := sum_{0 <= j < M} e(beta*10^j).
```

All ceilings and floors below are the usual real ceiling and floor. A
"denominator" means a positive denominator after reducing a rational number.

## 1. Exact candidate dichotomy

**Theorem 1 (finite cycle-or-preperiod dichotomy).** Let `M` be an integer
with `M>=2`, let `beta` be real, and let `0<delta<=1`. Define

```text
kappa := delta/(2-delta),
g0 := ceil(kappa*M),
epsilon := arccos(delta/2)/pi.                         (1)
```

Assume

```text
|S_M(beta)| >= delta*M                                (2)
```

and `g0>=2`. Put

```text
Sstar := floor((M-1)/(g0-1)).                         (3)
```

Then exactly one of the following two alternatives holds.

**C (cycle approximation).** There are integers `s,a` such that

```text
1 <= s <= Sstar,
|beta-a/(10^s-1)| <= epsilon/(10^s-1).                (4)
```

After reducing `a/(10^s-1)`, its denominator divides `10^s-1`.

**P (preperiod obstruction).** Alternative C is false, and there are integers
`j,s,a` such that

```text
1 <= j,
j+s <= M-1,
1 <= s <= Sstar,                                      (5)
|beta-a/(10^j*(10^s-1))|
    <= epsilon/(10^j*(10^s-1)).                       (6)
```

Thus P does not merely say "not C": it supplies an eventually periodic
approximation with preperiod `j`, while asserting explicitly that no rational
in C exists at the same error and period bounds. Its reduced denominator
divides `10^j*(10^s-1)`. The factor `10^j` is the precise obstruction left by
the proof; P does not claim that this factor survives rational reduction.

The alternatives are mutually exclusive because P includes the negation of
C. The proof below shows they are exhaustive.

### Proof of Theorem 1

Since the right side of (2) is positive, `S_M(beta)` is nonzero. Set

```text
u := S_M(beta)/|S_M(beta)|,
z_j := e(beta*10^j),
x_j := Re(conj(u)*z_j),
tau := delta/2.                                       (7)
```

Every `x_j<=1`, and rotation in the direction of the sum gives the exact
identity

```text
sum_{0 <= j < M} x_j = |S_M(beta)|.                   (8)
```

Let `G` be the set of indices `j` in `{0,...,M-1}` for which `x_j>=tau`, and
write `g=|G|`. For indices outside G, `x_j<tau`, hence also `x_j<=tau`.
Equations (2), (7), and (8) give

```text
delta*M <= sum_j x_j
            <= g+(M-g)*tau,
g >= ((delta-tau)/(1-tau))*M
  = (delta/(2-delta))*M = kappa*M.                    (9)
```

Since `g` is an integer, (9) implies

```text
g >= ceil(kappa*M) = g0 >= 2.                         (10)
```

For each `j` in G choose the unique `y_j` in `[-1/2,1/2)` satisfying

```text
conj(u)*z_j=e(y_j).
```

Because `cos(2*pi*y_j)=x_j>=tau>0`,

```text
|y_j| <= alpha := arccos(tau)/(2*pi).                 (11)
```

Consequently, for any `j,k` in G,

```text
||(10^k-10^j)*beta||
 = ||y_k-y_j||
 <= |y_k-y_j|
 <= 2*alpha = epsilon.                                (12)
```

List G increasingly as `b_0<...<b_(g-1)`. Its consecutive gaps are positive
integers and

```text
sum_{v=0}^{g-2} (b_(v+1)-b_v)
 = b_(g-1)-b_0 <= M-1.                                (13)
```

At least one consecutive pair `j=b_v`, `j+s=b_(v+1)` therefore satisfies

```text
1 <= s <= floor((M-1)/(g-1))
         <= floor((M-1)/(g0-1)) = Sstar,
j+s <= M-1.                                           (14)
```

Apply (12) to this pair. The infimum defining circle distance is attained by
some `a in Z`, so

```text
|10^j*(10^s-1)*beta-a| <= epsilon.                    (15)
```

Division by the positive integer `10^j*(10^s-1)` gives

```text
|beta-a/(10^j*(10^s-1))|
 <= epsilon/(10^j*(10^s-1)).                          (16)
```

Now use excluded middle on C. If C holds, that is the first alternative. If C
does not hold, the extracted `j` cannot be zero: with `j=0`, (14) and (16)
would be (4), contradicting not-C. Hence `j>=1`, and (14), (16), and not-C are
exactly P. This proves exhaustiveness and completes the proof.

## 2. What is and is not synchronized

The proof synchronizes two concentrated phases, not necessarily the initial
phase. The distinction is exact:

```text
j=0  gives  ||(10^s-1)*beta|| <= epsilon;              (17)
j>0  gives  ||10^j*(10^s-1)*beta|| <= epsilon.         (18)
```

Dividing (18) introduces the decimal preperiod factor `10^j`. There is no
valid cancellation of this factor modulo one. Alternative P records this
failure rather than hiding it. Also, from `0<delta<=1`,

```text
1/3 <= epsilon < 1/2,                                 (19)
```

because `0<delta/2<=1/2` and arccos is decreasing. Thus this elementary
inverse theorem has a coarse error even when its period bound is short.

## 3. Exact short-cycle tests

These are algebraic tests of Theorem 1, not numerical experiments.

### 3.1 The fixed cycle beta=1/9

Since `10^j=1 (mod 9)` for every `j>=0`, every summand equals `e(1/9)` and

```text
S_M(1/9)=M*e(1/9),  |S_M(1/9)|=M.                     (20)
```

Take any `M>=2` and `delta=1`. Then `g0=M`, `Sstar=1`, and C holds with
`s=1,a=1`, with zero error because `1/9=1/(10^1-1)`.

### 3.2 The period-two cycle beta=1/99

Here `10^2=1 (mod 99)` but `10` is not `1 (mod 99)`, so the exact least period
is two. For `M=2m`,

```text
S_(2m)(1/99)=m*(e(1/99)+e(10/99)),
|S_(2m)(1/99)|=2m*cos(pi/11).                          (21)
```

The second identity follows by taking the midpoint and half-difference of the
two angles; `0<pi/11<pi/2`, so the cosine is positive. The exact cycle rational
is `1/(10^2-1)`. Both period-two examples use the elementary estimate

```text
cos(2*pi/11) > 1-(2*pi/11)^2/2
             > 1-32/121=89/121>2/3,                  (21a)
```

where `cos x>1-x^2/2` for nonzero `x` and `pi<4`. Hence also
`cos(pi/11)>2/3`. If `2/3<delta<1`, then
`1/2<delta/(2-delta)<1`. Therefore, for the smallest test `M=2` and
`delta=cos(pi/11)`, Theorem 1 has `g0=2` and `Sstar=1`. Its coarser bounded
conclusion C holds with `s=1,a=0`, since (19) gives

```text
|1/99-0/9|=1/99 < 1/27 <= epsilon/9.                  (22)
```

Thus the theorem is valid but need not recover the least exact period.

### 3.3 The period-two cycle beta=1/11

Here `10=-1 (mod 11)`, so the exact least period is two. For `M=2m`,

```text
S_(2m)(1/11)=m*(e(1/11)+e(10/11)),
|S_(2m)(1/11)|=2m*cos(2*pi/11).                        (23)
```

For `M=2` and `delta=cos(2*pi/11)`, again `g0=2` and `Sstar=1`. C holds with
`s=1,a=1`, because (19) and `2/99<1/27` give

```text
|1/11-1/9|=2/99 < 1/27 <= epsilon/9.                  (24)
```

Again, the exact period is two while the theorem reports a coarse period-one
approximation.

### 3.4 Exact preperiod beta=1/20

The orbit is

```text
1/20, 1/2, 0, 0, ... (mod 1).
```

For `M=20`,

```text
S_20(1/20)=17+e(1/20),
|S_20(1/20)| >= Re(S_20)=17+cos(pi/10)>16=(4/5)*20.   (25)
```

Take `delta=4/5`. Then `kappa=2/3`, `g0=ceil(40/3)=14`, and `Sstar=1`.
Moreover

```text
epsilon=arccos(2/5)/pi < 9/20.                        (26)
```

For an exact proof of (26), `sin(pi/20)<pi/20<1/5<2/5`, using
`sin x<x` for `x>0` and `pi<4`. Hence
`cos(9*pi/20)=sin(pi/20)<2/5`; strict decrease of cosine on `[0,pi]`
gives `arccos(2/5)<9*pi/20`.

For every integer `a`,

```text
|1/20-a/9|=|9-20a|/180 >= 9/180=1/20.                (27)
```

Indeed, if `a<=0` then `9-20a>=9`, while if `a>=1` then
`20a-9>=11`. Equations (26)--(27) show that C is false, since
`epsilon/9<1/20`. But

```text
10^2*(10^1-1)*(1/20)=45,                              (28)
```

so P holds with `j=2,s=1,a=45` and zero error. This is an exact counterexample
to the stronger claim obtained by deleting P and insisting that every large
sum yield C. It is not a counterexample to Theorem 1.

The rational orbits, period congruences, the `g0,Sstar` values for this
preperiod example, the rational comparisons in (22), (24), and the integer
identity (28) are replayed by `verify_examples.py`.

## 4. Literal specialization to T13

The accepted machine-checked input is
`knowledge_library/t13/IteratedLagResonance.lean`, SHA-256

```text
14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13.
```

The relevant theorem is
`DecimalFactorComplexity.IteratedLagResonance.literal_not_A1_implies_arbitrary_depth_resonance`
at lines 629--702. The following is only a prose specialization of that
theorem and Theorem 1.

Assume T13's literal premise

```text
not (forall A : N, 1 <= A -> exists n0 : N, 1 <= n0 and
     forall n : N, n0 <= n -> exists N : N, 1 <= N and
     A*n*Q_pi(n,N) <= N^2).                            (29)
```

Then T13 supplies `A>=1` such that, for every `n0>=1`, there is an
`n>=n0`, `n>=1`, such that the following holds. For every depth `d>=0`, put

```text
D0 := 131072*A^2*n^2,
D := densityDenominator(D0,d).                        (30)
```

For every requested residual length `K>=2*D`, T13 supplies `N,r,h` and an
injective family `(s_t)_(t in Fin d)` satisfying, literally,

```text
N = 16*A*n*iterationLengthThresholdAux(D0,1,K,1,d),
1 <= r <= N-1,
1 <= h <= 256*A*n,
1 <= s_t,  s_t != r,
L := N-r-sum_t s_t >= K,                              (31)
|sum_{0 <= j < L} e(beta_T*10^j)| > L/D,              (32)
beta_T := h*(10^r-1)*prod_t(10^(s_t)-1)*pi.           (33)
```

The family `(s_t)` is pairwise distinct by T13's injectivity. No witness in
(31)--(33) is fixed before its T13 quantifier permits it to be fixed.

Apply Theorem 1 with

```text
M_T19=L,  delta_T19=1/D,  beta=beta_T.                 (34)
```

The strict inequality (32) implies (2). Here `D>=1` is explicit: `A,n>=1`
give `D0>=131072`, while T13 defines `densityDenominator(D0,0)=D0` and
recursively replaces every value `E` by `8*E^2`; induction on `d` gives
`D>=1`. Hence `0<delta_T19<=1`, and

```text
kappa_T19=1/(2*D-1),
g0_T19=ceil(L/(2*D-1))>=2                              (35)
```

by `L>=K>=2*D>2*D-1`. Therefore Theorem 1 applies with

```text
epsilon_D := arccos(1/(2*D))/pi,
S_D(L) := floor((L-1)/(ceil(L/(2*D-1))-1)).            (36)
```

It gives exactly one of:

```text
exists 1<=s<=S_D(L), exists a in Z,
  |beta_T-a/(10^s-1)| <= epsilon_D/(10^s-1);           (37)
```

or the negation of (37) together with

```text
exists j>=1, exists 1<=s<=S_D(L), j+s<=L-1,
exists a in Z,
  |beta_T-a/(10^j*(10^s-1))|
    <= epsilon_D/(10^j*(10^s-1)).                     (38)
```

The period bound also has the simpler explicit estimate

```text
S_D(L) <= 4*D-3.                                      (39)
```

To verify (39), set `q=2*D-1` and `m=ceil(L/q)>=2`. Then
`(m-1)q<L<=mq`, and hence

```text
(L-1)/(m-1) <= (m*q-1)/(m-1)
             = q+(q-1)/(m-1) <= 2*q-1=4*D-3.          (40)
```

Taking floors proves (39).

The dependency order of this specialization is

```text
exists A, forall n0, exists n, forall d,
forall K>=2*densityDenominator(131072*A^2*n^2,d),
exists T13 witnesses, then exactly one of (37) and (38). (41)
```

In particular, `D`, `K`, `N`, `r`, `h`, the shifts, `L`, `beta_T`, and the
inverse witnesses may all depend exactly as (30)--(41) state. This section
does not infer the premise (29), does not add cross-`K` coherence, and does not
deduce the canonical conclusion.

## 5. Gaps and final verdict

Theorem 1 is proved, but it exposes rather than closes the needed bridge:

1. Alternative P cannot be deleted while retaining Theorem 1's prescribed
   `Sstar` and `epsilon`; the exact terminating example `beta=1/20`
   demonstrates this. The example makes no claim about all possible inverse
   theorems with different bounds.
2. The permitted error coefficient is bounded below as in (19), so this
   theorem guarantees only coarse phase synchronization; the realized error
   can of course be smaller or zero.
3. The T13 specialization controls the period by (39) but leaves a preperiod
   `j` as large as `L-2` in (38).
4. T13 gives no coherence among the witnesses as `K` varies, and none is
   assumed here.

**PROVED:** the exact finite cycle-or-preperiod dichotomy in Theorem 1,
including its T13 specialization (29)--(41). The stronger pure-cycle-only
candidate is **REFUTED** by the exact example in Section 3.4. No statement
beyond these two finite conclusions is asserted.
