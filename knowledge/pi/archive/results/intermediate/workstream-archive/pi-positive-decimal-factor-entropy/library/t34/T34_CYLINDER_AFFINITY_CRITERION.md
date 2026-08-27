# T34: all-depth decimal-cylinder affinity

Status: `proof sketch` (a complete numbered prose proof, not a Lean artifact).

Verdict: **the proposed affinity criterion is valid under the exact hypotheses
in Theorem 1 below**.  For Borel probability measures on the full one-sided
decimal shift,

```text
inf_m A_m > 0  if and only if  the measures are not mutually singular.
```

The infimum must range over every depth.  Neither finitely many positive
affinities nor separate self-collision estimates imply the criterion.

This is a sibling measure-theoretic criterion, not a resolution of the
canonical pi question.  No measure required below is asserted to arise from
pi.

## 1. Provenance, target, and normalized ambiguities

The immutable canonical statement is vendored as
`pi-positive-decimal-factor-entropy.txt`.  Its original project location is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`; this locally
formulated question has no external source URL.  The byte-exact SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

That statement asks whether one fixed positive exponential lower bound holds
for the factor complexity of the decimal expansion of pi at every sufficiently
large length.  T34 does not weaken or answer it.

The following phrases are fixed before the proof.

1. `D={0,1,...,9}`, `X=D^N_0`, and `S:X->X` is the left shift.  The topology is
   the product topology of the discrete topology on `D`.
2. A measure means a countably additive Borel probability on `X`.
3. For `m>=0` and `w=(w_0,...,w_(m-1)) in D^m`,
   `[w]={x in X:x_j=w_j for 0<=j<m}`.  The sole depth-zero word has
   `[w]=X`.
4. `mu` and `nu` are mutually singular, written `mu perp nu`, when there is a
   Borel `E` with `mu(E)=1` and `nu(E)=0`.  "Non-mutual-singularity" is the
   negation of this statement; it is weaker than either direction of absolute
   continuity.
5. "Uniform order-1/2 Renyi control" means one finite constant works at every
   cylinder depth.  A constant depending on the tested depth or cutoff is not
   uniform.
6. The theorem is first proved intrinsically on `X`, where cylinders are
   clopen and have no boundary problem.  Decimal endpoint hypotheses enter
   only when circle measures or weak limits are encoded in `X`; Section 6
   states them exactly.

## 2. Cylinder generation and affinity

For `m>=0`, let

```text
P_m = {[w]:w in D^m},
F_m = sigma(P_m),
A_m(mu,nu) = sum_(w in D^m) sqrt(mu([w])*nu([w])).       (2.1)
```

### Step 1: exact partition and refinement facts

`P_m` is a finite disjoint partition of `X`.  Every `[w] in P_m` is the
disjoint union of its ten children `[wa]`, `a in D`.  Thus
`F_m subset F_(m+1)`.  Because the `F_m` are nested, their union

```text
A = union_(m>=0) F_m
```

is an algebra: two members occur together in some common `F_M`, where Boolean
operations stay.

Every cylinder belongs to `A`, and cylinders form a basis for the product
topology.  Therefore

```text
sigma(A) = Borel(X).                                    (2.2)
```

This is the generation hypothesis needed in the limit argument.  It would not
be enough to use a non-generating sequence of finite partitions.

### Step 2: monotonicity under refinement

Fix a parent word `w`.  Cauchy-Schwarz for the ten nonnegative pairs
`(mu([wa]),nu([wa]))` gives

```text
sum_(a in D) sqrt(mu([wa])*nu([wa]))
 <= sqrt((sum_a mu([wa]))*(sum_a nu([wa])))
 = sqrt(mu([w])*nu([w])).                               (2.3)
```

Summing (2.3) over all parent words proves

```text
1=A_0 >= A_1 >= A_2 >= ... >= 0.                        (2.4)
```

Hence `lim_(m->infinity) A_m` exists and equals `inf_m A_m`.  No invariance,
ergodicity, or entropy assumption is used.

## 3. Exact limit

The next steps identify the limit rather than merely use monotonicity.  The
only foundational measure-theory input to the intrinsic affinity theorem is
the Radon-Nikodym theorem for finite measures: if `alpha << lambda`, there is a
nonnegative measurable density `d alpha/d lambda`, unique `lambda`-almost
everywhere, whose integral over each measurable set is `alpha` of that set.
All convergence needed after that input is proved below from (2.2).  The
separate weak-limit transfer in Step 9 additionally invokes exactly the stated
continuity-set implication of the Portmanteau theorem.

Put

```text
lambda = mu+nu,
f = d mu/d lambda,
g = d nu/d lambda.                                     (3.1)
```

Then `lambda(X)=2`, `0<=f,g<=1`, and `f+g=1`
`lambda`-almost everywhere.

### Step 3: finite-cylinder averages

For `C in P_m`, define constant functions on `C` by

```text
f_m|C = mu(C)/lambda(C),
g_m|C = nu(C)/lambda(C)                                (3.2)
```

when `lambda(C)>0`, and set both values to zero when `lambda(C)=0`.  These are
the explicit `F_m`-conditional averages of `f` and `g`.  Direct substitution
on each atom gives

```text
integral_X sqrt(f_m*g_m) d lambda
 = sum_(C in P_m) lambda(C)
     sqrt(mu(C)/lambda(C) * nu(C)/lambda(C))
 = A_m(mu,nu),                                          (3.3)
```

with zero-mass atoms contributing zero.

### Step 4: cylinder-simple functions are dense in `L1(lambda)`

For completeness, let `L` be the class of Borel sets `E` such that for every
`epsilon>0` there is `U in A` with
`lambda(E symmetric_difference U)<epsilon`.  The class `L` contains `A`, is
closed under complements, and is closed under countable unions.  For the last
claim, if `E=union_i E_i`, continuity from below and `lambda(E)<infinity` give
an `N` for which
`lambda(E setminus union_(i<=N) E_i)` is arbitrarily small; approximate those
finitely many retained sets and use the union bound.  Thus `L` is a
sigma-algebra.  By (2.2), `L=Borel(X)`.

Approximating the level sets of a nonnegative measurable function first by a
bounded simple function and then by sets from `A` gives the nonnegative case;
applying this to positive and negative parts gives the signed case.  Changing
a completed-measurable representative on a null set, if necessary, gives:

```text
for every h in L1(lambda) and epsilon>0 there are M and an
F_M-measurable simple u with integral |h-u| d lambda < epsilon.  (3.4)
```

This paragraph is where finiteness of `lambda` and Borel generation by the
cylinder algebra are used.

### Step 5: `L1` convergence of the finite averages

For integrable `h`, define `P_m h` on `C in P_m` by

```text
(P_m h)|C = lambda(C)^(-1)*integral_C h d lambda
```

when `lambda(C)>0`, and by zero otherwise.  On each atom, the triangle
inequality gives the contraction

```text
integral |P_m h| d lambda <= integral |h| d lambda.      (3.5)
```

Given `epsilon>0`, use (3.4) to choose an `F_M`-measurable simple `u` with
`||f-u||_1<epsilon`.  For `m>=M`, `P_m u=u`, so (3.5) yields

```text
||f_m-f||_1
 <= ||P_m(f-u)||_1 + ||u-f||_1
 <= 2*epsilon.                                          (3.6)
```

Thus `f_m->f` in `L1(lambda)`; identically, `g_m->g` in `L1(lambda)`.

### Step 6: Hellinger limit

For numbers in `[0,1]`,

```text
|sqrt(a*b)-sqrt(c*d)|
 <= |sqrt(a)-sqrt(c)| + |sqrt(b)-sqrt(d)|
 <= sqrt(|a-c|)+sqrt(|b-d|).                            (3.7)
```

The first inequality follows by adding and subtracting `sqrt(c*b)`; the
second uses `|sqrt(a)-sqrt(c)|^2<=|a-c|`.  Cauchy-Schwarz and
`lambda(X)=2` then give

```text
integral sqrt(|f_m-f|) d lambda <= sqrt(2*||f_m-f||_1), (3.8)
```

and the analogous estimate for `g`.  Equations (3.3), (3.6)-(3.8) prove

```text
lim_m A_m(mu,nu)
 = H(mu,nu)
 := integral_X sqrt(f*g) d lambda.                      (3.9)
```

The value in (3.9) does not depend on the chosen versions of the densities.

## 4. The affinity criterion

### Theorem 1 (all-depth cylinder affinity)

Let `mu,nu` be Borel probability measures on the full one-sided decimal shift,
and let `A_m` be (2.1) for the complete length-`m` cylinder partitions.  Then

```text
inf_(m>=0) A_m(mu,nu)>0  iff  mu and nu are not mutually singular. (4.1)
```

### Step 7: zero Hellinger affinity is exactly singularity

If `mu perp nu`, choose Borel `E` with `mu(E)=1`, `nu(E)=0`.  From (3.1),
`f=0` almost everywhere on `E^c` and `g=0` almost everywhere on `E`, so
`f*g=0` almost everywhere and `H(mu,nu)=0`.

Conversely, if `H(mu,nu)=0`, nonnegativity implies `f*g=0`
`lambda`-almost everywhere.  Let `E={f>0}`.  Then

```text
mu(E^c)=integral_(E^c) f d lambda=0,
nu(E)=integral_E g d lambda=0,
```

because `g=0` almost everywhere on `{f>0}`.  Hence `mu perp nu`.

Combining this equivalence with (2.4) and (3.9) proves (4.1).  This also shows
why the conclusion is only non-mutual-singularity: positive `H` does not imply
`mu<<nu`, `nu<<mu`, or equality.

## 5. Uniform order-1/2 Renyi control

At depth `m`, regard `mu_m(w)=mu([w])` and `nu_m(w)=nu([w])` as probability
vectors on `D^m`.  Using natural logarithms and the standard extended-value
convention, define the order-`1/2` Renyi divergence by

```text
D_(1/2)(mu_m || nu_m)
 := -2*log(sum_w sqrt(mu_m(w)*nu_m(w)))
 = -2*log A_m(mu,nu),                                  (5.1)
```

where `-log 0=+infinity`.  At order `1/2` this divergence is symmetric.

### Step 8: exact uniform translation

For a real `C<infinity`, (5.1) gives, with no hidden constants,

```text
for every m, D_(1/2)(mu_m||nu_m)<=C
 iff for every m, A_m(mu,nu)>=exp(-C/2).                (5.2)
```

Theorem 1 therefore gives

```text
sup_m D_(1/2)(mu_m||nu_m)<infinity
 iff mu and nu are not mutually singular.              (5.3)
```

If logarithms to base 2 or 10 are used, `exp(-C/2)` in (5.2) is replaced by
`2^(-C/2)` or `10^(-C/2)`.  Formula (5.3) concerns cross-divergence.  It is not
a statement about the one-measure Renyi entropy or collision sum
`sum_w mu_m(w)^2`.

## 6. Decimal coding, boundaries, and weak limits

Let `T=R/Z`, represented by `[0,1)`, and define

```text
beta(x) = sum_(j>=0) x_j*10^(-(j+1)) mod 1,
T_b(t) = b*t mod 1.                                    (6.1)
```

Then `beta` is continuous and

```text
beta o S = T_10 o beta.                                (6.2)
```

For `w in D^m`, let `k(w)=sum_(j=0)^(m-1)w_j*10^(m-1-j)` and set

```text
I(w)=[k(w)/10^m,(k(w)+1)/10^m) subset [0,1).           (6.3)
```

The half-open sets in (6.3) form an actual partition even for measures with
decimal atoms.  Define the canonical Borel section `s:T->X` by the unique
digits satisfying `t in I(s(t)|m)` for every `m`.  This chooses terminating
zeros rather than trailing nines.  Exactly,

```text
beta o s = identity_T,
s^(-1)([w])=I(w).                                      (6.4)
```

The decimal boundary set is the countable set

```text
B = {k/10^m mod 1 : m>=0, 0<=k<=10^m}.                 (6.5)
```

Off `B`, `beta` has a unique decimal name.  On `B`, the terminating-zero and
trailing-nine names account for the ambiguity.  Equations (6.3)-(6.4) make
all cylinder masses exact without a boundary-null assumption.  A null
assumption is needed only to change naming conventions almost surely or to
deduce cylinder-mass convergence from weak convergence.

### Step 9: a sequence-independent sufficient weak-limit hypothesis

Suppose circle probabilities `rho_n` converge weakly to `rho`.  The
Portmanteau continuity-set implication gives, for a fixed word `w`,

```text
rho_n(I(w))->rho(I(w)) provided rho(partial I(w))=0.    (6.6)
```

One sequence-independent sufficient all-depth condition is `rho(B)=0`.  If simultaneously
`tau_n=(T_16)_*rho_n` and `tau=(T_16)_*rho`, then `tau_n->tau` weakly because
`T_16` is continuous.  Cylinder convergence for both lifted limits at every
depth is ensured by the following convenient sufficient condition:

```text
rho(B union T_16^(-1)(B))=0,                           (6.7)
```

since `tau(B)=rho(T_16^(-1)(B))`.

Under (6.7), put `mu_n=s_*rho_n`, `nu_n=s_*tau_n`, `mu=s_*rho`, and
`nu=s_*tau`.  At each fixed `m`, the finite sum and continuity of square root
give

```text
A_m(mu_n,nu_n) -> A_m(mu,nu).                          (6.8)
```

Here is one exact sufficient uniformity package for a growing-depth
experiment.  If one number `delta>0` and integers `M_n->infinity` satisfy

```text
A_m(mu_n,nu_n)>=delta for every n and every 0<=m<=M_n, (6.9)
```

then fixing `m`, taking `n` sufficiently large that `M_n>=m`, and using
(6.8) gives `A_m(mu,nu)>=delta`.  Since the same `delta` works for every fixed
`m`, Theorem 1 applies.  Without a common positive lower bound, for example
when the available depth- or cutoff-dependent bounds have infimum zero, this
passage fails.  Finite digit computations remain experiments and do not
establish (6.7) or (6.9) for a limiting pi measure.

## 7. Checked counterexamples

### Counterexample 1: every prescribed finite cutoff can look perfect

Fix any integer `N>=1`.  Let

```text
x=000000...,
y=0^N 1 000...,
mu=delta_x,
nu=delta_y.
```

For `0<=m<=N`, both atoms lie in the same depth-`m` cylinder, so `A_m=1`.
At depth `N+1` they lie in different cylinders, so every summand has one zero
factor and `A_(N+1)=0`; refinement gives `A_m=0` thereafter.  The singleton
`{x}` separates the two Dirac measures.  Thus even perfect overlap through an
arbitrarily large finite depth does not imply non-mutual-singularity.  The full
refuted quantifier pattern is

```text
for every cutoff N there are measures mu_N perp nu_N such that
A_m(mu_N,nu_N)=1 for every m<=N
```

in place of one fixed pair of measures and one positive `delta` for all `m`.

### Counterexample 2: strong self-collision bounds do not control cross-affinity

Use only digits 0 and 1.  Let `mu` be the Bernoulli product measure with
`mu(x_j=1)=1/2`, and let `nu` be the Bernoulli product measure with
`nu(x_j=1)=3/4`.  Independence gives the exact depth-`m` self-collision sums

```text
sum_w mu([w])^2 = ((1/2)^2+(1/2)^2)^m = (1/2)^m,
sum_w nu([w])^2 = ((1/4)^2+(3/4)^2)^m = (5/8)^m.       (7.1)
```

Both decay exponentially, so each measure separately has excellent spread in
the collision sense.  But product factorization gives

```text
A_m(mu,nu)
 = (sqrt((1/2)*(1/4))+sqrt((1/2)*(3/4)))^m
 = ((1+sqrt(3))/(2*sqrt(2)))^m.                        (7.2)
```

The base in (7.2) is strictly below one because
`(1+sqrt(3))^2=4+2*sqrt(3)<8`; hence `A_m->0`.  Theorem 1 says
`mu perp nu`, despite the two exponential self-collision bounds and despite
`A_m>0` at every finite depth.

The machine-checked T27 artifact
`TheoryLib.PiPositiveDecimalFactorEntropy.T27T27SparseMicroscopicEquivalence`
(source SHA-256
`e4e7b2dd5d080616edee252e05c50c3cc9f56ddc7cd0420b71c3acaca2710c65`)
studies one-orbit, ordered, diagonal-inclusive near-return pair counts.  This
is a contextual pin, not a premise of Theorem 1.  Such a bound is likewise a
self-collision statement.  Equations (7.1)-(7.2) refute the abstract inference
"separate self-collision control implies cross-affinity control."  They do not
claim that these Bernoulli measures are a pi orbit measure or that they satisfy
T27's exact fixed-pi premise.  A bridge from a T27-type estimate to T34 would
need an additional cross estimate coupling `mu` to its proposed pushforward;
no such bridge is supplied by a self-bound alone.

## 8. Conditional times-16 specialization

For a circle probability `rho`, define its canonical decimal lift and the
canonical lift of its times-16 pushforward by

```text
mu = s_*rho,
nu = s_*((T_16)_*rho).                                 (8.1)
```

Equivalently, with the Borel symbolic map

```text
R_16 = s o T_16 o beta,
```

equation (8.1) gives `nu=(R_16)_*mu`.  No boundary-null assumption is needed
to define these exact pushforwards under the fixed canonical section.

### Step 10: the only unconditional conclusion of the specialization

If the pair in (8.1) satisfies either

```text
inf_m A_m(mu,nu)>0
```

or, equivalently, one finite uniform bound in (5.3), then Theorem 1 gives
`mu` and `nu` non-mutually-singular.  Their circle projections `rho` and
`(T_16)_*rho` are also non-mutually-singular: a separating circle set would
pull back under `beta` to a separating symbolic set.

That is the end of T34's unconditional theorem.  For the particular weak-limit
route in Section 6, conditions (6.7) and (6.9) are sufficient.  They may be
replaced by direct proofs of all fixed-depth cylinder convergence and one
common positive lower bound; neither displayed condition is claimed necessary
for every possible approximation.

The T32 note `T32_MEASURE_RIGIDITY_VIABILITY_AUDIT.md` (SHA-256
`6c91794046a9ea8f51a75ad70d297d44f1607abbef4ac871e7920d766de4ffb6`)
argues, at `proof sketch` level, that common-map invariance and ergodicity can
conditionally upgrade non-mutual-singularity to equality before a pinned
rigidity theorem is applied.  This is a contextual pin, and T34 uses none of
those unverified claims or external rigidity sources as a premise.  In
particular, selecting a positive-entropy ergodic component of a nonergodic
orbit limit is still explicit and unresolved: an affinity bound for the
original mixture has not been shown to pass to the selected component and its
times-16 pushforward.

## 9. Final scope and verdict

1. **Criterion verdict:** valid.  Under the complete generating decimal
   cylinder filtration, `inf_m A_m>0` is equivalent to
   non-mutual-singularity.
2. **Renyi verdict:** valid only with a single depth-independent upper bound on
   the order-`1/2` cross-divergence.
3. **Finite-depth substitute:** refuted by Counterexample 1.
4. **Self-collision substitute:** refuted by Counterexample 2.  Self and cross
   collision data are logically different.
5. **Circle-limit transfer:** the displayed sufficient route is conditional on
   the boundary continuity condition (6.7) and uniform growing-depth condition
   (6.9), or on direct substitutes proving the same two consequences.
6. **Times-16 route:** conditional on constructing the same measure/component
   with the all-depth cross bound.  Component selection remains unresolved.
7. **Canonical nonclaims:** this note proves no statement about the digits of
   pi, no existence of a positive-entropy pi orbit measure, and no instance of
   C1 or C6.  T32 is motivation only.

## 10. Reproduction

From a directory containing only the delivered files, run

```bash
bash verify.sh
```

The script verifies the canonical source pin, checks required note locators,
and runs exact finite-word and rational-arithmetic checks for both
counterexamples.  These checks support inspection; the universal theorem rests
on the numbered proof, not on finite computation.
