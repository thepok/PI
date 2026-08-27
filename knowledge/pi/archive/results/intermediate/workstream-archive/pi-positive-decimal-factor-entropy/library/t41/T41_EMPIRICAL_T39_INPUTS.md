# T41: empirical-orbit inputs for the T39 rigidity bootstrap

Status: `proof sketch` (rigorous numbered prose, not a Lean artifact).

## 1. Provenance, scope, and verdict

The immutable canonical statement is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`. It is a locally
formulated problem and has no original external source URL. Its SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The canonical question asks whether one fixed `eta > 0` gives
`p_pi(n) >= 10^(eta*n)` for every sufficiently large `n`. This note does not
prove that assertion. It gives an exact finite-orbit hypothesis package under
which empirical measures from the decimal orbit of pi supply every
non-rigidity premise of the kernel-checked T39 theorem.

The main verdict is conditional:

1. Probability, times-10 invariance, and support on the pi orbit closure pass
   automatically to every empirical weak limit.
2. Decimal-cylinder convergence requires a boundary hypothesis.
3. Ergodicity follows from the stated generating-cylinder variance condition,
   but not from empirical convergence alone.
4. All-depth affinity follows from one common finite-scale lower bound through
   depths tending to infinity, but not from finitely many tests or from
   separate self-collision estimates.
5. The stated empirical entropy floor gives positive metric entropy of the
   limit. More importantly, it already implies the canonical factor bound C1
   directly. Thus the entropy-floor package is not an independent proof of C1.
6. Lebesgue measure, full support, orbit-closure equality, and C6 use the
   source-shaped rigidity premise retained in Section 10. No such conclusion
   is unconditional for pi.

The kernel-checked files used here are:

```text
T35: TheoryLib.PiPositiveDecimalFactorEntropy.T35T35CylinderAffinity
source SHA-256: 0d62aa6ca27c5965b3e5733d9fcef68989a472c667a249f160125f4359d492e3

T39: TheoryLib.PiPositiveDecimalFactorEntropy.T39T39ErgodicAffinityRigidity
source SHA-256: f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09
```

The T32 and T34 notes are unverified `proof sketch` material. They are not used
to discharge any assertion below. No new literature theorem is invoked: the
only rigidity input is retained as an explicit premise exactly as in T39.

## 2. Normalization and ambiguous quantifiers

Let `T = R/Z`, represented by `[0,1)`, and let

```text
T_b(x) = b*x mod 1,
x_j = frac(10^j*pi),
K_pi = closure {x_j : j in N_0}.
```

For every integer `N >= 1`, define the Borel probability

```text
mu_N = (1/N) * sum_{0 <= j < N} delta_{x_j}.            (2.1)
```

All logarithms in finite decimal entropy are to base 10. For `m >= 1` and
`0 <= k < 10^m`, put

```text
C(m,k) = [k/10^m,(k+1)/10^m) subset T,                 (2.2)
P_m = {C(m,k) : 0 <= k < 10^m}.
```

Also let `P_0={T}`. The half-open convention makes each `P_m` an actual
partition, including for measures charging terminating decimals. Let

```text
D_10 = {k/10^m mod 1 : m in N_0, 0 <= k <= 10^m}.       (2.3)
```

This is the countable union of all decimal-cylinder boundaries.

For a probability `rho`, define

```text
H_m(rho) = -sum_{C in P_m} rho(C)*log_10(rho(C)),        (2.4)
A_m(rho,sigma) = sum_{C in P_m} sqrt(rho(C)*sigma(C)),  (2.5)
```

where `0*log_10(0)=0`. At depth zero, `H_0=0` and `A_0=1`.

The following quantifier distinctions are essential.

1. The subsequence `N_r` is one fixed strictly increasing sequence of positive
   integers. It is not allowed to depend on the tested cylinder or depth.
2. The depth sequence `m_r` is one fixed sequence of positive integers with
   `m_r -> infinity`. It need not be strictly increasing; replacing it by
   `min_{s>=r} m_s` if necessary gives an eventually nondecreasing cofinal
   sequence.
3. The entropy constant `eta` and affinity constant `delta` are each fixed
   before `r` and `m` are quantified. Cutoff-dependent constants do not suffice.
4. Every limit passage below fixes the cylinder depth first and then lets
   `r -> infinity`. There is no interchange of weak convergence with a growing
   depth.
5. Positive metric entropy means Kolmogorov-Sinai entropy for `T_10`, not
   one-digit entropy, empirical entropy at one depth, or topological entropy.
6. "Supported on `K_pi`" means `mu(K_pi)=1`, as required by T39. Equality of
   the topological support with `K_pi` is neither assumed nor initially proved.

## 3. Exact two-scale hypothesis package

After discarding finitely many terms and reindexing, assume the following one
package. None of (B), (E), (V), or (A) is asserted to hold for pi.

### (S) Subsequence and depth

There are positive integers `N_r`, positive integers `m_r`, and a Borel
probability `mu` on `T` such that

```text
N_0 < N_1 < N_2 < ...,
m_r -> infinity,
mu_{N_r} => mu weakly as r -> infinity.                 (S)
```

Write `mu_r=mu_{N_r}`, `nu_r=(T_16)_*mu_r`, and
`nu=(T_16)_*mu`.

Compactness of `T` guarantees a weakly convergent subsequence from any
`N -> infinity`; it does not guarantee any of the remaining hypotheses.

### (B) Decimal boundary safety

For every decimal endpoint and every one of its times-16 preimages,

```text
for every b in D_10,
  mu({b})=0 and mu(T_16^(-1){b})=0.                     (B)
```

Equivalently, `mu(D_10 union T_16^(-1)(D_10))=0`, since both sets are
countable. For the integer 16, `T_16^(-1)(D_10) subset D_10`, but the preimage
quantifier is displayed because it is exactly the continuity-set fact used for
convergence of `nu_r` on decimal cells. It is redundant once `mu(D_10)=0` is
known for this particular multiplier, not an additional independent premise.

### (E) Uniform cylinder-entropy floor

There is one real `eta>0` such that

```text
for every r and every integer m with 1 <= m <= m_r,
  H_m(mu_r) >= eta*m.                                  (E)
```

This is a two-scale statement: the sample length is `N_r`, the resolution is
`m`, and every resolution through the cofinal depth `m_r` is controlled.

### (V) Generating-cylinder Birkhoff variance

For a decimal cylinder `C=C(q,k)` and integer `L>=1`, define

```text
B_{C,L}(x) = (1/L) * sum_{0 <= i < L} 1_C(T_10^i x),

V_{r,L}(C)
 = integral (B_{C,L}(x)-mu_r(C))^2 d mu_r(x)
 = (1/N_r) * sum_{0 <= j < N_r}
     ((1/L) * sum_{0 <= i < L} 1_C(x_{j+i})-mu_r(C))^2. (3.1)
```

The exact variance hypothesis is

```text
for every q>=1, every 0<=k<10^q, and every epsilon>0,
  there is L_0>=1 such that for every L>=L_0,
    there is r_0 such that for every r>=r_0,
      q+L <= m_r and V_{r,L}(C(q,k)) < epsilon.          (V)
```

The harmless inequality `q+L<=m_r` records that all orbit coordinates used by
the length-`L` average of a depth-`q` cylinder lie below the declared finite
resolution. Because `m_r -> infinity`, it introduces no hidden diagonal limit.

### (A) Uniform growing-depth affinity

There is one real `delta>0` such that

```text
for every r and every integer m with 0 <= m <= m_r,
  A_m(mu_r,nu_r) >= delta.                              (A)
```

This is cross-affinity between `mu_r` and its actual times-16 pushforward. It
is not a self-collision estimate for either measure separately.

## 4. Numbered limit passage: probability and invariance

### Step 1: probability normalization

Every `mu_r` is a probability by (2.1). Weak convergence on the compact circle
preserves total mass, so `mu(T)=1`. Continuity of `T_16` also gives
`nu_r => nu`; each `nu_r` and `nu` is a probability.

### Step 2: exact endpoint telescoping

For every continuous `f:T->R`, the orbit identity `T_10(x_j)=x_{j+1}` gives

```text
integral f o T_10 d mu_N - integral f d mu_N
  = (f(x_N)-f(x_0))/N.                                 (4.1)
```

The absolute value of the right side is at most `2*||f||_infinity/N`.
Since strict increase of the positive integers `N_r` implies `N_r -> infinity`,
weak convergence in (S), continuity of `f` and `f o T_10`, and (4.1) yield

```text
integral f o T_10 d mu = integral f d mu.               (4.2)
```

Thus `(T_10)_*mu=mu`; equivalently, `T_10` is measure-preserving for `mu`.
No ergodicity follows from this telescoping argument.

## 5. Numbered limit passage: support

### Step 3: closed-support passage

Every atom `x_j` belongs to the closed set `K_pi`, hence
`mu_r(K_pi)=1`. Portmanteau for the closed set `K_pi` says

```text
limsup_r mu_r(K_pi) <= mu(K_pi).
```

Therefore `1<=mu(K_pi)<=1`, so

```text
mu(K_pi)=1.                                             (5.1)
```

This proves exactly T39's support premise. It does not prove
`support(mu)=K_pi` or `K_pi=T`.

## 6. Numbered limit passage: decimal boundaries

### Step 4: fixed cylinder masses

For every fixed `m,k`, the frontier of `C(m,k)` is contained in `D_10`.
Hypothesis (B) and Portmanteau's continuity-set theorem therefore give

```text
mu_r(C(m,k)) -> mu(C(m,k)).                             (6.1)
```

Moreover,

```text
nu_r(C(m,k)) = mu_r(T_16^(-1)C(m,k)),
nu(C(m,k))   = mu(T_16^(-1)C(m,k)).                     (6.2)
```

The frontier of the preimage in (6.2) is contained in
`T_16^(-1)(frontier C(m,k))`. The second clause of (B) gives

```text
nu_r(C(m,k)) -> nu(C(m,k)).                             (6.3)
```

Equations (6.1)-(6.3) hold separately for every fixed depth. They do not claim
uniformity over `m<=m_r`.

### Step 5: the canonical symbolic coding is T39-boundary-safe

Let `X={0,...,9}^N_0` with its product Borel sigma-algebra. Define the canonical
decimal section `s:T->X` by

```text
s(x)|m = the unique word w with x in C(m,k(w)),          (6.4)
```

choosing terminating zeros at decimal endpoints. Then
`s^(-1)([w])=C(m,k(w))`. The selected words are compatible under truncation
because `P_{m+1}` refines `P_m`, so they define one element of `X`. Prefix
cylinders generate the product Borel sigma-algebra, making `s` Borel. The
decimal value map `beta:X->T` is continuous and `beta o s=id_T`; this proves
injectivity and shows that every Borel set `E subset T` has the form
`s^(-1)(beta^(-1)(E))`. Thus the measurable structure on `T` is induced by
`s`, and `s` is a measurable embedding.

It remains to verify, rather than assume, T39's `GeneratesInMeasure` clause.
Let `alpha,gamma` be any two Borel probabilities on `X`, put
`lambda=alpha+gamma`, and let `E` be Borel. Finite unions of prefix cylinders
form an algebra `Q` generating the Borel sigma-algebra. To justify the required
approximation, let `L` be the sets `E` such that, for every `epsilon>0`, some
`U in Q` satisfies `lambda(E symmetric_difference U)<epsilon`. The class `L`
contains `Q` and is closed under complements. It is closed under countable
unions: first truncate the union using continuity from below and finiteness of
`lambda`, then approximate the finitely many retained sets and use the union
bound. Thus `L` is a sigma-algebra containing `Q`, so `L` is the full Borel
sigma-algebra. In particular, for each `epsilon>0` there is a finite-cylinder
union `U` with

```text
lambda(E symmetric_difference U)<epsilon.               (6.5)
```

Refine all cylinders in `U` to one common depth `m` and let `W` be the selected
depth-`m` words. Then

```text
alpha(U) <= alpha(E)+epsilon,
gamma(U^c) <= gamma(E^c)+epsilon.                        (6.6)
```

These are exactly the two inequalities in T35's `GeneratesInMeasure`
definition. Applying this to `alpha=s_*mu` and `gamma=s_*nu` proves T39's
`DecimalBoundarySafe s mu nu`: measurable embedding plus generation in
measure. Notice that this symbolic generation statement is automatic; (B) is
separately needed for the empirical weak-limit passages (6.1)-(6.3).

## 7. Numbered limit passage: entropy

### Step 6: fixed-depth entropy of the limit

Fix `m>=1`. Since `m_r->infinity`, there is `r_m` such that `m<=m_r` for all
`r>=r_m`. The finitely many masses in (6.1) converge, and
`t |-> -t*log_10(t)` extends continuously to `[0,1]` with value zero at zero.
Thus

```text
H_m(mu_r) -> H_m(mu),
H_m(mu) >= eta*m.                                       (7.1)
```

The partition `P_m` is the join of `P_1,T_10^(-1)P_1,...,
T_10^(-(m-1))P_1`. These joins generate the Borel sigma-algebra. Since `mu` is
`T_10`-invariant by Step 2, the finite-generator formula and subadditivity give

```text
h_mu(T_10)
 = lim_{m->infinity} H_m(mu)/m
 = inf_{m>=1} H_m(mu)/m
 >= eta > 0,                                            (7.2)
```

with entropy measured in decimal units. Changing the logarithm base multiplies
by a positive constant and does not affect positivity.

### Step 7: (E) already contains C1

For every `r,m`, the nonzero cells of the empirical vector
`(mu_r(C))_{C in P_m}` are cells visited by some `x_j`, `0<=j<N_r`. Such a
cell is labeled by the length-`m` decimal factor of pi starting at position
`j+1`; irrationality of pi ensures that no `x_j` has a terminating-decimal
ambiguity. Therefore

```text
number of nonzero P_m cells for mu_r <= p_pi(m).         (7.3)
```

Shannon entropy of a probability supported on at most `s` points is at most
`log_10(s)`. Given any `m>=1`, choose `r` with `m<=m_r`; (E) and (7.3) give

```text
eta*m <= H_m(mu_r) <= log_10(p_pi(m)),
p_pi(m) >= 10^(eta*m).                                  (7.4)
```

Thus (S) and (E) imply the canonical C1 quantifiers, even with `N=1`, and
imply positive topological entropy of the decimal shift-orbit closure. The
direct implication is (7.3)-(7.4), so no separate topological or variational
principle is needed. Since (E) is wholly unproved for pi, (7.4) is a conditional
reduction, not a proof of C1. In particular, the T39 route based on (E) is not
independent of the original positive-factor-entropy problem.

## 8. Numbered limit passage: variance and ergodicity

### Step 8: fixed-`L` variance convergence

Fix `C=C(q,k)` and `L>=1`. The discontinuity set of
`1_C o T_10^i` is contained in `T_10^(-i)(D_10)`, which is contained in
`D_10`. Products of two such indicators have the same boundary property.
Expanding the square in (3.1), (B), (6.1), and Portmanteau therefore give

```text
V_{r,L}(C) ->
V_L(C) := integral (B_{C,L}(x)-mu(C))^2 d mu(x).         (8.1)
```

There is no growing-`L` Portmanteau assertion here: (8.1) is proved for each
fixed `L`.

### Step 9: use the variance quantifiers in the correct order

Fix `C` and `epsilon>0`. Apply (V) with `epsilon/2`. For every `L>=L_0`, the
eventual inequality `V_{r,L}(C)<epsilon/2` and (8.1) imply
`V_L(C)<=epsilon/2<epsilon`. Hence

```text
lim_{L->infinity} V_L(C)=0                              (8.2)
```

for every decimal cylinder `C`. The order is: choose `C,epsilon`, then `L_0`,
then a fixed `L`, then let `r->infinity`.

### Step 10: generating-cylinder variance implies ergodicity

Let `U` be the Koopman operator `Uf=f o T_10` on `L^2(mu)`. By Step 2 it is an
isometry. The von Neumann mean ergodic theorem says

```text
(1/L) * sum_{0<=i<L} U^i 1_C -> Proj_I(1_C) in L^2(mu), (8.3)
```

where `Proj_I` is projection onto the `T_10`-invariant functions. Equation
(8.2) identifies the limit in (8.3) as the constant `mu(C)`. Thus

```text
Proj_I(1_C)=mu(C) for every decimal cylinder C.          (8.4)
```

Finite linear combinations of cylinder indicators are dense in `L^2(mu)`.
By continuity of orthogonal projection, (8.4) implies
`Proj_I(f)=integral f d mu` for every `f in L^2(mu)`. If `E` is invariant
modulo `mu`, then `1_E=Proj_I(1_E)` is almost surely the constant `mu(E)`.
Since an indicator takes only values zero and one, `mu(E)` is zero or one.
Therefore `mu` is ergodic for `T_10`, exactly as required by T39.

## 9. Numbered limit passage: affinity and T35

### Step 11: pass the common affinity floor to every fixed depth

Fix `m>=0`. For all sufficiently large `r`, `m<=m_r`. Equations (6.1) and
(6.3), finiteness of `P_m`, and continuity of square root give

```text
A_m(mu_r,nu_r) -> A_m(mu,nu).                           (9.1)
```

Hypothesis (A) and (9.1) yield

```text
for every m>=0, A_m(mu,nu)>=delta>0.                    (9.2)
```

The constant remains the original `delta`; it does not depend on the fixed
depth chosen after passage to the limit.

### Step 12: verify T35 before using it

Under the canonical section `s` from Step 5, each symbolic depth-`m` cylinder
pulls back to exactly one circle cell in `P_m`. Consequently

```text
affinity(s_*mu,s_*nu,m)=A_m(mu,nu).                     (9.3)
```

The prerequisites of the machine-checked T35 theorem are now all present:

1. `s_*mu` and `s_*nu` are probabilities by Step 1.
2. Their complete prefix cylinders are the finite generating partitions from
   Step 5.
3. `GeneratesInMeasure` was proved in (6.5)-(6.6).
4. The one depth-independent positive lower bound for every `m` is (9.2).

Before invoking T35, (9.2)-(9.3) give

```text
delta <= inf_{m>=0} affinity(s_*mu,s_*nu,m),
0 < inf_{m>=0} affinity(s_*mu,s_*nu,m).                  (9.4)
```

The first inequality is the defining lower-bound property of the infimum, and
the second follows from `delta>0`. The machine-checked T35 theorem
`positive_allDepth_inf_iff_not_mutuallySingular` therefore gives

```text
not (s_*mu mutually singular s_*nu).                    (9.5)
```

Measurable embeddings preserve mutual singularity under pushforward: if a
Borel set separates `mu` and `nu`, its measurable image under `s` separates
`s_*mu` and `s_*nu`. This is the contrapositive transfer used in the
machine-checked T39 theorem
`positive_allDepth_decimalAffinity_implies_not_mutuallySingular`. Hence

```text
not (mu mutually singular nu).                          (9.6)
```

No absolute continuity or equality is claimed at this step.

### Step 13: common ergodicity upgrades affinity to times-16 invariance

The maps `T_10` and `T_16` commute. Step 10 gives `T_10`-ergodicity of `mu`, so
the continuous factor pushforward `nu=(T_16)_*mu` is also `T_10`-ergodic. The
machine-checked T39 dichotomy says two probabilities ergodic for the same map
are equal or mutually singular. Equation (9.6) excludes the latter, giving

```text
(T_16)_*mu=mu.                                          (9.7)
```

This is the last conclusion before the external rigidity premise is used.

## 10. Exact T39 hypothesis audit and conditional conclusion

Let `h` be a total real-valued function on all Borel measures on `T` which, on
`T_10`-invariant probabilities, equals their Kolmogorov-Sinai entropy in any
fixed logarithm base; for example, set it to zero outside that class. This
matches T39's formal type `Measure T -> R`. Retain the exact source-shaped
premise formalized by T39:

```text
(R) For every Borel measure rho on T, if
      rho is a probability,
      (T_10)_*rho=rho,
      (T_16)_*rho=rho,
      rho is ergodic for T_10, and
      h(rho)>0,
    then rho is normalized Lebesgue measure on T.        (R)
```

This note does not prove (R), does not treat the T32 `proof sketch` as a proof
of (R), and makes no novelty claim about rigidity. It merely supplies (R) as
the explicit `RudolphJohnsonRigidityPremise` argument required by T39.

Here is the complete premise audit for the machine-checked theorem
`pi_conditional_ergodic_affinity_rigidity`:

| T39 premise | Discharge in this note |
|---|---|
| `mu` is a probability | Step 1 |
| times-10 measure-preserving | Step 2 |
| times-10 ergodic | Steps 8-10, conditional on (V) and (B) |
| `mu(K_pi)=1` | Step 3 |
| decimal measurable embedding | Step 5 |
| cylinder generation in measure | Step 5 |
| one `delta>0` at every affinity depth | Steps 11-12, conditional on (A) and (B) |
| positive metric entropy | Step 6, conditional on (E) and (B) |
| source rigidity | retained premise (R) |

Only after this audit may T39 be applied. Conditional on the single package
(S), (B), (E), (V), (A), and (R), its kernel-checked conclusion is

```text
(T_16)_*mu=mu,
mu=Lebesgue measure,
support(mu)=T,
K_pi=T,
and C6 holds with A=1, B=0, epsilon_0=1 and R=0.         (10.1)
```

Every assertion in (10.1) is conditional. In particular, this note proves no
unconditional times-16 invariance, full support, C6, normality, disjunctivity,
or new digit property of pi.

## 11. Counterexamples and failure diagnoses

Each example is a sibling dynamical system, not a claim about pi.

### Counterexample 1: an empirical weak limit need not be ergodic

Let a decimal seed have digit sequence

```text
0^1 1^1 0^2 1^2 0^3 1^3 ... .                          (11.1)
```

At the end of stage `s`, the total length is `s(s+1)`, with equal time in zero
and one blocks. A partial stage creates discrepancy at most `2(s+1)=O(s)`,
while the elapsed length is of order `s^2`. Up to that point there are only
`2s` digit transitions. For each fixed cylinder depth `q`, only `O(qs)=o(s^2)`
starting positions lie within `q-1` digits of a transition. Therefore the
empirical measures converge on every decimal cylinder, hence weakly, to

```text
(1/2)*delta_0 + (1/2)*delta_{1/9}.                       (11.2)
```

Both atoms are fixed by `T_10`, so the limit is invariant. It is not ergodic,
because the invariant set `{0}` has mass `1/2`. Thus Step 2 cannot replace (V),
and selecting a weak subsequence alone does not supply T39's ergodicity premise.

### Counterexample 2: affinity is not automatic for an empirical limit

Take the seed `x=1/9`. Its times-10 orbit is constant, so every empirical
measure and its limit equal `delta_{1/9}`. But

```text
T_16(1/9)=7/9,
(T_16)_*delta_{1/9}=delta_{7/9}.
```

The two measures lie in different depth-one decimal cylinders, so `A_1=0` and
they are mutually singular. Probability, support on the orbit closure,
times-10 invariance, and times-10 ergodicity do not imply (A). This example also
has zero entropy, so it makes no rigidity claim.

### Counterexample 3: every finite affinity cutoff can be misleading

For each cutoff `M`, let `u=000...` and let `v_M` agree with `u` in coordinates
`0,...,M-1` but have digit one at coordinate `M`. Then

```text
A_m(delta_u,delta_{v_M})=1 for every 0<=m<=M,
A_{M+1}(delta_u,delta_{v_M})=0,
delta_u mutually singular delta_{v_M}.                  (11.3)
```

This is the machine-checked T35 theorem
`finiteDepth_overlap_counterexample`. It refutes replacing (A) by "for every
cutoff there is a pair passing that cutoff" or by constants depending on the
cutoff. The successful passage in Step 11 instead uses one pair in the limit,
one `delta`, and `m_r->infinity`.

### Counterexample 4: ordinary decimal boundaries can break weak passage

Let `C=C(1,5)=[1/2,3/5)`, `rho_n=delta_{1/2-1/n}` for `n>10`, and
`rho=delta_{1/2}`. Then `rho_n=>rho`, but

```text
rho_n(C)=0 for every n,
rho(C)=1.                                                (11.4)
```

Thus weak convergence does not imply (6.1) when the limit charges a decimal
boundary.

### Counterexample 5: times-16 preimage boundaries can break pushforward passage

Let `y=1/32`, `y_n=y-1/(16n)` for `n>10`,
`rho_n=delta_{y_n}`, and `rho=delta_y`. Then `rho_n=>rho`, while

```text
T_16(y)=1/2,
T_16(y_n)=1/2-1/n,
(T_16)_*rho_n(C(1,5))=0,
(T_16)_*rho(C(1,5))=1.                                  (11.5)
```

Here the limit charges `T_16^(-1){1/2}`. This is why (B) explicitly quantifies
over preimages when auditing (6.2). For times 16, `y=1/32` is itself in
`D_10`, so the first clause of (B) also detects this failure; the example does
not claim that the preimage clause is logically independent in base 10.

### Counterexample 6: selecting an ergodic component can destroy overlap

Let

```text
Y={0,1}^Z x {0,1},
T(omega,i)=(shift(omega),i),
S(omega,i)=(omega,1-i).
```

The maps commute. If `beta` is fair two-sided Bernoulli measure, put

```text
lambda_0=beta x delta_0,
lambda_1=beta x delta_1,
lambda=(lambda_0+lambda_1)/2.
```

Then `S_*lambda=lambda`, so the mixture has perfect affinity with its
pushforward at every generating depth. Both `lambda_i` are positive-entropy
`T`-ergodic components, but `S_*lambda_0=lambda_1`, and these components are
mutually singular. Hence one may not establish affinity for a nonergodic
empirical limit and then select a positive-entropy ergodic component. Conditions
(V), (E), and (A) must hold in a way that yields the same limiting measure to
which T39 is applied.

## 12. Final conditional theorem and research frontier

### Theorem T41-E (finite-orbit extraction, conditional)

Suppose the decimal orbit of pi admits `N_r,m_r,mu,eta,delta` satisfying the
fully quantified hypotheses (S), (B), (E), (V), and (A). Then:

```text
mu is a T_10-invariant ergodic Borel probability,
mu(K_pi)=1,
h_mu(T_10)>=eta>0,
the canonical decimal coding is T39-boundary-safe,
inf_{m>=0} A_m(mu,(T_16)_*mu)>=delta>0,
and (T_16)_*mu=mu.                                      (12.1)
```

The first five assertions follow from Steps 1-12; the last is the
machine-checked non-rigidity part of T39 applied in Step 13. If, in addition,
the source-shaped premise (R) is supplied, all conditional conclusions in
(10.1) follow from the machine-checked final T39 theorem.

The unresolved fixed-pi frontier is not compactness or empirical invariance.
It is proving (B), (V), and (A) for one common subsequential limit. Hypothesis
(E) is also unresolved and, by Step 7, is already at least as strong as the
canonical C1 target. Failure of a proposed empirical strategy can therefore be
classified exactly as boundary failure, ergodicity/variance failure,
all-depth affinity failure, or use of an entropy premise that has already
assumed C1's substance.
