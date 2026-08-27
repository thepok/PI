# T32: times-10/times-16 measure-rigidity viability audit

Audit date: 2026-07-24 UTC

Status: `proof sketch`.  The reduction below is conditional and is not a proof of
C1, C6, or any new fact about pi.  Its elementary measure-theoretic steps are proved
in full here.  Its final rigidity step invokes the source-pinned theorems in Section
3.  The full Johnson article was not accessible in this sandbox; the exact theorem
statement in the publisher's abstract is pinned, and the directly applicable
Rudolph corollary is pinned in a complete primary PDF.

## 1. Provenance and immutable target

The canonical problem statement is the packaged file
`pi-positive-decimal-factor-entropy.txt`.  Its SHA-256 is

```
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

This equals the required hash of
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.  The canonical question is
the eventual exponential lower bound for decimal factor complexity (C1).  This item
audits a separate conditional route through C6.  It does not replace or weaken the
canonical question.

Let `T = R/Z`, represented by `[0,1)`, and write

```
T_m(x) = m*x mod 1,
alpha = pi mod 1,
K_pi = closure {T_10^j(alpha) : j >= 0}.
```

Throughout, `N_0={0,1,2,...}`.  In particular, the C6 depth parameter may be zero,
as required by this agenda item.

The exact C6 target is:

```
there exist A > 0, B in R, and eps_0 > 0 such that
for every 0 < eps < eps_0 there is R in N_0 with
R <= A*log(1/eps)+B
and union_{0 <= j <= R} T_16^j(K_pi) eps-dense in T.
```

## 2. Normalization and ambiguous phrases

For `n >= 1` and `0 <= k < 10^n`, define the half-open decimal cylinder

```
C(n,k) = [k/10^n, (k+1)/10^n) subset [0,1),
P_n = {C(n,k) : 0 <= k < 10^n}.
```

The half-open convention makes `P_n` an actual partition even when a measure has
atoms at terminating decimals.  The increasing family of finite algebras generated
by the `P_n` generates the Borel sigma-algebra of `T`.

For Borel probabilities `rho` and `sigma`, define their depth-`n` common mass by

```
O_n(rho,sigma) = sum_{C in P_n} min(rho(C), sigma(C)).
```

This audit gives "uniform all-depth cylinder overlap" the following exact meaning:

```
there exists delta > 0 such that for every n >= 1,
O_n(mu, (T_16)_*mu) >= delta.                         (Overlap)
```

The quantifier `exists delta, for every n` is essential.  A positive lower bound
depending on a tested cutoff is not (Overlap).  If "overlap bound" instead means the
stronger pointwise comparison

```
C^(-1)*mu(D) <= (T_16)_*mu(D) <= C*mu(D)
```

for every decimal cylinder `D` and one finite `C >= 1`, then (Overlap) follows with
`delta=1/C`; thus the reduction below also covers that interpretation.

Other normalized phrases are:

1. "Supported on `K_pi`" means `mu(K_pi)=1`; because `K_pi` is closed, this implies
   `supp(mu) subset K_pi`.
2. "Invariant" means `(T_10)_*mu=mu`.
3. "Ergodic" means every Borel set invariant modulo `mu` under `T_10` has measure
   zero or one.
4. "Positive entropy" means Kolmogorov-Sinai metric entropy
   `h_mu(T_10)>0`, not single-digit Shannon entropy, empirical Renyi entropy, or
   topological entropy of `K_pi`.
5. No premise below is asserted for pi.  In particular, existence of `mu`, its
   positive entropy, and (Overlap) are all explicit unproved premises.

## 3. Exact rigidity sources and applicability

Full retrieval data, URLs, and hashes are in `SOURCE_MANIFEST.md`; `verify.sh`
checks the pins and locators.

### 3.1 Rudolph's theorem and its applicable corollary

Rudolph's abstract, printed page 395/PDF page 1, assumes relatively prime natural
numbers `p,q`, invariance under both multiplication maps, and ergodicity for their
generated semigroup.  It concludes that a non-Lebesgue measure has zero entropy for
both maps.  The definitions on printed page 399/PDF page 5 identify `M` as the
simultaneously invariant Borel probabilities and `M_0` as its ergodic extreme
points.  The formal result is Theorem 4.9, printed page 405/PDF page 11.

Theorem 4.9 alone cannot be inserted with `p=10,q=16`, because their gcd is 2.
However, Corollary 4.11, printed page 406/PDF page 12, says that Theorem 4.9 also
holds when

```
gcd(u,v)=1,
u != 1 and v != 1,
p=u^n1*v^m1,
q=u^n2*v^m2,
n1*m2-m1*n2 != 0.
```

Set

```
u=2, v=5,
(n1,m1)=(1,1), so p=10,
(n2,m2)=(4,0), so q=16.
```

Then `gcd(2,5)=1` and the determinant is `1*0-1*4=-4 != 0`.
Consequently Rudolph Corollary 4.11 applies to the pair 10,16.  In contrapositive
form, a simultaneously invariant, semigroup-ergodic Borel probability with
`h_mu(T_10)>0` must be Lebesgue measure.

Here is the explicit circle-to-symbolic bridge behind that last sentence.  Rudolph
Lemma 2.2, printed pages 397-398/PDF pages 3-4, constructs a natural almost
one-to-one coding from the one-sided symbolic system `Y` to the circle system.  The
paper then passes to the doubly-infinite inverse-limit system `Yhat`; this latter map
is an extension of the circle system, not an almost one-to-one map.  Corollary 3.2 on
printed page 399/PDF page 5 says that a simultaneously invariant circle probability
with no mass at zero lifts uniquely through this inverse-limit construction.  The
introduction on printed pages 395-396/PDF pages 1-2 explicitly states that an
invariant ergodic circle measure lifts invariantly and ergodically.

A positive-entropy ergodic measure cannot be atomic: an ergodic invariant
probability with an atom is supported on a finite periodic orbit and has entropy
zero.  Thus H4 excludes `delta_0`; ergodicity gives `mu({0})=0`, so Corollary 3.2
supplies the invariant ergodic lift `muhat`.

Only the factor entropy inequality is needed.  If `Phi:Yhat->T` is the factor map,
then for every finite Borel partition `Q` of the circle and every `N`, the joined
pullback partition

```
join_{j=0}^{N-1} T^(-j)(Phi^(-1)Q)
```

has exactly the same atom probabilities under `muhat` as
`join_{j=0}^{N-1} T_10^(-j)Q` has under `mu`.  Taking normalized Shannon entropies,
limits, and then the supremum over `Q` gives

```
h_muhat(T) >= h_mu(T_10)>0.
```

Rudolph Lemma 3.5, printed page 400/PDF page 6, identifies the lift's
Kolmogorov-Sinai entropy with the coordinate-partition entropy used in Theorem 4.9:
`h_muhat(T)=h_muhat(T,P)`.  Therefore the exact entropy appearing in Theorem 4.9 is
positive.  Theorem 4.9 applies to this invariant ergodic lift, and Corollary 4.11
extends its conclusion to the displayed 10,16 exponents.  It forces the lift to be
Rudolph's Lebesgue lift `mhat`; projecting by `Phi` gives `mu=m_T` on the circle.
Corollary 4.10, printed page 405/PDF page 11, is the adjacent circle-map formulation
of the zero-entropy alternative.  No almost-one-to-one claim about `Yhat` and no
unmentioned entropy-preservation or entropy-notation premise is used.

### 3.2 Johnson's nonlacunary extension

Johnson's publisher abstract (`johnson-1992-publisher.html`, HTML element `#Abs1`)
states:

```
Let S be a nonlacunary subsemigroup of the natural numbers and let mu be an
S-invariant and ergodic measure.  If any element in S has positive entropy with
respect to mu, then mu is Lebesgue.
```

The publisher metadata identifies the article's subject as Borel probability
measures.  This audit in any case assumes from the outset that `mu` is a Borel
probability, so it does not exploit any possible ambiguity in the abstract's word
"measure".

Furstenberg Definition IV.1, printed page 47/PDF page 47, defines a multiplicative
semigroup of integers to be lacunary when all of its positive members are powers of
one integer, and nonlacunary otherwise.  The semigroup

```
S = {10^a*16^b : a,b in N_0}
```

is nonlacunary.  Indeed, if both 10 and 16 were positive powers of one integer `c`,
then the prime 5 dividing 10 would divide `c`, hence would divide every positive
power of `c`, contradicting `5` not dividing `16`.

Thus Johnson's publisher-stated theorem also has the right hypotheses once the
conditional argument below establishes simultaneous invariance and semigroup
ergodicity.  The complete Johnson PDF was not available without subscription, so
this audit uses Rudolph Corollary 4.11 as its fully inspectable primary-PDF route and
records the Johnson access limitation rather than inventing an internal theorem
number.

## 4. Conditional reduction theorem

### Proposition T32-R

Assume there is a Borel probability `mu` on `T` satisfying all six premises:

```
H1. mu(K_pi)=1.
H2. (T_10)_*mu=mu.
H3. mu is ergodic for T_10.
H4. h_mu(T_10)>0.
H5. delta>0.
H6. O_n(mu,(T_16)_*mu)>=delta for every n>=1.
```

Then

```
(T_16)_*mu=mu,
mu is Lebesgue measure,
K_pi=T,
and C6 holds with R=0.
```

Everything after H1-H6 is conditional.  No H1-H6 package is known here for pi.

### Step 1: the pushforward is a probability

Put `nu=(T_16)_*mu`.  Since `T_16` is continuous and Borel measurable, `nu` is a
Borel probability.  This step supplies no invariance by itself.

### Step 2: commutation and T_10-invariance of the pushforward

For every `x in T`,

```
T_10(T_16(x)) = 160*x mod 1 = T_16(T_10(x)).
```

Therefore, using H2,

```
(T_10)_*nu
  = (T_10)_*(T_16)_*mu
  = (T_16)_*(T_10)_*mu
  = (T_16)_*mu
  = nu.
```

Thus `nu` is `T_10`-invariant.

### Step 3: T_10-ergodicity passes to the pushforward

Let `A` be Borel and invariant modulo `nu` under `T_10`, meaning
`nu(T_10^(-1)A triangle A)=0`.  Commutation gives

```
mu(T_10^(-1)(T_16^(-1)A) triangle T_16^(-1)A)
 = mu(T_16^(-1)(T_10^(-1)A triangle A))
 = nu(T_10^(-1)A triangle A)
 = 0.
```

By H3, `mu(T_16^(-1)A)` is zero or one.  This number equals `nu(A)`, so `nu` is
`T_10`-ergodic.  No invertibility of either multiplication map is used.

### Step 4: all-depth overlap rules out mutual singularity

Refining a partition cannot increase common mass: for nonnegative `a_i,b_i`,

```
sum_i min(a_i,b_i) <= min(sum_i a_i, sum_i b_i).
```

Hence `O_(n+1)(mu,nu)<=O_n(mu,nu)`.

Suppose for contradiction that `mu` and `nu` are mutually singular.  There is a
Borel set `E` with `mu(E)=1` and `nu(E)=0`.  Put `lambda=mu+nu`.  Finite unions of
decimal cylinders form an algebra generating the Borel sets, so for every
`epsilon>0` there is a union `U` of atoms of one `P_N` such that

```
lambda(E triangle U)<epsilon.
```

It follows that `mu(U^c)<epsilon` and `nu(U)<epsilon`.  Split the atoms of `P_N`
according as they lie in `U` or `U^c`.  Then

```
O_N(mu,nu)
 <= sum_{C subset U} nu(C) + sum_{C subset U^c} mu(C)
 = nu(U)+mu(U^c)
 < 2*epsilon.
```

Taking `epsilon<delta/2` contradicts H6.  Therefore `mu` and `nu` are not mutually
singular.  Notice the precise conclusion: overlap first gives non-mutual-singularity,
not absolute continuity or nonsingularity of `T_16`.

### Step 5: ergodicity upgrades non-singularity to equality

Any two distinct ergodic invariant probabilities for the same measurable map are
mutually singular.  Here is the required proof.  If invariant probabilities
`rho != sigma`, choose a Borel set `B` with `rho(B) != sigma(B)`.  By Birkhoff's
ergodic theorem, the averages

```
(1/N)*sum_{j=0}^{N-1} 1_B(T_10^j x)
```

converge to `rho(B)` on a `rho`-full Borel set and to `sigma(B)` on a `sigma`-full
Borel set.  Those two sets are disjoint, proving `rho` and `sigma` mutually
singular.

Steps 2 and 3 show that both `mu` and `nu` are `T_10`-invariant and ergodic.  Step 4
shows they are not mutually singular.  Therefore

```
nu=mu, equivalently (T_16)_*mu=mu.                    (1)
```

Equation (1) also proves standard measure-theoretic nonsingularity of `T_16`: if
`mu(A)=0`, then `mu(T_16^(-1)A)=((T_16)_*mu)(A)=0`.  Nonsingularity is a conclusion,
not a silently assumed premise.

### Step 6: every rigidity hypothesis is now present

Equation (1) and H2 give invariance under both generators, hence under every member
of `S=<10,16>`.  If a Borel set is invariant modulo `mu` under all of `S`, then it is
in particular invariant under `T_10`; H3 therefore makes its measure zero or one.
Thus `mu` is ergodic for the semigroup action.  H4 supplies positive entropy for the
element 10 of `S`.

All Rudolph Corollary 4.11 hypotheses listed in Section 3.1 are now checked.
Equivalently, all hypotheses in Johnson's pinned publisher statement and the
nonlacunarity check in Section 3.2 are present.  The source theorem therefore gives

```
mu = m_T,
```

where `m_T` is normalized Lebesgue/Haar measure on the circle.

### Step 7: support forces K_pi to be the circle

Since `K_pi` is closed and H1 says `mu(K_pi)=1`, every point outside `K_pi` has an
open neighborhood of `mu`-measure zero.  Hence

```
supp(mu) subset K_pi.
```

Lebesgue measure has support all of `T`.  Therefore

```
T=supp(mu) subset K_pi subset T,
```

so `K_pi=T`.  Equality between `K_pi` and the support was not assumed.

### Step 8: exact C6 constants and R=0

Choose

```
A=1, B=0, eps_0=1.
```

For each `0<eps<1`, choose the integer `R=0`.  Then

```
R=0 <= log(1/eps)=A*log(1/eps)+B,
union_{0<=j<=R} T_16^j(K_pi)=K_pi=T,
```

which is `eps`-dense.  This proves C6 with `R=0`, conditional on H1-H6.

## 5. Counterexample: finite-depth overlap is insufficient

This example is not about pi.  Let `Sigma={0,1}^N`, let `beta` be the fair Bernoulli
product probability, and define

```
q(a_1,a_2,...) = sum_{j>=1} a_j*10^(-j),
mu=q_*beta,
nu=(T_16)_*mu.
```

If two sequences first differ at position `r`, their images differ by at least

```
10^(-r)-sum_{j>r}10^(-j)=(8/9)*10^(-r)>0.
```

Thus `q` is injective, and `T_10 q=q shift`.  It follows that `mu` is `T_10`-invariant
and ergodic and

```
h_mu(T_10)=log 2>0.
```

As in Steps 2 and 3, `nu` is also `T_10`-invariant and ergodic.

The measures are distinct.  The support of `mu` lies in `[0,1/9]`.  Conditional on
first digit 1, `x in [1/10,1/9]`, so

```
T_16(x)=16*x-1 in [3/5,7/9].
```

For `B=[3/5,7/9]`, therefore, `mu(B)=0` and `nu(B)=1/2`.  Distinct ergodic
`T_10`-invariant probabilities are mutually singular by Step 5, so `mu` and `nu` are
mutually singular.

Nevertheless every fixed finite depth sees positive overlap.  For the all-zero
cylinder `C(n,0)=[0,10^(-n))`,

```
mu(C(n,0))=2^(-n).
```

If the first `n+2` Bernoulli digits are zero, then

```
x <= sum_{j>=n+3}10^(-j)=10^(-(n+2))/9,
16*x < 10^(-n).
```

Hence

```
nu(C(n,0)) >= 2^(-(n+2)),
O_n(mu,nu) >= 2^(-(n+2))>0.
```

For every prescribed cutoff `N`, the one constant `delta_N=2^(-(N+2))` passes all
tests `1<=n<=N`.  But mutual singularity and the approximation argument of Step 4
imply `O_n(mu,nu)` decreases to zero.  Thus no finite list of overlap tests supplies
the one all-depth `delta` in H5-H6.

## 6. Counterexample: an empirical limit need not be ergodic

This example is also not about pi.  Define one fixed nonterminating decimal seed by
the digit sequence

```
d = 0^1 1^1 0^2 1^2 0^3 1^3 ...
```

or explicitly

```
x = sum_{k>=1} sum_{n=k^2+1}^{k(k+1)} 10^(-n).
```

Let

```
E_N=(1/N)*sum_{j=0}^{N-1} delta_(T_10^j x).
```

The first `m` complete stages have length `m(m+1)` and contain equally many zeros
and ones.  A partial stage changes this balance by at most `m=O(sqrt(N))`.  Up to
stage `m` there are at most `2m` symbol transitions.  For each fixed word length
`r`, only `O(r*m)=o(N)` starting positions are within `r-1` places of a transition.
Consequently the limiting frequency of `0^r` is `1/2`, that of `1^r` is `1/2`, and
every mixed length-`r` word has limiting frequency zero.

Cylinder functions are dense in the continuous functions on `{0,1}^N`.  Passing
through the continuous decimal coding gives

```
E_N weak-* converges to eta=(1/2)*delta_0+(1/2)*delta_(1/9).
```

Both 0 and 1/9 are fixed by `T_10`, so `eta` is invariant.  It is not ergodic:
the invariant set `{0}` has `eta`-measure `1/2`.  Therefore invariance of an
empirical weak limit does not imply ergodicity.  For general weak limits there is
an additional boundary warning: indicators of half-open decimal cylinders are not
weak-* continuous when the limit charges their endpoints.

## 7. Counterexample: component selection can destroy overlap

This is an abstract commuting-system counterexample, not a circle or pi example.  It
isolates the invalid component-selection inference.

Let

```
X={0,1}^Z x {0,1},
T(omega,i)=(shift(omega),i),
S(omega,i)=(omega,1-i).
```

Then `T S=S T`.  Let `beta` be the fair two-sided Bernoulli measure, put

```
mu_0=beta x delta_0,
mu_1=beta x delta_1,
mu=(mu_0+mu_1)/2.
```

The measure `mu` is `T`-invariant but not `T`-ergodic.  Before selecting a component,

```
S_*mu=mu,
```

so every possible finite or all-depth overlap coefficient equals one.  Each `mu_i`
is a `T`-ergodic component and has entropy `log 2>0`.  But

```
S_*mu_0=mu_1,
mu_0({i=0})=1,
mu_1({i=0})=0.
```

Thus `mu_0` and `S_*mu_0` are mutually singular.  Even exact equality with a
commuting pushforward at the nonergodic level need not survive selection of a
positive-entropy ergodic component.  A valid pi argument must establish overlap for
the same ergodic component to which rigidity is applied.

## 8. Frontier and explicit nonclaims

The valid reduction frontier is exactly H1-H6.  In particular:

1. An empirical orbit measure is automatically a probability, and any weak cluster
   point is `T_10`-invariant, but it need not be ergodic.
2. Positive topological entropy of an orbit closure can produce some
   positive-metric-entropy ergodic measure through the variational principle, but it
   does not transfer an overlap property to that selected component.
3. Positive overlap at each separately tested finite depth does not produce one
   depth-independent positive constant.
4. The overlap coefficient gives non-mutual-singularity.  Equality, invariance, and
   nonsingularity under `T_16` arise only after the common-map ergodicity argument.
5. Positive entropy is indispensable for rigidity: `delta_0` is invariant under
   both multiplication maps and has perfect overlap with its pushforward, but it is
   not Lebesgue and has zero entropy.
6. No empirical Renyi bound is used or proved.  No finite digit computation, finite
   overlap test, or empirical entropy estimate proves H1-H6 for pi.
7. Accordingly, this note does not prove C1, C6, normality, disjunctivity, or any
   previously unknown fact about pi.  It proves only the displayed conditional
   reduction, subject to the pinned rigidity theorem.

## 9. Literature search log

| Date | Source/query | Finding |
|---|---|---|
| 2026-07-24 | Rudolph DOI `10.1017/S0143385700005629` | Complete primary PDF retrieved; Abstract, Theorem 4.9, and Corollary 4.11 checked. |
| 2026-07-24 | Johnson DOI `10.1007/BF02808018` | Publisher abstract gives the complete nonlacunary positive-entropy conclusion; PDF endpoint returned paywall HTML. |
| 2026-07-24 | Furstenberg DOI `10.1007/BF01692494` | Definition IV.1 pins "nonlacunary" on printed/PDF page 47. |

## 10. Reproducibility

From a directory containing only these delivered artifacts, run:

```bash
bash verify.sh
```

The script verifies all pinned bytes and searches extracted source text for every
theorem/definition locator used above.
